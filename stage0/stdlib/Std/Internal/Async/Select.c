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
lean_object* v___x_189_; 
v___x_189_ = l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_match__1_splitter___redArg(v_x_187_, v_h__1_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt___redArg(lean_object* v_xs_190_, lean_object* v_gen_191_){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_unsigned_to_nat(0u);
v___x_193_ = l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go___redArg(v_xs_190_, v_gen_191_, v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt(lean_object* v_00_u03b1_194_, lean_object* v_xs_195_, lean_object* v_gen_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt___redArg(v_xs_195_, v_gen_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg(lean_object* v_e_198_){
_start:
{
if (lean_obj_tag(v_e_198_) == 0)
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_209_; 
v_a_200_ = lean_ctor_get(v_e_198_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v_e_198_);
if (v_isSharedCheck_209_ == 0)
{
v___x_202_ = v_e_198_;
v_isShared_203_ = v_isSharedCheck_209_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v_e_198_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_209_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_207_; 
v___x_204_ = lean_io_error_to_string(v_a_200_);
v___x_205_ = lean_mk_io_user_error(v___x_204_);
if (v_isShared_203_ == 0)
{
lean_ctor_set_tag(v___x_202_, 1);
lean_ctor_set(v___x_202_, 0, v___x_205_);
v___x_207_ = v___x_202_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_205_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
else
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
v_a_210_ = lean_ctor_get(v_e_198_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v_e_198_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v_e_198_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v_e_198_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
lean_ctor_set_tag(v___x_212_, 0);
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg___boxed(lean_object* v_e_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg(v_e_218_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1(lean_object* v_00_u03b1_221_, lean_object* v_e_222_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg(v_e_222_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___boxed(lean_object* v_00_u03b1_225_, lean_object* v_e_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1(v_00_u03b1_225_, v_e_226_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__0(lean_object* v___x_229_, lean_object* v_x_230_){
_start:
{
if (lean_obj_tag(v_x_230_) == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_mk_io_user_error(v___x_229_);
v___x_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
return v___x_232_;
}
else
{
lean_object* v_val_233_; 
lean_dec_ref(v___x_229_);
v_val_233_ = lean_ctor_get(v_x_230_, 0);
lean_inc(v_val_233_);
return v_val_233_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__0___boxed(lean_object* v___x_234_, lean_object* v_x_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__0(v___x_234_, v_x_235_);
lean_dec(v_x_235_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__1(lean_object* v___f_237_, uint8_t v___x_238_, lean_object* v_x_239_){
_start:
{
if (lean_obj_tag(v_x_239_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_249_; 
lean_dec_ref(v___f_237_);
v_a_241_ = lean_ctor_get(v_x_239_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v_x_239_);
if (v_isSharedCheck_249_ == 0)
{
v___x_243_ = v_x_239_;
v_isShared_244_ = v_isSharedCheck_249_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v_x_239_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_249_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_244_ == 0)
{
v___x_246_ = v___x_243_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_241_);
v___x_246_ = v_reuseFailAlloc_248_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_247_; 
v___x_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
return v___x_247_;
}
}
}
else
{
lean_object* v_a_250_; 
v_a_250_ = lean_ctor_get(v_x_239_, 0);
lean_inc(v_a_250_);
lean_dec_ref(v_x_239_);
if (lean_obj_tag(v_a_250_) == 0)
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_259_; 
lean_dec_ref(v___f_237_);
v_a_251_ = lean_ctor_get(v_a_250_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v_a_250_);
if (v_isSharedCheck_259_ == 0)
{
v___x_253_ = v_a_250_;
v_isShared_254_ = v_isSharedCheck_259_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v_a_250_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_259_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_251_);
v___x_256_ = v_reuseFailAlloc_258_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_257_; 
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
return v___x_257_;
}
}
}
else
{
lean_object* v_a_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_a_260_ = lean_ctor_get(v_a_250_, 0);
lean_inc(v_a_260_);
lean_dec_ref(v_a_250_);
v___x_261_ = lean_io_promise_result_opt(v_a_260_);
lean_dec(v_a_260_);
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_task_map(v___f_237_, v___x_261_, v___x_262_, v___x_238_);
v___x_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
return v___x_264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__1___boxed(lean_object* v___f_265_, lean_object* v___x_266_, lean_object* v_x_267_, lean_object* v___y_268_){
_start:
{
uint8_t v___x_7692__boxed_269_; lean_object* v_res_270_; 
v___x_7692__boxed_269_ = lean_unbox(v___x_266_);
v_res_270_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__1(v___f_265_, v___x_7692__boxed_269_, v_x_267_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2(uint8_t v___x_274_, lean_object* v_x_275_, lean_object* v_x_276_){
_start:
{
if (lean_obj_tag(v_x_276_) == 0)
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_286_; 
lean_dec_ref(v_x_275_);
v_a_278_ = lean_ctor_get(v_x_276_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v_x_276_);
if (v_isSharedCheck_286_ == 0)
{
v___x_280_ = v_x_276_;
v_isShared_281_ = v_isSharedCheck_286_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v_x_276_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_286_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_285_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_284_; 
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
return v___x_284_;
}
}
}
else
{
lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_299_; 
v_isSharedCheck_299_ = !lean_is_exclusive(v_x_276_);
if (v_isSharedCheck_299_ == 0)
{
lean_object* v_unused_300_; 
v_unused_300_ = lean_ctor_get(v_x_276_, 0);
lean_dec(v_unused_300_);
v___x_288_ = v_x_276_;
v_isShared_289_ = v_isSharedCheck_299_;
goto v_resetjp_287_;
}
else
{
lean_dec(v_x_276_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_299_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___f_290_; lean_object* v___x_291_; lean_object* v___f_292_; lean_object* v___x_294_; 
v___f_290_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___closed__1));
v___x_291_ = lean_box(v___x_274_);
v___f_292_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_292_, 0, v___f_290_);
lean_closure_set(v___f_292_, 1, v___x_291_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v_x_275_);
v___x_294_ = v___x_288_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_x_275_);
v___x_294_ = v_reuseFailAlloc_298_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
v___x_296_ = lean_unsigned_to_nat(0u);
v___x_297_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_296_, v___x_274_, v___x_295_, v___f_292_);
return v___x_297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___boxed(lean_object* v___x_301_, lean_object* v_x_302_, lean_object* v_x_303_, lean_object* v___y_304_){
_start:
{
uint8_t v___x_7757__boxed_305_; lean_object* v_res_306_; 
v___x_7757__boxed_305_ = lean_unbox(v___x_301_);
v_res_306_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2(v___x_7757__boxed_305_, v_x_302_, v_x_303_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__4(lean_object* v___x_307_, uint8_t v___x_308_, lean_object* v___f_309_, lean_object* v___f_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_val_314_; 
if (lean_obj_tag(v_a_311_) == 0)
{
lean_object* v___x_322_; lean_object* v___x_323_; 
lean_dec_ref(v___f_310_);
lean_dec_ref(v___f_309_);
v___x_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_307_);
v___x_323_ = lean_task_pure(v___x_322_);
return v___x_323_;
}
else
{
lean_object* v_val_324_; lean_object* v___x_325_; 
v_val_324_ = lean_ctor_get(v_a_311_, 0);
lean_inc(v_val_324_);
lean_dec_ref(v_a_311_);
v___x_325_ = l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg(v_val_324_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_325_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_325_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set_tag(v___x_328_, 1);
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
v_val_314_ = v___x_331_;
goto v___jp_313_;
}
}
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
v_a_334_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_325_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_325_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
lean_ctor_set_tag(v___x_336_, 0);
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
v_val_314_ = v___x_339_;
goto v___jp_313_;
}
}
}
}
v___jp_313_:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v_val_314_);
v___x_316_ = lean_unsigned_to_nat(0u);
v___x_317_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_316_, v___x_308_, v___x_315_, v___f_309_);
v___x_318_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_316_, v___x_308_, v___x_317_, v___f_310_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; lean_object* v___x_320_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_a_319_);
lean_dec_ref(v___x_318_);
v___x_320_ = lean_task_pure(v_a_319_);
return v___x_320_;
}
else
{
lean_object* v_a_321_; 
v_a_321_ = lean_ctor_get(v___x_318_, 0);
lean_inc_ref(v_a_321_);
lean_dec_ref(v___x_318_);
return v_a_321_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__4___boxed(lean_object* v___x_342_, lean_object* v___x_343_, lean_object* v___f_344_, lean_object* v___f_345_, lean_object* v_a_346_, lean_object* v___y_347_){
_start:
{
uint8_t v___x_7820__boxed_348_; lean_object* v_res_349_; 
v___x_7820__boxed_348_ = lean_unbox(v___x_343_);
v_res_349_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__4(v___x_342_, v___x_7820__boxed_348_, v___f_344_, v___f_345_, v_a_346_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__0(lean_object* v_a_350_, lean_object* v_x_351_){
_start:
{
if (lean_obj_tag(v_x_351_) == 0)
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_363_; 
v_a_353_ = lean_ctor_get(v_x_351_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v_x_351_);
if (v_isSharedCheck_363_ == 0)
{
v___x_355_ = v_x_351_;
v_isShared_356_ = v_isSharedCheck_363_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v_x_351_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_363_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_362_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = lean_io_promise_resolve(v___x_358_, v_a_350_);
v___x_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
v___x_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
return v___x_361_;
}
}
}
else
{
lean_object* v___x_364_; 
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v_x_351_);
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__0___boxed(lean_object* v_a_365_, lean_object* v_x_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__0(v_a_365_, v_x_366_);
lean_dec(v_a_365_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__0(lean_object* v___x_369_, lean_object* v_x_370_){
_start:
{
if (lean_obj_tag(v_x_370_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_380_; 
v_a_372_ = lean_ctor_get(v_x_370_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v_x_370_);
if (v_isSharedCheck_380_ == 0)
{
v___x_374_ = v_x_370_;
v_isShared_375_ = v_isSharedCheck_380_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v_x_370_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_380_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_379_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_378_; 
v___x_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
return v___x_378_;
}
}
}
else
{
lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_389_; 
v_isSharedCheck_389_ = !lean_is_exclusive(v_x_370_);
if (v_isSharedCheck_389_ == 0)
{
lean_object* v_unused_390_; 
v_unused_390_ = lean_ctor_get(v_x_370_, 0);
lean_dec(v_unused_390_);
v___x_382_ = v_x_370_;
v_isShared_383_ = v_isSharedCheck_389_;
goto v_resetjp_381_;
}
else
{
lean_dec(v_x_370_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_389_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_384_, 0, v___x_369_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_384_);
v___x_386_ = v___x_382_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_384_);
v___x_386_ = v_reuseFailAlloc_388_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v___x_387_; 
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__0___boxed(lean_object* v___x_391_, lean_object* v_x_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__0(v___x_391_, v_x_392_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__3(lean_object* v_a_395_, lean_object* v_a_396_, uint8_t v___x_397_, lean_object* v___f_398_, lean_object* v_x_399_){
_start:
{
if (lean_obj_tag(v_x_399_) == 0)
{
lean_object* v___x_401_; 
lean_dec_ref(v___f_398_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
v___x_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_401_, 0, v_x_399_);
return v___x_401_;
}
else
{
lean_object* v_cont_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
lean_dec_ref(v_x_399_);
v_cont_402_ = lean_ctor_get(v_a_395_, 1);
lean_inc_ref(v_cont_402_);
lean_dec_ref(v_a_395_);
v___x_403_ = lean_apply_2(v_cont_402_, v_a_396_, lean_box(0));
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_404_, v___x_397_, v___x_403_, v___f_398_);
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__3___boxed(lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v___x_408_, lean_object* v___f_409_, lean_object* v_x_410_, lean_object* v___y_411_){
_start:
{
uint8_t v___x_7975__boxed_412_; lean_object* v_res_413_; 
v___x_7975__boxed_412_ = lean_unbox(v___x_408_);
v_res_413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__3(v_a_406_, v_a_407_, v___x_7975__boxed_412_, v___f_409_, v_x_410_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__1___boxed(lean_object* v_i_416_, lean_object* v_as_417_, lean_object* v_sz_418_, lean_object* v_x_419_, lean_object* v___y_420_){
_start:
{
size_t v_i_boxed_421_; size_t v_sz_boxed_422_; lean_object* v_res_423_; 
v_i_boxed_421_ = lean_unbox_usize(v_i_416_);
lean_dec(v_i_416_);
v_sz_boxed_422_ = lean_unbox_usize(v_sz_418_);
lean_dec(v_sz_418_);
v_res_423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__1(v_i_boxed_421_, v_as_417_, v_sz_boxed_422_, v_x_419_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg(lean_object* v_as_424_, size_t v_sz_425_, size_t v_i_426_, lean_object* v_b_427_){
_start:
{
uint8_t v___x_429_; 
v___x_429_ = lean_usize_dec_lt(v_i_426_, v_sz_425_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; 
lean_dec_ref(v_as_424_);
v___x_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_430_, 0, v_b_427_);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
return v___x_431_;
}
else
{
lean_object* v_a_432_; lean_object* v_selector_433_; lean_object* v_unregisterFn_434_; lean_object* v___x_435_; lean_object* v___f_436_; lean_object* v___x_437_; uint8_t v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___f_442_; lean_object* v___x_443_; 
v_a_432_ = lean_array_uget_borrowed(v_as_424_, v_i_426_);
v_selector_433_ = lean_ctor_get(v_a_432_, 0);
v_unregisterFn_434_ = lean_ctor_get(v_selector_433_, 2);
lean_inc_ref(v_unregisterFn_434_);
v___x_435_ = lean_apply_1(v_unregisterFn_434_, lean_box(0));
v___f_436_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___closed__0));
v___x_437_ = lean_unsigned_to_nat(0u);
v___x_438_ = 0;
v___x_439_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_437_, v___x_438_, v___x_435_, v___f_436_);
v___x_440_ = lean_box_usize(v_i_426_);
v___x_441_ = lean_box_usize(v_sz_425_);
v___f_442_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_442_, 0, v___x_440_);
lean_closure_set(v___f_442_, 1, v_as_424_);
lean_closure_set(v___f_442_, 2, v___x_441_);
v___x_443_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_437_, v___x_438_, v___x_439_, v___f_442_);
return v___x_443_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__1(size_t v_i_444_, lean_object* v_as_445_, size_t v_sz_446_, lean_object* v_x_447_){
_start:
{
if (lean_obj_tag(v_x_447_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_457_; 
lean_dec_ref(v_as_445_);
v_a_449_ = lean_ctor_get(v_x_447_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v_x_447_);
if (v_isSharedCheck_457_ == 0)
{
v___x_451_ = v_x_447_;
v_isShared_452_ = v_isSharedCheck_457_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v_x_447_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_457_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_456_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_455_; 
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
}
}
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_477_; 
v_a_458_ = lean_ctor_get(v_x_447_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v_x_447_);
if (v_isSharedCheck_477_ == 0)
{
v___x_460_ = v_x_447_;
v_isShared_461_ = v_isSharedCheck_477_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v_x_447_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_477_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
if (lean_obj_tag(v_a_458_) == 0)
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_472_; 
lean_dec_ref(v_as_445_);
v_a_462_ = lean_ctor_get(v_a_458_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v_a_458_);
if (v_isSharedCheck_472_ == 0)
{
v___x_464_ = v_a_458_;
v_isShared_465_ = v_isSharedCheck_472_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v_a_458_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_472_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v_a_462_);
v___x_467_ = v___x_460_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_471_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v___x_469_; 
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_467_);
v___x_469_ = v___x_464_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
else
{
lean_object* v_a_473_; size_t v___x_474_; size_t v___x_475_; lean_object* v___x_476_; 
lean_del_object(v___x_460_);
v_a_473_ = lean_ctor_get(v_a_458_, 0);
lean_inc(v_a_473_);
lean_dec_ref(v_a_458_);
v___x_474_ = ((size_t)1ULL);
v___x_475_ = lean_usize_add(v_i_444_, v___x_474_);
v___x_476_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg(v_as_445_, v_sz_446_, v___x_475_, v_a_473_);
return v___x_476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___boxed(lean_object* v_as_478_, lean_object* v_sz_479_, lean_object* v_i_480_, lean_object* v_b_481_, lean_object* v___y_482_){
_start:
{
size_t v_sz_boxed_483_; size_t v_i_boxed_484_; lean_object* v_res_485_; 
v_sz_boxed_483_ = lean_unbox_usize(v_sz_479_);
lean_dec(v_sz_479_);
v_i_boxed_484_ = lean_unbox_usize(v_i_480_);
lean_dec(v_i_480_);
v_res_485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg(v_as_478_, v_sz_boxed_483_, v_i_boxed_484_, v_b_481_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__2(lean_object* v___x_486_, lean_object* v___x_487_, lean_object* v_a_488_, uint8_t v___x_489_, lean_object* v___f_490_, lean_object* v_x_491_){
_start:
{
if (lean_obj_tag(v_x_491_) == 0)
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_501_; 
lean_dec_ref(v___f_490_);
lean_dec_ref(v_a_488_);
lean_dec_ref(v___x_486_);
v_a_493_ = lean_ctor_get(v_x_491_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v_x_491_);
if (v_isSharedCheck_501_ == 0)
{
v___x_495_ = v_x_491_;
v_isShared_496_ = v_isSharedCheck_501_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v_x_491_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_501_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_500_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_499_; 
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
}
}
else
{
lean_object* v_a_502_; size_t v_sz_503_; size_t v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___f_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v_a_502_ = lean_ctor_get(v_x_491_, 0);
lean_inc(v_a_502_);
lean_dec_ref(v_x_491_);
v_sz_503_ = lean_array_size(v___x_486_);
v___x_504_ = ((size_t)0ULL);
v___x_505_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg(v___x_486_, v_sz_503_, v___x_504_, v___x_487_);
v___x_506_ = lean_box(v___x_489_);
v___f_507_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_507_, 0, v_a_488_);
lean_closure_set(v___f_507_, 1, v_a_502_);
lean_closure_set(v___f_507_, 2, v___x_506_);
lean_closure_set(v___f_507_, 3, v___f_490_);
v___x_508_ = lean_unsigned_to_nat(0u);
v___x_509_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_508_, v___x_489_, v___x_505_, v___f_507_);
return v___x_509_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__2___boxed(lean_object* v___x_510_, lean_object* v___x_511_, lean_object* v_a_512_, lean_object* v___x_513_, lean_object* v___f_514_, lean_object* v_x_515_, lean_object* v___y_516_){
_start:
{
uint8_t v___x_8097__boxed_517_; lean_object* v_res_518_; 
v___x_8097__boxed_517_ = lean_unbox(v___x_513_);
v_res_518_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__2(v___x_510_, v___x_511_, v_a_512_, v___x_8097__boxed_517_, v___f_514_, v_x_515_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__1(lean_object* v_a_519_, lean_object* v_x_520_){
_start:
{
if (lean_obj_tag(v_x_520_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_530_; 
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
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_531_ = lean_io_promise_resolve(v_x_520_, v_a_519_);
v___x_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
return v___x_533_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__1___boxed(lean_object* v_a_534_, lean_object* v_x_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__1(v_a_534_, v_x_535_);
lean_dec(v_a_534_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__5(lean_object* v_a_538_, lean_object* v___f_539_, uint8_t v___x_540_, lean_object* v___x_541_, lean_object* v___f_542_, lean_object* v_x_543_){
_start:
{
if (lean_obj_tag(v_x_543_) == 0)
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_553_; 
lean_dec_ref(v___f_542_);
lean_dec_ref(v___f_539_);
v_a_545_ = lean_ctor_get(v_x_543_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v_x_543_);
if (v_isSharedCheck_553_ == 0)
{
v___x_547_ = v_x_543_;
v_isShared_548_ = v_isSharedCheck_553_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v_x_543_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_553_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_552_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_551_; 
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
}
}
else
{
lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_565_; 
v_isSharedCheck_565_ = !lean_is_exclusive(v_x_543_);
if (v_isSharedCheck_565_ == 0)
{
lean_object* v_unused_566_; 
v_unused_566_ = lean_ctor_get(v_x_543_, 0);
lean_dec(v_unused_566_);
v___x_555_ = v_x_543_;
v_isShared_556_ = v_isSharedCheck_565_;
goto v_resetjp_554_;
}
else
{
lean_dec(v_x_543_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_565_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_557_ = lean_io_promise_result_opt(v_a_538_);
v___x_558_ = lean_unsigned_to_nat(0u);
v___x_559_ = lean_io_bind_task(v___x_557_, v___f_539_, v___x_558_, v___x_540_);
lean_dec_ref(v___x_559_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v___x_541_);
v___x_561_ = v___x_555_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_541_);
v___x_561_ = v_reuseFailAlloc_564_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
v___x_563_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_558_, v___x_540_, v___x_562_, v___f_542_);
return v___x_563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__5___boxed(lean_object* v_a_567_, lean_object* v___f_568_, lean_object* v___x_569_, lean_object* v___x_570_, lean_object* v___f_571_, lean_object* v_x_572_, lean_object* v___y_573_){
_start:
{
uint8_t v___x_8181__boxed_574_; lean_object* v_res_575_; 
v___x_8181__boxed_574_ = lean_unbox(v___x_569_);
v_res_575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__5(v_a_567_, v___f_568_, v___x_8181__boxed_574_, v___x_570_, v___f_571_, v_x_572_);
lean_dec(v_a_567_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__6(lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v___f_578_, uint8_t v___x_579_, lean_object* v___x_580_, lean_object* v___f_581_, lean_object* v_x_582_){
_start:
{
if (lean_obj_tag(v_x_582_) == 0)
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_592_; 
lean_dec_ref(v___f_581_);
lean_dec_ref(v___f_578_);
lean_dec(v_a_577_);
lean_dec_ref(v_a_576_);
v_a_584_ = lean_ctor_get(v_x_582_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v_x_582_);
if (v_isSharedCheck_592_ == 0)
{
v___x_586_ = v_x_582_;
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v_x_582_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_584_);
v___x_589_ = v_reuseFailAlloc_591_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_590_; 
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
return v___x_590_;
}
}
}
else
{
lean_object* v_selector_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_607_; 
v_selector_593_ = lean_ctor_get(v_a_576_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v_a_576_);
if (v_isSharedCheck_607_ == 0)
{
lean_object* v_unused_608_; 
v_unused_608_ = lean_ctor_get(v_a_576_, 1);
lean_dec(v_unused_608_);
v___x_595_ = v_a_576_;
v_isShared_596_ = v_isSharedCheck_607_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_selector_593_);
lean_dec(v_a_576_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_607_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v_a_597_; lean_object* v_registerFn_598_; lean_object* v___x_600_; 
v_a_597_ = lean_ctor_get(v_x_582_, 0);
lean_inc(v_a_597_);
lean_dec_ref(v_x_582_);
v_registerFn_598_ = lean_ctor_get(v_selector_593_, 1);
lean_inc_ref(v_registerFn_598_);
lean_dec_ref(v_selector_593_);
lean_inc(v_a_597_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 1, v_a_597_);
lean_ctor_set(v___x_595_, 0, v_a_577_);
v___x_600_ = v___x_595_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_577_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_a_597_);
v___x_600_ = v_reuseFailAlloc_606_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___f_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_601_ = lean_apply_2(v_registerFn_598_, v___x_600_, lean_box(0));
v___x_602_ = lean_box(v___x_579_);
v___f_603_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__5___boxed), 7, 5);
lean_closure_set(v___f_603_, 0, v_a_597_);
lean_closure_set(v___f_603_, 1, v___f_578_);
lean_closure_set(v___f_603_, 2, v___x_602_);
lean_closure_set(v___f_603_, 3, v___x_580_);
lean_closure_set(v___f_603_, 4, v___f_581_);
v___x_604_ = lean_unsigned_to_nat(0u);
v___x_605_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_604_, v___x_579_, v___x_601_, v___f_603_);
return v___x_605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__6___boxed(lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v___f_611_, lean_object* v___x_612_, lean_object* v___x_613_, lean_object* v___f_614_, lean_object* v_x_615_, lean_object* v___y_616_){
_start:
{
uint8_t v___x_8247__boxed_617_; lean_object* v_res_618_; 
v___x_8247__boxed_617_ = lean_unbox(v___x_612_);
v_res_618_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__6(v_a_609_, v_a_610_, v___f_611_, v___x_8247__boxed_617_, v___x_613_, v___f_614_, v_x_615_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__7___boxed(lean_object* v_i_619_, lean_object* v_a_620_, lean_object* v___x_621_, lean_object* v_a_622_, lean_object* v_as_623_, lean_object* v_sz_624_, lean_object* v_x_625_, lean_object* v___y_626_){
_start:
{
size_t v_i_boxed_627_; size_t v_sz_boxed_628_; lean_object* v_res_629_; 
v_i_boxed_627_ = lean_unbox_usize(v_i_619_);
lean_dec(v_i_619_);
v_sz_boxed_628_ = lean_unbox_usize(v_sz_624_);
lean_dec(v_sz_624_);
v_res_629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__7(v_i_boxed_627_, v_a_620_, v___x_621_, v_a_622_, v_as_623_, v_sz_boxed_628_, v_x_625_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg(lean_object* v_a_630_, lean_object* v___x_631_, lean_object* v_a_632_, lean_object* v_as_633_, size_t v_sz_634_, size_t v_i_635_, lean_object* v_b_636_){
_start:
{
uint8_t v___x_638_; 
v___x_638_ = lean_usize_dec_lt(v_i_635_, v_sz_634_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; 
lean_dec_ref(v_as_633_);
lean_dec(v_a_632_);
lean_dec_ref(v___x_631_);
lean_dec(v_a_630_);
v___x_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_639_, 0, v_b_636_);
v___x_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
return v___x_640_;
}
else
{
lean_object* v___x_641_; lean_object* v___f_642_; lean_object* v___f_643_; lean_object* v___x_644_; lean_object* v___f_645_; uint8_t v___x_646_; lean_object* v_a_647_; lean_object* v___x_648_; lean_object* v___f_649_; lean_object* v___x_650_; lean_object* v___f_651_; lean_object* v___x_652_; lean_object* v___f_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___f_660_; lean_object* v___x_661_; 
v___x_641_ = lean_io_promise_new();
lean_inc(v_a_630_);
v___f_642_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_642_, 0, v_a_630_);
lean_inc(v_a_630_);
v___f_643_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_643_, 0, v_a_630_);
v___x_644_ = lean_box(0);
v___f_645_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___closed__0));
v___x_646_ = 0;
v_a_647_ = lean_array_uget_borrowed(v_as_633_, v_i_635_);
v___x_648_ = lean_box(v___x_646_);
lean_inc(v_a_647_);
lean_inc_ref(v___x_631_);
v___f_649_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__2___boxed), 7, 5);
lean_closure_set(v___f_649_, 0, v___x_631_);
lean_closure_set(v___f_649_, 1, v___x_644_);
lean_closure_set(v___f_649_, 2, v_a_647_);
lean_closure_set(v___f_649_, 3, v___x_648_);
lean_closure_set(v___f_649_, 4, v___f_643_);
v___x_650_ = lean_box(v___x_646_);
v___f_651_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_651_, 0, v___x_644_);
lean_closure_set(v___f_651_, 1, v___x_650_);
lean_closure_set(v___f_651_, 2, v___f_649_);
lean_closure_set(v___f_651_, 3, v___f_642_);
v___x_652_ = lean_box(v___x_646_);
lean_inc(v_a_632_);
lean_inc(v_a_647_);
v___f_653_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__6___boxed), 8, 6);
lean_closure_set(v___f_653_, 0, v_a_647_);
lean_closure_set(v___f_653_, 1, v_a_632_);
lean_closure_set(v___f_653_, 2, v___f_651_);
lean_closure_set(v___f_653_, 3, v___x_652_);
lean_closure_set(v___f_653_, 4, v___x_644_);
lean_closure_set(v___f_653_, 5, v___f_645_);
v___x_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_654_, 0, v___x_641_);
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_656_, v___x_646_, v___x_655_, v___f_653_);
v___x_658_ = lean_box_usize(v_i_635_);
v___x_659_ = lean_box_usize(v_sz_634_);
v___f_660_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__7___boxed), 8, 6);
lean_closure_set(v___f_660_, 0, v___x_658_);
lean_closure_set(v___f_660_, 1, v_a_630_);
lean_closure_set(v___f_660_, 2, v___x_631_);
lean_closure_set(v___f_660_, 3, v_a_632_);
lean_closure_set(v___f_660_, 4, v_as_633_);
lean_closure_set(v___f_660_, 5, v___x_659_);
v___x_661_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_656_, v___x_646_, v___x_657_, v___f_660_);
return v___x_661_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__7(size_t v_i_662_, lean_object* v_a_663_, lean_object* v___x_664_, lean_object* v_a_665_, lean_object* v_as_666_, size_t v_sz_667_, lean_object* v_x_668_){
_start:
{
if (lean_obj_tag(v_x_668_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_678_; 
lean_dec_ref(v_as_666_);
lean_dec(v_a_665_);
lean_dec_ref(v___x_664_);
lean_dec(v_a_663_);
v_a_670_ = lean_ctor_get(v_x_668_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v_x_668_);
if (v_isSharedCheck_678_ == 0)
{
v___x_672_ = v_x_668_;
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v_x_668_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_677_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_676_; 
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_698_; 
v_a_679_ = lean_ctor_get(v_x_668_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v_x_668_);
if (v_isSharedCheck_698_ == 0)
{
v___x_681_ = v_x_668_;
v_isShared_682_ = v_isSharedCheck_698_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v_x_668_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_698_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
if (lean_obj_tag(v_a_679_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_693_; 
lean_dec_ref(v_as_666_);
lean_dec(v_a_665_);
lean_dec_ref(v___x_664_);
lean_dec(v_a_663_);
v_a_683_ = lean_ctor_get(v_a_679_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v_a_679_);
if (v_isSharedCheck_693_ == 0)
{
v___x_685_ = v_a_679_;
v_isShared_686_ = v_isSharedCheck_693_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v_a_679_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_693_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v_a_683_);
v___x_688_ = v___x_681_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_692_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_690_; 
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 0, v___x_688_);
v___x_690_ = v___x_685_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
else
{
lean_object* v_a_694_; size_t v___x_695_; size_t v___x_696_; lean_object* v___x_697_; 
lean_del_object(v___x_681_);
v_a_694_ = lean_ctor_get(v_a_679_, 0);
lean_inc(v_a_694_);
lean_dec_ref(v_a_679_);
v___x_695_ = ((size_t)1ULL);
v___x_696_ = lean_usize_add(v_i_662_, v___x_695_);
v___x_697_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg(v_a_663_, v___x_664_, v_a_665_, v_as_666_, v_sz_667_, v___x_696_, v_a_694_);
return v___x_697_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___boxed(lean_object* v_a_699_, lean_object* v___x_700_, lean_object* v_a_701_, lean_object* v_as_702_, lean_object* v_sz_703_, lean_object* v_i_704_, lean_object* v_b_705_, lean_object* v___y_706_){
_start:
{
size_t v_sz_boxed_707_; size_t v_i_boxed_708_; lean_object* v_res_709_; 
v_sz_boxed_707_ = lean_unbox_usize(v_sz_703_);
lean_dec(v_sz_703_);
v_i_boxed_708_ = lean_unbox_usize(v_i_704_);
lean_dec(v_i_704_);
v_res_709_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg(v_a_699_, v___x_700_, v_a_701_, v_as_702_, v_sz_boxed_707_, v_i_boxed_708_, v_b_705_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__3(lean_object* v___x_710_, lean_object* v_a_711_, lean_object* v___x_712_, uint8_t v___x_713_, lean_object* v_x_714_){
_start:
{
if (lean_obj_tag(v_x_714_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_724_; 
lean_dec(v_a_711_);
lean_dec_ref(v___x_710_);
v_a_716_ = lean_ctor_get(v_x_714_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v_x_714_);
if (v_isSharedCheck_724_ == 0)
{
v___x_718_ = v_x_714_;
v_isShared_719_ = v_isSharedCheck_724_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v_x_714_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_724_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_716_);
v___x_721_ = v_reuseFailAlloc_723_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_722_; 
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
return v___x_722_;
}
}
}
else
{
lean_object* v_a_725_; size_t v_sz_726_; size_t v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___f_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v_a_725_ = lean_ctor_get(v_x_714_, 0);
v_sz_726_ = lean_array_size(v___x_710_);
v___x_727_ = ((size_t)0ULL);
lean_inc_ref(v___x_710_);
lean_inc(v_a_725_);
v___x_728_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg(v_a_725_, v___x_710_, v_a_711_, v___x_710_, v_sz_726_, v___x_727_, v___x_712_);
v___x_729_ = lean_box(v___x_713_);
v___f_730_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_730_, 0, v___x_729_);
lean_closure_set(v___f_730_, 1, v_x_714_);
v___x_731_ = lean_unsigned_to_nat(0u);
v___x_732_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_731_, v___x_713_, v___x_728_, v___f_730_);
return v___x_732_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__3___boxed(lean_object* v___x_733_, lean_object* v_a_734_, lean_object* v___x_735_, lean_object* v___x_736_, lean_object* v_x_737_, lean_object* v___y_738_){
_start:
{
uint8_t v___x_8448__boxed_739_; lean_object* v_res_740_; 
v___x_8448__boxed_739_ = lean_unbox(v___x_736_);
v_res_740_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__3(v___x_733_, v_a_734_, v___x_735_, v___x_8448__boxed_739_, v_x_737_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__4(lean_object* v___x_741_, lean_object* v___x_742_, uint8_t v___x_743_, lean_object* v_x_744_){
_start:
{
if (lean_obj_tag(v_x_744_) == 0)
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_754_; 
lean_dec_ref(v___x_741_);
v_a_746_ = lean_ctor_get(v_x_744_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v_x_744_);
if (v_isSharedCheck_754_ == 0)
{
v___x_748_ = v_x_744_;
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v_x_744_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_753_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_752_; 
v___x_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
return v___x_752_;
}
}
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_768_; 
v_a_755_ = lean_ctor_get(v_x_744_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v_x_744_);
if (v_isSharedCheck_768_ == 0)
{
v___x_757_ = v_x_744_;
v_isShared_758_ = v_isSharedCheck_768_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v_x_744_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_768_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___f_761_; lean_object* v___x_763_; 
v___x_759_ = lean_io_promise_new();
v___x_760_ = lean_box(v___x_743_);
v___f_761_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_761_, 0, v___x_741_);
lean_closure_set(v___f_761_, 1, v_a_755_);
lean_closure_set(v___f_761_, 2, v___x_742_);
lean_closure_set(v___f_761_, 3, v___x_760_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v___x_759_);
v___x_763_ = v___x_757_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_759_);
v___x_763_ = v_reuseFailAlloc_767_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
v___x_765_ = lean_unsigned_to_nat(0u);
v___x_766_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_765_, v___x_743_, v___x_764_, v___f_761_);
return v___x_766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__4___boxed(lean_object* v___x_769_, lean_object* v___x_770_, lean_object* v___x_771_, lean_object* v_x_772_, lean_object* v___y_773_){
_start:
{
uint8_t v___x_8497__boxed_774_; lean_object* v_res_775_; 
v___x_8497__boxed_774_ = lean_unbox(v___x_771_);
v_res_775_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__4(v___x_769_, v___x_770_, v___x_8497__boxed_774_, v_x_772_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__5(lean_object* v___x_776_, lean_object* v___x_777_, lean_object* v_x_778_){
_start:
{
if (lean_obj_tag(v_x_778_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_788_; 
lean_dec_ref(v___x_776_);
v_a_780_ = lean_ctor_get(v_x_778_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v_x_778_);
if (v_isSharedCheck_788_ == 0)
{
v___x_782_ = v_x_778_;
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v_x_778_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_787_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_786_; 
v___x_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
return v___x_786_;
}
}
}
else
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_816_; 
v_a_789_ = lean_ctor_get(v_x_778_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v_x_778_);
if (v_isSharedCheck_816_ == 0)
{
v___x_791_ = v_x_778_;
v_isShared_792_ = v_isSharedCheck_816_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v_x_778_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_816_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v_fst_793_; 
v_fst_793_ = lean_ctor_get(v_a_789_, 0);
lean_inc(v_fst_793_);
lean_dec(v_a_789_);
if (lean_obj_tag(v_fst_793_) == 0)
{
uint8_t v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___f_798_; lean_object* v___x_800_; 
v___x_794_ = 0;
v___x_795_ = lean_box(v___x_794_);
v___x_796_ = lean_st_mk_ref(v___x_795_);
v___x_797_ = lean_box(v___x_794_);
v___f_798_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_798_, 0, v___x_776_);
lean_closure_set(v___f_798_, 1, v___x_777_);
lean_closure_set(v___f_798_, 2, v___x_797_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_796_);
v___x_800_ = v___x_791_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_796_);
v___x_800_ = v_reuseFailAlloc_804_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_802_, v___x_794_, v___x_801_, v___f_798_);
return v___x_803_;
}
}
else
{
lean_object* v_val_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_815_; 
lean_dec_ref(v___x_776_);
v_val_805_ = lean_ctor_get(v_fst_793_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v_fst_793_);
if (v_isSharedCheck_815_ == 0)
{
v___x_807_ = v_fst_793_;
v_isShared_808_ = v_isSharedCheck_815_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_val_805_);
lean_dec(v_fst_793_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_815_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v_val_805_);
v___x_810_ = v___x_791_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_val_805_);
v___x_810_ = v_reuseFailAlloc_814_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_812_; 
if (v_isShared_808_ == 0)
{
lean_ctor_set_tag(v___x_807_, 0);
lean_ctor_set(v___x_807_, 0, v___x_810_);
v___x_812_ = v___x_807_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_810_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__5___boxed(lean_object* v___x_817_, lean_object* v___x_818_, lean_object* v_x_819_, lean_object* v___y_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__5(v___x_817_, v___x_818_, v_x_819_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__0(lean_object* v___x_822_, lean_object* v_x_823_){
_start:
{
if (lean_obj_tag(v_x_823_) == 0)
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_833_; 
v_a_825_ = lean_ctor_get(v_x_823_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v_x_823_);
if (v_isSharedCheck_833_ == 0)
{
v___x_827_ = v_x_823_;
v_isShared_828_ = v_isSharedCheck_833_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v_x_823_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_833_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_832_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_831_; 
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
return v___x_831_;
}
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_845_; 
v_a_834_ = lean_ctor_get(v_x_823_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v_x_823_);
if (v_isSharedCheck_845_ == 0)
{
v___x_836_ = v_x_823_;
v_isShared_837_ = v_isSharedCheck_845_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v_x_823_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_845_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_842_; 
v___x_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_838_, 0, v_a_834_);
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
lean_ctor_set(v___x_839_, 1, v___x_822_);
v___x_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_840_);
v___x_842_ = v___x_836_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_840_);
v___x_842_ = v_reuseFailAlloc_844_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
lean_object* v___x_843_; 
v___x_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
return v___x_843_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__0___boxed(lean_object* v___x_846_, lean_object* v_x_847_, lean_object* v___y_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__0(v___x_846_, v_x_847_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__1(lean_object* v_a_850_, lean_object* v___f_851_, lean_object* v___x_852_, lean_object* v_x_853_){
_start:
{
if (lean_obj_tag(v_x_853_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_863_; 
lean_dec_ref(v___x_852_);
lean_dec_ref(v___f_851_);
lean_dec_ref(v_a_850_);
v_a_855_ = lean_ctor_get(v_x_853_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v_x_853_);
if (v_isSharedCheck_863_ == 0)
{
v___x_857_ = v_x_853_;
v_isShared_858_ = v_isSharedCheck_863_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v_x_853_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_863_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_862_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_861_; 
v___x_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
return v___x_861_;
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_879_; 
v_a_864_ = lean_ctor_get(v_x_853_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v_x_853_);
if (v_isSharedCheck_879_ == 0)
{
v___x_866_ = v_x_853_;
v_isShared_867_ = v_isSharedCheck_879_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v_x_853_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_879_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
if (lean_obj_tag(v_a_864_) == 1)
{
lean_object* v_val_868_; lean_object* v_cont_869_; lean_object* v___x_870_; lean_object* v___x_871_; uint8_t v___x_872_; lean_object* v___x_873_; 
lean_del_object(v___x_866_);
lean_dec_ref(v___x_852_);
v_val_868_ = lean_ctor_get(v_a_864_, 0);
lean_inc(v_val_868_);
lean_dec_ref(v_a_864_);
v_cont_869_ = lean_ctor_get(v_a_850_, 1);
lean_inc_ref(v_cont_869_);
lean_dec_ref(v_a_850_);
v___x_870_ = lean_apply_2(v_cont_869_, v_val_868_, lean_box(0));
v___x_871_ = lean_unsigned_to_nat(0u);
v___x_872_ = 0;
v___x_873_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_871_, v___x_872_, v___x_870_, v___f_851_);
return v___x_873_;
}
else
{
lean_object* v___x_874_; lean_object* v___x_876_; 
lean_dec(v_a_864_);
lean_dec_ref(v___f_851_);
lean_dec_ref(v_a_850_);
v___x_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_874_, 0, v___x_852_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_874_);
v___x_876_ = v___x_866_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_878_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_877_; 
v___x_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
return v___x_877_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__1___boxed(lean_object* v_a_880_, lean_object* v___f_881_, lean_object* v___x_882_, lean_object* v_x_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__1(v_a_880_, v___f_881_, v___x_882_, v_x_883_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__2___boxed(lean_object* v_i_891_, lean_object* v_as_892_, lean_object* v_sz_893_, lean_object* v_x_894_, lean_object* v___y_895_){
_start:
{
size_t v_i_boxed_896_; size_t v_sz_boxed_897_; lean_object* v_res_898_; 
v_i_boxed_896_ = lean_unbox_usize(v_i_891_);
lean_dec(v_i_891_);
v_sz_boxed_897_ = lean_unbox_usize(v_sz_893_);
lean_dec(v_sz_893_);
v_res_898_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__2(v_i_boxed_896_, v_as_892_, v_sz_boxed_897_, v_x_894_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg(lean_object* v_as_899_, size_t v_sz_900_, size_t v_i_901_, lean_object* v_b_902_){
_start:
{
uint8_t v___x_904_; 
v___x_904_ = lean_usize_dec_lt(v_i_901_, v_sz_900_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; 
lean_dec_ref(v_as_899_);
v___x_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_905_, 0, v_b_902_);
v___x_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
return v___x_906_;
}
else
{
lean_object* v_a_907_; lean_object* v_selector_908_; lean_object* v_tryFn_909_; lean_object* v___x_910_; lean_object* v___f_911_; lean_object* v___x_912_; lean_object* v___f_913_; lean_object* v___x_914_; uint8_t v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___f_919_; lean_object* v___x_920_; 
lean_dec_ref(v_b_902_);
v_a_907_ = lean_array_uget_borrowed(v_as_899_, v_i_901_);
v_selector_908_ = lean_ctor_get(v_a_907_, 0);
v_tryFn_909_ = lean_ctor_get(v_selector_908_, 0);
lean_inc_ref(v_tryFn_909_);
v___x_910_ = lean_apply_1(v_tryFn_909_, lean_box(0));
v___f_911_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__0));
v___x_912_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__1));
lean_inc(v_a_907_);
v___f_913_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_913_, 0, v_a_907_);
lean_closure_set(v___f_913_, 1, v___f_911_);
lean_closure_set(v___f_913_, 2, v___x_912_);
v___x_914_ = lean_unsigned_to_nat(0u);
v___x_915_ = 0;
v___x_916_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_914_, v___x_915_, v___x_910_, v___f_913_);
v___x_917_ = lean_box_usize(v_i_901_);
v___x_918_ = lean_box_usize(v_sz_900_);
v___f_919_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_919_, 0, v___x_917_);
lean_closure_set(v___f_919_, 1, v_as_899_);
lean_closure_set(v___f_919_, 2, v___x_918_);
v___x_920_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_914_, v___x_915_, v___x_916_, v___f_919_);
return v___x_920_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__2(size_t v_i_921_, lean_object* v_as_922_, size_t v_sz_923_, lean_object* v_x_924_){
_start:
{
if (lean_obj_tag(v_x_924_) == 0)
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_934_; 
lean_dec_ref(v_as_922_);
v_a_926_ = lean_ctor_get(v_x_924_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v_x_924_);
if (v_isSharedCheck_934_ == 0)
{
v___x_928_ = v_x_924_;
v_isShared_929_ = v_isSharedCheck_934_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v_x_924_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_934_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_933_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_932_; 
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
return v___x_932_;
}
}
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_954_; 
v_a_935_ = lean_ctor_get(v_x_924_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v_x_924_);
if (v_isSharedCheck_954_ == 0)
{
v___x_937_ = v_x_924_;
v_isShared_938_ = v_isSharedCheck_954_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v_x_924_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_954_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
if (lean_obj_tag(v_a_935_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_949_; 
lean_dec_ref(v_as_922_);
v_a_939_ = lean_ctor_get(v_a_935_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v_a_935_);
if (v_isSharedCheck_949_ == 0)
{
v___x_941_ = v_a_935_;
v_isShared_942_ = v_isSharedCheck_949_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v_a_935_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_949_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v_a_939_);
v___x_944_ = v___x_937_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_948_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_946_; 
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_944_);
v___x_946_ = v___x_941_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
else
{
lean_object* v_a_950_; size_t v___x_951_; size_t v___x_952_; lean_object* v___x_953_; 
lean_del_object(v___x_937_);
v_a_950_ = lean_ctor_get(v_a_935_, 0);
lean_inc(v_a_950_);
lean_dec_ref(v_a_935_);
v___x_951_ = ((size_t)1ULL);
v___x_952_ = lean_usize_add(v_i_921_, v___x_951_);
v___x_953_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg(v_as_922_, v_sz_923_, v___x_952_, v_a_950_);
return v___x_953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___boxed(lean_object* v_as_955_, lean_object* v_sz_956_, lean_object* v_i_957_, lean_object* v_b_958_, lean_object* v___y_959_){
_start:
{
size_t v_sz_boxed_960_; size_t v_i_boxed_961_; lean_object* v_res_962_; 
v_sz_boxed_960_ = lean_unbox_usize(v_sz_956_);
lean_dec(v_sz_956_);
v_i_boxed_961_ = lean_unbox_usize(v_i_957_);
lean_dec(v_i_957_);
v_res_962_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg(v_as_955_, v_sz_boxed_960_, v_i_boxed_961_, v_b_958_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__6(lean_object* v_selectables_963_, lean_object* v_x_964_){
_start:
{
if (lean_obj_tag(v_x_964_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_974_; 
lean_dec_ref(v_selectables_963_);
v_a_966_ = lean_ctor_get(v_x_964_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v_x_964_);
if (v_isSharedCheck_974_ == 0)
{
v___x_968_ = v_x_964_;
v_isShared_969_ = v_isSharedCheck_974_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v_x_964_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_974_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_973_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_object* v___x_972_; 
v___x_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
return v___x_972_;
}
}
}
else
{
lean_object* v_a_975_; uint64_t v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; size_t v_sz_982_; size_t v___x_983_; lean_object* v___x_984_; lean_object* v___f_985_; lean_object* v___x_986_; uint8_t v___x_987_; lean_object* v___x_988_; 
v_a_975_ = lean_ctor_get(v_x_964_, 0);
lean_inc(v_a_975_);
lean_dec_ref(v_x_964_);
v___x_976_ = l_ByteArray_toUInt64LE_x21(v_a_975_);
lean_dec(v_a_975_);
v___x_977_ = lean_uint64_to_nat(v___x_976_);
v___x_978_ = l_mkStdGen(v___x_977_);
lean_dec(v___x_977_);
v___x_979_ = l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt___redArg(v_selectables_963_, v___x_978_);
v___x_980_ = lean_box(0);
v___x_981_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__1));
v_sz_982_ = lean_array_size(v___x_979_);
v___x_983_ = ((size_t)0ULL);
lean_inc_ref(v___x_979_);
v___x_984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg(v___x_979_, v_sz_982_, v___x_983_, v___x_981_);
v___f_985_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_985_, 0, v___x_979_);
lean_closure_set(v___f_985_, 1, v___x_980_);
v___x_986_ = lean_unsigned_to_nat(0u);
v___x_987_ = 0;
v___x_988_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_986_, v___x_987_, v___x_984_, v___f_985_);
return v___x_988_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__6___boxed(lean_object* v_selectables_989_, lean_object* v_x_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__6(v_selectables_989_, v_x_990_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__7(lean_object* v___f_993_, lean_object* v_____r_994_){
_start:
{
lean_object* v_val_997_; size_t v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = ((size_t)8ULL);
v___x_1003_ = lean_io_get_random_bytes(v___x_1002_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
lean_ctor_set_tag(v___x_1006_, 1);
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
v_val_997_ = v___x_1009_;
goto v___jp_996_;
}
}
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
v_a_1012_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_1003_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1003_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
lean_ctor_set_tag(v___x_1014_, 0);
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
v_val_997_ = v___x_1017_;
goto v___jp_996_;
}
}
}
v___jp_996_:
{
lean_object* v___x_998_; lean_object* v___x_999_; uint8_t v___x_1000_; lean_object* v___x_1001_; 
v___x_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_998_, 0, v_val_997_);
v___x_999_ = lean_unsigned_to_nat(0u);
v___x_1000_ = 0;
v___x_1001_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_999_, v___x_1000_, v___x_998_, v___f_993_);
return v___x_1001_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__7___boxed(lean_object* v___f_1020_, lean_object* v_____r_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__7(v___f_1020_, v_____r_1021_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__8(lean_object* v___f_1024_, lean_object* v_x_1025_){
_start:
{
if (lean_obj_tag(v_x_1025_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1035_; 
lean_dec_ref(v___f_1024_);
v_a_1027_ = lean_ctor_get(v_x_1025_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_x_1025_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1029_ = v_x_1025_;
v_isShared_1030_ = v_isSharedCheck_1035_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v_x_1025_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1035_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1033_; 
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
return v___x_1033_;
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1037_; 
v_a_1036_ = lean_ctor_get(v_x_1025_, 0);
lean_inc(v_a_1036_);
lean_dec_ref(v_x_1025_);
v___x_1037_ = lean_apply_2(v___f_1024_, v_a_1036_, lean_box(0));
return v___x_1037_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__8___boxed(lean_object* v___f_1038_, lean_object* v_x_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__8(v___f_1038_, v_x_1039_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg(lean_object* v_selectables_1049_){
_start:
{
lean_object* v___f_1051_; lean_object* v___f_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; uint8_t v___x_1055_; 
lean_inc_ref(v_selectables_1049_);
v___f_1051_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__6___boxed), 3, 1);
lean_closure_set(v___f_1051_, 0, v_selectables_1049_);
lean_inc_ref(v___f_1051_);
v___f_1052_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_1052_, 0, v___f_1051_);
v___x_1053_ = lean_array_get_size(v_selectables_1049_);
lean_dec_ref(v_selectables_1049_);
v___x_1054_ = lean_unsigned_to_nat(0u);
v___x_1055_ = lean_nat_dec_eq(v___x_1053_, v___x_1054_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
lean_dec_ref(v___f_1052_);
v___x_1056_ = lean_box(0);
v___x_1057_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__7(v___f_1051_, v___x_1056_);
return v___x_1057_;
}
else
{
lean_object* v___f_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; lean_object* v___x_1061_; 
lean_dec_ref(v___f_1051_);
v___f_1058_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__8___boxed), 3, 1);
lean_closure_set(v___f_1058_, 0, v___f_1052_);
v___x_1059_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_one___redArg___closed__3));
v___x_1060_ = 0;
v___x_1061_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1054_, v___x_1060_, v___x_1059_, v___f_1058_);
return v___x_1061_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___boxed(lean_object* v_selectables_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Std_Internal_IO_Async_Selectable_one___redArg(v_selectables_1062_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one(lean_object* v_00_u03b1_1065_, lean_object* v_selectables_1066_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Std_Internal_IO_Async_Selectable_one___redArg(v_selectables_1066_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___boxed(lean_object* v_00_u03b1_1069_, lean_object* v_selectables_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Std_Internal_IO_Async_Selectable_one(v_00_u03b1_1069_, v_selectables_1070_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0(lean_object* v_00_u03b1_1073_, lean_object* v_as_1074_, size_t v_sz_1075_, size_t v_i_1076_, lean_object* v_b_1077_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg(v_as_1074_, v_sz_1075_, v_i_1076_, v_b_1077_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___boxed(lean_object* v_00_u03b1_1080_, lean_object* v_as_1081_, lean_object* v_sz_1082_, lean_object* v_i_1083_, lean_object* v_b_1084_, lean_object* v___y_1085_){
_start:
{
size_t v_sz_boxed_1086_; size_t v_i_boxed_1087_; lean_object* v_res_1088_; 
v_sz_boxed_1086_ = lean_unbox_usize(v_sz_1082_);
lean_dec(v_sz_1082_);
v_i_boxed_1087_ = lean_unbox_usize(v_i_1083_);
lean_dec(v_i_1083_);
v_res_1088_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0(v_00_u03b1_1080_, v_as_1081_, v_sz_boxed_1086_, v_i_boxed_1087_, v_b_1084_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2(lean_object* v_00_u03b1_1089_, lean_object* v_a_1090_, lean_object* v___x_1091_, lean_object* v_a_1092_, lean_object* v_as_1093_, size_t v_sz_1094_, size_t v_i_1095_, lean_object* v_b_1096_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg(v_a_1090_, v___x_1091_, v_a_1092_, v_as_1093_, v_sz_1094_, v_i_1095_, v_b_1096_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___boxed(lean_object* v_00_u03b1_1099_, lean_object* v_a_1100_, lean_object* v___x_1101_, lean_object* v_a_1102_, lean_object* v_as_1103_, lean_object* v_sz_1104_, lean_object* v_i_1105_, lean_object* v_b_1106_, lean_object* v___y_1107_){
_start:
{
size_t v_sz_boxed_1108_; size_t v_i_boxed_1109_; lean_object* v_res_1110_; 
v_sz_boxed_1108_ = lean_unbox_usize(v_sz_1104_);
lean_dec(v_sz_1104_);
v_i_boxed_1109_ = lean_unbox_usize(v_i_1105_);
lean_dec(v_i_1105_);
v_res_1110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2(v_00_u03b1_1099_, v_a_1100_, v___x_1101_, v_a_1102_, v_as_1103_, v_sz_boxed_1108_, v_i_boxed_1109_, v_b_1106_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3(lean_object* v_00_u03b1_1111_, lean_object* v_as_1112_, size_t v_sz_1113_, size_t v_i_1114_, lean_object* v_b_1115_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg(v_as_1112_, v_sz_1113_, v_i_1114_, v_b_1115_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___boxed(lean_object* v_00_u03b1_1118_, lean_object* v_as_1119_, lean_object* v_sz_1120_, lean_object* v_i_1121_, lean_object* v_b_1122_, lean_object* v___y_1123_){
_start:
{
size_t v_sz_boxed_1124_; size_t v_i_boxed_1125_; lean_object* v_res_1126_; 
v_sz_boxed_1124_ = lean_unbox_usize(v_sz_1120_);
lean_dec(v_sz_1120_);
v_i_boxed_1125_ = lean_unbox_usize(v_i_1121_);
lean_dec(v_i_1121_);
v_res_1126_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3(v_00_u03b1_1118_, v_as_1119_, v_sz_boxed_1124_, v_i_boxed_1125_, v_b_1122_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0(lean_object* v_x_1131_){
_start:
{
if (lean_obj_tag(v_x_1131_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1141_; 
v_a_1133_ = lean_ctor_get(v_x_1131_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_x_1131_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1135_ = v_x_1131_;
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v_x_1131_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
return v___x_1139_;
}
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1159_; 
v_a_1142_ = lean_ctor_get(v_x_1131_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_x_1131_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1144_ = v_x_1131_;
v_isShared_1145_ = v_isSharedCheck_1159_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v_x_1131_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1159_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v_fst_1146_; 
v_fst_1146_ = lean_ctor_get(v_a_1142_, 0);
lean_inc(v_fst_1146_);
lean_dec(v_a_1142_);
if (lean_obj_tag(v_fst_1146_) == 0)
{
lean_object* v___x_1147_; 
lean_del_object(v___x_1144_);
v___x_1147_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0___closed__1));
return v___x_1147_;
}
else
{
lean_object* v_val_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1158_; 
v_val_1148_ = lean_ctor_get(v_fst_1146_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_fst_1146_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1150_ = v_fst_1146_;
v_isShared_1151_ = v_isSharedCheck_1158_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_val_1148_);
lean_dec(v_fst_1146_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1158_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v_val_1148_);
v___x_1153_ = v___x_1144_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_val_1148_);
v___x_1153_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1155_; 
if (v_isShared_1151_ == 0)
{
lean_ctor_set_tag(v___x_1150_, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1153_);
v___x_1155_ = v___x_1150_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0___boxed(lean_object* v_x_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0(v_x_1160_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__1(lean_object* v_a_1163_, lean_object* v___x_1164_, uint8_t v___x_1165_, lean_object* v___f_1166_, lean_object* v___x_1167_, lean_object* v_x_1168_){
_start:
{
if (lean_obj_tag(v_x_1168_) == 0)
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1178_; 
lean_dec_ref(v___x_1167_);
lean_dec_ref(v___f_1166_);
lean_dec(v___x_1164_);
lean_dec_ref(v_a_1163_);
v_a_1170_ = lean_ctor_get(v_x_1168_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_x_1168_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1172_ = v_x_1168_;
v_isShared_1173_ = v_isSharedCheck_1178_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v_x_1168_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1178_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1176_; 
v___x_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
return v___x_1176_;
}
}
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1192_; 
v_a_1179_ = lean_ctor_get(v_x_1168_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_x_1168_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1181_ = v_x_1168_;
v_isShared_1182_ = v_isSharedCheck_1192_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v_x_1168_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1192_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
if (lean_obj_tag(v_a_1179_) == 1)
{
lean_object* v_val_1183_; lean_object* v_cont_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_del_object(v___x_1181_);
lean_dec_ref(v___x_1167_);
v_val_1183_ = lean_ctor_get(v_a_1179_, 0);
lean_inc(v_val_1183_);
lean_dec_ref(v_a_1179_);
v_cont_1184_ = lean_ctor_get(v_a_1163_, 1);
lean_inc_ref(v_cont_1184_);
lean_dec_ref(v_a_1163_);
v___x_1185_ = lean_apply_2(v_cont_1184_, v_val_1183_, lean_box(0));
v___x_1186_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1164_, v___x_1165_, v___x_1185_, v___f_1166_);
return v___x_1186_;
}
else
{
lean_object* v___x_1187_; lean_object* v___x_1189_; 
lean_dec(v_a_1179_);
lean_dec_ref(v___f_1166_);
lean_dec(v___x_1164_);
lean_dec_ref(v_a_1163_);
v___x_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1167_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1187_);
v___x_1189_ = v___x_1181_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_object* v___x_1190_; 
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
return v___x_1190_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__1___boxed(lean_object* v_a_1193_, lean_object* v___x_1194_, lean_object* v___x_1195_, lean_object* v___f_1196_, lean_object* v___x_1197_, lean_object* v_x_1198_, lean_object* v___y_1199_){
_start:
{
uint8_t v___x_2272__boxed_1200_; lean_object* v_res_1201_; 
v___x_2272__boxed_1200_ = lean_unbox(v___x_1195_);
v_res_1201_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__1(v_a_1193_, v___x_1194_, v___x_2272__boxed_1200_, v___f_1196_, v___x_1197_, v_x_1198_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__0(lean_object* v___x_1202_, lean_object* v_x_1203_){
_start:
{
if (lean_obj_tag(v_x_1203_) == 0)
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1213_; 
v_a_1205_ = lean_ctor_get(v_x_1203_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_x_1203_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1207_ = v_x_1203_;
v_isShared_1208_ = v_isSharedCheck_1213_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v_x_1203_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1213_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
lean_object* v___x_1211_; 
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
return v___x_1211_;
}
}
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1226_; 
v_a_1214_ = lean_ctor_get(v_x_1203_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_x_1203_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1216_ = v_x_1203_;
v_isShared_1217_ = v_isSharedCheck_1226_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v_x_1203_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1226_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1223_; 
v___x_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1218_, 0, v_a_1214_);
v___x_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
v___x_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
lean_ctor_set(v___x_1220_, 1, v___x_1202_);
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v___x_1221_);
v___x_1223_ = v___x_1216_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1224_; 
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__0___boxed(lean_object* v___x_1227_, lean_object* v_x_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__0(v___x_1227_, v_x_1228_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__2___boxed(lean_object* v_i_1236_, lean_object* v___x_1237_, lean_object* v_as_1238_, lean_object* v_sz_1239_, lean_object* v_x_1240_, lean_object* v___y_1241_){
_start:
{
size_t v_i_boxed_1242_; size_t v_sz_boxed_1243_; lean_object* v_res_1244_; 
v_i_boxed_1242_ = lean_unbox_usize(v_i_1236_);
lean_dec(v_i_1236_);
v_sz_boxed_1243_ = lean_unbox_usize(v_sz_1239_);
lean_dec(v_sz_1239_);
v_res_1244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__2(v_i_boxed_1242_, v___x_1237_, v_as_1238_, v_sz_boxed_1243_, v_x_1240_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(lean_object* v___x_1245_, lean_object* v_as_1246_, size_t v_sz_1247_, size_t v_i_1248_, lean_object* v_b_1249_){
_start:
{
uint8_t v___x_1251_; 
v___x_1251_ = lean_usize_dec_lt(v_i_1248_, v_sz_1247_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_dec_ref(v_as_1246_);
lean_dec(v___x_1245_);
v___x_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1252_, 0, v_b_1249_);
v___x_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
return v___x_1253_;
}
else
{
lean_object* v_a_1254_; lean_object* v_selector_1255_; lean_object* v_tryFn_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; lean_object* v___f_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___f_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___f_1267_; uint8_t v___x_1268_; lean_object* v___x_1269_; 
lean_dec_ref(v_b_1249_);
v_a_1254_ = lean_array_uget_borrowed(v_as_1246_, v_i_1248_);
v_selector_1255_ = lean_ctor_get(v_a_1254_, 0);
v_tryFn_1256_ = lean_ctor_get(v_selector_1255_, 0);
lean_inc_ref(v_tryFn_1256_);
v___x_1257_ = lean_apply_1(v_tryFn_1256_, lean_box(0));
v___x_1258_ = lean_unsigned_to_nat(0u);
v___x_1259_ = lean_nat_dec_eq(v___x_1245_, v___x_1258_);
v___f_1260_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__0));
v___x_1261_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__1));
v___x_1262_ = lean_box(v___x_1259_);
lean_inc(v_a_1254_);
v___f_1263_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_1263_, 0, v_a_1254_);
lean_closure_set(v___f_1263_, 1, v___x_1258_);
lean_closure_set(v___f_1263_, 2, v___x_1262_);
lean_closure_set(v___f_1263_, 3, v___f_1260_);
lean_closure_set(v___f_1263_, 4, v___x_1261_);
v___x_1264_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1258_, v___x_1259_, v___x_1257_, v___f_1263_);
v___x_1265_ = lean_box_usize(v_i_1248_);
v___x_1266_ = lean_box_usize(v_sz_1247_);
v___f_1267_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_1267_, 0, v___x_1265_);
lean_closure_set(v___f_1267_, 1, v___x_1245_);
lean_closure_set(v___f_1267_, 2, v_as_1246_);
lean_closure_set(v___f_1267_, 3, v___x_1266_);
v___x_1268_ = 0;
v___x_1269_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1258_, v___x_1268_, v___x_1264_, v___f_1267_);
return v___x_1269_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__2(size_t v_i_1270_, lean_object* v___x_1271_, lean_object* v_as_1272_, size_t v_sz_1273_, lean_object* v_x_1274_){
_start:
{
if (lean_obj_tag(v_x_1274_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1284_; 
lean_dec_ref(v_as_1272_);
lean_dec(v___x_1271_);
v_a_1276_ = lean_ctor_get(v_x_1274_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_x_1274_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1278_ = v_x_1274_;
v_isShared_1279_ = v_isSharedCheck_1284_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v_x_1274_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1284_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
lean_object* v___x_1282_; 
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
return v___x_1282_;
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1304_; 
v_a_1285_ = lean_ctor_get(v_x_1274_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v_x_1274_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1287_ = v_x_1274_;
v_isShared_1288_ = v_isSharedCheck_1304_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v_x_1274_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1304_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
if (lean_obj_tag(v_a_1285_) == 0)
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1299_; 
lean_dec_ref(v_as_1272_);
lean_dec(v___x_1271_);
v_a_1289_ = lean_ctor_get(v_a_1285_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v_a_1285_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1291_ = v_a_1285_;
v_isShared_1292_ = v_isSharedCheck_1299_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v_a_1285_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1299_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v_a_1289_);
v___x_1294_ = v___x_1287_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
lean_object* v___x_1296_; 
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v___x_1294_);
v___x_1296_ = v___x_1291_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1294_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
else
{
lean_object* v_a_1300_; size_t v___x_1301_; size_t v___x_1302_; lean_object* v___x_1303_; 
lean_del_object(v___x_1287_);
v_a_1300_ = lean_ctor_get(v_a_1285_, 0);
lean_inc(v_a_1300_);
lean_dec_ref(v_a_1285_);
v___x_1301_ = ((size_t)1ULL);
v___x_1302_ = lean_usize_add(v_i_1270_, v___x_1301_);
v___x_1303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(v___x_1271_, v_as_1272_, v_sz_1273_, v___x_1302_, v_a_1300_);
return v___x_1303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___boxed(lean_object* v___x_1305_, lean_object* v_as_1306_, lean_object* v_sz_1307_, lean_object* v_i_1308_, lean_object* v_b_1309_, lean_object* v___y_1310_){
_start:
{
size_t v_sz_boxed_1311_; size_t v_i_boxed_1312_; lean_object* v_res_1313_; 
v_sz_boxed_1311_ = lean_unbox_usize(v_sz_1307_);
lean_dec(v_sz_1307_);
v_i_boxed_1312_ = lean_unbox_usize(v_i_1308_);
lean_dec(v_i_1308_);
v_res_1313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(v___x_1305_, v_as_1306_, v_sz_boxed_1311_, v_i_boxed_1312_, v_b_1309_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__1(lean_object* v_selectables_1314_, lean_object* v___x_1315_, lean_object* v___x_1316_, uint8_t v___x_1317_, lean_object* v___f_1318_, lean_object* v_x_1319_){
_start:
{
if (lean_obj_tag(v_x_1319_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1329_; 
lean_dec_ref(v___f_1318_);
lean_dec(v___x_1316_);
lean_dec(v___x_1315_);
lean_dec_ref(v_selectables_1314_);
v_a_1321_ = lean_ctor_get(v_x_1319_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_x_1319_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1323_ = v_x_1319_;
v_isShared_1324_ = v_isSharedCheck_1329_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v_x_1319_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1329_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
return v___x_1327_;
}
}
}
else
{
lean_object* v_a_1330_; uint64_t v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; size_t v_sz_1336_; size_t v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v_a_1330_ = lean_ctor_get(v_x_1319_, 0);
lean_inc(v_a_1330_);
lean_dec_ref(v_x_1319_);
v___x_1331_ = l_ByteArray_toUInt64LE_x21(v_a_1330_);
lean_dec(v_a_1330_);
v___x_1332_ = lean_uint64_to_nat(v___x_1331_);
v___x_1333_ = l_mkStdGen(v___x_1332_);
lean_dec(v___x_1332_);
v___x_1334_ = l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt___redArg(v_selectables_1314_, v___x_1333_);
v___x_1335_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__1));
v_sz_1336_ = lean_array_size(v___x_1334_);
v___x_1337_ = ((size_t)0ULL);
v___x_1338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(v___x_1315_, v___x_1334_, v_sz_1336_, v___x_1337_, v___x_1335_);
v___x_1339_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1316_, v___x_1317_, v___x_1338_, v___f_1318_);
return v___x_1339_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__1___boxed(lean_object* v_selectables_1340_, lean_object* v___x_1341_, lean_object* v___x_1342_, lean_object* v___x_1343_, lean_object* v___f_1344_, lean_object* v_x_1345_, lean_object* v___y_1346_){
_start:
{
uint8_t v___x_2511__boxed_1347_; lean_object* v_res_1348_; 
v___x_2511__boxed_1347_ = lean_unbox(v___x_1343_);
v_res_1348_ = l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__1(v_selectables_1340_, v___x_1341_, v___x_1342_, v___x_2511__boxed_1347_, v___f_1344_, v_x_1345_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg(lean_object* v_selectables_1350_){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; 
v___x_1352_ = lean_array_get_size(v_selectables_1350_);
v___x_1353_ = lean_unsigned_to_nat(0u);
v___x_1354_ = lean_nat_dec_eq(v___x_1352_, v___x_1353_);
if (v___x_1354_ == 0)
{
lean_object* v___f_1355_; lean_object* v___x_1356_; lean_object* v___f_1357_; lean_object* v_val_1359_; size_t v___x_1362_; lean_object* v___x_1363_; 
v___f_1355_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_tryOne___redArg___closed__0));
v___x_1356_ = lean_box(v___x_1354_);
v___f_1357_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_1357_, 0, v_selectables_1350_);
lean_closure_set(v___f_1357_, 1, v___x_1352_);
lean_closure_set(v___f_1357_, 2, v___x_1353_);
lean_closure_set(v___f_1357_, 3, v___x_1356_);
lean_closure_set(v___f_1357_, 4, v___f_1355_);
v___x_1362_ = ((size_t)8ULL);
v___x_1363_ = lean_io_get_random_bytes(v___x_1362_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1363_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1363_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
lean_ctor_set_tag(v___x_1366_, 1);
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
v_val_1359_ = v___x_1369_;
goto v___jp_1358_;
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
v_a_1372_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1363_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1363_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
lean_ctor_set_tag(v___x_1374_, 0);
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
v_val_1359_ = v___x_1377_;
goto v___jp_1358_;
}
}
}
v___jp_1358_:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1360_, 0, v_val_1359_);
v___x_1361_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1353_, v___x_1354_, v___x_1360_, v___f_1357_);
return v___x_1361_;
}
}
else
{
lean_object* v___x_1380_; 
lean_dec_ref(v_selectables_1350_);
v___x_1380_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0___closed__1));
return v___x_1380_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___boxed(lean_object* v_selectables_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Std_Internal_IO_Async_Selectable_tryOne___redArg(v_selectables_1381_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne(lean_object* v_00_u03b1_1384_, lean_object* v_selectables_1385_){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = l_Std_Internal_IO_Async_Selectable_tryOne___redArg(v_selectables_1385_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___boxed(lean_object* v_00_u03b1_1388_, lean_object* v_selectables_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Std_Internal_IO_Async_Selectable_tryOne(v_00_u03b1_1388_, v_selectables_1389_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0(lean_object* v_00_u03b1_1392_, lean_object* v___x_1393_, lean_object* v_as_1394_, size_t v_sz_1395_, size_t v_i_1396_, lean_object* v_b_1397_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(v___x_1393_, v_as_1394_, v_sz_1395_, v_i_1396_, v_b_1397_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___boxed(lean_object* v_00_u03b1_1400_, lean_object* v___x_1401_, lean_object* v_as_1402_, lean_object* v_sz_1403_, lean_object* v_i_1404_, lean_object* v_b_1405_, lean_object* v___y_1406_){
_start:
{
size_t v_sz_boxed_1407_; size_t v_i_boxed_1408_; lean_object* v_res_1409_; 
v_sz_boxed_1407_ = lean_unbox_usize(v_sz_1403_);
lean_dec(v_sz_1403_);
v_i_boxed_1408_ = lean_unbox_usize(v_i_1404_);
lean_dec(v_i_1404_);
v_res_1409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0(v_00_u03b1_1400_, v___x_1401_, v_as_1402_, v_sz_boxed_1407_, v_i_boxed_1408_, v_b_1405_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__1(lean_object* v___x_1410_, lean_object* v_x_1411_){
_start:
{
if (lean_obj_tag(v_x_1411_) == 0)
{
lean_object* v___x_1413_; 
v___x_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1413_, 0, v_x_1411_);
return v___x_1413_;
}
else
{
lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1421_; 
v_isSharedCheck_1421_ = !lean_is_exclusive(v_x_1411_);
if (v_isSharedCheck_1421_ == 0)
{
lean_object* v_unused_1422_; 
v_unused_1422_ = lean_ctor_get(v_x_1411_, 0);
lean_dec(v_unused_1422_);
v___x_1415_ = v_x_1411_;
v_isShared_1416_ = v_isSharedCheck_1421_;
goto v_resetjp_1414_;
}
else
{
lean_dec(v_x_1411_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1421_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 0, v___x_1410_);
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1410_);
v___x_1418_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
return v___x_1419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__1___boxed(lean_object* v___x_1423_, lean_object* v_x_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__1(v___x_1423_, v_x_1424_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__5(lean_object* v_a_1427_, lean_object* v___f_1428_, lean_object* v___x_1429_, uint8_t v___x_1430_, lean_object* v___x_1431_, lean_object* v___f_1432_, lean_object* v_x_1433_){
_start:
{
if (lean_obj_tag(v_x_1433_) == 0)
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1443_; 
lean_dec_ref(v___f_1432_);
lean_dec(v___x_1429_);
lean_dec_ref(v___f_1428_);
v_a_1435_ = lean_ctor_get(v_x_1433_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_x_1433_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1437_ = v_x_1433_;
v_isShared_1438_ = v_isSharedCheck_1443_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v_x_1433_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1443_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1441_; 
v___x_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
return v___x_1441_;
}
}
}
else
{
lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1454_; 
v_isSharedCheck_1454_ = !lean_is_exclusive(v_x_1433_);
if (v_isSharedCheck_1454_ == 0)
{
lean_object* v_unused_1455_; 
v_unused_1455_ = lean_ctor_get(v_x_1433_, 0);
lean_dec(v_unused_1455_);
v___x_1445_ = v_x_1433_;
v_isShared_1446_ = v_isSharedCheck_1454_;
goto v_resetjp_1444_;
}
else
{
lean_dec(v_x_1433_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1454_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1447_ = lean_io_promise_result_opt(v_a_1427_);
lean_inc(v___x_1429_);
v___x_1448_ = lean_io_bind_task(v___x_1447_, v___f_1428_, v___x_1429_, v___x_1430_);
lean_dec_ref(v___x_1448_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 0, v___x_1431_);
v___x_1450_ = v___x_1445_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1431_);
v___x_1450_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
v___x_1452_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1429_, v___x_1430_, v___x_1451_, v___f_1432_);
return v___x_1452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__5___boxed(lean_object* v_a_1456_, lean_object* v___f_1457_, lean_object* v___x_1458_, lean_object* v___x_1459_, lean_object* v___x_1460_, lean_object* v___f_1461_, lean_object* v_x_1462_, lean_object* v___y_1463_){
_start:
{
uint8_t v___x_6868__boxed_1464_; lean_object* v_res_1465_; 
v___x_6868__boxed_1464_ = lean_unbox(v___x_1459_);
v_res_1465_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__5(v_a_1456_, v___f_1457_, v___x_1458_, v___x_6868__boxed_1464_, v___x_1460_, v___f_1461_, v_x_1462_);
lean_dec(v_a_1456_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__6(lean_object* v_waiter_1466_, lean_object* v_a_1467_, lean_object* v___f_1468_, lean_object* v___x_1469_, uint8_t v___x_1470_, lean_object* v___x_1471_, lean_object* v___f_1472_, lean_object* v_x_1473_){
_start:
{
if (lean_obj_tag(v_x_1473_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1483_; 
lean_dec_ref(v___f_1472_);
lean_dec(v___x_1469_);
lean_dec_ref(v___f_1468_);
lean_dec_ref(v_a_1467_);
lean_dec_ref(v_waiter_1466_);
v_a_1475_ = lean_ctor_get(v_x_1473_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_x_1473_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1477_ = v_x_1473_;
v_isShared_1478_ = v_isSharedCheck_1483_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v_x_1473_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1483_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
lean_object* v___x_1481_; 
v___x_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
return v___x_1481_;
}
}
}
else
{
lean_object* v_selector_1484_; lean_object* v_a_1485_; lean_object* v_finished_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1498_; 
v_selector_1484_ = lean_ctor_get(v_a_1467_, 0);
lean_inc_ref(v_selector_1484_);
lean_dec_ref(v_a_1467_);
v_a_1485_ = lean_ctor_get(v_x_1473_, 0);
lean_inc(v_a_1485_);
lean_dec_ref(v_x_1473_);
v_finished_1486_ = lean_ctor_get(v_waiter_1466_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v_waiter_1466_);
if (v_isSharedCheck_1498_ == 0)
{
lean_object* v_unused_1499_; 
v_unused_1499_ = lean_ctor_get(v_waiter_1466_, 1);
lean_dec(v_unused_1499_);
v___x_1488_ = v_waiter_1466_;
v_isShared_1489_ = v_isSharedCheck_1498_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_finished_1486_);
lean_dec(v_waiter_1466_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1498_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v_registerFn_1490_; lean_object* v___x_1492_; 
v_registerFn_1490_ = lean_ctor_get(v_selector_1484_, 1);
lean_inc_ref(v_registerFn_1490_);
lean_dec_ref(v_selector_1484_);
lean_inc(v_a_1485_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 1, v_a_1485_);
v___x_1492_ = v___x_1488_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_finished_1486_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_a_1485_);
v___x_1492_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___f_1495_; lean_object* v___x_1496_; 
v___x_1493_ = lean_apply_2(v_registerFn_1490_, v___x_1492_, lean_box(0));
v___x_1494_ = lean_box(v___x_1470_);
lean_inc(v___x_1469_);
v___f_1495_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__5___boxed), 8, 6);
lean_closure_set(v___f_1495_, 0, v_a_1485_);
lean_closure_set(v___f_1495_, 1, v___f_1468_);
lean_closure_set(v___f_1495_, 2, v___x_1469_);
lean_closure_set(v___f_1495_, 3, v___x_1494_);
lean_closure_set(v___f_1495_, 4, v___x_1471_);
lean_closure_set(v___f_1495_, 5, v___f_1472_);
v___x_1496_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1469_, v___x_1470_, v___x_1493_, v___f_1495_);
return v___x_1496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__6___boxed(lean_object* v_waiter_1500_, lean_object* v_a_1501_, lean_object* v___f_1502_, lean_object* v___x_1503_, lean_object* v___x_1504_, lean_object* v___x_1505_, lean_object* v___f_1506_, lean_object* v_x_1507_, lean_object* v___y_1508_){
_start:
{
uint8_t v___x_6934__boxed_1509_; lean_object* v_res_1510_; 
v___x_6934__boxed_1509_ = lean_unbox(v___x_1504_);
v_res_1510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__6(v_waiter_1500_, v_a_1501_, v___f_1502_, v___x_1503_, v___x_6934__boxed_1509_, v___x_1505_, v___f_1506_, v_x_1507_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg___lam__1___boxed(lean_object* v_i_1511_, lean_object* v___x_1512_, lean_object* v_as_1513_, lean_object* v_sz_1514_, lean_object* v_x_1515_, lean_object* v___y_1516_){
_start:
{
size_t v_i_boxed_1517_; size_t v_sz_boxed_1518_; lean_object* v_res_1519_; 
v_i_boxed_1517_ = lean_unbox_usize(v_i_1511_);
lean_dec(v_i_1511_);
v_sz_boxed_1518_ = lean_unbox_usize(v_sz_1514_);
lean_dec(v_sz_1514_);
v_res_1519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg___lam__1(v_i_boxed_1517_, v___x_1512_, v_as_1513_, v_sz_boxed_1518_, v_x_1515_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(lean_object* v___x_1520_, lean_object* v_as_1521_, size_t v_sz_1522_, size_t v_i_1523_, lean_object* v_b_1524_){
_start:
{
uint8_t v___x_1526_; 
v___x_1526_ = lean_usize_dec_lt(v_i_1523_, v_sz_1522_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
lean_dec_ref(v_as_1521_);
lean_dec(v___x_1520_);
v___x_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1527_, 0, v_b_1524_);
v___x_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
return v___x_1528_;
}
else
{
lean_object* v_a_1529_; lean_object* v_selector_1530_; lean_object* v_unregisterFn_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; lean_object* v___f_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___f_1539_; uint8_t v___x_1540_; lean_object* v___x_1541_; 
v_a_1529_ = lean_array_uget_borrowed(v_as_1521_, v_i_1523_);
v_selector_1530_ = lean_ctor_get(v_a_1529_, 0);
v_unregisterFn_1531_ = lean_ctor_get(v_selector_1530_, 2);
lean_inc_ref(v_unregisterFn_1531_);
v___x_1532_ = lean_apply_1(v_unregisterFn_1531_, lean_box(0));
v___x_1533_ = lean_unsigned_to_nat(0u);
v___x_1534_ = lean_nat_dec_eq(v___x_1520_, v___x_1533_);
v___f_1535_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___closed__0));
v___x_1536_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1533_, v___x_1534_, v___x_1532_, v___f_1535_);
v___x_1537_ = lean_box_usize(v_i_1523_);
v___x_1538_ = lean_box_usize(v_sz_1522_);
v___f_1539_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg___lam__1___boxed), 6, 4);
lean_closure_set(v___f_1539_, 0, v___x_1537_);
lean_closure_set(v___f_1539_, 1, v___x_1520_);
lean_closure_set(v___f_1539_, 2, v_as_1521_);
lean_closure_set(v___f_1539_, 3, v___x_1538_);
v___x_1540_ = 0;
v___x_1541_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1533_, v___x_1540_, v___x_1536_, v___f_1539_);
return v___x_1541_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg___lam__1(size_t v_i_1542_, lean_object* v___x_1543_, lean_object* v_as_1544_, size_t v_sz_1545_, lean_object* v_x_1546_){
_start:
{
if (lean_obj_tag(v_x_1546_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1556_; 
lean_dec_ref(v_as_1544_);
lean_dec(v___x_1543_);
v_a_1548_ = lean_ctor_get(v_x_1546_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v_x_1546_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1550_ = v_x_1546_;
v_isShared_1551_ = v_isSharedCheck_1556_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v_x_1546_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1556_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
lean_object* v___x_1554_; 
v___x_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
return v___x_1554_;
}
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1576_; 
v_a_1557_ = lean_ctor_get(v_x_1546_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v_x_1546_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1559_ = v_x_1546_;
v_isShared_1560_ = v_isSharedCheck_1576_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v_x_1546_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1576_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
if (lean_obj_tag(v_a_1557_) == 0)
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1571_; 
lean_dec_ref(v_as_1544_);
lean_dec(v___x_1543_);
v_a_1561_ = lean_ctor_get(v_a_1557_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_a_1557_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1563_ = v_a_1557_;
v_isShared_1564_ = v_isSharedCheck_1571_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v_a_1557_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1571_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v_a_1561_);
v___x_1566_ = v___x_1559_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1568_; 
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 0, v___x_1566_);
v___x_1568_ = v___x_1563_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1566_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
else
{
lean_object* v_a_1572_; size_t v___x_1573_; size_t v___x_1574_; lean_object* v___x_1575_; 
lean_del_object(v___x_1559_);
v_a_1572_ = lean_ctor_get(v_a_1557_, 0);
lean_inc(v_a_1572_);
lean_dec_ref(v_a_1557_);
v___x_1573_ = ((size_t)1ULL);
v___x_1574_ = lean_usize_add(v_i_1542_, v___x_1573_);
v___x_1575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(v___x_1543_, v_as_1544_, v_sz_1545_, v___x_1574_, v_a_1572_);
return v___x_1575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg___boxed(lean_object* v___x_1577_, lean_object* v_as_1578_, lean_object* v_sz_1579_, lean_object* v_i_1580_, lean_object* v_b_1581_, lean_object* v___y_1582_){
_start:
{
size_t v_sz_boxed_1583_; size_t v_i_boxed_1584_; lean_object* v_res_1585_; 
v_sz_boxed_1583_ = lean_unbox_usize(v_sz_1579_);
lean_dec(v_sz_1579_);
v_i_boxed_1584_ = lean_unbox_usize(v_i_1580_);
lean_dec(v_i_1580_);
v_res_1585_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(v___x_1577_, v_as_1578_, v_sz_boxed_1583_, v_i_boxed_1584_, v_b_1581_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__3(lean_object* v___x_1586_, uint8_t v___x_1587_, lean_object* v___f_1588_, lean_object* v___f_1589_, lean_object* v_val_1590_, lean_object* v_x_1591_){
_start:
{
lean_object* v_val_1594_; 
if (lean_obj_tag(v_x_1591_) == 0)
{
lean_object* v___x_1598_; 
lean_dec_ref(v_val_1590_);
lean_dec_ref(v___f_1589_);
lean_dec_ref(v___f_1588_);
lean_dec(v___x_1586_);
v___x_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1598_, 0, v_x_1591_);
return v___x_1598_;
}
else
{
lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1611_; 
v_isSharedCheck_1611_ = !lean_is_exclusive(v_x_1591_);
if (v_isSharedCheck_1611_ == 0)
{
lean_object* v_unused_1612_; 
v_unused_1612_ = lean_ctor_get(v_x_1591_, 0);
lean_dec(v_unused_1612_);
v___x_1600_ = v_x_1591_;
v_isShared_1601_ = v_isSharedCheck_1611_;
goto v_resetjp_1599_;
}
else
{
lean_dec(v_x_1591_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1611_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg(v_val_1590_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; lean_object* v___x_1605_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_a_1603_);
lean_dec_ref(v___x_1602_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v_a_1603_);
v___x_1605_ = v___x_1600_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
v_val_1594_ = v___x_1605_;
goto v___jp_1593_;
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; 
v_a_1607_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_a_1607_);
lean_dec_ref(v___x_1602_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set_tag(v___x_1600_, 0);
lean_ctor_set(v___x_1600_, 0, v_a_1607_);
v___x_1609_ = v___x_1600_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1607_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
v_val_1594_ = v___x_1609_;
goto v___jp_1593_;
}
}
}
}
v___jp_1593_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1595_, 0, v_val_1594_);
lean_inc(v___x_1586_);
v___x_1596_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1586_, v___x_1587_, v___x_1595_, v___f_1588_);
v___x_1597_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1586_, v___x_1587_, v___x_1596_, v___f_1589_);
return v___x_1597_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__3___boxed(lean_object* v___x_1613_, lean_object* v___x_1614_, lean_object* v___f_1615_, lean_object* v___f_1616_, lean_object* v_val_1617_, lean_object* v_x_1618_, lean_object* v___y_1619_){
_start:
{
uint8_t v___x_7100__boxed_1620_; lean_object* v_res_1621_; 
v___x_7100__boxed_1620_ = lean_unbox(v___x_1614_);
v_res_1621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__3(v___x_1613_, v___x_7100__boxed_1620_, v___f_1615_, v___f_1616_, v_val_1617_, v_x_1618_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__2(lean_object* v_a_1622_, lean_object* v___x_1623_, uint8_t v___x_1624_, lean_object* v___f_1625_, lean_object* v_x_1626_){
_start:
{
if (lean_obj_tag(v_x_1626_) == 0)
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1636_; 
lean_dec_ref(v___f_1625_);
lean_dec(v___x_1623_);
lean_dec_ref(v_a_1622_);
v_a_1628_ = lean_ctor_get(v_x_1626_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v_x_1626_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1630_ = v_x_1626_;
v_isShared_1631_ = v_isSharedCheck_1636_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v_x_1626_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1636_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
lean_object* v___x_1634_; 
v___x_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
return v___x_1634_;
}
}
}
else
{
lean_object* v_a_1637_; lean_object* v_cont_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v_a_1637_ = lean_ctor_get(v_x_1626_, 0);
lean_inc(v_a_1637_);
lean_dec_ref(v_x_1626_);
v_cont_1638_ = lean_ctor_get(v_a_1622_, 1);
lean_inc_ref(v_cont_1638_);
lean_dec_ref(v_a_1622_);
v___x_1639_ = lean_apply_2(v_cont_1638_, v_a_1637_, lean_box(0));
v___x_1640_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1623_, v___x_1624_, v___x_1639_, v___f_1625_);
return v___x_1640_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__2___boxed(lean_object* v_a_1641_, lean_object* v___x_1642_, lean_object* v___x_1643_, lean_object* v___f_1644_, lean_object* v_x_1645_, lean_object* v___y_1646_){
_start:
{
uint8_t v___x_7163__boxed_1647_; lean_object* v_res_1648_; 
v___x_7163__boxed_1647_ = lean_unbox(v___x_1643_);
v_res_1648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__2(v_a_1641_, v___x_1642_, v___x_7163__boxed_1647_, v___f_1644_, v_x_1645_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__0(lean_object* v_promise_1649_, lean_object* v_x_1650_){
_start:
{
if (lean_obj_tag(v_x_1650_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1660_; 
v_a_1652_ = lean_ctor_get(v_x_1650_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_x_1650_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1654_ = v_x_1650_;
v_isShared_1655_ = v_isSharedCheck_1660_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v_x_1650_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1660_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
return v___x_1658_;
}
}
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1661_ = lean_io_promise_resolve(v_x_1650_, v_promise_1649_);
v___x_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
v___x_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
return v___x_1663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__0___boxed(lean_object* v_promise_1664_, lean_object* v_x_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__0(v_promise_1664_, v_x_1665_);
lean_dec(v_promise_1664_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__1(lean_object* v_promise_1668_, lean_object* v_x_1669_){
_start:
{
if (lean_obj_tag(v_x_1669_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1681_; 
v_a_1671_ = lean_ctor_get(v_x_1669_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v_x_1669_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1673_ = v_x_1669_;
v_isShared_1674_ = v_isSharedCheck_1681_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v_x_1669_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1681_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1677_ = lean_io_promise_resolve(v___x_1676_, v_promise_1668_);
v___x_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
v___x_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1678_);
return v___x_1679_;
}
}
}
else
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1682_, 0, v_x_1669_);
return v___x_1682_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__1___boxed(lean_object* v_promise_1683_, lean_object* v_x_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__1(v_promise_1683_, v_x_1684_);
lean_dec(v_promise_1683_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__4(lean_object* v___x_1687_, lean_object* v___x_1688_, lean_object* v___x_1689_, lean_object* v_waiter_1690_, lean_object* v_a_1691_, lean_object* v___x_1692_, uint8_t v___x_1693_, lean_object* v_a_1694_){
_start:
{
if (lean_obj_tag(v_a_1694_) == 0)
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
lean_dec(v___x_1692_);
lean_dec_ref(v_a_1691_);
lean_dec_ref(v_waiter_1690_);
lean_dec(v___x_1689_);
lean_dec_ref(v___x_1688_);
v___x_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1687_);
v___x_1697_ = lean_task_pure(v___x_1696_);
return v___x_1697_;
}
else
{
lean_object* v_val_1698_; size_t v_sz_1699_; size_t v___x_1700_; lean_object* v___x_1701_; lean_object* v_promise_1702_; lean_object* v___f_1703_; lean_object* v___f_1704_; lean_object* v___x_1705_; lean_object* v___f_1706_; lean_object* v___x_1707_; lean_object* v___f_1708_; lean_object* v___x_1709_; 
v_val_1698_ = lean_ctor_get(v_a_1694_, 0);
lean_inc(v_val_1698_);
lean_dec_ref(v_a_1694_);
v_sz_1699_ = lean_array_size(v___x_1688_);
v___x_1700_ = ((size_t)0ULL);
v___x_1701_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(v___x_1689_, v___x_1688_, v_sz_1699_, v___x_1700_, v___x_1687_);
v_promise_1702_ = lean_ctor_get(v_waiter_1690_, 1);
lean_inc(v_promise_1702_);
lean_dec_ref(v_waiter_1690_);
lean_inc(v_promise_1702_);
v___f_1703_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1703_, 0, v_promise_1702_);
v___f_1704_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1704_, 0, v_promise_1702_);
v___x_1705_ = lean_box(v___x_1693_);
lean_inc(v___x_1692_);
v___f_1706_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_1706_, 0, v_a_1691_);
lean_closure_set(v___f_1706_, 1, v___x_1692_);
lean_closure_set(v___f_1706_, 2, v___x_1705_);
lean_closure_set(v___f_1706_, 3, v___f_1704_);
v___x_1707_ = lean_box(v___x_1693_);
lean_inc(v___x_1692_);
v___f_1708_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__3___boxed), 7, 5);
lean_closure_set(v___f_1708_, 0, v___x_1692_);
lean_closure_set(v___f_1708_, 1, v___x_1707_);
lean_closure_set(v___f_1708_, 2, v___f_1706_);
lean_closure_set(v___f_1708_, 3, v___f_1703_);
lean_closure_set(v___f_1708_, 4, v_val_1698_);
v___x_1709_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1692_, v___x_1693_, v___x_1701_, v___f_1708_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; lean_object* v___x_1711_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_a_1710_);
lean_dec_ref(v___x_1709_);
v___x_1711_ = lean_task_pure(v_a_1710_);
return v___x_1711_;
}
else
{
lean_object* v_a_1712_; 
v_a_1712_ = lean_ctor_get(v___x_1709_, 0);
lean_inc_ref(v_a_1712_);
lean_dec_ref(v___x_1709_);
return v_a_1712_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__4___boxed(lean_object* v___x_1713_, lean_object* v___x_1714_, lean_object* v___x_1715_, lean_object* v_waiter_1716_, lean_object* v_a_1717_, lean_object* v___x_1718_, lean_object* v___x_1719_, lean_object* v_a_1720_, lean_object* v___y_1721_){
_start:
{
uint8_t v___x_7267__boxed_1722_; lean_object* v_res_1723_; 
v___x_7267__boxed_1722_ = lean_unbox(v___x_1719_);
v_res_1723_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__4(v___x_1713_, v___x_1714_, v___x_1715_, v_waiter_1716_, v_a_1717_, v___x_1718_, v___x_7267__boxed_1722_, v_a_1720_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__7___boxed(lean_object* v_i_1724_, lean_object* v___x_1725_, lean_object* v___x_1726_, lean_object* v_waiter_1727_, lean_object* v_as_1728_, lean_object* v_sz_1729_, lean_object* v_x_1730_, lean_object* v___y_1731_){
_start:
{
size_t v_i_boxed_1732_; size_t v_sz_boxed_1733_; lean_object* v_res_1734_; 
v_i_boxed_1732_ = lean_unbox_usize(v_i_1724_);
lean_dec(v_i_1724_);
v_sz_boxed_1733_ = lean_unbox_usize(v_sz_1729_);
lean_dec(v_sz_1729_);
v_res_1734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__7(v_i_boxed_1732_, v___x_1725_, v___x_1726_, v_waiter_1727_, v_as_1728_, v_sz_boxed_1733_, v_x_1730_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg(lean_object* v___x_1735_, lean_object* v___x_1736_, lean_object* v_waiter_1737_, lean_object* v_as_1738_, size_t v_sz_1739_, size_t v_i_1740_, lean_object* v_b_1741_){
_start:
{
uint8_t v___x_1743_; 
v___x_1743_ = lean_usize_dec_lt(v_i_1740_, v_sz_1739_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
lean_dec_ref(v_as_1738_);
lean_dec_ref(v_waiter_1737_);
lean_dec(v___x_1736_);
lean_dec_ref(v___x_1735_);
v___x_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1744_, 0, v_b_1741_);
v___x_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
return v___x_1745_;
}
else
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___f_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; lean_object* v_a_1751_; lean_object* v___x_1752_; lean_object* v___f_1753_; lean_object* v___x_1754_; lean_object* v___f_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___f_1761_; uint8_t v___x_1762_; lean_object* v___x_1763_; 
v___x_1746_ = lean_io_promise_new();
v___x_1747_ = lean_box(0);
v___f_1748_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___closed__0));
v___x_1749_ = lean_unsigned_to_nat(0u);
v___x_1750_ = lean_nat_dec_eq(v___x_1736_, v___x_1749_);
v_a_1751_ = lean_array_uget_borrowed(v_as_1738_, v_i_1740_);
v___x_1752_ = lean_box(v___x_1750_);
lean_inc(v_a_1751_);
lean_inc_ref(v_waiter_1737_);
lean_inc(v___x_1736_);
lean_inc_ref(v___x_1735_);
v___f_1753_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__4___boxed), 9, 7);
lean_closure_set(v___f_1753_, 0, v___x_1747_);
lean_closure_set(v___f_1753_, 1, v___x_1735_);
lean_closure_set(v___f_1753_, 2, v___x_1736_);
lean_closure_set(v___f_1753_, 3, v_waiter_1737_);
lean_closure_set(v___f_1753_, 4, v_a_1751_);
lean_closure_set(v___f_1753_, 5, v___x_1749_);
lean_closure_set(v___f_1753_, 6, v___x_1752_);
v___x_1754_ = lean_box(v___x_1750_);
lean_inc(v_a_1751_);
lean_inc_ref(v_waiter_1737_);
v___f_1755_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__6___boxed), 9, 7);
lean_closure_set(v___f_1755_, 0, v_waiter_1737_);
lean_closure_set(v___f_1755_, 1, v_a_1751_);
lean_closure_set(v___f_1755_, 2, v___f_1753_);
lean_closure_set(v___f_1755_, 3, v___x_1749_);
lean_closure_set(v___f_1755_, 4, v___x_1754_);
lean_closure_set(v___f_1755_, 5, v___x_1747_);
lean_closure_set(v___f_1755_, 6, v___f_1748_);
v___x_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1746_);
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
v___x_1758_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1749_, v___x_1750_, v___x_1757_, v___f_1755_);
v___x_1759_ = lean_box_usize(v_i_1740_);
v___x_1760_ = lean_box_usize(v_sz_1739_);
v___f_1761_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__7___boxed), 8, 6);
lean_closure_set(v___f_1761_, 0, v___x_1759_);
lean_closure_set(v___f_1761_, 1, v___x_1735_);
lean_closure_set(v___f_1761_, 2, v___x_1736_);
lean_closure_set(v___f_1761_, 3, v_waiter_1737_);
lean_closure_set(v___f_1761_, 4, v_as_1738_);
lean_closure_set(v___f_1761_, 5, v___x_1760_);
v___x_1762_ = 0;
v___x_1763_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1749_, v___x_1762_, v___x_1758_, v___f_1761_);
return v___x_1763_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__7(size_t v_i_1764_, lean_object* v___x_1765_, lean_object* v___x_1766_, lean_object* v_waiter_1767_, lean_object* v_as_1768_, size_t v_sz_1769_, lean_object* v_x_1770_){
_start:
{
if (lean_obj_tag(v_x_1770_) == 0)
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1780_; 
lean_dec_ref(v_as_1768_);
lean_dec_ref(v_waiter_1767_);
lean_dec(v___x_1766_);
lean_dec_ref(v___x_1765_);
v_a_1772_ = lean_ctor_get(v_x_1770_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_x_1770_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1774_ = v_x_1770_;
v_isShared_1775_ = v_isSharedCheck_1780_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v_x_1770_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1780_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1778_; 
v___x_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1777_);
return v___x_1778_;
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1800_; 
v_a_1781_ = lean_ctor_get(v_x_1770_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_x_1770_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1783_ = v_x_1770_;
v_isShared_1784_ = v_isSharedCheck_1800_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v_x_1770_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1800_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
if (lean_obj_tag(v_a_1781_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1795_; 
lean_dec_ref(v_as_1768_);
lean_dec_ref(v_waiter_1767_);
lean_dec(v___x_1766_);
lean_dec_ref(v___x_1765_);
v_a_1785_ = lean_ctor_get(v_a_1781_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_a_1781_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1787_ = v_a_1781_;
v_isShared_1788_ = v_isSharedCheck_1795_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v_a_1781_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1795_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 0, v_a_1785_);
v___x_1790_ = v___x_1783_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
lean_object* v___x_1792_; 
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 0, v___x_1790_);
v___x_1792_ = v___x_1787_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1790_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
else
{
lean_object* v_a_1796_; size_t v___x_1797_; size_t v___x_1798_; lean_object* v___x_1799_; 
lean_del_object(v___x_1783_);
v_a_1796_ = lean_ctor_get(v_a_1781_, 0);
lean_inc(v_a_1796_);
lean_dec_ref(v_a_1781_);
v___x_1797_ = ((size_t)1ULL);
v___x_1798_ = lean_usize_add(v_i_1764_, v___x_1797_);
v___x_1799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg(v___x_1765_, v___x_1766_, v_waiter_1767_, v_as_1768_, v_sz_1769_, v___x_1798_, v_a_1796_);
return v___x_1799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___boxed(lean_object* v___x_1801_, lean_object* v___x_1802_, lean_object* v_waiter_1803_, lean_object* v_as_1804_, lean_object* v_sz_1805_, lean_object* v_i_1806_, lean_object* v_b_1807_, lean_object* v___y_1808_){
_start:
{
size_t v_sz_boxed_1809_; size_t v_i_boxed_1810_; lean_object* v_res_1811_; 
v_sz_boxed_1809_ = lean_unbox_usize(v_sz_1805_);
lean_dec(v_sz_1805_);
v_i_boxed_1810_ = lean_unbox_usize(v_i_1806_);
lean_dec(v_i_1806_);
v_res_1811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg(v___x_1801_, v___x_1802_, v_waiter_1803_, v_as_1804_, v_sz_boxed_1809_, v_i_boxed_1810_, v_b_1807_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__0(lean_object* v___x_1812_, lean_object* v___x_1813_, lean_object* v___x_1814_, lean_object* v___x_1815_, uint8_t v___x_1816_, lean_object* v___f_1817_, lean_object* v_waiter_1818_){
_start:
{
size_t v_sz_1820_; size_t v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v_sz_1820_ = lean_array_size(v___x_1812_);
v___x_1821_ = ((size_t)0ULL);
lean_inc_ref(v___x_1812_);
v___x_1822_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg(v___x_1812_, v___x_1813_, v_waiter_1818_, v___x_1812_, v_sz_1820_, v___x_1821_, v___x_1814_);
v___x_1823_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1815_, v___x_1816_, v___x_1822_, v___f_1817_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__0___boxed(lean_object* v___x_1824_, lean_object* v___x_1825_, lean_object* v___x_1826_, lean_object* v___x_1827_, lean_object* v___x_1828_, lean_object* v___f_1829_, lean_object* v_waiter_1830_, lean_object* v___y_1831_){
_start:
{
uint8_t v___x_7436__boxed_1832_; lean_object* v_res_1833_; 
v___x_7436__boxed_1832_ = lean_unbox(v___x_1828_);
v_res_1833_ = l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__0(v___x_1824_, v___x_1825_, v___x_1826_, v___x_1827_, v___x_7436__boxed_1832_, v___f_1829_, v_waiter_1830_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__3(lean_object* v___x_1834_, lean_object* v___x_1835_, size_t v_sz_1836_, size_t v___x_1837_, lean_object* v___x_1838_, lean_object* v___x_1839_, uint8_t v___x_1840_, lean_object* v___f_1841_){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(v___x_1834_, v___x_1835_, v_sz_1836_, v___x_1837_, v___x_1838_);
v___x_1844_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1839_, v___x_1840_, v___x_1843_, v___f_1841_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__3___boxed(lean_object* v___x_1845_, lean_object* v___x_1846_, lean_object* v_sz_1847_, lean_object* v___x_1848_, lean_object* v___x_1849_, lean_object* v___x_1850_, lean_object* v___x_1851_, lean_object* v___f_1852_, lean_object* v___y_1853_){
_start:
{
size_t v_sz_boxed_1854_; size_t v___x_7461__boxed_1855_; uint8_t v___x_7464__boxed_1856_; lean_object* v_res_1857_; 
v_sz_boxed_1854_ = lean_unbox_usize(v_sz_1847_);
lean_dec(v_sz_1847_);
v___x_7461__boxed_1855_ = lean_unbox_usize(v___x_1848_);
lean_dec(v___x_1848_);
v___x_7464__boxed_1856_ = lean_unbox(v___x_1851_);
v_res_1857_ = l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__3(v___x_1845_, v___x_1846_, v_sz_boxed_1854_, v___x_7461__boxed_1855_, v___x_1849_, v___x_1850_, v___x_7464__boxed_1856_, v___f_1852_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__2(lean_object* v___x_1858_, lean_object* v___x_1859_, size_t v_sz_1860_, size_t v___x_1861_, lean_object* v___x_1862_, lean_object* v___x_1863_, uint8_t v___x_1864_, lean_object* v___f_1865_){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(v___x_1858_, v___x_1859_, v_sz_1860_, v___x_1861_, v___x_1862_);
v___x_1868_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1863_, v___x_1864_, v___x_1867_, v___f_1865_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__2___boxed(lean_object* v___x_1869_, lean_object* v___x_1870_, lean_object* v_sz_1871_, lean_object* v___x_1872_, lean_object* v___x_1873_, lean_object* v___x_1874_, lean_object* v___x_1875_, lean_object* v___f_1876_, lean_object* v___y_1877_){
_start:
{
size_t v_sz_boxed_1878_; size_t v___x_7489__boxed_1879_; uint8_t v___x_7492__boxed_1880_; lean_object* v_res_1881_; 
v_sz_boxed_1878_ = lean_unbox_usize(v_sz_1871_);
lean_dec(v_sz_1871_);
v___x_7489__boxed_1879_ = lean_unbox_usize(v___x_1872_);
lean_dec(v___x_1872_);
v___x_7492__boxed_1880_ = lean_unbox(v___x_1875_);
v_res_1881_ = l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__2(v___x_1869_, v___x_1870_, v_sz_boxed_1878_, v___x_7489__boxed_1879_, v___x_1873_, v___x_1874_, v___x_7492__boxed_1880_, v___f_1876_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg(lean_object* v_selectables_1886_){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; uint8_t v___x_1890_; 
v___x_1888_ = lean_array_get_size(v_selectables_1886_);
v___x_1889_ = lean_unsigned_to_nat(0u);
v___x_1890_ = lean_nat_dec_eq(v___x_1888_, v___x_1889_);
if (v___x_1890_ == 0)
{
size_t v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = ((size_t)8ULL);
v___x_1892_ = lean_io_get_random_bytes(v___x_1891_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1920_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1920_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1920_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___f_1897_; uint64_t v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___f_1903_; lean_object* v___x_1904_; lean_object* v___f_1905_; lean_object* v___x_1906_; size_t v_sz_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___f_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___f_1915_; lean_object* v___x_1916_; lean_object* v___x_1918_; 
v___f_1897_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_tryOne___redArg___closed__0));
v___x_1898_ = l_ByteArray_toUInt64LE_x21(v_a_1893_);
lean_dec(v_a_1893_);
v___x_1899_ = lean_uint64_to_nat(v___x_1898_);
v___x_1900_ = l_mkStdGen(v___x_1899_);
lean_dec(v___x_1899_);
v___x_1901_ = l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt___redArg(v_selectables_1886_, v___x_1900_);
v___x_1902_ = lean_box(0);
v___f_1903_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_combine___redArg___closed__0));
v___x_1904_ = lean_box(v___x_1890_);
lean_inc_ref(v___x_1901_);
v___f_1905_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_1905_, 0, v___x_1901_);
lean_closure_set(v___f_1905_, 1, v___x_1888_);
lean_closure_set(v___f_1905_, 2, v___x_1902_);
lean_closure_set(v___f_1905_, 3, v___x_1889_);
lean_closure_set(v___f_1905_, 4, v___x_1904_);
lean_closure_set(v___f_1905_, 5, v___f_1903_);
v___x_1906_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__1));
v_sz_1907_ = lean_array_size(v___x_1901_);
v___x_1908_ = lean_box_usize(v_sz_1907_);
v___x_1909_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_combine___redArg___boxed__const__1));
v___x_1910_ = lean_box(v___x_1890_);
lean_inc_ref(v___x_1901_);
v___f_1911_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_1911_, 0, v___x_1888_);
lean_closure_set(v___f_1911_, 1, v___x_1901_);
lean_closure_set(v___f_1911_, 2, v___x_1908_);
lean_closure_set(v___f_1911_, 3, v___x_1909_);
lean_closure_set(v___f_1911_, 4, v___x_1902_);
lean_closure_set(v___f_1911_, 5, v___x_1889_);
lean_closure_set(v___f_1911_, 6, v___x_1910_);
lean_closure_set(v___f_1911_, 7, v___f_1903_);
v___x_1912_ = lean_box_usize(v_sz_1907_);
v___x_1913_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_combine___redArg___boxed__const__1));
v___x_1914_ = lean_box(v___x_1890_);
v___f_1915_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_1915_, 0, v___x_1888_);
lean_closure_set(v___f_1915_, 1, v___x_1901_);
lean_closure_set(v___f_1915_, 2, v___x_1912_);
lean_closure_set(v___f_1915_, 3, v___x_1913_);
lean_closure_set(v___f_1915_, 4, v___x_1906_);
lean_closure_set(v___f_1915_, 5, v___x_1889_);
lean_closure_set(v___f_1915_, 6, v___x_1914_);
lean_closure_set(v___f_1915_, 7, v___f_1897_);
v___x_1916_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1916_, 0, v___f_1915_);
lean_ctor_set(v___x_1916_, 1, v___f_1905_);
lean_ctor_set(v___x_1916_, 2, v___f_1911_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v___x_1916_);
v___x_1918_ = v___x_1895_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1916_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
lean_dec_ref(v_selectables_1886_);
v_a_1921_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1892_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1892_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
else
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
lean_dec_ref(v_selectables_1886_);
v___x_1929_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_one___redArg___closed__1));
v___x_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1929_);
return v___x_1930_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___boxed(lean_object* v_selectables_1931_, lean_object* v_a_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_Std_Internal_IO_Async_Selectable_combine___redArg(v_selectables_1931_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine(lean_object* v_00_u03b1_1934_, lean_object* v_selectables_1935_){
_start:
{
lean_object* v___x_1937_; 
v___x_1937_ = l_Std_Internal_IO_Async_Selectable_combine___redArg(v_selectables_1935_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___boxed(lean_object* v_00_u03b1_1938_, lean_object* v_selectables_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Std_Internal_IO_Async_Selectable_combine(v_00_u03b1_1938_, v_selectables_1939_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0(lean_object* v_00_u03b1_1942_, lean_object* v___x_1943_, lean_object* v_as_1944_, size_t v_sz_1945_, size_t v_i_1946_, lean_object* v_b_1947_){
_start:
{
lean_object* v___x_1949_; 
v___x_1949_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(v___x_1943_, v_as_1944_, v_sz_1945_, v_i_1946_, v_b_1947_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___boxed(lean_object* v_00_u03b1_1950_, lean_object* v___x_1951_, lean_object* v_as_1952_, lean_object* v_sz_1953_, lean_object* v_i_1954_, lean_object* v_b_1955_, lean_object* v___y_1956_){
_start:
{
size_t v_sz_boxed_1957_; size_t v_i_boxed_1958_; lean_object* v_res_1959_; 
v_sz_boxed_1957_ = lean_unbox_usize(v_sz_1953_);
lean_dec(v_sz_1953_);
v_i_boxed_1958_ = lean_unbox_usize(v_i_1954_);
lean_dec(v_i_1954_);
v_res_1959_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0(v_00_u03b1_1950_, v___x_1951_, v_as_1952_, v_sz_boxed_1957_, v_i_boxed_1958_, v_b_1955_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1(lean_object* v_00_u03b1_1960_, lean_object* v___x_1961_, lean_object* v___x_1962_, lean_object* v_waiter_1963_, lean_object* v_as_1964_, size_t v_sz_1965_, size_t v_i_1966_, lean_object* v_b_1967_){
_start:
{
lean_object* v___x_1969_; 
v___x_1969_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg(v___x_1961_, v___x_1962_, v_waiter_1963_, v_as_1964_, v_sz_1965_, v_i_1966_, v_b_1967_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___boxed(lean_object* v_00_u03b1_1970_, lean_object* v___x_1971_, lean_object* v___x_1972_, lean_object* v_waiter_1973_, lean_object* v_as_1974_, lean_object* v_sz_1975_, lean_object* v_i_1976_, lean_object* v_b_1977_, lean_object* v___y_1978_){
_start:
{
size_t v_sz_boxed_1979_; size_t v_i_boxed_1980_; lean_object* v_res_1981_; 
v_sz_boxed_1979_ = lean_unbox_usize(v_sz_1975_);
lean_dec(v_sz_1975_);
v_i_boxed_1980_ = lean_unbox_usize(v_i_1976_);
lean_dec(v_i_1976_);
v_res_1981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1(v_00_u03b1_1970_, v___x_1971_, v___x_1972_, v_waiter_1973_, v_as_1974_, v_sz_boxed_1979_, v_i_boxed_1980_, v_b_1977_);
return v_res_1981_;
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
