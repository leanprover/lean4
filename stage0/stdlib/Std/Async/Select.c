// Lean compiler output
// Module: Std.Async.Select
// Imports: public import Init.Data.Random public import Std.Async.Basic import Init.Data.ByteArray.Extra import Init.Data.Array.Lemmas import Init.Omega
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
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_io_promise_new();
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_stdRange;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_stdNext(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
uint64_t l_ByteArray_toUInt64LE_x21(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_mkStdGen(lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_random_bytes(size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_withPromise___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_withPromise(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___redArg___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Waiter_race___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Waiter_race___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_Waiter_race___redArg___closed__0 = (const lean_object*)&l_Std_Async_Waiter_race___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_checkFinished___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_checkFinished(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_checkFinished___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Select_0__Std_Async_shuffleIt_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Select_0__Std_Async_shuffleIt_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Select_0__Std_Async_shuffleIt_go_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Select_0__Std_Async_shuffleIt_go_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Select_0__Std_Async_shuffleIt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Async_Selectable_one___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "the promise linked to the Async was dropped"};
static const lean_object* l_Std_Async_Selectable_one___redArg___lam__2___closed__0 = (const lean_object*)&l_Std_Async_Selectable_one___redArg___lam__2___closed__0_value;
static const lean_closure_object l_Std_Async_Selectable_one___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Selectable_one___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_Selectable_one___redArg___lam__2___closed__0_value)} };
static const lean_object* l_Std_Async_Selectable_one___redArg___lam__2___closed__1 = (const lean_object*)&l_Std_Async_Selectable_one___redArg___lam__2___closed__1_value;
static const lean_closure_object l_Std_Async_Selectable_one___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Selectable_one___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_Selectable_one___redArg___lam__2___closed__1_value)} };
static const lean_object* l_Std_Async_Selectable_one___redArg___lam__2___closed__2 = (const lean_object*)&l_Std_Async_Selectable_one___redArg___lam__2___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__8(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__9(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__1(size_t, uint8_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___closed__0_value;
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__4, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__11(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__2(size_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Async_Selectable_one___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Selectable.one requires at least one Selectable"};
static const lean_object* l_Std_Async_Selectable_one___redArg___closed__0 = (const lean_object*)&l_Std_Async_Selectable_one___redArg___closed__0_value;
static const lean_ctor_object l_Std_Async_Selectable_one___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Std_Async_Selectable_one___redArg___closed__0_value)}};
static const lean_object* l_Std_Async_Selectable_one___redArg___closed__1 = (const lean_object*)&l_Std_Async_Selectable_one___redArg___closed__1_value;
static const lean_ctor_object l_Std_Async_Selectable_one___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Selectable_one___redArg___closed__1_value)}};
static const lean_object* l_Std_Async_Selectable_one___redArg___closed__2 = (const lean_object*)&l_Std_Async_Selectable_one___redArg___closed__2_value;
static const lean_ctor_object l_Std_Async_Selectable_one___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Selectable_one___redArg___closed__2_value)}};
static const lean_object* l_Std_Async_Selectable_one___redArg___closed__3 = (const lean_object*)&l_Std_Async_Selectable_one___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_Selectable_tryOne___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__0___closed__0 = (const lean_object*)&l_Std_Async_Selectable_tryOne___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Async_Selectable_tryOne___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Selectable_tryOne___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__0___closed__1 = (const lean_object*)&l_Std_Async_Selectable_tryOne___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__2(size_t, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Selectable_tryOne___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Selectable_tryOne___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_Selectable_tryOne___redArg___closed__0 = (const lean_object*)&l_Std_Async_Selectable_tryOne___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg___lam__1(size_t, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__8(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__10(size_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Selectable_combine___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Selectable_combine___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Async_Selectable_combine___redArg___closed__0 = (const lean_object*)&l_Std_Async_Selectable_combine___redArg___closed__0_value;
static const lean_ctor_object l_Std_Async_Selectable_combine___redArg___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Std_Async_Selectable_combine___redArg___boxed__const__1 = (const lean_object*)&l_Std_Async_Selectable_combine___redArg___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_withPromise___redArg(lean_object* v_w_1_, lean_object* v_p_2_){
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
LEAN_EXPORT lean_object* l_Std_Async_Waiter_withPromise(lean_object* v_00_u03b1_12_, lean_object* v_00_u03b2_13_, lean_object* v_w_14_, lean_object* v_p_15_){
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
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___redArg___lam__0(uint8_t v_s_25_){
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
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___redArg___lam__0___boxed(lean_object* v_s_34_){
_start:
{
uint8_t v_s_boxed_35_; lean_object* v_res_36_; 
v_s_boxed_35_ = lean_unbox(v_s_34_);
v_res_36_ = l_Std_Async_Waiter_race___redArg___lam__0(v_s_boxed_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___redArg___lam__1(lean_object* v_lose_37_, lean_object* v_win_38_, lean_object* v_promise_39_, uint8_t v_first_40_){
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
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___redArg___lam__1___boxed(lean_object* v_lose_42_, lean_object* v_win_43_, lean_object* v_promise_44_, lean_object* v_first_45_){
_start:
{
uint8_t v_first_boxed_46_; lean_object* v_res_47_; 
v_first_boxed_46_ = lean_unbox(v_first_45_);
v_res_47_ = l_Std_Async_Waiter_race___redArg___lam__1(v_lose_42_, v_win_43_, v_promise_44_, v_first_boxed_46_);
lean_dec(v_lose_42_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___redArg(lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_w_51_, lean_object* v_lose_52_, lean_object* v_win_53_){
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
v___f_57_ = ((lean_object*)(l_Std_Async_Waiter_race___redArg___closed__0));
v___f_58_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___redArg___lam__1___boxed), 4, 3);
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
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race(lean_object* v_m_62_, lean_object* v_00_u03b1_63_, lean_object* v_00_u03b2_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_w_67_, lean_object* v_lose_68_, lean_object* v_win_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Std_Async_Waiter_race___redArg(v_inst_65_, v_inst_66_, v_w_67_, v_lose_68_, v_win_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_checkFinished___redArg(lean_object* v_inst_71_, lean_object* v_w_72_){
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
LEAN_EXPORT lean_object* l_Std_Async_Waiter_checkFinished(lean_object* v_m_76_, lean_object* v_00_u03b1_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_w_80_){
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
LEAN_EXPORT lean_object* l_Std_Async_Waiter_checkFinished___boxed(lean_object* v_m_84_, lean_object* v_00_u03b1_85_, lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_w_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Std_Async_Waiter_checkFinished(v_m_84_, v_00_u03b1_85_, v_inst_86_, v_inst_87_, v_w_88_);
lean_dec_ref(v_inst_86_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0_spec__0(lean_object* v_genLo_90_, lean_object* v_genMag_91_, lean_object* v_x_92_, lean_object* v_x_93_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0_spec__0___boxed(lean_object* v_genLo_115_, lean_object* v_genMag_116_, lean_object* v_x_117_, lean_object* v_x_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0_spec__0(v_genLo_115_, v_genMag_116_, v_x_117_, v_x_118_);
lean_dec(v_genMag_116_);
lean_dec(v_genLo_115_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0(lean_object* v_g_120_, lean_object* v_lo_121_, lean_object* v_hi_122_){
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
v___x_138_ = l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0_spec__0(v_fst_127_, v_genMag_131_, v_tgtMag_135_, v___x_137_);
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
LEAN_EXPORT lean_object* l_randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0___boxed(lean_object* v_g_153_, lean_object* v_lo_154_, lean_object* v_hi_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0(v_g_153_, v_lo_154_, v_hi_155_);
lean_dec(v_hi_155_);
lean_dec(v_lo_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Select_0__Std_Async_shuffleIt_go___redArg(lean_object* v_xs_157_, lean_object* v_gen_158_, lean_object* v_i_159_){
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
v___x_164_ = l_randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0(v_gen_158_, v_i_159_, v___x_162_);
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
LEAN_EXPORT lean_object* l___private_Std_Async_Select_0__Std_Async_shuffleIt_go(lean_object* v_00_u03b1_170_, lean_object* v_xs_171_, lean_object* v_gen_172_, lean_object* v_i_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt_go___redArg(v_xs_171_, v_gen_172_, v_i_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Select_0__Std_Async_shuffleIt_go_match__1_splitter___redArg(lean_object* v_x_175_, lean_object* v_h__1_176_){
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
LEAN_EXPORT lean_object* l___private_Std_Async_Select_0__Std_Async_shuffleIt_go_match__1_splitter(lean_object* v_motive_180_, lean_object* v_x_181_, lean_object* v_h__1_182_){
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
LEAN_EXPORT lean_object* l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(lean_object* v_xs_186_, lean_object* v_gen_187_){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt_go___redArg(v_xs_186_, v_gen_187_, v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Select_0__Std_Async_shuffleIt(lean_object* v_00_u03b1_190_, lean_object* v_xs_191_, lean_object* v_gen_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(v_xs_191_, v_gen_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___redArg(lean_object* v_e_194_){
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
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___redArg___boxed(lean_object* v_e_214_, lean_object* v_a_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___redArg(v_e_214_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1(lean_object* v_00_u03b1_217_, lean_object* v_e_218_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___redArg(v_e_218_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___boxed(lean_object* v_00_u03b1_221_, lean_object* v_e_222_, lean_object* v_a_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1(v_00_u03b1_221_, v_e_222_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__0(lean_object* v___x_225_, lean_object* v_x_226_){
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
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__0___boxed(lean_object* v___x_230_, lean_object* v_x_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Std_Async_Selectable_one___redArg___lam__0(v___x_230_, v_x_231_);
lean_dec(v_x_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__1(lean_object* v___f_233_, lean_object* v_x_234_){
_start:
{
if (lean_obj_tag(v_x_234_) == 0)
{
lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_244_; 
lean_dec_ref(v___f_233_);
v_a_236_ = lean_ctor_get(v_x_234_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v_x_234_);
if (v_isSharedCheck_244_ == 0)
{
v___x_238_ = v_x_234_;
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v_x_234_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_236_);
v___x_241_ = v_reuseFailAlloc_243_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; 
v___x_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
return v___x_242_;
}
}
}
else
{
lean_object* v_a_245_; 
v_a_245_ = lean_ctor_get(v_x_234_, 0);
lean_inc(v_a_245_);
lean_dec_ref(v_x_234_);
if (lean_obj_tag(v_a_245_) == 0)
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_254_; 
lean_dec_ref(v___f_233_);
v_a_246_ = lean_ctor_get(v_a_245_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v_a_245_);
if (v_isSharedCheck_254_ == 0)
{
v___x_248_ = v_a_245_;
v_isShared_249_ = v_isSharedCheck_254_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v_a_245_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_254_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_246_);
v___x_251_ = v_reuseFailAlloc_253_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_252_; 
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
return v___x_252_;
}
}
}
else
{
lean_object* v_a_255_; lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v_a_255_ = lean_ctor_get(v_a_245_, 0);
lean_inc(v_a_255_);
lean_dec_ref(v_a_245_);
v___x_256_ = lean_io_promise_result_opt(v_a_255_);
lean_dec(v_a_255_);
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = 0;
v___x_259_ = lean_task_map(v___f_233_, v___x_256_, v___x_257_, v___x_258_);
v___x_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
return v___x_260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__1___boxed(lean_object* v___f_261_, lean_object* v_x_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Std_Async_Selectable_one___redArg___lam__1(v___f_261_, v_x_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__2(lean_object* v_x_270_, lean_object* v_x_271_){
_start:
{
if (lean_obj_tag(v_x_271_) == 0)
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_281_; 
lean_dec_ref(v_x_270_);
v_a_273_ = lean_ctor_get(v_x_271_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v_x_271_);
if (v_isSharedCheck_281_ == 0)
{
v___x_275_ = v_x_271_;
v_isShared_276_ = v_isSharedCheck_281_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v_x_271_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_281_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_273_);
v___x_278_ = v_reuseFailAlloc_280_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_279_; 
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
}
else
{
lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_293_; 
v_isSharedCheck_293_ = !lean_is_exclusive(v_x_271_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; 
v_unused_294_ = lean_ctor_get(v_x_271_, 0);
lean_dec(v_unused_294_);
v___x_283_ = v_x_271_;
v_isShared_284_ = v_isSharedCheck_293_;
goto v_resetjp_282_;
}
else
{
lean_dec(v_x_271_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_293_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___f_285_; lean_object* v___x_287_; 
v___f_285_ = ((lean_object*)(l_Std_Async_Selectable_one___redArg___lam__2___closed__2));
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v_x_270_);
v___x_287_ = v___x_283_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_x_270_);
v___x_287_ = v_reuseFailAlloc_292_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; lean_object* v___x_291_; 
v___x_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
v___x_289_ = lean_unsigned_to_nat(0u);
v___x_290_ = 0;
v___x_291_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_289_, v___x_290_, v___x_288_, v___f_285_);
return v___x_291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__2___boxed(lean_object* v_x_295_, lean_object* v_x_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Std_Async_Selectable_one___redArg___lam__2(v_x_295_, v_x_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__3(lean_object* v___x_299_, lean_object* v_a_300_, lean_object* v___f_301_, lean_object* v_x_302_){
_start:
{
if (lean_obj_tag(v_x_302_) == 0)
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_312_; 
lean_dec_ref(v___f_301_);
v_a_304_ = lean_ctor_get(v_x_302_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v_x_302_);
if (v_isSharedCheck_312_ == 0)
{
v___x_306_ = v_x_302_;
v_isShared_307_ = v_isSharedCheck_312_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v_x_302_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_312_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_304_);
v___x_309_ = v_reuseFailAlloc_311_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_310_; 
v___x_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
return v___x_310_;
}
}
}
else
{
lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_324_; 
v_isSharedCheck_324_ = !lean_is_exclusive(v_x_302_);
if (v_isSharedCheck_324_ == 0)
{
lean_object* v_unused_325_; 
v_unused_325_ = lean_ctor_get(v_x_302_, 0);
lean_dec(v_unused_325_);
v___x_314_ = v_x_302_;
v_isShared_315_ = v_isSharedCheck_324_;
goto v_resetjp_313_;
}
else
{
lean_dec(v_x_302_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_324_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_316_ = lean_io_promise_resolve(v___x_299_, v_a_300_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_316_);
v___x_318_ = v___x_314_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_316_);
v___x_318_ = v_reuseFailAlloc_323_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; lean_object* v___x_322_; 
v___x_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
v___x_320_ = lean_unsigned_to_nat(0u);
v___x_321_ = 0;
v___x_322_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_320_, v___x_321_, v___x_319_, v___f_301_);
return v___x_322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__3___boxed(lean_object* v___x_326_, lean_object* v_a_327_, lean_object* v___f_328_, lean_object* v_x_329_, lean_object* v___y_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_Async_Selectable_one___redArg___lam__3(v___x_326_, v_a_327_, v___f_328_, v_x_329_);
lean_dec(v_a_327_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__4(lean_object* v___x_332_, lean_object* v___y_333_){
_start:
{
if (lean_obj_tag(v___y_333_) == 0)
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
v_a_334_ = lean_ctor_get(v___y_333_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___y_333_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___y_333_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___y_333_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
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
return v___x_339_;
}
}
}
else
{
lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
v_isSharedCheck_348_ = !lean_is_exclusive(v___y_333_);
if (v_isSharedCheck_348_ == 0)
{
lean_object* v_unused_349_; 
v_unused_349_ = lean_ctor_get(v___y_333_, 0);
lean_dec(v_unused_349_);
v___x_343_ = v___y_333_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_dec(v___y_333_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v___x_332_);
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_332_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__2(lean_object* v_a_350_, lean_object* v_x_351_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__2___boxed(lean_object* v_a_365_, lean_object* v_x_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__2(v_a_365_, v_x_366_);
lean_dec(v_a_365_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__1(lean_object* v_a_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_370_, 0, v_a_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__0(lean_object* v_a_371_, lean_object* v_x_372_){
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
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_383_ = lean_io_promise_resolve(v_x_372_, v_a_371_);
v___x_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__0___boxed(lean_object* v_a_386_, lean_object* v_x_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__0(v_a_386_, v_x_387_);
lean_dec(v_a_386_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__8(lean_object* v_a_390_, lean_object* v___f_391_, uint8_t v___x_392_, lean_object* v___x_393_, uint8_t v_a_394_, lean_object* v___f_395_, lean_object* v_x_396_){
_start:
{
if (lean_obj_tag(v_x_396_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_406_; 
lean_dec_ref(v___f_395_);
lean_dec_ref(v___f_391_);
v_a_398_ = lean_ctor_get(v_x_396_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v_x_396_);
if (v_isSharedCheck_406_ == 0)
{
v___x_400_ = v_x_396_;
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v_x_396_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_398_);
v___x_403_ = v_reuseFailAlloc_405_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; 
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
return v___x_404_;
}
}
}
else
{
lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_418_; 
v_isSharedCheck_418_ = !lean_is_exclusive(v_x_396_);
if (v_isSharedCheck_418_ == 0)
{
lean_object* v_unused_419_; 
v_unused_419_ = lean_ctor_get(v_x_396_, 0);
lean_dec(v_unused_419_);
v___x_408_ = v_x_396_;
v_isShared_409_ = v_isSharedCheck_418_;
goto v_resetjp_407_;
}
else
{
lean_dec(v_x_396_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_418_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_410_ = lean_io_promise_result_opt(v_a_390_);
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = lean_io_bind_task(v___x_410_, v___f_391_, v___x_411_, v___x_392_);
lean_dec_ref(v___x_412_);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 0, v___x_393_);
v___x_414_ = v___x_408_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_393_);
v___x_414_ = v_reuseFailAlloc_417_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
v___x_416_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_411_, v_a_394_, v___x_415_, v___f_395_);
return v___x_416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__8___boxed(lean_object* v_a_420_, lean_object* v___f_421_, lean_object* v___x_422_, lean_object* v___x_423_, lean_object* v_a_424_, lean_object* v___f_425_, lean_object* v_x_426_, lean_object* v___y_427_){
_start:
{
uint8_t v___x_10927__boxed_428_; uint8_t v_a_10929__boxed_429_; lean_object* v_res_430_; 
v___x_10927__boxed_428_ = lean_unbox(v___x_422_);
v_a_10929__boxed_429_ = lean_unbox(v_a_424_);
v_res_430_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__8(v_a_420_, v___f_421_, v___x_10927__boxed_428_, v___x_423_, v_a_10929__boxed_429_, v___f_425_, v_x_426_);
lean_dec(v_a_420_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__9(lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v___f_433_, uint8_t v___x_434_, lean_object* v___x_435_, uint8_t v_a_436_, lean_object* v___f_437_, lean_object* v_x_438_){
_start:
{
if (lean_obj_tag(v_x_438_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_448_; 
lean_dec_ref(v___f_437_);
lean_dec_ref(v___f_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
v_a_440_ = lean_ctor_get(v_x_438_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v_x_438_);
if (v_isSharedCheck_448_ == 0)
{
v___x_442_ = v_x_438_;
v_isShared_443_ = v_isSharedCheck_448_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v_x_438_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_448_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_440_);
v___x_445_ = v_reuseFailAlloc_447_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_446_; 
v___x_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
return v___x_446_;
}
}
}
else
{
lean_object* v_selector_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_464_; 
v_selector_449_ = lean_ctor_get(v_a_431_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v_a_431_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; 
v_unused_465_ = lean_ctor_get(v_a_431_, 1);
lean_dec(v_unused_465_);
v___x_451_ = v_a_431_;
v_isShared_452_ = v_isSharedCheck_464_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_selector_449_);
lean_dec(v_a_431_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_464_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v_a_453_; lean_object* v_registerFn_454_; lean_object* v___x_456_; 
v_a_453_ = lean_ctor_get(v_x_438_, 0);
lean_inc_n(v_a_453_, 2);
lean_dec_ref(v_x_438_);
v_registerFn_454_ = lean_ctor_get(v_selector_449_, 1);
lean_inc_ref(v_registerFn_454_);
lean_dec_ref(v_selector_449_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v_a_453_);
lean_ctor_set(v___x_451_, 0, v_a_432_);
v___x_456_ = v___x_451_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_432_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_a_453_);
v___x_456_ = v_reuseFailAlloc_463_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___f_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_457_ = lean_apply_2(v_registerFn_454_, v___x_456_, lean_box(0));
v___x_458_ = lean_box(v___x_434_);
v___x_459_ = lean_box(v_a_436_);
v___f_460_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__8___boxed), 8, 6);
lean_closure_set(v___f_460_, 0, v_a_453_);
lean_closure_set(v___f_460_, 1, v___f_433_);
lean_closure_set(v___f_460_, 2, v___x_458_);
lean_closure_set(v___f_460_, 3, v___x_435_);
lean_closure_set(v___f_460_, 4, v___x_459_);
lean_closure_set(v___f_460_, 5, v___f_437_);
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_461_, v_a_436_, v___x_457_, v___f_460_);
return v___x_462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__9___boxed(lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v___f_468_, lean_object* v___x_469_, lean_object* v___x_470_, lean_object* v_a_471_, lean_object* v___f_472_, lean_object* v_x_473_, lean_object* v___y_474_){
_start:
{
uint8_t v___x_10996__boxed_475_; uint8_t v_a_10998__boxed_476_; lean_object* v_res_477_; 
v___x_10996__boxed_475_ = lean_unbox(v___x_469_);
v_a_10998__boxed_476_ = lean_unbox(v_a_471_);
v_res_477_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__9(v_a_466_, v_a_467_, v___f_468_, v___x_10996__boxed_475_, v___x_470_, v_a_10998__boxed_476_, v___f_472_, v_x_473_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__3(lean_object* v_a_478_, lean_object* v_a_479_, uint8_t v_a_480_, lean_object* v___f_481_, lean_object* v_x_482_){
_start:
{
if (lean_obj_tag(v_x_482_) == 0)
{
lean_object* v___x_484_; 
lean_dec_ref(v___f_481_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
v___x_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_484_, 0, v_x_482_);
return v___x_484_;
}
else
{
lean_object* v_cont_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
lean_dec_ref(v_x_482_);
v_cont_485_ = lean_ctor_get(v_a_478_, 1);
lean_inc_ref(v_cont_485_);
lean_dec_ref(v_a_478_);
v___x_486_ = lean_apply_2(v_cont_485_, v_a_479_, lean_box(0));
v___x_487_ = lean_unsigned_to_nat(0u);
v___x_488_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_487_, v_a_480_, v___x_486_, v___f_481_);
return v___x_488_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__3___boxed(lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v___f_492_, lean_object* v_x_493_, lean_object* v___y_494_){
_start:
{
uint8_t v_a_11067__boxed_495_; lean_object* v_res_496_; 
v_a_11067__boxed_495_ = lean_unbox(v_a_491_);
v_res_496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__3(v_a_489_, v_a_490_, v_a_11067__boxed_495_, v___f_492_, v_x_493_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__0(lean_object* v___x_497_, lean_object* v_x_498_){
_start:
{
if (lean_obj_tag(v_x_498_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_508_; 
v_a_500_ = lean_ctor_get(v_x_498_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v_x_498_);
if (v_isSharedCheck_508_ == 0)
{
v___x_502_ = v_x_498_;
v_isShared_503_ = v_isSharedCheck_508_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v_x_498_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_508_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_507_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_506_; 
v___x_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
}
}
else
{
lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_517_; 
v_isSharedCheck_517_ = !lean_is_exclusive(v_x_498_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; 
v_unused_518_ = lean_ctor_get(v_x_498_, 0);
lean_dec(v_unused_518_);
v___x_510_ = v_x_498_;
v_isShared_511_ = v_isSharedCheck_517_;
goto v_resetjp_509_;
}
else
{
lean_dec(v_x_498_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_517_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; lean_object* v___x_514_; 
v___x_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_497_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v___x_512_);
v___x_514_ = v___x_510_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_512_);
v___x_514_ = v_reuseFailAlloc_516_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_515_; 
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
return v___x_515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__0___boxed(lean_object* v___x_519_, lean_object* v_x_520_, lean_object* v___y_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__0(v___x_519_, v_x_520_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__1___boxed(lean_object* v_i_525_, lean_object* v_a_526_, lean_object* v_as_527_, lean_object* v_sz_528_, lean_object* v_x_529_, lean_object* v___y_530_){
_start:
{
size_t v_i_boxed_531_; uint8_t v_a_11140__boxed_532_; size_t v_sz_boxed_533_; lean_object* v_res_534_; 
v_i_boxed_531_ = lean_unbox_usize(v_i_525_);
lean_dec(v_i_525_);
v_a_11140__boxed_532_ = lean_unbox(v_a_526_);
v_sz_boxed_533_ = lean_unbox_usize(v_sz_528_);
lean_dec(v_sz_528_);
v_res_534_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__1(v_i_boxed_531_, v_a_11140__boxed_532_, v_as_527_, v_sz_boxed_533_, v_x_529_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg(uint8_t v_a_535_, lean_object* v_as_536_, size_t v_sz_537_, size_t v_i_538_, lean_object* v_b_539_){
_start:
{
uint8_t v___x_541_; 
v___x_541_ = lean_usize_dec_lt(v_i_538_, v_sz_537_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; lean_object* v___x_543_; 
lean_dec_ref(v_as_536_);
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v_b_539_);
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
else
{
lean_object* v_a_544_; lean_object* v_selector_545_; lean_object* v_unregisterFn_546_; lean_object* v___x_547_; lean_object* v___f_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___f_554_; uint8_t v___x_555_; lean_object* v___x_556_; 
v_a_544_ = lean_array_uget_borrowed(v_as_536_, v_i_538_);
v_selector_545_ = lean_ctor_get(v_a_544_, 0);
v_unregisterFn_546_ = lean_ctor_get(v_selector_545_, 2);
lean_inc_ref(v_unregisterFn_546_);
v___x_547_ = lean_apply_1(v_unregisterFn_546_, lean_box(0));
v___f_548_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___closed__0));
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_549_, v_a_535_, v___x_547_, v___f_548_);
v___x_551_ = lean_box_usize(v_i_538_);
v___x_552_ = lean_box(v_a_535_);
v___x_553_ = lean_box_usize(v_sz_537_);
v___f_554_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__1___boxed), 6, 4);
lean_closure_set(v___f_554_, 0, v___x_551_);
lean_closure_set(v___f_554_, 1, v___x_552_);
lean_closure_set(v___f_554_, 2, v_as_536_);
lean_closure_set(v___f_554_, 3, v___x_553_);
v___x_555_ = 0;
v___x_556_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_549_, v___x_555_, v___x_550_, v___f_554_);
return v___x_556_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__1(size_t v_i_557_, uint8_t v_a_558_, lean_object* v_as_559_, size_t v_sz_560_, lean_object* v_x_561_){
_start:
{
if (lean_obj_tag(v_x_561_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_571_; 
lean_dec_ref(v_as_559_);
v_a_563_ = lean_ctor_get(v_x_561_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v_x_561_);
if (v_isSharedCheck_571_ == 0)
{
v___x_565_ = v_x_561_;
v_isShared_566_ = v_isSharedCheck_571_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v_x_561_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_571_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_570_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_569_; 
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
}
}
else
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_591_; 
v_a_572_ = lean_ctor_get(v_x_561_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v_x_561_);
if (v_isSharedCheck_591_ == 0)
{
v___x_574_ = v_x_561_;
v_isShared_575_ = v_isSharedCheck_591_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v_x_561_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_591_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
if (lean_obj_tag(v_a_572_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_586_; 
lean_dec_ref(v_as_559_);
v_a_576_ = lean_ctor_get(v_a_572_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v_a_572_);
if (v_isSharedCheck_586_ == 0)
{
v___x_578_ = v_a_572_;
v_isShared_579_ = v_isSharedCheck_586_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v_a_572_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_586_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v_a_576_);
v___x_581_ = v___x_574_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_585_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_583_; 
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v___x_581_);
v___x_583_ = v___x_578_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
else
{
lean_object* v_a_587_; size_t v___x_588_; size_t v___x_589_; lean_object* v___x_590_; 
lean_del_object(v___x_574_);
v_a_587_ = lean_ctor_get(v_a_572_, 0);
lean_inc(v_a_587_);
lean_dec_ref(v_a_572_);
v___x_588_ = ((size_t)1ULL);
v___x_589_ = lean_usize_add(v_i_557_, v___x_588_);
v___x_590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg(v_a_558_, v_as_559_, v_sz_560_, v___x_589_, v_a_587_);
return v___x_590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___boxed(lean_object* v_a_592_, lean_object* v_as_593_, lean_object* v_sz_594_, lean_object* v_i_595_, lean_object* v_b_596_, lean_object* v___y_597_){
_start:
{
uint8_t v_a_11156__boxed_598_; size_t v_sz_boxed_599_; size_t v_i_boxed_600_; lean_object* v_res_601_; 
v_a_11156__boxed_598_ = lean_unbox(v_a_592_);
v_sz_boxed_599_ = lean_unbox_usize(v_sz_594_);
lean_dec(v_sz_594_);
v_i_boxed_600_ = lean_unbox_usize(v_i_595_);
lean_dec(v_i_595_);
v_res_601_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg(v_a_11156__boxed_598_, v_as_593_, v_sz_boxed_599_, v_i_boxed_600_, v_b_596_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__5(lean_object* v___x_602_, uint8_t v_a_603_, lean_object* v___x_604_, lean_object* v___f_605_, lean_object* v_x_606_){
_start:
{
if (lean_obj_tag(v_x_606_) == 0)
{
lean_object* v___x_608_; 
lean_dec_ref(v___f_605_);
lean_dec_ref(v___x_602_);
v___x_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_608_, 0, v_x_606_);
return v___x_608_;
}
else
{
size_t v_sz_609_; size_t v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
lean_dec_ref(v_x_606_);
v_sz_609_ = lean_array_size(v___x_602_);
v___x_610_ = ((size_t)0ULL);
v___x_611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg(v_a_603_, v___x_602_, v_sz_609_, v___x_610_, v___x_604_);
v___x_612_ = lean_unsigned_to_nat(0u);
v___x_613_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_612_, v_a_603_, v___x_611_, v___f_605_);
return v___x_613_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__5___boxed(lean_object* v___x_614_, lean_object* v_a_615_, lean_object* v___x_616_, lean_object* v___f_617_, lean_object* v_x_618_, lean_object* v___y_619_){
_start:
{
uint8_t v_a_11244__boxed_620_; lean_object* v_res_621_; 
v_a_11244__boxed_620_ = lean_unbox(v_a_615_);
v_res_621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__5(v___x_614_, v_a_11244__boxed_620_, v___x_616_, v___f_617_, v_x_618_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__6(lean_object* v_a_622_, uint8_t v_a_623_, lean_object* v___f_624_, lean_object* v___x_625_, lean_object* v___x_626_, lean_object* v_a_627_, lean_object* v___f_628_, lean_object* v___f_629_, lean_object* v_x_630_){
_start:
{
if (lean_obj_tag(v_x_630_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_640_; 
lean_dec_ref(v___f_629_);
lean_dec_ref(v___f_628_);
lean_dec_ref(v___x_625_);
lean_dec_ref(v___f_624_);
lean_dec_ref(v_a_622_);
v_a_632_ = lean_ctor_get(v_x_630_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v_x_630_);
if (v_isSharedCheck_640_ == 0)
{
v___x_634_ = v_x_630_;
v_isShared_635_ = v_isSharedCheck_640_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v_x_630_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_640_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_639_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_638_; 
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
return v___x_638_;
}
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_642_; lean_object* v___f_643_; lean_object* v___x_644_; lean_object* v___f_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v_a_641_ = lean_ctor_get(v_x_630_, 0);
lean_inc(v_a_641_);
lean_dec_ref(v_x_630_);
v___x_642_ = lean_box(v_a_623_);
v___f_643_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_643_, 0, v_a_622_);
lean_closure_set(v___f_643_, 1, v_a_641_);
lean_closure_set(v___f_643_, 2, v___x_642_);
lean_closure_set(v___f_643_, 3, v___f_624_);
v___x_644_ = lean_box(v_a_623_);
v___f_645_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__5___boxed), 6, 4);
lean_closure_set(v___f_645_, 0, v___x_625_);
lean_closure_set(v___f_645_, 1, v___x_644_);
lean_closure_set(v___f_645_, 2, v___x_626_);
lean_closure_set(v___f_645_, 3, v___f_643_);
v___x_646_ = lean_io_promise_result_opt(v_a_627_);
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = lean_task_map(v___f_628_, v___x_646_, v___x_647_, v_a_623_);
v___x_649_ = lean_task_map(v___f_629_, v___x_648_, v___x_647_, v_a_623_);
v___x_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
v___x_651_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_647_, v_a_623_, v___x_650_, v___f_645_);
return v___x_651_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__6___boxed(lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v___f_654_, lean_object* v___x_655_, lean_object* v___x_656_, lean_object* v_a_657_, lean_object* v___f_658_, lean_object* v___f_659_, lean_object* v_x_660_, lean_object* v___y_661_){
_start:
{
uint8_t v_a_11273__boxed_662_; lean_object* v_res_663_; 
v_a_11273__boxed_662_ = lean_unbox(v_a_653_);
v_res_663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__6(v_a_652_, v_a_11273__boxed_662_, v___f_654_, v___x_655_, v___x_656_, v_a_657_, v___f_658_, v___f_659_, v_x_660_);
lean_dec(v_a_657_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__7(lean_object* v___x_664_, uint8_t v_a_665_, lean_object* v___f_666_, lean_object* v___f_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_val_671_; 
if (lean_obj_tag(v_a_668_) == 0)
{
lean_object* v___x_679_; lean_object* v___x_680_; 
lean_dec_ref(v___f_667_);
lean_dec_ref(v___f_666_);
v___x_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_664_);
v___x_680_ = lean_task_pure(v___x_679_);
return v___x_680_;
}
else
{
lean_object* v_val_681_; lean_object* v___x_682_; 
v_val_681_ = lean_ctor_get(v_a_668_, 0);
lean_inc(v_val_681_);
lean_dec_ref(v_a_668_);
v___x_682_ = l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___redArg(v_val_681_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_682_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_682_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
lean_ctor_set_tag(v___x_685_, 1);
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
v_val_671_ = v___x_688_;
goto v___jp_670_;
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
v_a_691_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_682_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_682_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
lean_ctor_set_tag(v___x_693_, 0);
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
v_val_671_ = v___x_696_;
goto v___jp_670_;
}
}
}
}
v___jp_670_:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v_val_671_);
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_673_, v_a_665_, v___x_672_, v___f_666_);
v___x_675_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_673_, v_a_665_, v___x_674_, v___f_667_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_677_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_676_);
lean_dec_ref(v___x_675_);
v___x_677_ = lean_task_pure(v_a_676_);
return v___x_677_;
}
else
{
lean_object* v_a_678_; 
v_a_678_ = lean_ctor_get(v___x_675_, 0);
lean_inc_ref(v_a_678_);
lean_dec_ref(v___x_675_);
return v_a_678_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__7___boxed(lean_object* v___x_699_, lean_object* v_a_700_, lean_object* v___f_701_, lean_object* v___f_702_, lean_object* v_a_703_, lean_object* v___y_704_){
_start:
{
uint8_t v_a_11341__boxed_705_; lean_object* v_res_706_; 
v_a_11341__boxed_705_ = lean_unbox(v_a_700_);
v_res_706_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__7(v___x_699_, v_a_11341__boxed_705_, v___f_701_, v___f_702_, v_a_703_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__10(lean_object* v_a_707_, lean_object* v___f_708_, lean_object* v___x_709_, lean_object* v___x_710_, lean_object* v_a_711_, lean_object* v___f_712_, lean_object* v___f_713_, lean_object* v___f_714_, lean_object* v_a_715_, uint8_t v___x_716_, lean_object* v___f_717_, lean_object* v_x_718_){
_start:
{
if (lean_obj_tag(v_x_718_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_728_; 
lean_dec_ref(v___f_717_);
lean_dec(v_a_715_);
lean_dec_ref(v___f_714_);
lean_dec_ref(v___f_713_);
lean_dec_ref(v___f_712_);
lean_dec(v_a_711_);
lean_dec_ref(v___x_709_);
lean_dec_ref(v___f_708_);
lean_dec_ref(v_a_707_);
v_a_720_ = lean_ctor_get(v_x_718_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v_x_718_);
if (v_isSharedCheck_728_ == 0)
{
v___x_722_ = v_x_718_;
v_isShared_723_ = v_isSharedCheck_728_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v_x_718_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_728_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_727_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_726_; 
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
return v___x_726_;
}
}
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_751_; 
v_a_729_ = lean_ctor_get(v_x_718_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v_x_718_);
if (v_isSharedCheck_751_ == 0)
{
v___x_731_ = v_x_718_;
v_isShared_732_ = v_isSharedCheck_751_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v_x_718_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_751_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
uint8_t v___x_733_; 
v___x_733_ = lean_unbox(v_a_729_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___f_735_; lean_object* v___f_736_; lean_object* v___x_737_; lean_object* v___f_738_; lean_object* v___x_740_; 
v___x_734_ = lean_io_promise_new();
lean_inc_n(v_a_729_, 3);
lean_inc_ref(v_a_707_);
v___f_735_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__6___boxed), 10, 8);
lean_closure_set(v___f_735_, 0, v_a_707_);
lean_closure_set(v___f_735_, 1, v_a_729_);
lean_closure_set(v___f_735_, 2, v___f_708_);
lean_closure_set(v___f_735_, 3, v___x_709_);
lean_closure_set(v___f_735_, 4, v___x_710_);
lean_closure_set(v___f_735_, 5, v_a_711_);
lean_closure_set(v___f_735_, 6, v___f_712_);
lean_closure_set(v___f_735_, 7, v___f_713_);
v___f_736_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_736_, 0, v___x_710_);
lean_closure_set(v___f_736_, 1, v_a_729_);
lean_closure_set(v___f_736_, 2, v___f_735_);
lean_closure_set(v___f_736_, 3, v___f_714_);
v___x_737_ = lean_box(v___x_716_);
v___f_738_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__9___boxed), 9, 7);
lean_closure_set(v___f_738_, 0, v_a_707_);
lean_closure_set(v___f_738_, 1, v_a_715_);
lean_closure_set(v___f_738_, 2, v___f_736_);
lean_closure_set(v___f_738_, 3, v___x_737_);
lean_closure_set(v___f_738_, 4, v___x_710_);
lean_closure_set(v___f_738_, 5, v_a_729_);
lean_closure_set(v___f_738_, 6, v___f_717_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v___x_734_);
v___x_740_ = v___x_731_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_734_);
v___x_740_ = v_reuseFailAlloc_745_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; lean_object* v___x_744_; 
v___x_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
v___x_742_ = lean_unsigned_to_nat(0u);
v___x_743_ = lean_unbox(v_a_729_);
lean_dec(v_a_729_);
v___x_744_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_742_, v___x_743_, v___x_741_, v___f_738_);
return v___x_744_;
}
}
else
{
lean_object* v___x_746_; lean_object* v___x_748_; 
lean_dec(v_a_729_);
lean_dec_ref(v___f_717_);
lean_dec(v_a_715_);
lean_dec_ref(v___f_714_);
lean_dec_ref(v___f_713_);
lean_dec_ref(v___f_712_);
lean_dec(v_a_711_);
lean_dec_ref(v___x_709_);
lean_dec_ref(v___f_708_);
lean_dec_ref(v_a_707_);
v___x_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_710_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v___x_746_);
v___x_748_ = v___x_731_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_746_);
v___x_748_ = v_reuseFailAlloc_750_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_749_; 
v___x_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
return v___x_749_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__10___boxed(lean_object* v_a_752_, lean_object* v___f_753_, lean_object* v___x_754_, lean_object* v___x_755_, lean_object* v_a_756_, lean_object* v___f_757_, lean_object* v___f_758_, lean_object* v___f_759_, lean_object* v_a_760_, lean_object* v___x_761_, lean_object* v___f_762_, lean_object* v_x_763_, lean_object* v___y_764_){
_start:
{
uint8_t v___x_11421__boxed_765_; lean_object* v_res_766_; 
v___x_11421__boxed_765_ = lean_unbox(v___x_761_);
v_res_766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__10(v_a_752_, v___f_753_, v___x_754_, v___x_755_, v_a_756_, v___f_757_, v___f_758_, v___f_759_, v_a_760_, v___x_11421__boxed_765_, v___f_762_, v_x_763_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__11___boxed(lean_object* v_i_770_, lean_object* v_a_771_, lean_object* v___x_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_as_775_, lean_object* v_sz_776_, lean_object* v_x_777_, lean_object* v___y_778_){
_start:
{
size_t v_i_boxed_779_; size_t v_sz_boxed_780_; lean_object* v_res_781_; 
v_i_boxed_779_ = lean_unbox_usize(v_i_770_);
lean_dec(v_i_770_);
v_sz_boxed_780_ = lean_unbox_usize(v_sz_776_);
lean_dec(v_sz_776_);
v_res_781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__11(v_i_boxed_779_, v_a_771_, v___x_772_, v_a_773_, v_a_774_, v_as_775_, v_sz_boxed_780_, v_x_777_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg(lean_object* v_a_782_, lean_object* v___x_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_as_786_, size_t v_sz_787_, size_t v_i_788_, lean_object* v_b_789_){
_start:
{
uint8_t v___x_791_; 
v___x_791_ = lean_usize_dec_lt(v_i_788_, v_sz_787_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; lean_object* v___x_793_; 
lean_dec_ref(v_as_786_);
lean_dec(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v___x_783_);
lean_dec(v_a_782_);
v___x_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_792_, 0, v_b_789_);
v___x_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
return v___x_793_;
}
else
{
lean_object* v___x_794_; lean_object* v___f_795_; lean_object* v___f_796_; lean_object* v___f_797_; lean_object* v___x_798_; lean_object* v___f_799_; lean_object* v___f_800_; lean_object* v_a_801_; lean_object* v___x_802_; lean_object* v___f_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; uint8_t v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___f_811_; lean_object* v___x_812_; 
v___x_794_ = lean_st_ref_get(v_a_785_);
lean_inc_n(v_a_782_, 2);
v___f_795_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_795_, 0, v_a_782_);
v___f_796_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___closed__0));
v___f_797_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_797_, 0, v_a_782_);
v___x_798_ = lean_box(0);
v___f_799_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___closed__0));
v___f_800_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___closed__1));
v_a_801_ = lean_array_uget_borrowed(v_as_786_, v_i_788_);
v___x_802_ = lean_box(v___x_791_);
lean_inc(v_a_785_);
lean_inc(v_a_784_);
lean_inc_ref(v___x_783_);
lean_inc(v_a_801_);
v___f_803_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__10___boxed), 13, 11);
lean_closure_set(v___f_803_, 0, v_a_801_);
lean_closure_set(v___f_803_, 1, v___f_795_);
lean_closure_set(v___f_803_, 2, v___x_783_);
lean_closure_set(v___f_803_, 3, v___x_798_);
lean_closure_set(v___f_803_, 4, v_a_784_);
lean_closure_set(v___f_803_, 5, v___f_796_);
lean_closure_set(v___f_803_, 6, v___f_800_);
lean_closure_set(v___f_803_, 7, v___f_797_);
lean_closure_set(v___f_803_, 8, v_a_785_);
lean_closure_set(v___f_803_, 9, v___x_802_);
lean_closure_set(v___f_803_, 10, v___f_799_);
v___x_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_794_);
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
v___x_806_ = lean_unsigned_to_nat(0u);
v___x_807_ = 0;
v___x_808_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_806_, v___x_807_, v___x_805_, v___f_803_);
v___x_809_ = lean_box_usize(v_i_788_);
v___x_810_ = lean_box_usize(v_sz_787_);
v___f_811_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__11___boxed), 9, 7);
lean_closure_set(v___f_811_, 0, v___x_809_);
lean_closure_set(v___f_811_, 1, v_a_782_);
lean_closure_set(v___f_811_, 2, v___x_783_);
lean_closure_set(v___f_811_, 3, v_a_784_);
lean_closure_set(v___f_811_, 4, v_a_785_);
lean_closure_set(v___f_811_, 5, v_as_786_);
lean_closure_set(v___f_811_, 6, v___x_810_);
v___x_812_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_806_, v___x_807_, v___x_808_, v___f_811_);
return v___x_812_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__11(size_t v_i_813_, lean_object* v_a_814_, lean_object* v___x_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_as_818_, size_t v_sz_819_, lean_object* v_x_820_){
_start:
{
if (lean_obj_tag(v_x_820_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_830_; 
lean_dec_ref(v_as_818_);
lean_dec(v_a_817_);
lean_dec(v_a_816_);
lean_dec_ref(v___x_815_);
lean_dec(v_a_814_);
v_a_822_ = lean_ctor_get(v_x_820_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v_x_820_);
if (v_isSharedCheck_830_ == 0)
{
v___x_824_ = v_x_820_;
v_isShared_825_ = v_isSharedCheck_830_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v_x_820_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_830_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_829_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_828_; 
v___x_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
return v___x_828_;
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_850_; 
v_a_831_ = lean_ctor_get(v_x_820_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v_x_820_);
if (v_isSharedCheck_850_ == 0)
{
v___x_833_ = v_x_820_;
v_isShared_834_ = v_isSharedCheck_850_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v_x_820_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_850_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
if (lean_obj_tag(v_a_831_) == 0)
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_845_; 
lean_dec_ref(v_as_818_);
lean_dec(v_a_817_);
lean_dec(v_a_816_);
lean_dec_ref(v___x_815_);
lean_dec(v_a_814_);
v_a_835_ = lean_ctor_get(v_a_831_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v_a_831_);
if (v_isSharedCheck_845_ == 0)
{
v___x_837_ = v_a_831_;
v_isShared_838_ = v_isSharedCheck_845_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v_a_831_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_845_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v_a_835_);
v___x_840_ = v___x_833_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_844_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v___x_842_; 
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v___x_840_);
v___x_842_ = v___x_837_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_840_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
else
{
lean_object* v_a_846_; size_t v___x_847_; size_t v___x_848_; lean_object* v___x_849_; 
lean_del_object(v___x_833_);
v_a_846_ = lean_ctor_get(v_a_831_, 0);
lean_inc(v_a_846_);
lean_dec_ref(v_a_831_);
v___x_847_ = ((size_t)1ULL);
v___x_848_ = lean_usize_add(v_i_813_, v___x_847_);
v___x_849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg(v_a_814_, v___x_815_, v_a_816_, v_a_817_, v_as_818_, v_sz_819_, v___x_848_, v_a_846_);
return v___x_849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___boxed(lean_object* v_a_851_, lean_object* v___x_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_as_855_, lean_object* v_sz_856_, lean_object* v_i_857_, lean_object* v_b_858_, lean_object* v___y_859_){
_start:
{
size_t v_sz_boxed_860_; size_t v_i_boxed_861_; lean_object* v_res_862_; 
v_sz_boxed_860_ = lean_unbox_usize(v_sz_856_);
lean_dec(v_sz_856_);
v_i_boxed_861_ = lean_unbox_usize(v_i_857_);
lean_dec(v_i_857_);
v_res_862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg(v_a_851_, v___x_852_, v_a_853_, v_a_854_, v_as_855_, v_sz_boxed_860_, v_i_boxed_861_, v_b_858_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__4(lean_object* v___x_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v___x_866_, lean_object* v_x_867_){
_start:
{
if (lean_obj_tag(v_x_867_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_877_; 
lean_dec(v_a_865_);
lean_dec(v_a_864_);
lean_dec_ref(v___x_863_);
v_a_869_ = lean_ctor_get(v_x_867_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v_x_867_);
if (v_isSharedCheck_877_ == 0)
{
v___x_871_ = v_x_867_;
v_isShared_872_ = v_isSharedCheck_877_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v_x_867_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_877_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_876_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_875_; 
v___x_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
return v___x_875_;
}
}
}
else
{
lean_object* v_a_878_; size_t v_sz_879_; size_t v___x_880_; lean_object* v___x_881_; lean_object* v___f_882_; lean_object* v___f_883_; lean_object* v___x_884_; uint8_t v___x_885_; lean_object* v___x_886_; 
v_a_878_ = lean_ctor_get(v_x_867_, 0);
v_sz_879_ = lean_array_size(v___x_863_);
v___x_880_ = ((size_t)0ULL);
lean_inc(v_a_864_);
lean_inc_ref(v___x_863_);
lean_inc(v_a_878_);
v___x_881_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg(v_a_878_, v___x_863_, v_a_864_, v_a_865_, v___x_863_, v_sz_879_, v___x_880_, v___x_866_);
v___f_882_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_882_, 0, v_x_867_);
v___f_883_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_883_, 0, v___x_866_);
lean_closure_set(v___f_883_, 1, v_a_864_);
lean_closure_set(v___f_883_, 2, v___f_882_);
v___x_884_ = lean_unsigned_to_nat(0u);
v___x_885_ = 0;
v___x_886_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_884_, v___x_885_, v___x_881_, v___f_883_);
return v___x_886_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__4___boxed(lean_object* v___x_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v___x_890_, lean_object* v_x_891_, lean_object* v___y_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Std_Async_Selectable_one___redArg___lam__4(v___x_887_, v_a_888_, v_a_889_, v___x_890_, v_x_891_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__5(lean_object* v___x_894_, lean_object* v_a_895_, lean_object* v___x_896_, lean_object* v_x_897_){
_start:
{
if (lean_obj_tag(v_x_897_) == 0)
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_907_; 
lean_dec(v_a_895_);
lean_dec_ref(v___x_894_);
v_a_899_ = lean_ctor_get(v_x_897_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v_x_897_);
if (v_isSharedCheck_907_ == 0)
{
v___x_901_ = v_x_897_;
v_isShared_902_ = v_isSharedCheck_907_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v_x_897_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_907_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_906_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_905_; 
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
return v___x_905_;
}
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_921_; 
v_a_908_ = lean_ctor_get(v_x_897_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v_x_897_);
if (v_isSharedCheck_921_ == 0)
{
v___x_910_ = v_x_897_;
v_isShared_911_ = v_isSharedCheck_921_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v_x_897_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_921_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v___f_913_; lean_object* v___x_915_; 
v___x_912_ = lean_io_promise_new();
v___f_913_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_913_, 0, v___x_894_);
lean_closure_set(v___f_913_, 1, v_a_895_);
lean_closure_set(v___f_913_, 2, v_a_908_);
lean_closure_set(v___f_913_, 3, v___x_896_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v___x_912_);
v___x_915_ = v___x_910_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_912_);
v___x_915_ = v_reuseFailAlloc_920_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; lean_object* v___x_919_; 
v___x_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
v___x_917_ = lean_unsigned_to_nat(0u);
v___x_918_ = 0;
v___x_919_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_917_, v___x_918_, v___x_916_, v___f_913_);
return v___x_919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__5___boxed(lean_object* v___x_922_, lean_object* v_a_923_, lean_object* v___x_924_, lean_object* v_x_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Std_Async_Selectable_one___redArg___lam__5(v___x_922_, v_a_923_, v___x_924_, v_x_925_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__6(lean_object* v___f_928_, lean_object* v_x_929_){
_start:
{
if (lean_obj_tag(v_x_929_) == 0)
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_939_; 
lean_dec_ref(v___f_928_);
v_a_931_ = lean_ctor_get(v_x_929_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v_x_929_);
if (v_isSharedCheck_939_ == 0)
{
v___x_933_ = v_x_929_;
v_isShared_934_ = v_isSharedCheck_939_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v_x_929_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_939_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_938_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v___x_937_; 
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
return v___x_937_;
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_965_; 
v_a_940_ = lean_ctor_get(v_x_929_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v_x_929_);
if (v_isSharedCheck_965_ == 0)
{
v___x_942_ = v_x_929_;
v_isShared_943_ = v_isSharedCheck_965_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v_x_929_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_965_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v_fst_944_; 
v_fst_944_ = lean_ctor_get(v_a_940_, 0);
lean_inc(v_fst_944_);
lean_dec(v_a_940_);
if (lean_obj_tag(v_fst_944_) == 0)
{
uint8_t v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_945_ = 0;
v___x_946_ = lean_box(v___x_945_);
v___x_947_ = lean_st_mk_ref(v___x_946_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v___x_947_);
v___x_949_ = v___x_942_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_947_);
v___x_949_ = v_reuseFailAlloc_953_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
v___x_951_ = lean_unsigned_to_nat(0u);
v___x_952_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_951_, v___x_945_, v___x_950_, v___f_928_);
return v___x_952_;
}
}
else
{
lean_object* v_val_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_964_; 
lean_dec_ref(v___f_928_);
v_val_954_ = lean_ctor_get(v_fst_944_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v_fst_944_);
if (v_isSharedCheck_964_ == 0)
{
v___x_956_ = v_fst_944_;
v_isShared_957_ = v_isSharedCheck_964_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_val_954_);
lean_dec(v_fst_944_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_964_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v_val_954_);
v___x_959_ = v___x_942_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_val_954_);
v___x_959_ = v_reuseFailAlloc_963_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
lean_object* v___x_961_; 
if (v_isShared_957_ == 0)
{
lean_ctor_set_tag(v___x_956_, 0);
lean_ctor_set(v___x_956_, 0, v___x_959_);
v___x_961_ = v___x_956_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_959_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__6___boxed(lean_object* v___f_966_, lean_object* v_x_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Std_Async_Selectable_one___redArg___lam__6(v___f_966_, v_x_967_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__1(lean_object* v_a_970_, lean_object* v___f_971_, lean_object* v___x_972_, lean_object* v_x_973_){
_start:
{
if (lean_obj_tag(v_x_973_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_983_; 
lean_dec_ref(v___x_972_);
lean_dec_ref(v___f_971_);
lean_dec_ref(v_a_970_);
v_a_975_ = lean_ctor_get(v_x_973_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v_x_973_);
if (v_isSharedCheck_983_ == 0)
{
v___x_977_ = v_x_973_;
v_isShared_978_ = v_isSharedCheck_983_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v_x_973_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_983_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_982_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_981_; 
v___x_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
return v___x_981_;
}
}
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_999_; 
v_a_984_ = lean_ctor_get(v_x_973_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v_x_973_);
if (v_isSharedCheck_999_ == 0)
{
v___x_986_ = v_x_973_;
v_isShared_987_ = v_isSharedCheck_999_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v_x_973_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_999_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
if (lean_obj_tag(v_a_984_) == 1)
{
lean_object* v_val_988_; lean_object* v_cont_989_; lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v___x_992_; lean_object* v___x_993_; 
lean_del_object(v___x_986_);
lean_dec_ref(v___x_972_);
v_val_988_ = lean_ctor_get(v_a_984_, 0);
lean_inc(v_val_988_);
lean_dec_ref(v_a_984_);
v_cont_989_ = lean_ctor_get(v_a_970_, 1);
lean_inc_ref(v_cont_989_);
lean_dec_ref(v_a_970_);
v___x_990_ = lean_apply_2(v_cont_989_, v_val_988_, lean_box(0));
v___x_991_ = lean_unsigned_to_nat(0u);
v___x_992_ = 0;
v___x_993_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_991_, v___x_992_, v___x_990_, v___f_971_);
return v___x_993_;
}
else
{
lean_object* v___x_994_; lean_object* v___x_996_; 
lean_dec(v_a_984_);
lean_dec_ref(v___f_971_);
lean_dec_ref(v_a_970_);
v___x_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_972_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v___x_994_);
v___x_996_ = v___x_986_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_994_);
v___x_996_ = v_reuseFailAlloc_998_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_997_; 
v___x_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
return v___x_997_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__1___boxed(lean_object* v_a_1000_, lean_object* v___f_1001_, lean_object* v___x_1002_, lean_object* v_x_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__1(v_a_1000_, v___f_1001_, v___x_1002_, v_x_1003_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__0(lean_object* v___x_1006_, lean_object* v_x_1007_){
_start:
{
if (lean_obj_tag(v_x_1007_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1017_; 
v_a_1009_ = lean_ctor_get(v_x_1007_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_x_1007_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1011_ = v_x_1007_;
v_isShared_1012_ = v_isSharedCheck_1017_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v_x_1007_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1017_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
return v___x_1015_;
}
}
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1029_; 
v_a_1018_ = lean_ctor_get(v_x_1007_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_x_1007_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1020_ = v_x_1007_;
v_isShared_1021_ = v_isSharedCheck_1029_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v_x_1007_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1029_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1022_, 0, v_a_1018_);
v___x_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set(v___x_1023_, 1, v___x_1006_);
v___x_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 0, v___x_1024_);
v___x_1026_ = v___x_1020_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; 
v___x_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
return v___x_1027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__0___boxed(lean_object* v___x_1030_, lean_object* v_x_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__0(v___x_1030_, v_x_1031_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__2___boxed(lean_object* v_i_1039_, lean_object* v_as_1040_, lean_object* v_sz_1041_, lean_object* v_x_1042_, lean_object* v___y_1043_){
_start:
{
size_t v_i_boxed_1044_; size_t v_sz_boxed_1045_; lean_object* v_res_1046_; 
v_i_boxed_1044_ = lean_unbox_usize(v_i_1039_);
lean_dec(v_i_1039_);
v_sz_boxed_1045_ = lean_unbox_usize(v_sz_1041_);
lean_dec(v_sz_1041_);
v_res_1046_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__2(v_i_boxed_1044_, v_as_1040_, v_sz_boxed_1045_, v_x_1042_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg(lean_object* v_as_1047_, size_t v_sz_1048_, size_t v_i_1049_, lean_object* v_b_1050_){
_start:
{
uint8_t v___x_1052_; 
v___x_1052_ = lean_usize_dec_lt(v_i_1049_, v_sz_1048_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_dec_ref(v_as_1047_);
v___x_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1053_, 0, v_b_1050_);
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
return v___x_1054_;
}
else
{
lean_object* v_a_1055_; lean_object* v_selector_1056_; lean_object* v_tryFn_1057_; lean_object* v___x_1058_; lean_object* v___f_1059_; lean_object* v___x_1060_; lean_object* v___f_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___f_1067_; lean_object* v___x_1068_; 
lean_dec_ref(v_b_1050_);
v_a_1055_ = lean_array_uget_borrowed(v_as_1047_, v_i_1049_);
v_selector_1056_ = lean_ctor_get(v_a_1055_, 0);
v_tryFn_1057_ = lean_ctor_get(v_selector_1056_, 0);
lean_inc_ref(v_tryFn_1057_);
v___x_1058_ = lean_apply_1(v_tryFn_1057_, lean_box(0));
v___f_1059_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___closed__0));
v___x_1060_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___closed__1));
lean_inc(v_a_1055_);
v___f_1061_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1061_, 0, v_a_1055_);
lean_closure_set(v___f_1061_, 1, v___f_1059_);
lean_closure_set(v___f_1061_, 2, v___x_1060_);
v___x_1062_ = lean_unsigned_to_nat(0u);
v___x_1063_ = 0;
v___x_1064_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1062_, v___x_1063_, v___x_1058_, v___f_1061_);
v___x_1065_ = lean_box_usize(v_i_1049_);
v___x_1066_ = lean_box_usize(v_sz_1048_);
v___f_1067_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_1067_, 0, v___x_1065_);
lean_closure_set(v___f_1067_, 1, v_as_1047_);
lean_closure_set(v___f_1067_, 2, v___x_1066_);
v___x_1068_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1062_, v___x_1063_, v___x_1064_, v___f_1067_);
return v___x_1068_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__2(size_t v_i_1069_, lean_object* v_as_1070_, size_t v_sz_1071_, lean_object* v_x_1072_){
_start:
{
if (lean_obj_tag(v_x_1072_) == 0)
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1082_; 
lean_dec_ref(v_as_1070_);
v_a_1074_ = lean_ctor_get(v_x_1072_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_x_1072_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1076_ = v_x_1072_;
v_isShared_1077_ = v_isSharedCheck_1082_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v_x_1072_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1082_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
return v___x_1080_;
}
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1102_; 
v_a_1083_ = lean_ctor_get(v_x_1072_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_x_1072_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1085_ = v_x_1072_;
v_isShared_1086_ = v_isSharedCheck_1102_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v_x_1072_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1102_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
if (lean_obj_tag(v_a_1083_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1097_; 
lean_dec_ref(v_as_1070_);
v_a_1087_ = lean_ctor_get(v_a_1083_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_a_1083_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1089_ = v_a_1083_;
v_isShared_1090_ = v_isSharedCheck_1097_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v_a_1083_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1097_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v_a_1087_);
v___x_1092_ = v___x_1085_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
lean_object* v___x_1094_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1092_);
v___x_1094_ = v___x_1089_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
else
{
lean_object* v_a_1098_; size_t v___x_1099_; size_t v___x_1100_; lean_object* v___x_1101_; 
lean_del_object(v___x_1085_);
v_a_1098_ = lean_ctor_get(v_a_1083_, 0);
lean_inc(v_a_1098_);
lean_dec_ref(v_a_1083_);
v___x_1099_ = ((size_t)1ULL);
v___x_1100_ = lean_usize_add(v_i_1069_, v___x_1099_);
v___x_1101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg(v_as_1070_, v_sz_1071_, v___x_1100_, v_a_1098_);
return v___x_1101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___boxed(lean_object* v_as_1103_, lean_object* v_sz_1104_, lean_object* v_i_1105_, lean_object* v_b_1106_, lean_object* v___y_1107_){
_start:
{
size_t v_sz_boxed_1108_; size_t v_i_boxed_1109_; lean_object* v_res_1110_; 
v_sz_boxed_1108_ = lean_unbox_usize(v_sz_1104_);
lean_dec(v_sz_1104_);
v_i_boxed_1109_ = lean_unbox_usize(v_i_1105_);
lean_dec(v_i_1105_);
v_res_1110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg(v_as_1103_, v_sz_boxed_1108_, v_i_boxed_1109_, v_b_1106_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__7(lean_object* v___x_1111_, lean_object* v_x_1112_){
_start:
{
if (lean_obj_tag(v_x_1112_) == 0)
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1122_; 
lean_dec_ref(v___x_1111_);
v_a_1114_ = lean_ctor_get(v_x_1112_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_x_1112_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1116_ = v_x_1112_;
v_isShared_1117_ = v_isSharedCheck_1122_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v_x_1112_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1122_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
return v___x_1120_;
}
}
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; size_t v_sz_1126_; size_t v___x_1127_; lean_object* v___x_1128_; lean_object* v___f_1129_; lean_object* v___f_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; lean_object* v___x_1133_; 
v_a_1123_ = lean_ctor_get(v_x_1112_, 0);
lean_inc(v_a_1123_);
lean_dec_ref(v_x_1112_);
v___x_1124_ = lean_box(0);
v___x_1125_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___closed__1));
v_sz_1126_ = lean_array_size(v___x_1111_);
v___x_1127_ = ((size_t)0ULL);
lean_inc_ref(v___x_1111_);
v___x_1128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg(v___x_1111_, v_sz_1126_, v___x_1127_, v___x_1125_);
v___f_1129_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_1129_, 0, v___x_1111_);
lean_closure_set(v___f_1129_, 1, v_a_1123_);
lean_closure_set(v___f_1129_, 2, v___x_1124_);
v___f_1130_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__6___boxed), 3, 1);
lean_closure_set(v___f_1130_, 0, v___f_1129_);
v___x_1131_ = lean_unsigned_to_nat(0u);
v___x_1132_ = 0;
v___x_1133_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1131_, v___x_1132_, v___x_1128_, v___f_1130_);
return v___x_1133_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__7___boxed(lean_object* v___x_1134_, lean_object* v_x_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Std_Async_Selectable_one___redArg___lam__7(v___x_1134_, v_x_1135_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__8(lean_object* v_selectables_1138_, lean_object* v_x_1139_){
_start:
{
if (lean_obj_tag(v_x_1139_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1149_; 
lean_dec_ref(v_selectables_1138_);
v_a_1141_ = lean_ctor_get(v_x_1139_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1143_ = v_x_1139_;
v_isShared_1144_ = v_isSharedCheck_1149_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v_x_1139_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1149_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
return v___x_1147_;
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1167_; 
v_a_1150_ = lean_ctor_get(v_x_1139_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1152_ = v_x_1139_;
v_isShared_1153_ = v_isSharedCheck_1167_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v_x_1139_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1167_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; uint64_t v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___f_1159_; lean_object* v___x_1161_; 
v___x_1154_ = lean_io_promise_new();
v___x_1155_ = l_ByteArray_toUInt64LE_x21(v_a_1150_);
lean_dec(v_a_1150_);
v___x_1156_ = lean_uint64_to_nat(v___x_1155_);
v___x_1157_ = l_mkStdGen(v___x_1156_);
lean_dec(v___x_1156_);
v___x_1158_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(v_selectables_1138_, v___x_1157_);
v___f_1159_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_1159_, 0, v___x_1158_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1154_);
v___x_1161_ = v___x_1152_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1154_);
v___x_1161_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; lean_object* v___x_1165_; 
v___x_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
v___x_1163_ = lean_unsigned_to_nat(0u);
v___x_1164_ = 0;
v___x_1165_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1163_, v___x_1164_, v___x_1162_, v___f_1159_);
return v___x_1165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__8___boxed(lean_object* v_selectables_1168_, lean_object* v_x_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Std_Async_Selectable_one___redArg___lam__8(v_selectables_1168_, v_x_1169_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__9(lean_object* v___f_1172_, lean_object* v_____r_1173_){
_start:
{
lean_object* v_val_1176_; size_t v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = ((size_t)8ULL);
v___x_1182_ = lean_io_get_random_bytes(v___x_1181_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1182_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
lean_ctor_set_tag(v___x_1185_, 1);
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
v_val_1176_ = v___x_1188_;
goto v___jp_1175_;
}
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
v_a_1191_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1182_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1182_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
lean_ctor_set_tag(v___x_1193_, 0);
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
v_val_1176_ = v___x_1196_;
goto v___jp_1175_;
}
}
}
v___jp_1175_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; lean_object* v___x_1180_; 
v___x_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1177_, 0, v_val_1176_);
v___x_1178_ = lean_unsigned_to_nat(0u);
v___x_1179_ = 0;
v___x_1180_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1178_, v___x_1179_, v___x_1177_, v___f_1172_);
return v___x_1180_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__9___boxed(lean_object* v___f_1199_, lean_object* v_____r_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Std_Async_Selectable_one___redArg___lam__9(v___f_1199_, v_____r_1200_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__10(lean_object* v___f_1203_, lean_object* v_x_1204_){
_start:
{
if (lean_obj_tag(v_x_1204_) == 0)
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1214_; 
lean_dec_ref(v___f_1203_);
v_a_1206_ = lean_ctor_get(v_x_1204_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_x_1204_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1208_ = v_x_1204_;
v_isShared_1209_ = v_isSharedCheck_1214_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v_x_1204_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1214_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1212_; 
v___x_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
return v___x_1212_;
}
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1216_; 
v_a_1215_ = lean_ctor_get(v_x_1204_, 0);
lean_inc(v_a_1215_);
lean_dec_ref(v_x_1204_);
v___x_1216_ = lean_apply_2(v___f_1203_, v_a_1215_, lean_box(0));
return v___x_1216_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__10___boxed(lean_object* v___f_1217_, lean_object* v_x_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Std_Async_Selectable_one___redArg___lam__10(v___f_1217_, v_x_1218_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg(lean_object* v_selectables_1228_){
_start:
{
lean_object* v___f_1230_; lean_object* v___f_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
lean_inc_ref(v_selectables_1228_);
v___f_1230_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__8___boxed), 3, 1);
lean_closure_set(v___f_1230_, 0, v_selectables_1228_);
lean_inc_ref(v___f_1230_);
v___f_1231_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_1231_, 0, v___f_1230_);
v___x_1232_ = lean_array_get_size(v_selectables_1228_);
lean_dec_ref(v_selectables_1228_);
v___x_1233_ = lean_unsigned_to_nat(0u);
v___x_1234_ = lean_nat_dec_eq(v___x_1232_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_dec_ref(v___f_1231_);
v___x_1235_ = lean_box(0);
v___x_1236_ = l_Std_Async_Selectable_one___redArg___lam__9(v___f_1230_, v___x_1235_);
return v___x_1236_;
}
else
{
lean_object* v___f_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; lean_object* v___x_1240_; 
lean_dec_ref(v___f_1230_);
v___f_1237_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__10___boxed), 3, 1);
lean_closure_set(v___f_1237_, 0, v___f_1231_);
v___x_1238_ = ((lean_object*)(l_Std_Async_Selectable_one___redArg___closed__3));
v___x_1239_ = 0;
v___x_1240_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1233_, v___x_1239_, v___x_1238_, v___f_1237_);
return v___x_1240_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___boxed(lean_object* v_selectables_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Std_Async_Selectable_one___redArg(v_selectables_1241_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one(lean_object* v_00_u03b1_1244_, lean_object* v_selectables_1245_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Std_Async_Selectable_one___redArg(v_selectables_1245_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___boxed(lean_object* v_00_u03b1_1248_, lean_object* v_selectables_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Std_Async_Selectable_one(v_00_u03b1_1248_, v_selectables_1249_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0(lean_object* v_00_u03b1_1252_, uint8_t v_a_1253_, lean_object* v_as_1254_, size_t v_sz_1255_, size_t v_i_1256_, lean_object* v_b_1257_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg(v_a_1253_, v_as_1254_, v_sz_1255_, v_i_1256_, v_b_1257_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___boxed(lean_object* v_00_u03b1_1260_, lean_object* v_a_1261_, lean_object* v_as_1262_, lean_object* v_sz_1263_, lean_object* v_i_1264_, lean_object* v_b_1265_, lean_object* v___y_1266_){
_start:
{
uint8_t v_a_12318__boxed_1267_; size_t v_sz_boxed_1268_; size_t v_i_boxed_1269_; lean_object* v_res_1270_; 
v_a_12318__boxed_1267_ = lean_unbox(v_a_1261_);
v_sz_boxed_1268_ = lean_unbox_usize(v_sz_1263_);
lean_dec(v_sz_1263_);
v_i_boxed_1269_ = lean_unbox_usize(v_i_1264_);
lean_dec(v_i_1264_);
v_res_1270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0(v_00_u03b1_1260_, v_a_12318__boxed_1267_, v_as_1262_, v_sz_boxed_1268_, v_i_boxed_1269_, v_b_1265_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2(lean_object* v_00_u03b1_1271_, lean_object* v_a_1272_, lean_object* v___x_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_as_1276_, size_t v_sz_1277_, size_t v_i_1278_, lean_object* v_b_1279_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg(v_a_1272_, v___x_1273_, v_a_1274_, v_a_1275_, v_as_1276_, v_sz_1277_, v_i_1278_, v_b_1279_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___boxed(lean_object* v_00_u03b1_1282_, lean_object* v_a_1283_, lean_object* v___x_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_as_1287_, lean_object* v_sz_1288_, lean_object* v_i_1289_, lean_object* v_b_1290_, lean_object* v___y_1291_){
_start:
{
size_t v_sz_boxed_1292_; size_t v_i_boxed_1293_; lean_object* v_res_1294_; 
v_sz_boxed_1292_ = lean_unbox_usize(v_sz_1288_);
lean_dec(v_sz_1288_);
v_i_boxed_1293_ = lean_unbox_usize(v_i_1289_);
lean_dec(v_i_1289_);
v_res_1294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2(v_00_u03b1_1282_, v_a_1283_, v___x_1284_, v_a_1285_, v_a_1286_, v_as_1287_, v_sz_boxed_1292_, v_i_boxed_1293_, v_b_1290_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3(lean_object* v_00_u03b1_1295_, lean_object* v_as_1296_, size_t v_sz_1297_, size_t v_i_1298_, lean_object* v_b_1299_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg(v_as_1296_, v_sz_1297_, v_i_1298_, v_b_1299_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___boxed(lean_object* v_00_u03b1_1302_, lean_object* v_as_1303_, lean_object* v_sz_1304_, lean_object* v_i_1305_, lean_object* v_b_1306_, lean_object* v___y_1307_){
_start:
{
size_t v_sz_boxed_1308_; size_t v_i_boxed_1309_; lean_object* v_res_1310_; 
v_sz_boxed_1308_ = lean_unbox_usize(v_sz_1304_);
lean_dec(v_sz_1304_);
v_i_boxed_1309_ = lean_unbox_usize(v_i_1305_);
lean_dec(v_i_1305_);
v_res_1310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3(v_00_u03b1_1302_, v_as_1303_, v_sz_boxed_1308_, v_i_boxed_1309_, v_b_1306_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__0(lean_object* v_x_1315_){
_start:
{
if (lean_obj_tag(v_x_1315_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1325_; 
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
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1343_; 
v_a_1326_ = lean_ctor_get(v_x_1315_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_x_1315_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1328_ = v_x_1315_;
v_isShared_1329_ = v_isSharedCheck_1343_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v_x_1315_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1343_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v_fst_1330_; 
v_fst_1330_ = lean_ctor_get(v_a_1326_, 0);
lean_inc(v_fst_1330_);
lean_dec(v_a_1326_);
if (lean_obj_tag(v_fst_1330_) == 0)
{
lean_object* v___x_1331_; 
lean_del_object(v___x_1328_);
v___x_1331_ = ((lean_object*)(l_Std_Async_Selectable_tryOne___redArg___lam__0___closed__1));
return v___x_1331_;
}
else
{
lean_object* v_val_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1342_; 
v_val_1332_ = lean_ctor_get(v_fst_1330_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_fst_1330_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1334_ = v_fst_1330_;
v_isShared_1335_ = v_isSharedCheck_1342_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_val_1332_);
lean_dec(v_fst_1330_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1342_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 0, v_val_1332_);
v___x_1337_ = v___x_1328_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_val_1332_);
v___x_1337_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1339_; 
if (v_isShared_1335_ == 0)
{
lean_ctor_set_tag(v___x_1334_, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1337_);
v___x_1339_ = v___x_1334_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__0___boxed(lean_object* v_x_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Std_Async_Selectable_tryOne___redArg___lam__0(v_x_1344_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__0(lean_object* v___x_1347_, lean_object* v_x_1348_){
_start:
{
if (lean_obj_tag(v_x_1348_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1358_; 
v_a_1350_ = lean_ctor_get(v_x_1348_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_x_1348_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1352_ = v_x_1348_;
v_isShared_1353_ = v_isSharedCheck_1358_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v_x_1348_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1358_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1356_; 
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
return v___x_1356_;
}
}
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1371_; 
v_a_1359_ = lean_ctor_get(v_x_1348_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_x_1348_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1361_ = v_x_1348_;
v_isShared_1362_ = v_isSharedCheck_1371_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v_x_1348_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1371_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1363_, 0, v_a_1359_);
v___x_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
v___x_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
lean_ctor_set(v___x_1365_, 1, v___x_1347_);
v___x_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v___x_1366_);
v___x_1368_ = v___x_1361_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1369_; 
v___x_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
return v___x_1369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__0___boxed(lean_object* v___x_1372_, lean_object* v_x_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__0(v___x_1372_, v_x_1373_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__1(lean_object* v_a_1376_, lean_object* v___x_1377_, uint8_t v___x_1378_, lean_object* v___f_1379_, lean_object* v___x_1380_, lean_object* v_x_1381_){
_start:
{
if (lean_obj_tag(v_x_1381_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1391_; 
lean_dec_ref(v___x_1380_);
lean_dec_ref(v___f_1379_);
lean_dec(v___x_1377_);
lean_dec_ref(v_a_1376_);
v_a_1383_ = lean_ctor_get(v_x_1381_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v_x_1381_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1385_ = v_x_1381_;
v_isShared_1386_ = v_isSharedCheck_1391_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v_x_1381_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1391_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1389_; 
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
}
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1405_; 
v_a_1392_ = lean_ctor_get(v_x_1381_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_x_1381_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1394_ = v_x_1381_;
v_isShared_1395_ = v_isSharedCheck_1405_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v_x_1381_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1405_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
if (lean_obj_tag(v_a_1392_) == 1)
{
lean_object* v_val_1396_; lean_object* v_cont_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
lean_del_object(v___x_1394_);
lean_dec_ref(v___x_1380_);
v_val_1396_ = lean_ctor_get(v_a_1392_, 0);
lean_inc(v_val_1396_);
lean_dec_ref(v_a_1392_);
v_cont_1397_ = lean_ctor_get(v_a_1376_, 1);
lean_inc_ref(v_cont_1397_);
lean_dec_ref(v_a_1376_);
v___x_1398_ = lean_apply_2(v_cont_1397_, v_val_1396_, lean_box(0));
v___x_1399_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1377_, v___x_1378_, v___x_1398_, v___f_1379_);
return v___x_1399_;
}
else
{
lean_object* v___x_1400_; lean_object* v___x_1402_; 
lean_dec(v_a_1392_);
lean_dec_ref(v___f_1379_);
lean_dec(v___x_1377_);
lean_dec_ref(v_a_1376_);
v___x_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1380_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v___x_1400_);
v___x_1402_ = v___x_1394_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1403_; 
v___x_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1402_);
return v___x_1403_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__1___boxed(lean_object* v_a_1406_, lean_object* v___x_1407_, lean_object* v___x_1408_, lean_object* v___f_1409_, lean_object* v___x_1410_, lean_object* v_x_1411_, lean_object* v___y_1412_){
_start:
{
uint8_t v___x_2325__boxed_1413_; lean_object* v_res_1414_; 
v___x_2325__boxed_1413_ = lean_unbox(v___x_1408_);
v_res_1414_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__1(v_a_1406_, v___x_1407_, v___x_2325__boxed_1413_, v___f_1409_, v___x_1410_, v_x_1411_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__2___boxed(lean_object* v_i_1420_, lean_object* v___x_1421_, lean_object* v_as_1422_, lean_object* v_sz_1423_, lean_object* v_x_1424_, lean_object* v___y_1425_){
_start:
{
size_t v_i_boxed_1426_; size_t v_sz_boxed_1427_; lean_object* v_res_1428_; 
v_i_boxed_1426_ = lean_unbox_usize(v_i_1420_);
lean_dec(v_i_1420_);
v_sz_boxed_1427_ = lean_unbox_usize(v_sz_1423_);
lean_dec(v_sz_1423_);
v_res_1428_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__2(v_i_boxed_1426_, v___x_1421_, v_as_1422_, v_sz_boxed_1427_, v_x_1424_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg(lean_object* v___x_1429_, lean_object* v_as_1430_, size_t v_sz_1431_, size_t v_i_1432_, lean_object* v_b_1433_){
_start:
{
uint8_t v___x_1435_; 
v___x_1435_ = lean_usize_dec_lt(v_i_1432_, v_sz_1431_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
lean_dec_ref(v_as_1430_);
lean_dec(v___x_1429_);
v___x_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1436_, 0, v_b_1433_);
v___x_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
return v___x_1437_;
}
else
{
lean_object* v_a_1438_; lean_object* v_selector_1439_; lean_object* v_tryFn_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; uint8_t v___x_1443_; lean_object* v___f_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___f_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___f_1451_; uint8_t v___x_1452_; lean_object* v___x_1453_; 
lean_dec_ref(v_b_1433_);
v_a_1438_ = lean_array_uget_borrowed(v_as_1430_, v_i_1432_);
v_selector_1439_ = lean_ctor_get(v_a_1438_, 0);
v_tryFn_1440_ = lean_ctor_get(v_selector_1439_, 0);
lean_inc_ref(v_tryFn_1440_);
v___x_1441_ = lean_apply_1(v_tryFn_1440_, lean_box(0));
v___x_1442_ = lean_unsigned_to_nat(0u);
v___x_1443_ = lean_nat_dec_eq(v___x_1429_, v___x_1442_);
v___f_1444_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__0));
v___x_1445_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__1));
v___x_1446_ = lean_box(v___x_1443_);
lean_inc(v_a_1438_);
v___f_1447_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_1447_, 0, v_a_1438_);
lean_closure_set(v___f_1447_, 1, v___x_1442_);
lean_closure_set(v___f_1447_, 2, v___x_1446_);
lean_closure_set(v___f_1447_, 3, v___f_1444_);
lean_closure_set(v___f_1447_, 4, v___x_1445_);
v___x_1448_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1442_, v___x_1443_, v___x_1441_, v___f_1447_);
v___x_1449_ = lean_box_usize(v_i_1432_);
v___x_1450_ = lean_box_usize(v_sz_1431_);
v___f_1451_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_1451_, 0, v___x_1449_);
lean_closure_set(v___f_1451_, 1, v___x_1429_);
lean_closure_set(v___f_1451_, 2, v_as_1430_);
lean_closure_set(v___f_1451_, 3, v___x_1450_);
v___x_1452_ = 0;
v___x_1453_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1442_, v___x_1452_, v___x_1448_, v___f_1451_);
return v___x_1453_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__2(size_t v_i_1454_, lean_object* v___x_1455_, lean_object* v_as_1456_, size_t v_sz_1457_, lean_object* v_x_1458_){
_start:
{
if (lean_obj_tag(v_x_1458_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1468_; 
lean_dec_ref(v_as_1456_);
lean_dec(v___x_1455_);
v_a_1460_ = lean_ctor_get(v_x_1458_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_x_1458_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1462_ = v_x_1458_;
v_isShared_1463_ = v_isSharedCheck_1468_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v_x_1458_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1468_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
lean_object* v___x_1466_; 
v___x_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
return v___x_1466_;
}
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1488_; 
v_a_1469_ = lean_ctor_get(v_x_1458_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_x_1458_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1471_ = v_x_1458_;
v_isShared_1472_ = v_isSharedCheck_1488_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v_x_1458_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1488_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
if (lean_obj_tag(v_a_1469_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1483_; 
lean_dec_ref(v_as_1456_);
lean_dec(v___x_1455_);
v_a_1473_ = lean_ctor_get(v_a_1469_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_a_1469_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1475_ = v_a_1469_;
v_isShared_1476_ = v_isSharedCheck_1483_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v_a_1469_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1483_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v_a_1473_);
v___x_1478_ = v___x_1471_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v___x_1480_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 0, v___x_1478_);
v___x_1480_ = v___x_1475_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
else
{
lean_object* v_a_1484_; size_t v___x_1485_; size_t v___x_1486_; lean_object* v___x_1487_; 
lean_del_object(v___x_1471_);
v_a_1484_ = lean_ctor_get(v_a_1469_, 0);
lean_inc(v_a_1484_);
lean_dec_ref(v_a_1469_);
v___x_1485_ = ((size_t)1ULL);
v___x_1486_ = lean_usize_add(v_i_1454_, v___x_1485_);
v___x_1487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg(v___x_1455_, v_as_1456_, v_sz_1457_, v___x_1486_, v_a_1484_);
return v___x_1487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___boxed(lean_object* v___x_1489_, lean_object* v_as_1490_, lean_object* v_sz_1491_, lean_object* v_i_1492_, lean_object* v_b_1493_, lean_object* v___y_1494_){
_start:
{
size_t v_sz_boxed_1495_; size_t v_i_boxed_1496_; lean_object* v_res_1497_; 
v_sz_boxed_1495_ = lean_unbox_usize(v_sz_1491_);
lean_dec(v_sz_1491_);
v_i_boxed_1496_ = lean_unbox_usize(v_i_1492_);
lean_dec(v_i_1492_);
v_res_1497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg(v___x_1489_, v_as_1490_, v_sz_boxed_1495_, v_i_boxed_1496_, v_b_1493_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__1(lean_object* v_selectables_1498_, lean_object* v___x_1499_, lean_object* v___x_1500_, uint8_t v___x_1501_, lean_object* v___f_1502_, lean_object* v_x_1503_){
_start:
{
if (lean_obj_tag(v_x_1503_) == 0)
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1513_; 
lean_dec_ref(v___f_1502_);
lean_dec(v___x_1500_);
lean_dec(v___x_1499_);
lean_dec_ref(v_selectables_1498_);
v_a_1505_ = lean_ctor_get(v_x_1503_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_x_1503_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1507_ = v_x_1503_;
v_isShared_1508_ = v_isSharedCheck_1513_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v_x_1503_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1513_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
return v___x_1511_;
}
}
}
else
{
lean_object* v_a_1514_; uint64_t v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; size_t v_sz_1520_; size_t v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v_a_1514_ = lean_ctor_get(v_x_1503_, 0);
lean_inc(v_a_1514_);
lean_dec_ref(v_x_1503_);
v___x_1515_ = l_ByteArray_toUInt64LE_x21(v_a_1514_);
lean_dec(v_a_1514_);
v___x_1516_ = lean_uint64_to_nat(v___x_1515_);
v___x_1517_ = l_mkStdGen(v___x_1516_);
lean_dec(v___x_1516_);
v___x_1518_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(v_selectables_1498_, v___x_1517_);
v___x_1519_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__1));
v_sz_1520_ = lean_array_size(v___x_1518_);
v___x_1521_ = ((size_t)0ULL);
v___x_1522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg(v___x_1499_, v___x_1518_, v_sz_1520_, v___x_1521_, v___x_1519_);
v___x_1523_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1500_, v___x_1501_, v___x_1522_, v___f_1502_);
return v___x_1523_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__1___boxed(lean_object* v_selectables_1524_, lean_object* v___x_1525_, lean_object* v___x_1526_, lean_object* v___x_1527_, lean_object* v___f_1528_, lean_object* v_x_1529_, lean_object* v___y_1530_){
_start:
{
uint8_t v___x_2511__boxed_1531_; lean_object* v_res_1532_; 
v___x_2511__boxed_1531_ = lean_unbox(v___x_1527_);
v_res_1532_ = l_Std_Async_Selectable_tryOne___redArg___lam__1(v_selectables_1524_, v___x_1525_, v___x_1526_, v___x_2511__boxed_1531_, v___f_1528_, v_x_1529_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg(lean_object* v_selectables_1534_){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v___x_1536_ = lean_array_get_size(v_selectables_1534_);
v___x_1537_ = lean_unsigned_to_nat(0u);
v___x_1538_ = lean_nat_dec_eq(v___x_1536_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_object* v___f_1539_; lean_object* v___x_1540_; lean_object* v___f_1541_; lean_object* v_val_1543_; size_t v___x_1546_; lean_object* v___x_1547_; 
v___f_1539_ = ((lean_object*)(l_Std_Async_Selectable_tryOne___redArg___closed__0));
v___x_1540_ = lean_box(v___x_1538_);
v___f_1541_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_tryOne___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_1541_, 0, v_selectables_1534_);
lean_closure_set(v___f_1541_, 1, v___x_1536_);
lean_closure_set(v___f_1541_, 2, v___x_1537_);
lean_closure_set(v___f_1541_, 3, v___x_1540_);
lean_closure_set(v___f_1541_, 4, v___f_1539_);
v___x_1546_ = ((size_t)8ULL);
v___x_1547_ = lean_io_get_random_bytes(v___x_1546_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1547_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
lean_ctor_set_tag(v___x_1550_, 1);
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
v_val_1543_ = v___x_1553_;
goto v___jp_1542_;
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
v_a_1556_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1547_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1547_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
lean_ctor_set_tag(v___x_1558_, 0);
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
v_val_1543_ = v___x_1561_;
goto v___jp_1542_;
}
}
}
v___jp_1542_:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1544_, 0, v_val_1543_);
v___x_1545_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1537_, v___x_1538_, v___x_1544_, v___f_1541_);
return v___x_1545_;
}
}
else
{
lean_object* v___x_1564_; 
lean_dec_ref(v_selectables_1534_);
v___x_1564_ = ((lean_object*)(l_Std_Async_Selectable_tryOne___redArg___lam__0___closed__1));
return v___x_1564_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___boxed(lean_object* v_selectables_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Std_Async_Selectable_tryOne___redArg(v_selectables_1565_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne(lean_object* v_00_u03b1_1568_, lean_object* v_selectables_1569_){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Std_Async_Selectable_tryOne___redArg(v_selectables_1569_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___boxed(lean_object* v_00_u03b1_1572_, lean_object* v_selectables_1573_, lean_object* v_a_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Std_Async_Selectable_tryOne(v_00_u03b1_1572_, v_selectables_1573_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0(lean_object* v_00_u03b1_1576_, lean_object* v___x_1577_, lean_object* v_as_1578_, size_t v_sz_1579_, size_t v_i_1580_, lean_object* v_b_1581_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg(v___x_1577_, v_as_1578_, v_sz_1579_, v_i_1580_, v_b_1581_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___boxed(lean_object* v_00_u03b1_1584_, lean_object* v___x_1585_, lean_object* v_as_1586_, lean_object* v_sz_1587_, lean_object* v_i_1588_, lean_object* v_b_1589_, lean_object* v___y_1590_){
_start:
{
size_t v_sz_boxed_1591_; size_t v_i_boxed_1592_; lean_object* v_res_1593_; 
v_sz_boxed_1591_ = lean_unbox_usize(v_sz_1587_);
lean_dec(v_sz_1587_);
v_i_boxed_1592_ = lean_unbox_usize(v_i_1588_);
lean_dec(v_i_1588_);
v_res_1593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0(v_00_u03b1_1584_, v___x_1585_, v_as_1586_, v_sz_boxed_1591_, v_i_boxed_1592_, v_b_1589_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__1(lean_object* v___x_1594_, lean_object* v_x_1595_){
_start:
{
if (lean_obj_tag(v_x_1595_) == 0)
{
lean_object* v___x_1597_; 
v___x_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1597_, 0, v_x_1595_);
return v___x_1597_;
}
else
{
lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1605_; 
v_isSharedCheck_1605_ = !lean_is_exclusive(v_x_1595_);
if (v_isSharedCheck_1605_ == 0)
{
lean_object* v_unused_1606_; 
v_unused_1606_ = lean_ctor_get(v_x_1595_, 0);
lean_dec(v_unused_1606_);
v___x_1599_ = v_x_1595_;
v_isShared_1600_ = v_isSharedCheck_1605_;
goto v_resetjp_1598_;
}
else
{
lean_dec(v_x_1595_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1605_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v___x_1594_);
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1594_);
v___x_1602_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
lean_object* v___x_1603_; 
v___x_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
return v___x_1603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__1___boxed(lean_object* v___x_1607_, lean_object* v_x_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Std_Async_Selectable_combine___redArg___lam__1(v___x_1607_, v_x_1608_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__0(lean_object* v_a_1611_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1612_, 0, v_a_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__3(lean_object* v_a_1613_, lean_object* v___x_1614_, uint8_t v___x_1615_, lean_object* v___f_1616_, lean_object* v_x_1617_){
_start:
{
if (lean_obj_tag(v_x_1617_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1627_; 
lean_dec_ref(v___f_1616_);
lean_dec(v___x_1614_);
lean_dec_ref(v_a_1613_);
v_a_1619_ = lean_ctor_get(v_x_1617_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v_x_1617_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1621_ = v_x_1617_;
v_isShared_1622_ = v_isSharedCheck_1627_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v_x_1617_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1627_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
lean_object* v___x_1625_; 
v___x_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
return v___x_1625_;
}
}
}
else
{
lean_object* v_a_1628_; lean_object* v_cont_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v_a_1628_ = lean_ctor_get(v_x_1617_, 0);
lean_inc(v_a_1628_);
lean_dec_ref(v_x_1617_);
v_cont_1629_ = lean_ctor_get(v_a_1613_, 1);
lean_inc_ref(v_cont_1629_);
lean_dec_ref(v_a_1613_);
v___x_1630_ = lean_apply_2(v_cont_1629_, v_a_1628_, lean_box(0));
v___x_1631_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1614_, v___x_1615_, v___x_1630_, v___f_1616_);
return v___x_1631_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__3___boxed(lean_object* v_a_1632_, lean_object* v___x_1633_, lean_object* v___x_1634_, lean_object* v___f_1635_, lean_object* v_x_1636_, lean_object* v___y_1637_){
_start:
{
uint8_t v___x_7636__boxed_1638_; lean_object* v_res_1639_; 
v___x_7636__boxed_1638_ = lean_unbox(v___x_1634_);
v_res_1639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__3(v_a_1632_, v___x_1633_, v___x_7636__boxed_1638_, v___f_1635_, v_x_1636_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__2(lean_object* v_promise_1640_, lean_object* v_x_1641_){
_start:
{
if (lean_obj_tag(v_x_1641_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1653_; 
v_a_1643_ = lean_ctor_get(v_x_1641_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v_x_1641_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1645_ = v_x_1641_;
v_isShared_1646_ = v_isSharedCheck_1653_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v_x_1641_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1653_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1649_ = lean_io_promise_resolve(v___x_1648_, v_promise_1640_);
v___x_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
v___x_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
return v___x_1651_;
}
}
}
else
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1654_, 0, v_x_1641_);
return v___x_1654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__2___boxed(lean_object* v_promise_1655_, lean_object* v_x_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__2(v_promise_1655_, v_x_1656_);
lean_dec(v_promise_1655_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__4(lean_object* v___x_1659_, uint8_t v___x_1660_, lean_object* v___f_1661_, lean_object* v___f_1662_, lean_object* v_val_1663_, lean_object* v_x_1664_){
_start:
{
lean_object* v_val_1667_; 
if (lean_obj_tag(v_x_1664_) == 0)
{
lean_object* v___x_1671_; 
lean_dec_ref(v_val_1663_);
lean_dec_ref(v___f_1662_);
lean_dec_ref(v___f_1661_);
lean_dec(v___x_1659_);
v___x_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1671_, 0, v_x_1664_);
return v___x_1671_;
}
else
{
lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1684_; 
v_isSharedCheck_1684_ = !lean_is_exclusive(v_x_1664_);
if (v_isSharedCheck_1684_ == 0)
{
lean_object* v_unused_1685_; 
v_unused_1685_ = lean_ctor_get(v_x_1664_, 0);
lean_dec(v_unused_1685_);
v___x_1673_ = v_x_1664_;
v_isShared_1674_ = v_isSharedCheck_1684_;
goto v_resetjp_1672_;
}
else
{
lean_dec(v_x_1664_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1684_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; 
v___x_1675_ = l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___redArg(v_val_1663_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v___x_1678_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1676_);
lean_dec_ref(v___x_1675_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v_a_1676_);
v___x_1678_ = v___x_1673_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1676_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
v_val_1667_ = v___x_1678_;
goto v___jp_1666_;
}
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; 
v_a_1680_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1680_);
lean_dec_ref(v___x_1675_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set_tag(v___x_1673_, 0);
lean_ctor_set(v___x_1673_, 0, v_a_1680_);
v___x_1682_ = v___x_1673_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1680_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
v_val_1667_ = v___x_1682_;
goto v___jp_1666_;
}
}
}
}
v___jp_1666_:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1668_, 0, v_val_1667_);
lean_inc(v___x_1659_);
v___x_1669_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1659_, v___x_1660_, v___x_1668_, v___f_1661_);
v___x_1670_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1659_, v___x_1660_, v___x_1669_, v___f_1662_);
return v___x_1670_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__4___boxed(lean_object* v___x_1686_, lean_object* v___x_1687_, lean_object* v___f_1688_, lean_object* v___f_1689_, lean_object* v_val_1690_, lean_object* v_x_1691_, lean_object* v___y_1692_){
_start:
{
uint8_t v___x_7706__boxed_1693_; lean_object* v_res_1694_; 
v___x_7706__boxed_1693_ = lean_unbox(v___x_1687_);
v_res_1694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__4(v___x_1686_, v___x_7706__boxed_1693_, v___f_1688_, v___f_1689_, v_val_1690_, v_x_1691_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg___lam__1___boxed(lean_object* v_i_1695_, lean_object* v___x_1696_, lean_object* v_as_1697_, lean_object* v_sz_1698_, lean_object* v_x_1699_, lean_object* v___y_1700_){
_start:
{
size_t v_i_boxed_1701_; size_t v_sz_boxed_1702_; lean_object* v_res_1703_; 
v_i_boxed_1701_ = lean_unbox_usize(v_i_1695_);
lean_dec(v_i_1695_);
v_sz_boxed_1702_ = lean_unbox_usize(v_sz_1698_);
lean_dec(v_sz_1698_);
v_res_1703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg___lam__1(v_i_boxed_1701_, v___x_1696_, v_as_1697_, v_sz_boxed_1702_, v_x_1699_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg(lean_object* v___x_1704_, lean_object* v_as_1705_, size_t v_sz_1706_, size_t v_i_1707_, lean_object* v_b_1708_){
_start:
{
uint8_t v___x_1710_; 
v___x_1710_ = lean_usize_dec_lt(v_i_1707_, v_sz_1706_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
lean_dec_ref(v_as_1705_);
lean_dec(v___x_1704_);
v___x_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1711_, 0, v_b_1708_);
v___x_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1711_);
return v___x_1712_;
}
else
{
lean_object* v_a_1713_; lean_object* v_selector_1714_; lean_object* v_unregisterFn_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; lean_object* v___f_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___f_1723_; uint8_t v___x_1724_; lean_object* v___x_1725_; 
v_a_1713_ = lean_array_uget_borrowed(v_as_1705_, v_i_1707_);
v_selector_1714_ = lean_ctor_get(v_a_1713_, 0);
v_unregisterFn_1715_ = lean_ctor_get(v_selector_1714_, 2);
lean_inc_ref(v_unregisterFn_1715_);
v___x_1716_ = lean_apply_1(v_unregisterFn_1715_, lean_box(0));
v___x_1717_ = lean_unsigned_to_nat(0u);
v___x_1718_ = lean_nat_dec_eq(v___x_1704_, v___x_1717_);
v___f_1719_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___closed__0));
v___x_1720_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1717_, v___x_1718_, v___x_1716_, v___f_1719_);
v___x_1721_ = lean_box_usize(v_i_1707_);
v___x_1722_ = lean_box_usize(v_sz_1706_);
v___f_1723_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg___lam__1___boxed), 6, 4);
lean_closure_set(v___f_1723_, 0, v___x_1721_);
lean_closure_set(v___f_1723_, 1, v___x_1704_);
lean_closure_set(v___f_1723_, 2, v_as_1705_);
lean_closure_set(v___f_1723_, 3, v___x_1722_);
v___x_1724_ = 0;
v___x_1725_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1717_, v___x_1724_, v___x_1720_, v___f_1723_);
return v___x_1725_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg___lam__1(size_t v_i_1726_, lean_object* v___x_1727_, lean_object* v_as_1728_, size_t v_sz_1729_, lean_object* v_x_1730_){
_start:
{
if (lean_obj_tag(v_x_1730_) == 0)
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1740_; 
lean_dec_ref(v_as_1728_);
lean_dec(v___x_1727_);
v_a_1732_ = lean_ctor_get(v_x_1730_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v_x_1730_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1734_ = v_x_1730_;
v_isShared_1735_ = v_isSharedCheck_1740_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v_x_1730_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1740_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
lean_object* v___x_1738_; 
v___x_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
return v___x_1738_;
}
}
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1760_; 
v_a_1741_ = lean_ctor_get(v_x_1730_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v_x_1730_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1743_ = v_x_1730_;
v_isShared_1744_ = v_isSharedCheck_1760_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v_x_1730_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1760_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
if (lean_obj_tag(v_a_1741_) == 0)
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1755_; 
lean_dec_ref(v_as_1728_);
lean_dec(v___x_1727_);
v_a_1745_ = lean_ctor_get(v_a_1741_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_a_1741_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1747_ = v_a_1741_;
v_isShared_1748_ = v_isSharedCheck_1755_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v_a_1741_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1755_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v_a_1745_);
v___x_1750_ = v___x_1743_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
lean_object* v___x_1752_; 
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1750_);
v___x_1752_ = v___x_1747_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1750_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
else
{
lean_object* v_a_1756_; size_t v___x_1757_; size_t v___x_1758_; lean_object* v___x_1759_; 
lean_del_object(v___x_1743_);
v_a_1756_ = lean_ctor_get(v_a_1741_, 0);
lean_inc(v_a_1756_);
lean_dec_ref(v_a_1741_);
v___x_1757_ = ((size_t)1ULL);
v___x_1758_ = lean_usize_add(v_i_1726_, v___x_1757_);
v___x_1759_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg(v___x_1727_, v_as_1728_, v_sz_1729_, v___x_1758_, v_a_1756_);
return v___x_1759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg___boxed(lean_object* v___x_1761_, lean_object* v_as_1762_, lean_object* v_sz_1763_, lean_object* v_i_1764_, lean_object* v_b_1765_, lean_object* v___y_1766_){
_start:
{
size_t v_sz_boxed_1767_; size_t v_i_boxed_1768_; lean_object* v_res_1769_; 
v_sz_boxed_1767_ = lean_unbox_usize(v_sz_1763_);
lean_dec(v_sz_1763_);
v_i_boxed_1768_ = lean_unbox_usize(v_i_1764_);
lean_dec(v_i_1764_);
v_res_1769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg(v___x_1761_, v_as_1762_, v_sz_boxed_1767_, v_i_boxed_1768_, v_b_1765_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__5(lean_object* v___x_1770_, lean_object* v___x_1771_, lean_object* v___x_1772_, lean_object* v___x_1773_, uint8_t v___x_1774_, lean_object* v___f_1775_, lean_object* v_x_1776_){
_start:
{
if (lean_obj_tag(v_x_1776_) == 0)
{
lean_object* v___x_1778_; 
lean_dec_ref(v___f_1775_);
lean_dec(v___x_1773_);
lean_dec(v___x_1771_);
lean_dec_ref(v___x_1770_);
v___x_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1778_, 0, v_x_1776_);
return v___x_1778_;
}
else
{
size_t v_sz_1779_; size_t v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
lean_dec_ref(v_x_1776_);
v_sz_1779_ = lean_array_size(v___x_1770_);
v___x_1780_ = ((size_t)0ULL);
v___x_1781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg(v___x_1771_, v___x_1770_, v_sz_1779_, v___x_1780_, v___x_1772_);
v___x_1782_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1773_, v___x_1774_, v___x_1781_, v___f_1775_);
return v___x_1782_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__5___boxed(lean_object* v___x_1783_, lean_object* v___x_1784_, lean_object* v___x_1785_, lean_object* v___x_1786_, lean_object* v___x_1787_, lean_object* v___f_1788_, lean_object* v_x_1789_, lean_object* v___y_1790_){
_start:
{
uint8_t v___x_7874__boxed_1791_; lean_object* v_res_1792_; 
v___x_7874__boxed_1791_ = lean_unbox(v___x_1787_);
v_res_1792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__5(v___x_1783_, v___x_1784_, v___x_1785_, v___x_1786_, v___x_7874__boxed_1791_, v___f_1788_, v_x_1789_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__1(lean_object* v_promise_1793_, lean_object* v_x_1794_){
_start:
{
if (lean_obj_tag(v_x_1794_) == 0)
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1804_; 
v_a_1796_ = lean_ctor_get(v_x_1794_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v_x_1794_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1798_ = v_x_1794_;
v_isShared_1799_ = v_isSharedCheck_1804_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v_x_1794_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1804_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
lean_object* v___x_1802_; 
v___x_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1801_);
return v___x_1802_;
}
}
}
else
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1805_ = lean_io_promise_resolve(v_x_1794_, v_promise_1793_);
v___x_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
v___x_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
return v___x_1807_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__1___boxed(lean_object* v_promise_1808_, lean_object* v_x_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__1(v_promise_1808_, v_x_1809_);
lean_dec(v_promise_1808_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__6(lean_object* v___x_1812_, lean_object* v_promise_1813_, lean_object* v_a_1814_, lean_object* v___x_1815_, uint8_t v___x_1816_, lean_object* v___x_1817_, lean_object* v___x_1818_, lean_object* v_a_1819_, lean_object* v___f_1820_, lean_object* v_a_1821_){
_start:
{
if (lean_obj_tag(v_a_1821_) == 0)
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
lean_dec_ref(v___f_1820_);
lean_dec(v___x_1818_);
lean_dec_ref(v___x_1817_);
lean_dec(v___x_1815_);
lean_dec_ref(v_a_1814_);
lean_dec(v_promise_1813_);
v___x_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1812_);
v___x_1824_ = lean_task_pure(v___x_1823_);
return v___x_1824_;
}
else
{
lean_object* v_val_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1846_; 
v_val_1825_ = lean_ctor_get(v_a_1821_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v_a_1821_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1827_ = v_a_1821_;
v_isShared_1828_ = v_isSharedCheck_1846_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_val_1825_);
lean_dec(v_a_1821_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1846_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___f_1829_; lean_object* v___f_1830_; lean_object* v___x_1831_; lean_object* v___f_1832_; lean_object* v___x_1833_; lean_object* v___f_1834_; lean_object* v___x_1835_; lean_object* v___f_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; 
lean_inc(v_promise_1813_);
v___f_1829_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1829_, 0, v_promise_1813_);
v___f_1830_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1830_, 0, v_promise_1813_);
v___x_1831_ = lean_box(v___x_1816_);
lean_inc_n(v___x_1815_, 4);
v___f_1832_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_1832_, 0, v_a_1814_);
lean_closure_set(v___f_1832_, 1, v___x_1815_);
lean_closure_set(v___f_1832_, 2, v___x_1831_);
lean_closure_set(v___f_1832_, 3, v___f_1830_);
v___x_1833_ = lean_box(v___x_1816_);
v___f_1834_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__4___boxed), 7, 5);
lean_closure_set(v___f_1834_, 0, v___x_1815_);
lean_closure_set(v___f_1834_, 1, v___x_1833_);
lean_closure_set(v___f_1834_, 2, v___f_1832_);
lean_closure_set(v___f_1834_, 3, v___f_1829_);
lean_closure_set(v___f_1834_, 4, v_val_1825_);
v___x_1835_ = lean_box(v___x_1816_);
v___f_1836_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__5___boxed), 8, 6);
lean_closure_set(v___f_1836_, 0, v___x_1817_);
lean_closure_set(v___f_1836_, 1, v___x_1818_);
lean_closure_set(v___f_1836_, 2, v___x_1812_);
lean_closure_set(v___f_1836_, 3, v___x_1815_);
lean_closure_set(v___f_1836_, 4, v___x_1835_);
lean_closure_set(v___f_1836_, 5, v___f_1834_);
v___x_1837_ = l_IO_Promise_result_x21___redArg(v_a_1819_);
v___x_1838_ = lean_task_map(v___f_1820_, v___x_1837_, v___x_1815_, v___x_1816_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1838_);
v___x_1840_ = v___x_1827_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
lean_object* v___x_1841_; 
v___x_1841_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1815_, v___x_1816_, v___x_1840_, v___f_1836_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1843_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref(v___x_1841_);
v___x_1843_ = lean_task_pure(v_a_1842_);
return v___x_1843_;
}
else
{
lean_object* v_a_1844_; 
v_a_1844_ = lean_ctor_get(v___x_1841_, 0);
lean_inc_ref(v_a_1844_);
lean_dec_ref(v___x_1841_);
return v_a_1844_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__6___boxed(lean_object* v___x_1847_, lean_object* v_promise_1848_, lean_object* v_a_1849_, lean_object* v___x_1850_, lean_object* v___x_1851_, lean_object* v___x_1852_, lean_object* v___x_1853_, lean_object* v_a_1854_, lean_object* v___f_1855_, lean_object* v_a_1856_, lean_object* v___y_1857_){
_start:
{
uint8_t v___x_7937__boxed_1858_; lean_object* v_res_1859_; 
v___x_7937__boxed_1858_ = lean_unbox(v___x_1851_);
v_res_1859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__6(v___x_1847_, v_promise_1848_, v_a_1849_, v___x_1850_, v___x_7937__boxed_1858_, v___x_1852_, v___x_1853_, v_a_1854_, v___f_1855_, v_a_1856_);
lean_dec(v_a_1854_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__7(lean_object* v___x_1860_, lean_object* v_promise_1861_, lean_object* v_a_1862_, lean_object* v___x_1863_, uint8_t v___x_1864_, lean_object* v___x_1865_, lean_object* v___x_1866_, lean_object* v___f_1867_, lean_object* v_a_1868_, lean_object* v___f_1869_, lean_object* v_x_1870_){
_start:
{
if (lean_obj_tag(v_x_1870_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1880_; 
lean_dec_ref(v___f_1869_);
lean_dec_ref(v___f_1867_);
lean_dec(v___x_1866_);
lean_dec_ref(v___x_1865_);
lean_dec(v___x_1863_);
lean_dec_ref(v_a_1862_);
lean_dec(v_promise_1861_);
v_a_1872_ = lean_ctor_get(v_x_1870_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v_x_1870_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1874_ = v_x_1870_;
v_isShared_1875_ = v_isSharedCheck_1880_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v_x_1870_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1880_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
return v___x_1878_;
}
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1894_; 
v_a_1881_ = lean_ctor_get(v_x_1870_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v_x_1870_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1883_ = v_x_1870_;
v_isShared_1884_ = v_isSharedCheck_1894_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v_x_1870_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1894_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; lean_object* v___f_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1885_ = lean_box(v___x_1864_);
lean_inc_n(v___x_1863_, 2);
v___f_1886_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__6___boxed), 11, 9);
lean_closure_set(v___f_1886_, 0, v___x_1860_);
lean_closure_set(v___f_1886_, 1, v_promise_1861_);
lean_closure_set(v___f_1886_, 2, v_a_1862_);
lean_closure_set(v___f_1886_, 3, v___x_1863_);
lean_closure_set(v___f_1886_, 4, v___x_1885_);
lean_closure_set(v___f_1886_, 5, v___x_1865_);
lean_closure_set(v___f_1886_, 6, v___x_1866_);
lean_closure_set(v___f_1886_, 7, v_a_1881_);
lean_closure_set(v___f_1886_, 8, v___f_1867_);
v___x_1887_ = lean_io_promise_result_opt(v_a_1868_);
v___x_1888_ = lean_io_bind_task(v___x_1887_, v___f_1886_, v___x_1863_, v___x_1864_);
lean_dec_ref(v___x_1888_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 0, v___x_1860_);
v___x_1890_ = v___x_1883_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1860_);
v___x_1890_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
v___x_1892_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1863_, v___x_1864_, v___x_1891_, v___f_1869_);
return v___x_1892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__7___boxed(lean_object* v___x_1895_, lean_object* v_promise_1896_, lean_object* v_a_1897_, lean_object* v___x_1898_, lean_object* v___x_1899_, lean_object* v___x_1900_, lean_object* v___x_1901_, lean_object* v___f_1902_, lean_object* v_a_1903_, lean_object* v___f_1904_, lean_object* v_x_1905_, lean_object* v___y_1906_){
_start:
{
uint8_t v___x_8009__boxed_1907_; lean_object* v_res_1908_; 
v___x_8009__boxed_1907_ = lean_unbox(v___x_1899_);
v_res_1908_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__7(v___x_1895_, v_promise_1896_, v_a_1897_, v___x_1898_, v___x_8009__boxed_1907_, v___x_1900_, v___x_1901_, v___f_1902_, v_a_1903_, v___f_1904_, v_x_1905_);
lean_dec(v_a_1903_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__8(lean_object* v___x_1909_, uint8_t v___x_1910_, lean_object* v___f_1911_, lean_object* v_x_1912_){
_start:
{
if (lean_obj_tag(v_x_1912_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1922_; 
lean_dec_ref(v___f_1911_);
lean_dec(v___x_1909_);
v_a_1914_ = lean_ctor_get(v_x_1912_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v_x_1912_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1916_ = v_x_1912_;
v_isShared_1917_ = v_isSharedCheck_1922_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v_x_1912_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1922_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
lean_object* v___x_1920_; 
v___x_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
return v___x_1920_;
}
}
}
else
{
lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1932_; 
v_isSharedCheck_1932_ = !lean_is_exclusive(v_x_1912_);
if (v_isSharedCheck_1932_ == 0)
{
lean_object* v_unused_1933_; 
v_unused_1933_ = lean_ctor_get(v_x_1912_, 0);
lean_dec(v_unused_1933_);
v___x_1924_ = v_x_1912_;
v_isShared_1925_ = v_isSharedCheck_1932_;
goto v_resetjp_1923_;
}
else
{
lean_dec(v_x_1912_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1932_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1926_; lean_object* v___x_1928_; 
v___x_1926_ = lean_io_promise_new();
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 0, v___x_1926_);
v___x_1928_ = v___x_1924_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1926_);
v___x_1928_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
v___x_1930_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1909_, v___x_1910_, v___x_1929_, v___f_1911_);
return v___x_1930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__8___boxed(lean_object* v___x_1934_, lean_object* v___x_1935_, lean_object* v___f_1936_, lean_object* v_x_1937_, lean_object* v___y_1938_){
_start:
{
uint8_t v___x_8084__boxed_1939_; lean_object* v_res_1940_; 
v___x_8084__boxed_1939_ = lean_unbox(v___x_1935_);
v_res_1940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__8(v___x_1934_, v___x_8084__boxed_1939_, v___f_1936_, v_x_1937_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__9(lean_object* v_waiter_1941_, lean_object* v_a_1942_, lean_object* v___x_1943_, lean_object* v___x_1944_, uint8_t v___x_1945_, lean_object* v___x_1946_, lean_object* v___x_1947_, lean_object* v___f_1948_, lean_object* v___f_1949_, lean_object* v_x_1950_){
_start:
{
if (lean_obj_tag(v_x_1950_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1960_; 
lean_dec_ref(v___f_1949_);
lean_dec_ref(v___f_1948_);
lean_dec(v___x_1947_);
lean_dec_ref(v___x_1946_);
lean_dec(v___x_1944_);
lean_dec_ref(v_a_1942_);
lean_dec_ref(v_waiter_1941_);
v_a_1952_ = lean_ctor_get(v_x_1950_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v_x_1950_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1954_ = v_x_1950_;
v_isShared_1955_ = v_isSharedCheck_1960_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v_x_1950_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1960_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
lean_object* v___x_1958_; 
v___x_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1957_);
return v___x_1958_;
}
}
}
else
{
lean_object* v_selector_1961_; lean_object* v_a_1962_; lean_object* v_finished_1963_; lean_object* v_promise_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1978_; 
v_selector_1961_ = lean_ctor_get(v_a_1942_, 0);
v_a_1962_ = lean_ctor_get(v_x_1950_, 0);
lean_inc(v_a_1962_);
lean_dec_ref(v_x_1950_);
v_finished_1963_ = lean_ctor_get(v_waiter_1941_, 0);
v_promise_1964_ = lean_ctor_get(v_waiter_1941_, 1);
v_isSharedCheck_1978_ = !lean_is_exclusive(v_waiter_1941_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1966_ = v_waiter_1941_;
v_isShared_1967_ = v_isSharedCheck_1978_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_promise_1964_);
lean_inc(v_finished_1963_);
lean_dec(v_waiter_1941_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1978_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v_registerFn_1968_; lean_object* v___x_1970_; 
v_registerFn_1968_ = lean_ctor_get(v_selector_1961_, 1);
lean_inc(v_a_1962_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 1, v_a_1962_);
v___x_1970_ = v___x_1966_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_finished_1963_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_a_1962_);
v___x_1970_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___f_1973_; lean_object* v___x_1974_; lean_object* v___f_1975_; lean_object* v___x_1976_; 
lean_inc_ref(v_registerFn_1968_);
v___x_1971_ = lean_apply_2(v_registerFn_1968_, v___x_1970_, lean_box(0));
v___x_1972_ = lean_box(v___x_1945_);
lean_inc_n(v___x_1944_, 2);
v___f_1973_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__7___boxed), 12, 10);
lean_closure_set(v___f_1973_, 0, v___x_1943_);
lean_closure_set(v___f_1973_, 1, v_promise_1964_);
lean_closure_set(v___f_1973_, 2, v_a_1942_);
lean_closure_set(v___f_1973_, 3, v___x_1944_);
lean_closure_set(v___f_1973_, 4, v___x_1972_);
lean_closure_set(v___f_1973_, 5, v___x_1946_);
lean_closure_set(v___f_1973_, 6, v___x_1947_);
lean_closure_set(v___f_1973_, 7, v___f_1948_);
lean_closure_set(v___f_1973_, 8, v_a_1962_);
lean_closure_set(v___f_1973_, 9, v___f_1949_);
v___x_1974_ = lean_box(v___x_1945_);
v___f_1975_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_1975_, 0, v___x_1944_);
lean_closure_set(v___f_1975_, 1, v___x_1974_);
lean_closure_set(v___f_1975_, 2, v___f_1973_);
v___x_1976_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1944_, v___x_1945_, v___x_1971_, v___f_1975_);
return v___x_1976_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__9___boxed(lean_object* v_waiter_1979_, lean_object* v_a_1980_, lean_object* v___x_1981_, lean_object* v___x_1982_, lean_object* v___x_1983_, lean_object* v___x_1984_, lean_object* v___x_1985_, lean_object* v___f_1986_, lean_object* v___f_1987_, lean_object* v_x_1988_, lean_object* v___y_1989_){
_start:
{
uint8_t v___x_8141__boxed_1990_; lean_object* v_res_1991_; 
v___x_8141__boxed_1990_ = lean_unbox(v___x_1983_);
v_res_1991_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__9(v_waiter_1979_, v_a_1980_, v___x_1981_, v___x_1982_, v___x_8141__boxed_1990_, v___x_1984_, v___x_1985_, v___f_1986_, v___f_1987_, v_x_1988_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__10___boxed(lean_object* v_i_1993_, lean_object* v_waiter_1994_, lean_object* v___x_1995_, lean_object* v___x_1996_, lean_object* v_as_1997_, lean_object* v_sz_1998_, lean_object* v_x_1999_, lean_object* v___y_2000_){
_start:
{
size_t v_i_boxed_2001_; size_t v_sz_boxed_2002_; lean_object* v_res_2003_; 
v_i_boxed_2001_ = lean_unbox_usize(v_i_1993_);
lean_dec(v_i_1993_);
v_sz_boxed_2002_ = lean_unbox_usize(v_sz_1998_);
lean_dec(v_sz_1998_);
v_res_2003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__10(v_i_boxed_2001_, v_waiter_1994_, v___x_1995_, v___x_1996_, v_as_1997_, v_sz_boxed_2002_, v_x_1999_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg(lean_object* v_waiter_2004_, lean_object* v___x_2005_, lean_object* v___x_2006_, lean_object* v_as_2007_, size_t v_sz_2008_, size_t v_i_2009_, lean_object* v_b_2010_){
_start:
{
uint8_t v___x_2012_; 
v___x_2012_ = lean_usize_dec_lt(v_i_2009_, v_sz_2008_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
lean_dec_ref(v_as_2007_);
lean_dec_ref(v___x_2006_);
lean_dec(v___x_2005_);
lean_dec_ref(v_waiter_2004_);
v___x_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2013_, 0, v_b_2010_);
v___x_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
return v___x_2014_;
}
else
{
lean_object* v___x_2015_; lean_object* v___f_2016_; lean_object* v___x_2017_; lean_object* v___f_2018_; lean_object* v___x_2019_; uint8_t v___x_2020_; lean_object* v_a_2021_; lean_object* v___x_2022_; lean_object* v___f_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___f_2029_; uint8_t v___x_2030_; lean_object* v___x_2031_; 
v___x_2015_ = lean_io_promise_new();
v___f_2016_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___closed__0));
v___x_2017_ = lean_box(0);
v___f_2018_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___closed__0));
v___x_2019_ = lean_unsigned_to_nat(0u);
v___x_2020_ = lean_nat_dec_eq(v___x_2005_, v___x_2019_);
v_a_2021_ = lean_array_uget_borrowed(v_as_2007_, v_i_2009_);
v___x_2022_ = lean_box(v___x_2020_);
lean_inc(v___x_2005_);
lean_inc_ref(v___x_2006_);
lean_inc(v_a_2021_);
lean_inc_ref(v_waiter_2004_);
v___f_2023_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__9___boxed), 11, 9);
lean_closure_set(v___f_2023_, 0, v_waiter_2004_);
lean_closure_set(v___f_2023_, 1, v_a_2021_);
lean_closure_set(v___f_2023_, 2, v___x_2017_);
lean_closure_set(v___f_2023_, 3, v___x_2019_);
lean_closure_set(v___f_2023_, 4, v___x_2022_);
lean_closure_set(v___f_2023_, 5, v___x_2006_);
lean_closure_set(v___f_2023_, 6, v___x_2005_);
lean_closure_set(v___f_2023_, 7, v___f_2016_);
lean_closure_set(v___f_2023_, 8, v___f_2018_);
v___x_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2015_);
v___x_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2024_);
v___x_2026_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2019_, v___x_2020_, v___x_2025_, v___f_2023_);
v___x_2027_ = lean_box_usize(v_i_2009_);
v___x_2028_ = lean_box_usize(v_sz_2008_);
v___f_2029_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__10___boxed), 8, 6);
lean_closure_set(v___f_2029_, 0, v___x_2027_);
lean_closure_set(v___f_2029_, 1, v_waiter_2004_);
lean_closure_set(v___f_2029_, 2, v___x_2005_);
lean_closure_set(v___f_2029_, 3, v___x_2006_);
lean_closure_set(v___f_2029_, 4, v_as_2007_);
lean_closure_set(v___f_2029_, 5, v___x_2028_);
v___x_2030_ = 0;
v___x_2031_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2019_, v___x_2030_, v___x_2026_, v___f_2029_);
return v___x_2031_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__10(size_t v_i_2032_, lean_object* v_waiter_2033_, lean_object* v___x_2034_, lean_object* v___x_2035_, lean_object* v_as_2036_, size_t v_sz_2037_, lean_object* v_x_2038_){
_start:
{
if (lean_obj_tag(v_x_2038_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2048_; 
lean_dec_ref(v_as_2036_);
lean_dec_ref(v___x_2035_);
lean_dec(v___x_2034_);
lean_dec_ref(v_waiter_2033_);
v_a_2040_ = lean_ctor_get(v_x_2038_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v_x_2038_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2042_ = v_x_2038_;
v_isShared_2043_ = v_isSharedCheck_2048_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v_x_2038_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2048_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
lean_object* v___x_2046_; 
v___x_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
return v___x_2046_;
}
}
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2068_; 
v_a_2049_ = lean_ctor_get(v_x_2038_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v_x_2038_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2051_ = v_x_2038_;
v_isShared_2052_ = v_isSharedCheck_2068_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v_x_2038_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2068_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
if (lean_obj_tag(v_a_2049_) == 0)
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2063_; 
lean_dec_ref(v_as_2036_);
lean_dec_ref(v___x_2035_);
lean_dec(v___x_2034_);
lean_dec_ref(v_waiter_2033_);
v_a_2053_ = lean_ctor_get(v_a_2049_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v_a_2049_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2055_ = v_a_2049_;
v_isShared_2056_ = v_isSharedCheck_2063_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v_a_2049_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2063_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 0, v_a_2053_);
v___x_2058_ = v___x_2051_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
lean_object* v___x_2060_; 
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 0, v___x_2058_);
v___x_2060_ = v___x_2055_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
else
{
lean_object* v_a_2064_; size_t v___x_2065_; size_t v___x_2066_; lean_object* v___x_2067_; 
lean_del_object(v___x_2051_);
v_a_2064_ = lean_ctor_get(v_a_2049_, 0);
lean_inc(v_a_2064_);
lean_dec_ref(v_a_2049_);
v___x_2065_ = ((size_t)1ULL);
v___x_2066_ = lean_usize_add(v_i_2032_, v___x_2065_);
v___x_2067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg(v_waiter_2033_, v___x_2034_, v___x_2035_, v_as_2036_, v_sz_2037_, v___x_2066_, v_a_2064_);
return v___x_2067_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___boxed(lean_object* v_waiter_2069_, lean_object* v___x_2070_, lean_object* v___x_2071_, lean_object* v_as_2072_, lean_object* v_sz_2073_, lean_object* v_i_2074_, lean_object* v_b_2075_, lean_object* v___y_2076_){
_start:
{
size_t v_sz_boxed_2077_; size_t v_i_boxed_2078_; lean_object* v_res_2079_; 
v_sz_boxed_2077_ = lean_unbox_usize(v_sz_2073_);
lean_dec(v_sz_2073_);
v_i_boxed_2078_ = lean_unbox_usize(v_i_2074_);
lean_dec(v_i_2074_);
v_res_2079_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg(v_waiter_2069_, v___x_2070_, v___x_2071_, v_as_2072_, v_sz_boxed_2077_, v_i_boxed_2078_, v_b_2075_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__0(lean_object* v___x_2080_, lean_object* v___x_2081_, lean_object* v___x_2082_, lean_object* v___x_2083_, uint8_t v___x_2084_, lean_object* v___f_2085_, lean_object* v_waiter_2086_){
_start:
{
size_t v_sz_2088_; size_t v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v_sz_2088_ = lean_array_size(v___x_2080_);
v___x_2089_ = ((size_t)0ULL);
lean_inc_ref(v___x_2080_);
v___x_2090_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg(v_waiter_2086_, v___x_2081_, v___x_2080_, v___x_2080_, v_sz_2088_, v___x_2089_, v___x_2082_);
v___x_2091_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2083_, v___x_2084_, v___x_2090_, v___f_2085_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__0___boxed(lean_object* v___x_2092_, lean_object* v___x_2093_, lean_object* v___x_2094_, lean_object* v___x_2095_, lean_object* v___x_2096_, lean_object* v___f_2097_, lean_object* v_waiter_2098_, lean_object* v___y_2099_){
_start:
{
uint8_t v___x_8338__boxed_2100_; lean_object* v_res_2101_; 
v___x_8338__boxed_2100_ = lean_unbox(v___x_2096_);
v_res_2101_ = l_Std_Async_Selectable_combine___redArg___lam__0(v___x_2092_, v___x_2093_, v___x_2094_, v___x_2095_, v___x_8338__boxed_2100_, v___f_2097_, v_waiter_2098_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__3(lean_object* v___x_2102_, lean_object* v___x_2103_, size_t v_sz_2104_, size_t v___x_2105_, lean_object* v___x_2106_, lean_object* v___x_2107_, uint8_t v___x_2108_, lean_object* v___f_2109_){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg(v___x_2102_, v___x_2103_, v_sz_2104_, v___x_2105_, v___x_2106_);
v___x_2112_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2107_, v___x_2108_, v___x_2111_, v___f_2109_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__3___boxed(lean_object* v___x_2113_, lean_object* v___x_2114_, lean_object* v_sz_2115_, lean_object* v___x_2116_, lean_object* v___x_2117_, lean_object* v___x_2118_, lean_object* v___x_2119_, lean_object* v___f_2120_, lean_object* v___y_2121_){
_start:
{
size_t v_sz_boxed_2122_; size_t v___x_8363__boxed_2123_; uint8_t v___x_8366__boxed_2124_; lean_object* v_res_2125_; 
v_sz_boxed_2122_ = lean_unbox_usize(v_sz_2115_);
lean_dec(v_sz_2115_);
v___x_8363__boxed_2123_ = lean_unbox_usize(v___x_2116_);
lean_dec(v___x_2116_);
v___x_8366__boxed_2124_ = lean_unbox(v___x_2119_);
v_res_2125_ = l_Std_Async_Selectable_combine___redArg___lam__3(v___x_2113_, v___x_2114_, v_sz_boxed_2122_, v___x_8363__boxed_2123_, v___x_2117_, v___x_2118_, v___x_8366__boxed_2124_, v___f_2120_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__2(lean_object* v___x_2126_, lean_object* v___x_2127_, size_t v_sz_2128_, size_t v___x_2129_, lean_object* v___x_2130_, lean_object* v___x_2131_, uint8_t v___x_2132_, lean_object* v___f_2133_){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg(v___x_2126_, v___x_2127_, v_sz_2128_, v___x_2129_, v___x_2130_);
v___x_2136_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2131_, v___x_2132_, v___x_2135_, v___f_2133_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__2___boxed(lean_object* v___x_2137_, lean_object* v___x_2138_, lean_object* v_sz_2139_, lean_object* v___x_2140_, lean_object* v___x_2141_, lean_object* v___x_2142_, lean_object* v___x_2143_, lean_object* v___f_2144_, lean_object* v___y_2145_){
_start:
{
size_t v_sz_boxed_2146_; size_t v___x_8391__boxed_2147_; uint8_t v___x_8394__boxed_2148_; lean_object* v_res_2149_; 
v_sz_boxed_2146_ = lean_unbox_usize(v_sz_2139_);
lean_dec(v_sz_2139_);
v___x_8391__boxed_2147_ = lean_unbox_usize(v___x_2140_);
lean_dec(v___x_2140_);
v___x_8394__boxed_2148_ = lean_unbox(v___x_2143_);
v_res_2149_ = l_Std_Async_Selectable_combine___redArg___lam__2(v___x_2137_, v___x_2138_, v_sz_boxed_2146_, v___x_8391__boxed_2147_, v___x_2141_, v___x_2142_, v___x_8394__boxed_2148_, v___f_2144_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg(lean_object* v_selectables_2154_){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; 
v___x_2156_ = lean_array_get_size(v_selectables_2154_);
v___x_2157_ = lean_unsigned_to_nat(0u);
v___x_2158_ = lean_nat_dec_eq(v___x_2156_, v___x_2157_);
if (v___x_2158_ == 0)
{
size_t v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = ((size_t)8ULL);
v___x_2160_ = lean_io_get_random_bytes(v___x_2159_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2188_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2163_ = v___x_2160_;
v_isShared_2164_ = v_isSharedCheck_2188_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2160_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2188_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___f_2165_; uint64_t v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___f_2171_; lean_object* v___x_2172_; lean_object* v___f_2173_; lean_object* v___x_2174_; size_t v_sz_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___f_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___f_2183_; lean_object* v___x_2184_; lean_object* v___x_2186_; 
v___f_2165_ = ((lean_object*)(l_Std_Async_Selectable_tryOne___redArg___closed__0));
v___x_2166_ = l_ByteArray_toUInt64LE_x21(v_a_2161_);
lean_dec(v_a_2161_);
v___x_2167_ = lean_uint64_to_nat(v___x_2166_);
v___x_2168_ = l_mkStdGen(v___x_2167_);
lean_dec(v___x_2167_);
v___x_2169_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(v_selectables_2154_, v___x_2168_);
v___x_2170_ = lean_box(0);
v___f_2171_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___closed__0));
v___x_2172_ = lean_box(v___x_2158_);
lean_inc_ref_n(v___x_2169_, 2);
v___f_2173_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_2173_, 0, v___x_2169_);
lean_closure_set(v___f_2173_, 1, v___x_2156_);
lean_closure_set(v___f_2173_, 2, v___x_2170_);
lean_closure_set(v___f_2173_, 3, v___x_2157_);
lean_closure_set(v___f_2173_, 4, v___x_2172_);
lean_closure_set(v___f_2173_, 5, v___f_2171_);
v___x_2174_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__1));
v_sz_2175_ = lean_array_size(v___x_2169_);
v___x_2176_ = lean_box_usize(v_sz_2175_);
v___x_2177_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___boxed__const__1));
v___x_2178_ = lean_box(v___x_2158_);
v___f_2179_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2179_, 0, v___x_2156_);
lean_closure_set(v___f_2179_, 1, v___x_2169_);
lean_closure_set(v___f_2179_, 2, v___x_2176_);
lean_closure_set(v___f_2179_, 3, v___x_2177_);
lean_closure_set(v___f_2179_, 4, v___x_2170_);
lean_closure_set(v___f_2179_, 5, v___x_2157_);
lean_closure_set(v___f_2179_, 6, v___x_2178_);
lean_closure_set(v___f_2179_, 7, v___f_2171_);
v___x_2180_ = lean_box_usize(v_sz_2175_);
v___x_2181_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___boxed__const__1));
v___x_2182_ = lean_box(v___x_2158_);
v___f_2183_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2183_, 0, v___x_2156_);
lean_closure_set(v___f_2183_, 1, v___x_2169_);
lean_closure_set(v___f_2183_, 2, v___x_2180_);
lean_closure_set(v___f_2183_, 3, v___x_2181_);
lean_closure_set(v___f_2183_, 4, v___x_2174_);
lean_closure_set(v___f_2183_, 5, v___x_2157_);
lean_closure_set(v___f_2183_, 6, v___x_2182_);
lean_closure_set(v___f_2183_, 7, v___f_2165_);
v___x_2184_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2184_, 0, v___f_2183_);
lean_ctor_set(v___x_2184_, 1, v___f_2173_);
lean_ctor_set(v___x_2184_, 2, v___f_2179_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v___x_2184_);
v___x_2186_ = v___x_2163_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec_ref(v_selectables_2154_);
v_a_2189_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2160_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2160_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
lean_dec_ref(v_selectables_2154_);
v___x_2197_ = ((lean_object*)(l_Std_Async_Selectable_one___redArg___closed__1));
v___x_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2197_);
return v___x_2198_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___boxed(lean_object* v_selectables_2199_, lean_object* v_a_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Std_Async_Selectable_combine___redArg(v_selectables_2199_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine(lean_object* v_00_u03b1_2202_, lean_object* v_selectables_2203_){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = l_Std_Async_Selectable_combine___redArg(v_selectables_2203_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___boxed(lean_object* v_00_u03b1_2206_, lean_object* v_selectables_2207_, lean_object* v_a_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_Std_Async_Selectable_combine(v_00_u03b1_2206_, v_selectables_2207_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0(lean_object* v_00_u03b1_2210_, lean_object* v___x_2211_, lean_object* v_as_2212_, size_t v_sz_2213_, size_t v_i_2214_, lean_object* v_b_2215_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg(v___x_2211_, v_as_2212_, v_sz_2213_, v_i_2214_, v_b_2215_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___boxed(lean_object* v_00_u03b1_2218_, lean_object* v___x_2219_, lean_object* v_as_2220_, lean_object* v_sz_2221_, lean_object* v_i_2222_, lean_object* v_b_2223_, lean_object* v___y_2224_){
_start:
{
size_t v_sz_boxed_2225_; size_t v_i_boxed_2226_; lean_object* v_res_2227_; 
v_sz_boxed_2225_ = lean_unbox_usize(v_sz_2221_);
lean_dec(v_sz_2221_);
v_i_boxed_2226_ = lean_unbox_usize(v_i_2222_);
lean_dec(v_i_2222_);
v_res_2227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0(v_00_u03b1_2218_, v___x_2219_, v_as_2220_, v_sz_boxed_2225_, v_i_boxed_2226_, v_b_2223_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1(lean_object* v_00_u03b1_2228_, lean_object* v_waiter_2229_, lean_object* v___x_2230_, lean_object* v___x_2231_, lean_object* v_as_2232_, size_t v_sz_2233_, size_t v_i_2234_, lean_object* v_b_2235_){
_start:
{
lean_object* v___x_2237_; 
v___x_2237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg(v_waiter_2229_, v___x_2230_, v___x_2231_, v_as_2232_, v_sz_2233_, v_i_2234_, v_b_2235_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___boxed(lean_object* v_00_u03b1_2238_, lean_object* v_waiter_2239_, lean_object* v___x_2240_, lean_object* v___x_2241_, lean_object* v_as_2242_, lean_object* v_sz_2243_, lean_object* v_i_2244_, lean_object* v_b_2245_, lean_object* v___y_2246_){
_start:
{
size_t v_sz_boxed_2247_; size_t v_i_boxed_2248_; lean_object* v_res_2249_; 
v_sz_boxed_2247_ = lean_unbox_usize(v_sz_2243_);
lean_dec(v_sz_2243_);
v_i_boxed_2248_ = lean_unbox_usize(v_i_2244_);
lean_dec(v_i_2244_);
v_res_2249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1(v_00_u03b1_2238_, v_waiter_2239_, v___x_2240_, v___x_2241_, v_as_2242_, v_sz_boxed_2247_, v_i_boxed_2248_, v_b_2245_);
return v_res_2249_;
}
}
lean_object* runtime_initialize_Init_Data_Random(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray_Extra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Async_Select(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Random(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_Basic(builtin);
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
LEAN_EXPORT lean_object* meta_initialize_Std_Async_Select(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Random(uint8_t builtin);
lean_object* initialize_Std_Async_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_ByteArray_Extra(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Async_Select(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Random(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Async_Basic(builtin);
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
res = runtime_initialize_Std_Async_Select(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Async_Select(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Async_Select(builtin);
}
#ifdef __cplusplus
}
#endif
