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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
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
uint64_t l_ByteArray_toUInt64LE_x21(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_mkStdGen(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* lean_io_promise_new();
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_io_get_random_bytes(size_t);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Async_Selectable_one___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "the promise linked to the Async was dropped"};
static const lean_object* l_Std_Async_Selectable_one___redArg___lam__2___closed__0 = (const lean_object*)&l_Std_Async_Selectable_one___redArg___lam__2___closed__0_value;
static const lean_closure_object l_Std_Async_Selectable_one___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Selectable_one___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_Selectable_one___redArg___lam__2___closed__0_value)} };
static const lean_object* l_Std_Async_Selectable_one___redArg___lam__2___closed__1 = (const lean_object*)&l_Std_Async_Selectable_one___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__2(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0(size_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__0(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg___lam__1(size_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__9(size_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__5(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__7(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Selectable_combine___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Selectable_combine___redArg___lam__6___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Async_Selectable_combine___redArg___closed__0 = (const lean_object*)&l_Std_Async_Selectable_combine___redArg___closed__0_value;
static const lean_ctor_object l_Std_Async_Selectable_combine___redArg___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Std_Async_Selectable_combine___redArg___boxed__const__1 = (const lean_object*)&l_Std_Async_Selectable_combine___redArg___boxed__const__1_value;
static const lean_ctor_object l_Std_Async_Selectable_combine___redArg___boxed__const__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(8ULL)}};
LEAN_EXPORT const lean_object* l_Std_Async_Selectable_combine___redArg___boxed__const__2 = (const lean_object*)&l_Std_Async_Selectable_combine___redArg___boxed__const__2_value;
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__1(lean_object* v___f_233_, uint8_t v___x_234_, lean_object* v_x_235_){
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
lean_dec_ref_known(v_x_235_, 1);
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
lean_dec_ref_known(v_a_246_, 1);
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
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__1___boxed(lean_object* v___f_261_, lean_object* v___x_262_, lean_object* v_x_263_, lean_object* v___y_264_){
_start:
{
uint8_t v___x_10621__boxed_265_; lean_object* v_res_266_; 
v___x_10621__boxed_265_ = lean_unbox(v___x_262_);
v_res_266_ = l_Std_Async_Selectable_one___redArg___lam__1(v___f_261_, v___x_10621__boxed_265_, v_x_263_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__2(uint8_t v___x_270_, lean_object* v_x_271_, lean_object* v_x_272_){
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
v___f_286_ = ((lean_object*)(l_Std_Async_Selectable_one___redArg___lam__2___closed__1));
v___x_287_ = lean_box(v___x_270_);
v___f_288_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__1___boxed), 4, 2);
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
v___x_293_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_292_, v___x_270_, v___x_291_, v___f_288_);
return v___x_293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__2___boxed(lean_object* v___x_297_, lean_object* v_x_298_, lean_object* v_x_299_, lean_object* v___y_300_){
_start:
{
uint8_t v___x_10686__boxed_301_; lean_object* v_res_302_; 
v___x_10686__boxed_301_ = lean_unbox(v___x_297_);
v_res_302_ = l_Std_Async_Selectable_one___redArg___lam__2(v___x_10686__boxed_301_, v_x_298_, v_x_299_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__3(lean_object* v___x_303_, lean_object* v_a_304_, uint8_t v___x_305_, lean_object* v___f_306_, lean_object* v_x_307_){
_start:
{
if (lean_obj_tag(v_x_307_) == 0)
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_317_; 
lean_dec_ref(v___f_306_);
v_a_309_ = lean_ctor_get(v_x_307_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v_x_307_);
if (v_isSharedCheck_317_ == 0)
{
v___x_311_ = v_x_307_;
v_isShared_312_ = v_isSharedCheck_317_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v_x_307_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_317_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_316_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v___x_315_; 
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
}
}
else
{
lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_328_; 
v_isSharedCheck_328_ = !lean_is_exclusive(v_x_307_);
if (v_isSharedCheck_328_ == 0)
{
lean_object* v_unused_329_; 
v_unused_329_ = lean_ctor_get(v_x_307_, 0);
lean_dec(v_unused_329_);
v___x_319_ = v_x_307_;
v_isShared_320_ = v_isSharedCheck_328_;
goto v_resetjp_318_;
}
else
{
lean_dec(v_x_307_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_328_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_321_ = lean_io_promise_resolve(v___x_303_, v_a_304_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_321_);
v___x_323_ = v___x_319_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_321_);
v___x_323_ = v_reuseFailAlloc_327_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
v___x_325_ = lean_unsigned_to_nat(0u);
v___x_326_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_325_, v___x_305_, v___x_324_, v___f_306_);
return v___x_326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__3___boxed(lean_object* v___x_330_, lean_object* v_a_331_, lean_object* v___x_332_, lean_object* v___f_333_, lean_object* v_x_334_, lean_object* v___y_335_){
_start:
{
uint8_t v___x_10750__boxed_336_; lean_object* v_res_337_; 
v___x_10750__boxed_336_ = lean_unbox(v___x_332_);
v_res_337_ = l_Std_Async_Selectable_one___redArg___lam__3(v___x_330_, v_a_331_, v___x_10750__boxed_336_, v___f_333_, v_x_334_);
lean_dec(v_a_331_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__4(lean_object* v___x_338_, lean_object* v___y_339_){
_start:
{
if (lean_obj_tag(v___y_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
v_a_340_ = lean_ctor_get(v___y_339_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___y_339_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___y_339_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___y_339_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
else
{
lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
v_isSharedCheck_354_ = !lean_is_exclusive(v___y_339_);
if (v_isSharedCheck_354_ == 0)
{
lean_object* v_unused_355_; 
v_unused_355_ = lean_ctor_get(v___y_339_, 0);
lean_dec(v_unused_355_);
v___x_349_ = v___y_339_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_dec(v___y_339_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v___x_338_);
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_338_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__2(lean_object* v_a_356_, lean_object* v_x_357_){
_start:
{
if (lean_obj_tag(v_x_357_) == 0)
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_369_; 
v_a_359_ = lean_ctor_get(v_x_357_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v_x_357_);
if (v_isSharedCheck_369_ == 0)
{
v___x_361_ = v_x_357_;
v_isShared_362_ = v_isSharedCheck_369_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v_x_357_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_369_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_368_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_365_ = lean_io_promise_resolve(v___x_364_, v_a_356_);
v___x_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
v___x_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
return v___x_367_;
}
}
}
else
{
lean_object* v___x_370_; 
v___x_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_370_, 0, v_x_357_);
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__2___boxed(lean_object* v_a_371_, lean_object* v_x_372_, lean_object* v___y_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__2(v_a_371_, v_x_372_);
lean_dec(v_a_371_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__1(lean_object* v_a_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_376_, 0, v_a_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__0(lean_object* v_a_377_, lean_object* v_x_378_){
_start:
{
if (lean_obj_tag(v_x_378_) == 0)
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_388_; 
v_a_380_ = lean_ctor_get(v_x_378_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v_x_378_);
if (v_isSharedCheck_388_ == 0)
{
v___x_382_ = v_x_378_;
v_isShared_383_ = v_isSharedCheck_388_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v_x_378_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_388_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_380_);
v___x_385_ = v_reuseFailAlloc_387_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v___x_386_; 
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
}
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_389_ = lean_io_promise_resolve(v_x_378_, v_a_377_);
v___x_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__0___boxed(lean_object* v_a_392_, lean_object* v_x_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__0(v_a_392_, v_x_393_);
lean_dec(v_a_392_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__8(lean_object* v_a_396_, lean_object* v___f_397_, uint8_t v___x_398_, lean_object* v___x_399_, uint8_t v_a_400_, lean_object* v___f_401_, lean_object* v_x_402_){
_start:
{
if (lean_obj_tag(v_x_402_) == 0)
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_412_; 
lean_dec_ref(v___f_401_);
lean_dec_ref(v___f_397_);
v_a_404_ = lean_ctor_get(v_x_402_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v_x_402_);
if (v_isSharedCheck_412_ == 0)
{
v___x_406_ = v_x_402_;
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v_x_402_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_404_);
v___x_409_ = v_reuseFailAlloc_411_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v___x_410_; 
v___x_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
return v___x_410_;
}
}
}
else
{
lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_424_; 
v_isSharedCheck_424_ = !lean_is_exclusive(v_x_402_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; 
v_unused_425_ = lean_ctor_get(v_x_402_, 0);
lean_dec(v_unused_425_);
v___x_414_ = v_x_402_;
v_isShared_415_ = v_isSharedCheck_424_;
goto v_resetjp_413_;
}
else
{
lean_dec(v_x_402_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_424_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_416_ = lean_io_promise_result_opt(v_a_396_);
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = lean_io_bind_task(v___x_416_, v___f_397_, v___x_417_, v___x_398_);
lean_dec_ref(v___x_418_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_399_);
v___x_420_ = v___x_414_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_399_);
v___x_420_ = v_reuseFailAlloc_423_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
v___x_422_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_417_, v_a_400_, v___x_421_, v___f_401_);
return v___x_422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__8___boxed(lean_object* v_a_426_, lean_object* v___f_427_, lean_object* v___x_428_, lean_object* v___x_429_, lean_object* v_a_430_, lean_object* v___f_431_, lean_object* v_x_432_, lean_object* v___y_433_){
_start:
{
uint8_t v___x_10920__boxed_434_; uint8_t v_a_10922__boxed_435_; lean_object* v_res_436_; 
v___x_10920__boxed_434_ = lean_unbox(v___x_428_);
v_a_10922__boxed_435_ = lean_unbox(v_a_430_);
v_res_436_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__8(v_a_426_, v___f_427_, v___x_10920__boxed_434_, v___x_429_, v_a_10922__boxed_435_, v___f_431_, v_x_432_);
lean_dec(v_a_426_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__9(lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v___f_439_, uint8_t v___x_440_, lean_object* v___x_441_, uint8_t v_a_442_, lean_object* v___f_443_, lean_object* v_x_444_){
_start:
{
if (lean_obj_tag(v_x_444_) == 0)
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_454_; 
lean_dec_ref(v___f_443_);
lean_dec_ref(v___f_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
v_a_446_ = lean_ctor_get(v_x_444_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v_x_444_);
if (v_isSharedCheck_454_ == 0)
{
v___x_448_ = v_x_444_;
v_isShared_449_ = v_isSharedCheck_454_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v_x_444_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_454_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_453_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_452_; 
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
return v___x_452_;
}
}
}
else
{
lean_object* v_selector_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_470_; 
v_selector_455_ = lean_ctor_get(v_a_437_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v_a_437_);
if (v_isSharedCheck_470_ == 0)
{
lean_object* v_unused_471_; 
v_unused_471_ = lean_ctor_get(v_a_437_, 1);
lean_dec(v_unused_471_);
v___x_457_ = v_a_437_;
v_isShared_458_ = v_isSharedCheck_470_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_selector_455_);
lean_dec(v_a_437_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_470_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v_a_459_; lean_object* v_registerFn_460_; lean_object* v___x_462_; 
v_a_459_ = lean_ctor_get(v_x_444_, 0);
lean_inc_n(v_a_459_, 2);
lean_dec_ref_known(v_x_444_, 1);
v_registerFn_460_ = lean_ctor_get(v_selector_455_, 1);
lean_inc_ref(v_registerFn_460_);
lean_dec_ref(v_selector_455_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 1, v_a_459_);
lean_ctor_set(v___x_457_, 0, v_a_438_);
v___x_462_ = v___x_457_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_438_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_a_459_);
v___x_462_ = v_reuseFailAlloc_469_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___f_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_463_ = lean_apply_2(v_registerFn_460_, v___x_462_, lean_box(0));
v___x_464_ = lean_box(v___x_440_);
v___x_465_ = lean_box(v_a_442_);
v___f_466_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__8___boxed), 8, 6);
lean_closure_set(v___f_466_, 0, v_a_459_);
lean_closure_set(v___f_466_, 1, v___f_439_);
lean_closure_set(v___f_466_, 2, v___x_464_);
lean_closure_set(v___f_466_, 3, v___x_441_);
lean_closure_set(v___f_466_, 4, v___x_465_);
lean_closure_set(v___f_466_, 5, v___f_443_);
v___x_467_ = lean_unsigned_to_nat(0u);
v___x_468_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_467_, v_a_442_, v___x_463_, v___f_466_);
return v___x_468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__9___boxed(lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v___f_474_, lean_object* v___x_475_, lean_object* v___x_476_, lean_object* v_a_477_, lean_object* v___f_478_, lean_object* v_x_479_, lean_object* v___y_480_){
_start:
{
uint8_t v___x_10989__boxed_481_; uint8_t v_a_10991__boxed_482_; lean_object* v_res_483_; 
v___x_10989__boxed_481_ = lean_unbox(v___x_475_);
v_a_10991__boxed_482_ = lean_unbox(v_a_477_);
v_res_483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__9(v_a_472_, v_a_473_, v___f_474_, v___x_10989__boxed_481_, v___x_476_, v_a_10991__boxed_482_, v___f_478_, v_x_479_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__3(lean_object* v_a_484_, lean_object* v_a_485_, uint8_t v_a_486_, lean_object* v___f_487_, lean_object* v_x_488_){
_start:
{
if (lean_obj_tag(v_x_488_) == 0)
{
lean_object* v___x_490_; 
lean_dec_ref(v___f_487_);
lean_dec(v_a_485_);
lean_dec_ref(v_a_484_);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v_x_488_);
return v___x_490_;
}
else
{
lean_object* v_cont_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
lean_dec_ref_known(v_x_488_, 1);
v_cont_491_ = lean_ctor_get(v_a_484_, 1);
lean_inc_ref(v_cont_491_);
lean_dec_ref(v_a_484_);
v___x_492_ = lean_apply_2(v_cont_491_, v_a_485_, lean_box(0));
v___x_493_ = lean_unsigned_to_nat(0u);
v___x_494_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_493_, v_a_486_, v___x_492_, v___f_487_);
return v___x_494_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__3___boxed(lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v___f_498_, lean_object* v_x_499_, lean_object* v___y_500_){
_start:
{
uint8_t v_a_11060__boxed_501_; lean_object* v_res_502_; 
v_a_11060__boxed_501_ = lean_unbox(v_a_497_);
v_res_502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__3(v_a_495_, v_a_496_, v_a_11060__boxed_501_, v___f_498_, v_x_499_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__0(lean_object* v___x_503_, lean_object* v_x_504_){
_start:
{
if (lean_obj_tag(v_x_504_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_514_; 
v_a_506_ = lean_ctor_get(v_x_504_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v_x_504_);
if (v_isSharedCheck_514_ == 0)
{
v___x_508_ = v_x_504_;
v_isShared_509_ = v_isSharedCheck_514_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v_x_504_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_514_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_506_);
v___x_511_ = v_reuseFailAlloc_513_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_512_; 
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
return v___x_512_;
}
}
}
else
{
lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_523_; 
v_isSharedCheck_523_ = !lean_is_exclusive(v_x_504_);
if (v_isSharedCheck_523_ == 0)
{
lean_object* v_unused_524_; 
v_unused_524_ = lean_ctor_get(v_x_504_, 0);
lean_dec(v_unused_524_);
v___x_516_ = v_x_504_;
v_isShared_517_ = v_isSharedCheck_523_;
goto v_resetjp_515_;
}
else
{
lean_dec(v_x_504_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_523_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_503_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_518_);
v___x_520_ = v___x_516_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_518_);
v___x_520_ = v_reuseFailAlloc_522_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_521_; 
v___x_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
return v___x_521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__0___boxed(lean_object* v___x_525_, lean_object* v_x_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__0(v___x_525_, v_x_526_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__1___boxed(lean_object* v_i_531_, lean_object* v_a_532_, lean_object* v_as_533_, lean_object* v_sz_534_, lean_object* v_x_535_, lean_object* v___y_536_){
_start:
{
size_t v_i_boxed_537_; uint8_t v_a_11133__boxed_538_; size_t v_sz_boxed_539_; lean_object* v_res_540_; 
v_i_boxed_537_ = lean_unbox_usize(v_i_531_);
lean_dec(v_i_531_);
v_a_11133__boxed_538_ = lean_unbox(v_a_532_);
v_sz_boxed_539_ = lean_unbox_usize(v_sz_534_);
lean_dec(v_sz_534_);
v_res_540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__1(v_i_boxed_537_, v_a_11133__boxed_538_, v_as_533_, v_sz_boxed_539_, v_x_535_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg(uint8_t v_a_541_, lean_object* v_as_542_, size_t v_sz_543_, size_t v_i_544_, lean_object* v_b_545_){
_start:
{
uint8_t v___x_547_; 
v___x_547_ = lean_usize_dec_lt(v_i_544_, v_sz_543_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec_ref(v_as_542_);
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v_b_545_);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
else
{
lean_object* v_a_550_; lean_object* v_selector_551_; lean_object* v_unregisterFn_552_; lean_object* v___x_553_; lean_object* v___f_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___f_560_; uint8_t v___x_561_; lean_object* v___x_562_; 
v_a_550_ = lean_array_uget_borrowed(v_as_542_, v_i_544_);
v_selector_551_ = lean_ctor_get(v_a_550_, 0);
v_unregisterFn_552_ = lean_ctor_get(v_selector_551_, 2);
lean_inc_ref(v_unregisterFn_552_);
v___x_553_ = lean_apply_1(v_unregisterFn_552_, lean_box(0));
v___f_554_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___closed__0));
v___x_555_ = lean_unsigned_to_nat(0u);
v___x_556_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_555_, v_a_541_, v___x_553_, v___f_554_);
v___x_557_ = lean_box_usize(v_i_544_);
v___x_558_ = lean_box(v_a_541_);
v___x_559_ = lean_box_usize(v_sz_543_);
v___f_560_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__1___boxed), 6, 4);
lean_closure_set(v___f_560_, 0, v___x_557_);
lean_closure_set(v___f_560_, 1, v___x_558_);
lean_closure_set(v___f_560_, 2, v_as_542_);
lean_closure_set(v___f_560_, 3, v___x_559_);
v___x_561_ = 0;
v___x_562_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_555_, v___x_561_, v___x_556_, v___f_560_);
return v___x_562_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__1(size_t v_i_563_, uint8_t v_a_564_, lean_object* v_as_565_, size_t v_sz_566_, lean_object* v_x_567_){
_start:
{
if (lean_obj_tag(v_x_567_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_577_; 
lean_dec_ref(v_as_565_);
v_a_569_ = lean_ctor_get(v_x_567_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v_x_567_);
if (v_isSharedCheck_577_ == 0)
{
v___x_571_ = v_x_567_;
v_isShared_572_ = v_isSharedCheck_577_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v_x_567_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_577_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_569_);
v___x_574_ = v_reuseFailAlloc_576_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_575_; 
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_597_; 
v_a_578_ = lean_ctor_get(v_x_567_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v_x_567_);
if (v_isSharedCheck_597_ == 0)
{
v___x_580_ = v_x_567_;
v_isShared_581_ = v_isSharedCheck_597_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v_x_567_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_597_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
if (lean_obj_tag(v_a_578_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_592_; 
lean_dec_ref(v_as_565_);
v_a_582_ = lean_ctor_get(v_a_578_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v_a_578_);
if (v_isSharedCheck_592_ == 0)
{
v___x_584_ = v_a_578_;
v_isShared_585_ = v_isSharedCheck_592_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v_a_578_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_592_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v_a_582_);
v___x_587_ = v___x_580_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_591_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_589_; 
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_587_);
v___x_589_ = v___x_584_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
else
{
lean_object* v_a_593_; size_t v___x_594_; size_t v___x_595_; lean_object* v___x_596_; 
lean_del_object(v___x_580_);
v_a_593_ = lean_ctor_get(v_a_578_, 0);
lean_inc(v_a_593_);
lean_dec_ref_known(v_a_578_, 1);
v___x_594_ = ((size_t)1ULL);
v___x_595_ = lean_usize_add(v_i_563_, v___x_594_);
v___x_596_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg(v_a_564_, v_as_565_, v_sz_566_, v___x_595_, v_a_593_);
return v___x_596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___boxed(lean_object* v_a_598_, lean_object* v_as_599_, lean_object* v_sz_600_, lean_object* v_i_601_, lean_object* v_b_602_, lean_object* v___y_603_){
_start:
{
uint8_t v_a_11149__boxed_604_; size_t v_sz_boxed_605_; size_t v_i_boxed_606_; lean_object* v_res_607_; 
v_a_11149__boxed_604_ = lean_unbox(v_a_598_);
v_sz_boxed_605_ = lean_unbox_usize(v_sz_600_);
lean_dec(v_sz_600_);
v_i_boxed_606_ = lean_unbox_usize(v_i_601_);
lean_dec(v_i_601_);
v_res_607_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg(v_a_11149__boxed_604_, v_as_599_, v_sz_boxed_605_, v_i_boxed_606_, v_b_602_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__5(lean_object* v___x_608_, uint8_t v_a_609_, lean_object* v___x_610_, lean_object* v___f_611_, lean_object* v_x_612_){
_start:
{
if (lean_obj_tag(v_x_612_) == 0)
{
lean_object* v___x_614_; 
lean_dec_ref(v___f_611_);
lean_dec_ref(v___x_608_);
v___x_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_614_, 0, v_x_612_);
return v___x_614_;
}
else
{
size_t v_sz_615_; size_t v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
lean_dec_ref_known(v_x_612_, 1);
v_sz_615_ = lean_array_size(v___x_608_);
v___x_616_ = ((size_t)0ULL);
v___x_617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg(v_a_609_, v___x_608_, v_sz_615_, v___x_616_, v___x_610_);
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_618_, v_a_609_, v___x_617_, v___f_611_);
return v___x_619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__5___boxed(lean_object* v___x_620_, lean_object* v_a_621_, lean_object* v___x_622_, lean_object* v___f_623_, lean_object* v_x_624_, lean_object* v___y_625_){
_start:
{
uint8_t v_a_11237__boxed_626_; lean_object* v_res_627_; 
v_a_11237__boxed_626_ = lean_unbox(v_a_621_);
v_res_627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__5(v___x_620_, v_a_11237__boxed_626_, v___x_622_, v___f_623_, v_x_624_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__6(lean_object* v_a_628_, uint8_t v_a_629_, lean_object* v___f_630_, lean_object* v___x_631_, lean_object* v___x_632_, lean_object* v_a_633_, lean_object* v___f_634_, lean_object* v___f_635_, lean_object* v_x_636_){
_start:
{
if (lean_obj_tag(v_x_636_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_646_; 
lean_dec_ref(v___f_635_);
lean_dec_ref(v___f_634_);
lean_dec_ref(v___x_631_);
lean_dec_ref(v___f_630_);
lean_dec_ref(v_a_628_);
v_a_638_ = lean_ctor_get(v_x_636_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v_x_636_);
if (v_isSharedCheck_646_ == 0)
{
v___x_640_ = v_x_636_;
v_isShared_641_ = v_isSharedCheck_646_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v_x_636_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_646_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_638_);
v___x_643_ = v_reuseFailAlloc_645_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_644_; 
v___x_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_648_; lean_object* v___f_649_; lean_object* v___x_650_; lean_object* v___f_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v_a_647_ = lean_ctor_get(v_x_636_, 0);
lean_inc(v_a_647_);
lean_dec_ref_known(v_x_636_, 1);
v___x_648_ = lean_box(v_a_629_);
v___f_649_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_649_, 0, v_a_628_);
lean_closure_set(v___f_649_, 1, v_a_647_);
lean_closure_set(v___f_649_, 2, v___x_648_);
lean_closure_set(v___f_649_, 3, v___f_630_);
v___x_650_ = lean_box(v_a_629_);
v___f_651_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__5___boxed), 6, 4);
lean_closure_set(v___f_651_, 0, v___x_631_);
lean_closure_set(v___f_651_, 1, v___x_650_);
lean_closure_set(v___f_651_, 2, v___x_632_);
lean_closure_set(v___f_651_, 3, v___f_649_);
v___x_652_ = lean_io_promise_result_opt(v_a_633_);
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = lean_task_map(v___f_634_, v___x_652_, v___x_653_, v_a_629_);
v___x_655_ = lean_task_map(v___f_635_, v___x_654_, v___x_653_, v_a_629_);
v___x_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
v___x_657_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_653_, v_a_629_, v___x_656_, v___f_651_);
return v___x_657_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__6___boxed(lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v___f_660_, lean_object* v___x_661_, lean_object* v___x_662_, lean_object* v_a_663_, lean_object* v___f_664_, lean_object* v___f_665_, lean_object* v_x_666_, lean_object* v___y_667_){
_start:
{
uint8_t v_a_11266__boxed_668_; lean_object* v_res_669_; 
v_a_11266__boxed_668_ = lean_unbox(v_a_659_);
v_res_669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__6(v_a_658_, v_a_11266__boxed_668_, v___f_660_, v___x_661_, v___x_662_, v_a_663_, v___f_664_, v___f_665_, v_x_666_);
lean_dec(v_a_663_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__7(lean_object* v___x_670_, uint8_t v_a_671_, lean_object* v___f_672_, lean_object* v___f_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_val_677_; 
if (lean_obj_tag(v_a_674_) == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; 
lean_dec_ref(v___f_673_);
lean_dec_ref(v___f_672_);
v___x_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_685_, 0, v___x_670_);
v___x_686_ = lean_task_pure(v___x_685_);
return v___x_686_;
}
else
{
lean_object* v_val_687_; lean_object* v___x_688_; 
v_val_687_ = lean_ctor_get(v_a_674_, 0);
lean_inc(v_val_687_);
lean_dec_ref_known(v_a_674_, 1);
v___x_688_ = l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___redArg(v_val_687_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_688_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set_tag(v___x_691_, 1);
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
v_val_677_ = v___x_694_;
goto v___jp_676_;
}
}
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
v_a_697_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_688_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_688_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
lean_ctor_set_tag(v___x_699_, 0);
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
v_val_677_ = v___x_702_;
goto v___jp_676_;
}
}
}
}
v___jp_676_:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v_val_677_);
v___x_679_ = lean_unsigned_to_nat(0u);
v___x_680_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_679_, v_a_671_, v___x_678_, v___f_672_);
v___x_681_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_679_, v_a_671_, v___x_680_, v___f_673_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v___x_683_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_a_682_);
lean_dec_ref_known(v___x_681_, 1);
v___x_683_ = lean_task_pure(v_a_682_);
return v___x_683_;
}
else
{
lean_object* v_a_684_; 
v_a_684_ = lean_ctor_get(v___x_681_, 0);
lean_inc_ref(v_a_684_);
lean_dec_ref_known(v___x_681_, 1);
return v_a_684_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__7___boxed(lean_object* v___x_705_, lean_object* v_a_706_, lean_object* v___f_707_, lean_object* v___f_708_, lean_object* v_a_709_, lean_object* v___y_710_){
_start:
{
uint8_t v_a_11334__boxed_711_; lean_object* v_res_712_; 
v_a_11334__boxed_711_ = lean_unbox(v_a_706_);
v_res_712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__7(v___x_705_, v_a_11334__boxed_711_, v___f_707_, v___f_708_, v_a_709_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__10(lean_object* v_a_713_, lean_object* v___f_714_, lean_object* v___x_715_, lean_object* v___x_716_, lean_object* v_a_717_, lean_object* v___f_718_, lean_object* v___f_719_, lean_object* v___f_720_, lean_object* v_a_721_, uint8_t v___x_722_, lean_object* v___f_723_, lean_object* v_x_724_){
_start:
{
if (lean_obj_tag(v_x_724_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_734_; 
lean_dec_ref(v___f_723_);
lean_dec(v_a_721_);
lean_dec_ref(v___f_720_);
lean_dec_ref(v___f_719_);
lean_dec_ref(v___f_718_);
lean_dec(v_a_717_);
lean_dec_ref(v___x_715_);
lean_dec_ref(v___f_714_);
lean_dec_ref(v_a_713_);
v_a_726_ = lean_ctor_get(v_x_724_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v_x_724_);
if (v_isSharedCheck_734_ == 0)
{
v___x_728_ = v_x_724_;
v_isShared_729_ = v_isSharedCheck_734_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v_x_724_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_734_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_733_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v___x_732_; 
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
return v___x_732_;
}
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_757_; 
v_a_735_ = lean_ctor_get(v_x_724_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v_x_724_);
if (v_isSharedCheck_757_ == 0)
{
v___x_737_ = v_x_724_;
v_isShared_738_ = v_isSharedCheck_757_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v_x_724_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_757_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
uint8_t v___x_739_; 
v___x_739_ = lean_unbox(v_a_735_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___f_741_; lean_object* v___f_742_; lean_object* v___x_743_; lean_object* v___f_744_; lean_object* v___x_746_; 
v___x_740_ = lean_io_promise_new();
lean_inc_n(v_a_735_, 3);
lean_inc_ref(v_a_713_);
v___f_741_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__6___boxed), 10, 8);
lean_closure_set(v___f_741_, 0, v_a_713_);
lean_closure_set(v___f_741_, 1, v_a_735_);
lean_closure_set(v___f_741_, 2, v___f_714_);
lean_closure_set(v___f_741_, 3, v___x_715_);
lean_closure_set(v___f_741_, 4, v___x_716_);
lean_closure_set(v___f_741_, 5, v_a_717_);
lean_closure_set(v___f_741_, 6, v___f_718_);
lean_closure_set(v___f_741_, 7, v___f_719_);
v___f_742_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_742_, 0, v___x_716_);
lean_closure_set(v___f_742_, 1, v_a_735_);
lean_closure_set(v___f_742_, 2, v___f_741_);
lean_closure_set(v___f_742_, 3, v___f_720_);
v___x_743_ = lean_box(v___x_722_);
v___f_744_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__9___boxed), 9, 7);
lean_closure_set(v___f_744_, 0, v_a_713_);
lean_closure_set(v___f_744_, 1, v_a_721_);
lean_closure_set(v___f_744_, 2, v___f_742_);
lean_closure_set(v___f_744_, 3, v___x_743_);
lean_closure_set(v___f_744_, 4, v___x_716_);
lean_closure_set(v___f_744_, 5, v_a_735_);
lean_closure_set(v___f_744_, 6, v___f_723_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_740_);
v___x_746_ = v___x_737_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_740_);
v___x_746_ = v_reuseFailAlloc_751_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; lean_object* v___x_750_; 
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
v___x_748_ = lean_unsigned_to_nat(0u);
v___x_749_ = lean_unbox(v_a_735_);
lean_dec(v_a_735_);
v___x_750_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_748_, v___x_749_, v___x_747_, v___f_744_);
return v___x_750_;
}
}
else
{
lean_object* v___x_752_; lean_object* v___x_754_; 
lean_dec(v_a_735_);
lean_dec_ref(v___f_723_);
lean_dec(v_a_721_);
lean_dec_ref(v___f_720_);
lean_dec_ref(v___f_719_);
lean_dec_ref(v___f_718_);
lean_dec(v_a_717_);
lean_dec_ref(v___x_715_);
lean_dec_ref(v___f_714_);
lean_dec_ref(v_a_713_);
v___x_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_716_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_752_);
v___x_754_ = v___x_737_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_756_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_755_; 
v___x_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
return v___x_755_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__10___boxed(lean_object* v_a_758_, lean_object* v___f_759_, lean_object* v___x_760_, lean_object* v___x_761_, lean_object* v_a_762_, lean_object* v___f_763_, lean_object* v___f_764_, lean_object* v___f_765_, lean_object* v_a_766_, lean_object* v___x_767_, lean_object* v___f_768_, lean_object* v_x_769_, lean_object* v___y_770_){
_start:
{
uint8_t v___x_11414__boxed_771_; lean_object* v_res_772_; 
v___x_11414__boxed_771_ = lean_unbox(v___x_767_);
v_res_772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__10(v_a_758_, v___f_759_, v___x_760_, v___x_761_, v_a_762_, v___f_763_, v___f_764_, v___f_765_, v_a_766_, v___x_11414__boxed_771_, v___f_768_, v_x_769_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__11___boxed(lean_object* v_i_776_, lean_object* v_a_777_, lean_object* v___x_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_as_781_, lean_object* v_sz_782_, lean_object* v_x_783_, lean_object* v___y_784_){
_start:
{
size_t v_i_boxed_785_; size_t v_sz_boxed_786_; lean_object* v_res_787_; 
v_i_boxed_785_ = lean_unbox_usize(v_i_776_);
lean_dec(v_i_776_);
v_sz_boxed_786_ = lean_unbox_usize(v_sz_782_);
lean_dec(v_sz_782_);
v_res_787_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__11(v_i_boxed_785_, v_a_777_, v___x_778_, v_a_779_, v_a_780_, v_as_781_, v_sz_boxed_786_, v_x_783_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg(lean_object* v_a_788_, lean_object* v___x_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_as_792_, size_t v_sz_793_, size_t v_i_794_, lean_object* v_b_795_){
_start:
{
uint8_t v___x_797_; 
v___x_797_ = lean_usize_dec_lt(v_i_794_, v_sz_793_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec_ref(v_as_792_);
lean_dec(v_a_791_);
lean_dec(v_a_790_);
lean_dec_ref(v___x_789_);
lean_dec(v_a_788_);
v___x_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_798_, 0, v_b_795_);
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
return v___x_799_;
}
else
{
lean_object* v___x_800_; lean_object* v___f_801_; lean_object* v___f_802_; lean_object* v___f_803_; lean_object* v___x_804_; lean_object* v___f_805_; lean_object* v___f_806_; uint8_t v___x_807_; lean_object* v_a_808_; lean_object* v___x_809_; lean_object* v___f_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___f_817_; lean_object* v___x_818_; 
v___x_800_ = lean_st_ref_get(v_a_791_);
lean_inc_n(v_a_788_, 2);
v___f_801_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_801_, 0, v_a_788_);
v___f_802_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___closed__0));
v___f_803_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_803_, 0, v_a_788_);
v___x_804_ = lean_box(0);
v___f_805_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___closed__0));
v___f_806_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___closed__1));
v___x_807_ = 0;
v_a_808_ = lean_array_uget_borrowed(v_as_792_, v_i_794_);
v___x_809_ = lean_box(v___x_807_);
lean_inc(v_a_791_);
lean_inc(v_a_790_);
lean_inc_ref(v___x_789_);
lean_inc(v_a_808_);
v___f_810_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__10___boxed), 13, 11);
lean_closure_set(v___f_810_, 0, v_a_808_);
lean_closure_set(v___f_810_, 1, v___f_801_);
lean_closure_set(v___f_810_, 2, v___x_789_);
lean_closure_set(v___f_810_, 3, v___x_804_);
lean_closure_set(v___f_810_, 4, v_a_790_);
lean_closure_set(v___f_810_, 5, v___f_802_);
lean_closure_set(v___f_810_, 6, v___f_806_);
lean_closure_set(v___f_810_, 7, v___f_803_);
lean_closure_set(v___f_810_, 8, v_a_791_);
lean_closure_set(v___f_810_, 9, v___x_809_);
lean_closure_set(v___f_810_, 10, v___f_805_);
v___x_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_800_);
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
v___x_813_ = lean_unsigned_to_nat(0u);
v___x_814_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_813_, v___x_807_, v___x_812_, v___f_810_);
v___x_815_ = lean_box_usize(v_i_794_);
v___x_816_ = lean_box_usize(v_sz_793_);
v___f_817_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__11___boxed), 9, 7);
lean_closure_set(v___f_817_, 0, v___x_815_);
lean_closure_set(v___f_817_, 1, v_a_788_);
lean_closure_set(v___f_817_, 2, v___x_789_);
lean_closure_set(v___f_817_, 3, v_a_790_);
lean_closure_set(v___f_817_, 4, v_a_791_);
lean_closure_set(v___f_817_, 5, v_as_792_);
lean_closure_set(v___f_817_, 6, v___x_816_);
v___x_818_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_813_, v___x_807_, v___x_814_, v___f_817_);
return v___x_818_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__11(size_t v_i_819_, lean_object* v_a_820_, lean_object* v___x_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_as_824_, size_t v_sz_825_, lean_object* v_x_826_){
_start:
{
if (lean_obj_tag(v_x_826_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_836_; 
lean_dec_ref(v_as_824_);
lean_dec(v_a_823_);
lean_dec(v_a_822_);
lean_dec_ref(v___x_821_);
lean_dec(v_a_820_);
v_a_828_ = lean_ctor_get(v_x_826_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v_x_826_);
if (v_isSharedCheck_836_ == 0)
{
v___x_830_ = v_x_826_;
v_isShared_831_ = v_isSharedCheck_836_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v_x_826_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_836_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_835_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_834_; 
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
return v___x_834_;
}
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_856_; 
v_a_837_ = lean_ctor_get(v_x_826_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v_x_826_);
if (v_isSharedCheck_856_ == 0)
{
v___x_839_ = v_x_826_;
v_isShared_840_ = v_isSharedCheck_856_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v_x_826_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_856_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
if (lean_obj_tag(v_a_837_) == 0)
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_851_; 
lean_dec_ref(v_as_824_);
lean_dec(v_a_823_);
lean_dec(v_a_822_);
lean_dec_ref(v___x_821_);
lean_dec(v_a_820_);
v_a_841_ = lean_ctor_get(v_a_837_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v_a_837_);
if (v_isSharedCheck_851_ == 0)
{
v___x_843_ = v_a_837_;
v_isShared_844_ = v_isSharedCheck_851_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v_a_837_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_851_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v_a_841_);
v___x_846_ = v___x_839_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_850_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
lean_object* v___x_848_; 
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v___x_846_);
v___x_848_ = v___x_843_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
else
{
lean_object* v_a_852_; size_t v___x_853_; size_t v___x_854_; lean_object* v___x_855_; 
lean_del_object(v___x_839_);
v_a_852_ = lean_ctor_get(v_a_837_, 0);
lean_inc(v_a_852_);
lean_dec_ref_known(v_a_837_, 1);
v___x_853_ = ((size_t)1ULL);
v___x_854_ = lean_usize_add(v_i_819_, v___x_853_);
v___x_855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg(v_a_820_, v___x_821_, v_a_822_, v_a_823_, v_as_824_, v_sz_825_, v___x_854_, v_a_852_);
return v___x_855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___boxed(lean_object* v_a_857_, lean_object* v___x_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_as_861_, lean_object* v_sz_862_, lean_object* v_i_863_, lean_object* v_b_864_, lean_object* v___y_865_){
_start:
{
size_t v_sz_boxed_866_; size_t v_i_boxed_867_; lean_object* v_res_868_; 
v_sz_boxed_866_ = lean_unbox_usize(v_sz_862_);
lean_dec(v_sz_862_);
v_i_boxed_867_ = lean_unbox_usize(v_i_863_);
lean_dec(v_i_863_);
v_res_868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg(v_a_857_, v___x_858_, v_a_859_, v_a_860_, v_as_861_, v_sz_boxed_866_, v_i_boxed_867_, v_b_864_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__4(lean_object* v___x_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v___x_872_, uint8_t v___x_873_, lean_object* v_x_874_){
_start:
{
if (lean_obj_tag(v_x_874_) == 0)
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_884_; 
lean_dec(v_a_871_);
lean_dec(v_a_870_);
lean_dec_ref(v___x_869_);
v_a_876_ = lean_ctor_get(v_x_874_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v_x_874_);
if (v_isSharedCheck_884_ == 0)
{
v___x_878_ = v_x_874_;
v_isShared_879_ = v_isSharedCheck_884_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v_x_874_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_884_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_883_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_882_; 
v___x_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
return v___x_882_;
}
}
}
else
{
lean_object* v_a_885_; size_t v_sz_886_; size_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___f_890_; lean_object* v___x_891_; lean_object* v___f_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v_a_885_ = lean_ctor_get(v_x_874_, 0);
v_sz_886_ = lean_array_size(v___x_869_);
v___x_887_ = ((size_t)0ULL);
lean_inc(v_a_870_);
lean_inc_ref(v___x_869_);
lean_inc(v_a_885_);
v___x_888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg(v_a_885_, v___x_869_, v_a_870_, v_a_871_, v___x_869_, v_sz_886_, v___x_887_, v___x_872_);
v___x_889_ = lean_box(v___x_873_);
v___f_890_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_890_, 0, v___x_889_);
lean_closure_set(v___f_890_, 1, v_x_874_);
v___x_891_ = lean_box(v___x_873_);
v___f_892_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_892_, 0, v___x_872_);
lean_closure_set(v___f_892_, 1, v_a_870_);
lean_closure_set(v___f_892_, 2, v___x_891_);
lean_closure_set(v___f_892_, 3, v___f_890_);
v___x_893_ = lean_unsigned_to_nat(0u);
v___x_894_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_893_, v___x_873_, v___x_888_, v___f_892_);
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__4___boxed(lean_object* v___x_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v___x_898_, lean_object* v___x_899_, lean_object* v_x_900_, lean_object* v___y_901_){
_start:
{
uint8_t v___x_11654__boxed_902_; lean_object* v_res_903_; 
v___x_11654__boxed_902_ = lean_unbox(v___x_899_);
v_res_903_ = l_Std_Async_Selectable_one___redArg___lam__4(v___x_895_, v_a_896_, v_a_897_, v___x_898_, v___x_11654__boxed_902_, v_x_900_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__5(lean_object* v___x_904_, lean_object* v_a_905_, lean_object* v___x_906_, uint8_t v___x_907_, lean_object* v_x_908_){
_start:
{
if (lean_obj_tag(v_x_908_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_918_; 
lean_dec(v_a_905_);
lean_dec_ref(v___x_904_);
v_a_910_ = lean_ctor_get(v_x_908_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v_x_908_);
if (v_isSharedCheck_918_ == 0)
{
v___x_912_ = v_x_908_;
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v_x_908_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_917_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_916_; 
v___x_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
return v___x_916_;
}
}
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_932_; 
v_a_919_ = lean_ctor_get(v_x_908_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v_x_908_);
if (v_isSharedCheck_932_ == 0)
{
v___x_921_ = v_x_908_;
v_isShared_922_ = v_isSharedCheck_932_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v_x_908_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_932_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___f_925_; lean_object* v___x_927_; 
v___x_923_ = lean_io_promise_new();
v___x_924_ = lean_box(v___x_907_);
v___f_925_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__4___boxed), 7, 5);
lean_closure_set(v___f_925_, 0, v___x_904_);
lean_closure_set(v___f_925_, 1, v_a_905_);
lean_closure_set(v___f_925_, 2, v_a_919_);
lean_closure_set(v___f_925_, 3, v___x_906_);
lean_closure_set(v___f_925_, 4, v___x_924_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_923_);
v___x_927_ = v___x_921_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_923_);
v___x_927_ = v_reuseFailAlloc_931_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
v___x_929_ = lean_unsigned_to_nat(0u);
v___x_930_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_929_, v___x_907_, v___x_928_, v___f_925_);
return v___x_930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__5___boxed(lean_object* v___x_933_, lean_object* v_a_934_, lean_object* v___x_935_, lean_object* v___x_936_, lean_object* v_x_937_, lean_object* v___y_938_){
_start:
{
uint8_t v___x_11710__boxed_939_; lean_object* v_res_940_; 
v___x_11710__boxed_939_ = lean_unbox(v___x_936_);
v_res_940_ = l_Std_Async_Selectable_one___redArg___lam__5(v___x_933_, v_a_934_, v___x_935_, v___x_11710__boxed_939_, v_x_937_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__6(lean_object* v___x_941_, lean_object* v_a_942_, lean_object* v___x_943_, lean_object* v_x_944_){
_start:
{
if (lean_obj_tag(v_x_944_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_954_; 
lean_dec(v_a_942_);
lean_dec_ref(v___x_941_);
v_a_946_ = lean_ctor_get(v_x_944_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v_x_944_);
if (v_isSharedCheck_954_ == 0)
{
v___x_948_ = v_x_944_;
v_isShared_949_ = v_isSharedCheck_954_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v_x_944_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_954_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_953_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_952_; 
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
return v___x_952_;
}
}
}
else
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_982_; 
v_a_955_ = lean_ctor_get(v_x_944_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v_x_944_);
if (v_isSharedCheck_982_ == 0)
{
v___x_957_ = v_x_944_;
v_isShared_958_ = v_isSharedCheck_982_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v_x_944_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_982_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v_fst_959_; 
v_fst_959_ = lean_ctor_get(v_a_955_, 0);
lean_inc(v_fst_959_);
lean_dec(v_a_955_);
if (lean_obj_tag(v_fst_959_) == 0)
{
uint8_t v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___f_964_; lean_object* v___x_966_; 
v___x_960_ = 0;
v___x_961_ = lean_box(v___x_960_);
v___x_962_ = lean_st_mk_ref(v___x_961_);
v___x_963_ = lean_box(v___x_960_);
v___f_964_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__5___boxed), 6, 4);
lean_closure_set(v___f_964_, 0, v___x_941_);
lean_closure_set(v___f_964_, 1, v_a_942_);
lean_closure_set(v___f_964_, 2, v___x_943_);
lean_closure_set(v___f_964_, 3, v___x_963_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v___x_962_);
v___x_966_ = v___x_957_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_962_);
v___x_966_ = v_reuseFailAlloc_970_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
v___x_968_ = lean_unsigned_to_nat(0u);
v___x_969_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_968_, v___x_960_, v___x_967_, v___f_964_);
return v___x_969_;
}
}
else
{
lean_object* v_val_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_981_; 
lean_dec(v_a_942_);
lean_dec_ref(v___x_941_);
v_val_971_ = lean_ctor_get(v_fst_959_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v_fst_959_);
if (v_isSharedCheck_981_ == 0)
{
v___x_973_ = v_fst_959_;
v_isShared_974_ = v_isSharedCheck_981_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_val_971_);
lean_dec(v_fst_959_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_981_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v_val_971_);
v___x_976_ = v___x_957_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_val_971_);
v___x_976_ = v_reuseFailAlloc_980_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
lean_object* v___x_978_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set_tag(v___x_973_, 0);
lean_ctor_set(v___x_973_, 0, v___x_976_);
v___x_978_ = v___x_973_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_976_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__6___boxed(lean_object* v___x_983_, lean_object* v_a_984_, lean_object* v___x_985_, lean_object* v_x_986_, lean_object* v___y_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Std_Async_Selectable_one___redArg___lam__6(v___x_983_, v_a_984_, v___x_985_, v_x_986_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__1(lean_object* v_a_989_, lean_object* v___f_990_, lean_object* v___x_991_, lean_object* v_x_992_){
_start:
{
if (lean_obj_tag(v_x_992_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1002_; 
lean_dec_ref(v___x_991_);
lean_dec_ref(v___f_990_);
lean_dec_ref(v_a_989_);
v_a_994_ = lean_ctor_get(v_x_992_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_x_992_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_996_ = v_x_992_;
v_isShared_997_ = v_isSharedCheck_1002_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v_x_992_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1002_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_994_);
v___x_999_ = v_reuseFailAlloc_1001_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1000_; 
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
return v___x_1000_;
}
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1018_; 
v_a_1003_ = lean_ctor_get(v_x_992_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_x_992_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1005_ = v_x_992_;
v_isShared_1006_ = v_isSharedCheck_1018_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v_x_992_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1018_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
if (lean_obj_tag(v_a_1003_) == 1)
{
lean_object* v_val_1007_; lean_object* v_cont_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; lean_object* v___x_1012_; 
lean_del_object(v___x_1005_);
lean_dec_ref(v___x_991_);
v_val_1007_ = lean_ctor_get(v_a_1003_, 0);
lean_inc(v_val_1007_);
lean_dec_ref_known(v_a_1003_, 1);
v_cont_1008_ = lean_ctor_get(v_a_989_, 1);
lean_inc_ref(v_cont_1008_);
lean_dec_ref(v_a_989_);
v___x_1009_ = lean_apply_2(v_cont_1008_, v_val_1007_, lean_box(0));
v___x_1010_ = lean_unsigned_to_nat(0u);
v___x_1011_ = 0;
v___x_1012_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1010_, v___x_1011_, v___x_1009_, v___f_990_);
return v___x_1012_;
}
else
{
lean_object* v___x_1013_; lean_object* v___x_1015_; 
lean_dec(v_a_1003_);
lean_dec_ref(v___f_990_);
lean_dec_ref(v_a_989_);
v___x_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_991_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1013_);
v___x_1015_ = v___x_1005_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1016_; 
v___x_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
return v___x_1016_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__1___boxed(lean_object* v_a_1019_, lean_object* v___f_1020_, lean_object* v___x_1021_, lean_object* v_x_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__1(v_a_1019_, v___f_1020_, v___x_1021_, v_x_1022_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__0(lean_object* v___x_1025_, lean_object* v_x_1026_){
_start:
{
if (lean_obj_tag(v_x_1026_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1036_; 
v_a_1028_ = lean_ctor_get(v_x_1026_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v_x_1026_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1030_ = v_x_1026_;
v_isShared_1031_ = v_isSharedCheck_1036_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v_x_1026_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1036_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
return v___x_1034_;
}
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1048_; 
v_a_1037_ = lean_ctor_get(v_x_1026_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_x_1026_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1039_ = v_x_1026_;
v_isShared_1040_ = v_isSharedCheck_1048_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v_x_1026_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1048_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1045_; 
v___x_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1041_, 0, v_a_1037_);
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v___x_1025_);
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 0, v___x_1043_);
v___x_1045_ = v___x_1039_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
return v___x_1046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__0___boxed(lean_object* v___x_1049_, lean_object* v_x_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__0(v___x_1049_, v_x_1050_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__2___boxed(lean_object* v_i_1058_, lean_object* v_as_1059_, lean_object* v_sz_1060_, lean_object* v_x_1061_, lean_object* v___y_1062_){
_start:
{
size_t v_i_boxed_1063_; size_t v_sz_boxed_1064_; lean_object* v_res_1065_; 
v_i_boxed_1063_ = lean_unbox_usize(v_i_1058_);
lean_dec(v_i_1058_);
v_sz_boxed_1064_ = lean_unbox_usize(v_sz_1060_);
lean_dec(v_sz_1060_);
v_res_1065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__2(v_i_boxed_1063_, v_as_1059_, v_sz_boxed_1064_, v_x_1061_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg(lean_object* v_as_1066_, size_t v_sz_1067_, size_t v_i_1068_, lean_object* v_b_1069_){
_start:
{
uint8_t v___x_1071_; 
v___x_1071_ = lean_usize_dec_lt(v_i_1068_, v_sz_1067_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
lean_dec_ref(v_as_1066_);
v___x_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1072_, 0, v_b_1069_);
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
return v___x_1073_;
}
else
{
lean_object* v_a_1074_; lean_object* v_selector_1075_; lean_object* v_tryFn_1076_; lean_object* v___x_1077_; lean_object* v___f_1078_; lean_object* v___x_1079_; lean_object* v___f_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___f_1086_; lean_object* v___x_1087_; 
lean_dec_ref(v_b_1069_);
v_a_1074_ = lean_array_uget_borrowed(v_as_1066_, v_i_1068_);
v_selector_1075_ = lean_ctor_get(v_a_1074_, 0);
v_tryFn_1076_ = lean_ctor_get(v_selector_1075_, 0);
lean_inc_ref(v_tryFn_1076_);
v___x_1077_ = lean_apply_1(v_tryFn_1076_, lean_box(0));
v___f_1078_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___closed__0));
v___x_1079_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___closed__1));
lean_inc(v_a_1074_);
v___f_1080_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1080_, 0, v_a_1074_);
lean_closure_set(v___f_1080_, 1, v___f_1078_);
lean_closure_set(v___f_1080_, 2, v___x_1079_);
v___x_1081_ = lean_unsigned_to_nat(0u);
v___x_1082_ = 0;
v___x_1083_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1081_, v___x_1082_, v___x_1077_, v___f_1080_);
v___x_1084_ = lean_box_usize(v_i_1068_);
v___x_1085_ = lean_box_usize(v_sz_1067_);
v___f_1086_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_1086_, 0, v___x_1084_);
lean_closure_set(v___f_1086_, 1, v_as_1066_);
lean_closure_set(v___f_1086_, 2, v___x_1085_);
v___x_1087_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1081_, v___x_1082_, v___x_1083_, v___f_1086_);
return v___x_1087_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__2(size_t v_i_1088_, lean_object* v_as_1089_, size_t v_sz_1090_, lean_object* v_x_1091_){
_start:
{
if (lean_obj_tag(v_x_1091_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1101_; 
lean_dec_ref(v_as_1089_);
v_a_1093_ = lean_ctor_get(v_x_1091_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_x_1091_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1095_ = v_x_1091_;
v_isShared_1096_ = v_isSharedCheck_1101_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v_x_1091_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1101_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
lean_object* v___x_1099_; 
v___x_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
return v___x_1099_;
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1121_; 
v_a_1102_ = lean_ctor_get(v_x_1091_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_x_1091_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1104_ = v_x_1091_;
v_isShared_1105_ = v_isSharedCheck_1121_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v_x_1091_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1121_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
if (lean_obj_tag(v_a_1102_) == 0)
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1116_; 
lean_dec_ref(v_as_1089_);
v_a_1106_ = lean_ctor_get(v_a_1102_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_a_1102_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1108_ = v_a_1102_;
v_isShared_1109_ = v_isSharedCheck_1116_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v_a_1102_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1116_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v_a_1106_);
v___x_1111_ = v___x_1104_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_object* v___x_1113_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v___x_1111_);
v___x_1113_ = v___x_1108_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1117_; size_t v___x_1118_; size_t v___x_1119_; lean_object* v___x_1120_; 
lean_del_object(v___x_1104_);
v_a_1117_ = lean_ctor_get(v_a_1102_, 0);
lean_inc(v_a_1117_);
lean_dec_ref_known(v_a_1102_, 1);
v___x_1118_ = ((size_t)1ULL);
v___x_1119_ = lean_usize_add(v_i_1088_, v___x_1118_);
v___x_1120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg(v_as_1089_, v_sz_1090_, v___x_1119_, v_a_1117_);
return v___x_1120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___boxed(lean_object* v_as_1122_, lean_object* v_sz_1123_, lean_object* v_i_1124_, lean_object* v_b_1125_, lean_object* v___y_1126_){
_start:
{
size_t v_sz_boxed_1127_; size_t v_i_boxed_1128_; lean_object* v_res_1129_; 
v_sz_boxed_1127_ = lean_unbox_usize(v_sz_1123_);
lean_dec(v_sz_1123_);
v_i_boxed_1128_ = lean_unbox_usize(v_i_1124_);
lean_dec(v_i_1124_);
v_res_1129_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg(v_as_1122_, v_sz_boxed_1127_, v_i_boxed_1128_, v_b_1125_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__7(lean_object* v___x_1130_, lean_object* v_x_1131_){
_start:
{
if (lean_obj_tag(v_x_1131_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1141_; 
lean_dec_ref(v___x_1130_);
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
lean_object* v_a_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; size_t v_sz_1145_; size_t v___x_1146_; lean_object* v___x_1147_; lean_object* v___f_1148_; lean_object* v___x_1149_; uint8_t v___x_1150_; lean_object* v___x_1151_; 
v_a_1142_ = lean_ctor_get(v_x_1131_, 0);
lean_inc(v_a_1142_);
lean_dec_ref_known(v_x_1131_, 1);
v___x_1143_ = lean_box(0);
v___x_1144_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___closed__1));
v_sz_1145_ = lean_array_size(v___x_1130_);
v___x_1146_ = ((size_t)0ULL);
lean_inc_ref(v___x_1130_);
v___x_1147_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg(v___x_1130_, v_sz_1145_, v___x_1146_, v___x_1144_);
v___f_1148_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__6___boxed), 5, 3);
lean_closure_set(v___f_1148_, 0, v___x_1130_);
lean_closure_set(v___f_1148_, 1, v_a_1142_);
lean_closure_set(v___f_1148_, 2, v___x_1143_);
v___x_1149_ = lean_unsigned_to_nat(0u);
v___x_1150_ = 0;
v___x_1151_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1149_, v___x_1150_, v___x_1147_, v___f_1148_);
return v___x_1151_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__7___boxed(lean_object* v___x_1152_, lean_object* v_x_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Std_Async_Selectable_one___redArg___lam__7(v___x_1152_, v_x_1153_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__8(lean_object* v_selectables_1156_, lean_object* v_x_1157_){
_start:
{
if (lean_obj_tag(v_x_1157_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1167_; 
lean_dec_ref(v_selectables_1156_);
v_a_1159_ = lean_ctor_get(v_x_1157_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_x_1157_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1161_ = v_x_1157_;
v_isShared_1162_ = v_isSharedCheck_1167_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v_x_1157_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1167_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
return v___x_1165_;
}
}
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1185_; 
v_a_1168_ = lean_ctor_get(v_x_1157_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_x_1157_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1170_ = v_x_1157_;
v_isShared_1171_ = v_isSharedCheck_1185_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v_x_1157_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1185_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1172_; uint64_t v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___f_1177_; lean_object* v___x_1179_; 
v___x_1172_ = lean_io_promise_new();
v___x_1173_ = l_ByteArray_toUInt64LE_x21(v_a_1168_);
lean_dec(v_a_1168_);
v___x_1174_ = lean_uint64_to_nat(v___x_1173_);
v___x_1175_ = l_mkStdGen(v___x_1174_);
lean_dec(v___x_1174_);
v___x_1176_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(v_selectables_1156_, v___x_1175_);
v___f_1177_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_1177_, 0, v___x_1176_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 0, v___x_1172_);
v___x_1179_ = v___x_1170_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1172_);
v___x_1179_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; lean_object* v___x_1183_; 
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
v___x_1181_ = lean_unsigned_to_nat(0u);
v___x_1182_ = 0;
v___x_1183_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1181_, v___x_1182_, v___x_1180_, v___f_1177_);
return v___x_1183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__8___boxed(lean_object* v_selectables_1186_, lean_object* v_x_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Std_Async_Selectable_one___redArg___lam__8(v_selectables_1186_, v_x_1187_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__9(lean_object* v___f_1190_, lean_object* v_____r_1191_){
_start:
{
lean_object* v_val_1194_; size_t v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = ((size_t)8ULL);
v___x_1200_ = lean_io_get_random_bytes(v___x_1199_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1200_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1200_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
lean_ctor_set_tag(v___x_1203_, 1);
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
v_val_1194_ = v___x_1206_;
goto v___jp_1193_;
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
v_a_1209_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1200_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1200_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
lean_ctor_set_tag(v___x_1211_, 0);
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
v_val_1194_ = v___x_1214_;
goto v___jp_1193_;
}
}
}
v___jp_1193_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; lean_object* v___x_1198_; 
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v_val_1194_);
v___x_1196_ = lean_unsigned_to_nat(0u);
v___x_1197_ = 0;
v___x_1198_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1196_, v___x_1197_, v___x_1195_, v___f_1190_);
return v___x_1198_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__9___boxed(lean_object* v___f_1217_, lean_object* v_____r_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Std_Async_Selectable_one___redArg___lam__9(v___f_1217_, v_____r_1218_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__10(lean_object* v___f_1221_, lean_object* v_x_1222_){
_start:
{
if (lean_obj_tag(v_x_1222_) == 0)
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1232_; 
lean_dec_ref(v___f_1221_);
v_a_1224_ = lean_ctor_get(v_x_1222_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_x_1222_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1226_ = v_x_1222_;
v_isShared_1227_ = v_isSharedCheck_1232_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v_x_1222_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1232_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1224_);
v___x_1229_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1230_; 
v___x_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
return v___x_1230_;
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1234_; 
v_a_1233_ = lean_ctor_get(v_x_1222_, 0);
lean_inc(v_a_1233_);
lean_dec_ref_known(v_x_1222_, 1);
v___x_1234_ = lean_apply_2(v___f_1221_, v_a_1233_, lean_box(0));
return v___x_1234_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__10___boxed(lean_object* v___f_1235_, lean_object* v_x_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Std_Async_Selectable_one___redArg___lam__10(v___f_1235_, v_x_1236_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg(lean_object* v_selectables_1246_){
_start:
{
lean_object* v___f_1248_; lean_object* v___f_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
lean_inc_ref(v_selectables_1246_);
v___f_1248_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__8___boxed), 3, 1);
lean_closure_set(v___f_1248_, 0, v_selectables_1246_);
lean_inc_ref(v___f_1248_);
v___f_1249_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_1249_, 0, v___f_1248_);
v___x_1250_ = lean_array_get_size(v_selectables_1246_);
lean_dec_ref(v_selectables_1246_);
v___x_1251_ = lean_unsigned_to_nat(0u);
v___x_1252_ = lean_nat_dec_eq(v___x_1250_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
lean_dec_ref(v___f_1249_);
v___x_1253_ = lean_box(0);
v___x_1254_ = l_Std_Async_Selectable_one___redArg___lam__9(v___f_1248_, v___x_1253_);
return v___x_1254_;
}
else
{
lean_object* v___f_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; lean_object* v___x_1258_; 
lean_dec_ref(v___f_1248_);
v___f_1255_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__10___boxed), 3, 1);
lean_closure_set(v___f_1255_, 0, v___f_1249_);
v___x_1256_ = ((lean_object*)(l_Std_Async_Selectable_one___redArg___closed__3));
v___x_1257_ = 0;
v___x_1258_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1251_, v___x_1257_, v___x_1256_, v___f_1255_);
return v___x_1258_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___boxed(lean_object* v_selectables_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Std_Async_Selectable_one___redArg(v_selectables_1259_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one(lean_object* v_00_u03b1_1262_, lean_object* v_selectables_1263_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Std_Async_Selectable_one___redArg(v_selectables_1263_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___boxed(lean_object* v_00_u03b1_1266_, lean_object* v_selectables_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Std_Async_Selectable_one(v_00_u03b1_1266_, v_selectables_1267_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0(lean_object* v_00_u03b1_1270_, uint8_t v_a_1271_, lean_object* v_as_1272_, size_t v_sz_1273_, size_t v_i_1274_, lean_object* v_b_1275_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg(v_a_1271_, v_as_1272_, v_sz_1273_, v_i_1274_, v_b_1275_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___boxed(lean_object* v_00_u03b1_1278_, lean_object* v_a_1279_, lean_object* v_as_1280_, lean_object* v_sz_1281_, lean_object* v_i_1282_, lean_object* v_b_1283_, lean_object* v___y_1284_){
_start:
{
uint8_t v_a_12327__boxed_1285_; size_t v_sz_boxed_1286_; size_t v_i_boxed_1287_; lean_object* v_res_1288_; 
v_a_12327__boxed_1285_ = lean_unbox(v_a_1279_);
v_sz_boxed_1286_ = lean_unbox_usize(v_sz_1281_);
lean_dec(v_sz_1281_);
v_i_boxed_1287_ = lean_unbox_usize(v_i_1282_);
lean_dec(v_i_1282_);
v_res_1288_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0(v_00_u03b1_1278_, v_a_12327__boxed_1285_, v_as_1280_, v_sz_boxed_1286_, v_i_boxed_1287_, v_b_1283_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2(lean_object* v_00_u03b1_1289_, lean_object* v_a_1290_, lean_object* v___x_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_as_1294_, size_t v_sz_1295_, size_t v_i_1296_, lean_object* v_b_1297_){
_start:
{
lean_object* v___x_1299_; 
v___x_1299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg(v_a_1290_, v___x_1291_, v_a_1292_, v_a_1293_, v_as_1294_, v_sz_1295_, v_i_1296_, v_b_1297_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___boxed(lean_object* v_00_u03b1_1300_, lean_object* v_a_1301_, lean_object* v___x_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_as_1305_, lean_object* v_sz_1306_, lean_object* v_i_1307_, lean_object* v_b_1308_, lean_object* v___y_1309_){
_start:
{
size_t v_sz_boxed_1310_; size_t v_i_boxed_1311_; lean_object* v_res_1312_; 
v_sz_boxed_1310_ = lean_unbox_usize(v_sz_1306_);
lean_dec(v_sz_1306_);
v_i_boxed_1311_ = lean_unbox_usize(v_i_1307_);
lean_dec(v_i_1307_);
v_res_1312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2(v_00_u03b1_1300_, v_a_1301_, v___x_1302_, v_a_1303_, v_a_1304_, v_as_1305_, v_sz_boxed_1310_, v_i_boxed_1311_, v_b_1308_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3(lean_object* v_00_u03b1_1313_, lean_object* v_as_1314_, size_t v_sz_1315_, size_t v_i_1316_, lean_object* v_b_1317_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg(v_as_1314_, v_sz_1315_, v_i_1316_, v_b_1317_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___boxed(lean_object* v_00_u03b1_1320_, lean_object* v_as_1321_, lean_object* v_sz_1322_, lean_object* v_i_1323_, lean_object* v_b_1324_, lean_object* v___y_1325_){
_start:
{
size_t v_sz_boxed_1326_; size_t v_i_boxed_1327_; lean_object* v_res_1328_; 
v_sz_boxed_1326_ = lean_unbox_usize(v_sz_1322_);
lean_dec(v_sz_1322_);
v_i_boxed_1327_ = lean_unbox_usize(v_i_1323_);
lean_dec(v_i_1323_);
v_res_1328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3(v_00_u03b1_1320_, v_as_1321_, v_sz_boxed_1326_, v_i_boxed_1327_, v_b_1324_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__0(lean_object* v_x_1333_){
_start:
{
if (lean_obj_tag(v_x_1333_) == 0)
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1343_; 
v_a_1335_ = lean_ctor_get(v_x_1333_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_x_1333_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1337_ = v_x_1333_;
v_isShared_1338_ = v_isSharedCheck_1343_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v_x_1333_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1343_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
return v___x_1341_;
}
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1361_; 
v_a_1344_ = lean_ctor_get(v_x_1333_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_x_1333_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1346_ = v_x_1333_;
v_isShared_1347_ = v_isSharedCheck_1361_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v_x_1333_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1361_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v_fst_1348_; 
v_fst_1348_ = lean_ctor_get(v_a_1344_, 0);
lean_inc(v_fst_1348_);
lean_dec(v_a_1344_);
if (lean_obj_tag(v_fst_1348_) == 0)
{
lean_object* v___x_1349_; 
lean_del_object(v___x_1346_);
v___x_1349_ = ((lean_object*)(l_Std_Async_Selectable_tryOne___redArg___lam__0___closed__1));
return v___x_1349_;
}
else
{
lean_object* v_val_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1360_; 
v_val_1350_ = lean_ctor_get(v_fst_1348_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_fst_1348_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1352_ = v_fst_1348_;
v_isShared_1353_ = v_isSharedCheck_1360_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_val_1350_);
lean_dec(v_fst_1348_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1360_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 0, v_val_1350_);
v___x_1355_ = v___x_1346_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_val_1350_);
v___x_1355_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1357_; 
if (v_isShared_1353_ == 0)
{
lean_ctor_set_tag(v___x_1352_, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1355_);
v___x_1357_ = v___x_1352_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__0___boxed(lean_object* v_x_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Std_Async_Selectable_tryOne___redArg___lam__0(v_x_1362_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__0(lean_object* v___x_1365_, lean_object* v_x_1366_){
_start:
{
if (lean_obj_tag(v_x_1366_) == 0)
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1376_; 
v_a_1368_ = lean_ctor_get(v_x_1366_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_x_1366_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1370_ = v_x_1366_;
v_isShared_1371_ = v_isSharedCheck_1376_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v_x_1366_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1376_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
return v___x_1374_;
}
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1389_; 
v_a_1377_ = lean_ctor_get(v_x_1366_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v_x_1366_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1379_ = v_x_1366_;
v_isShared_1380_ = v_isSharedCheck_1389_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v_x_1366_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1389_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1386_; 
v___x_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1381_, 0, v_a_1377_);
v___x_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
v___x_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
lean_ctor_set(v___x_1383_, 1, v___x_1365_);
v___x_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v___x_1384_);
v___x_1386_ = v___x_1379_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1384_);
v___x_1386_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1387_; 
v___x_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
return v___x_1387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__0___boxed(lean_object* v___x_1390_, lean_object* v_x_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__0(v___x_1390_, v_x_1391_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__1(lean_object* v_a_1394_, lean_object* v___x_1395_, uint8_t v___x_1396_, lean_object* v___f_1397_, lean_object* v___x_1398_, lean_object* v_x_1399_){
_start:
{
if (lean_obj_tag(v_x_1399_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1409_; 
lean_dec_ref(v___x_1398_);
lean_dec_ref(v___f_1397_);
lean_dec(v___x_1395_);
lean_dec_ref(v_a_1394_);
v_a_1401_ = lean_ctor_get(v_x_1399_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_x_1399_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1403_ = v_x_1399_;
v_isShared_1404_ = v_isSharedCheck_1409_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v_x_1399_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1409_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
lean_object* v___x_1407_; 
v___x_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
return v___x_1407_;
}
}
}
else
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1423_; 
v_a_1410_ = lean_ctor_get(v_x_1399_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_x_1399_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1412_ = v_x_1399_;
v_isShared_1413_ = v_isSharedCheck_1423_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v_x_1399_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1423_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
if (lean_obj_tag(v_a_1410_) == 1)
{
lean_object* v_val_1414_; lean_object* v_cont_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
lean_del_object(v___x_1412_);
lean_dec_ref(v___x_1398_);
v_val_1414_ = lean_ctor_get(v_a_1410_, 0);
lean_inc(v_val_1414_);
lean_dec_ref_known(v_a_1410_, 1);
v_cont_1415_ = lean_ctor_get(v_a_1394_, 1);
lean_inc_ref(v_cont_1415_);
lean_dec_ref(v_a_1394_);
v___x_1416_ = lean_apply_2(v_cont_1415_, v_val_1414_, lean_box(0));
v___x_1417_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1395_, v___x_1396_, v___x_1416_, v___f_1397_);
return v___x_1417_;
}
else
{
lean_object* v___x_1418_; lean_object* v___x_1420_; 
lean_dec(v_a_1410_);
lean_dec_ref(v___f_1397_);
lean_dec(v___x_1395_);
lean_dec_ref(v_a_1394_);
v___x_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1398_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 0, v___x_1418_);
v___x_1420_ = v___x_1412_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1418_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__1___boxed(lean_object* v_a_1424_, lean_object* v___x_1425_, lean_object* v___x_1426_, lean_object* v___f_1427_, lean_object* v___x_1428_, lean_object* v_x_1429_, lean_object* v___y_1430_){
_start:
{
uint8_t v___x_2325__boxed_1431_; lean_object* v_res_1432_; 
v___x_2325__boxed_1431_ = lean_unbox(v___x_1426_);
v_res_1432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__1(v_a_1424_, v___x_1425_, v___x_2325__boxed_1431_, v___f_1427_, v___x_1428_, v_x_1429_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__2___boxed(lean_object* v_i_1438_, lean_object* v___x_1439_, lean_object* v_as_1440_, lean_object* v_sz_1441_, lean_object* v_x_1442_, lean_object* v___y_1443_){
_start:
{
size_t v_i_boxed_1444_; size_t v_sz_boxed_1445_; lean_object* v_res_1446_; 
v_i_boxed_1444_ = lean_unbox_usize(v_i_1438_);
lean_dec(v_i_1438_);
v_sz_boxed_1445_ = lean_unbox_usize(v_sz_1441_);
lean_dec(v_sz_1441_);
v_res_1446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__2(v_i_boxed_1444_, v___x_1439_, v_as_1440_, v_sz_boxed_1445_, v_x_1442_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg(lean_object* v___x_1447_, lean_object* v_as_1448_, size_t v_sz_1449_, size_t v_i_1450_, lean_object* v_b_1451_){
_start:
{
uint8_t v___x_1453_; 
v___x_1453_ = lean_usize_dec_lt(v_i_1450_, v_sz_1449_);
if (v___x_1453_ == 0)
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
lean_dec_ref(v_as_1448_);
lean_dec(v___x_1447_);
v___x_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1454_, 0, v_b_1451_);
v___x_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
return v___x_1455_;
}
else
{
lean_object* v_a_1456_; lean_object* v_selector_1457_; lean_object* v_tryFn_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; lean_object* v___f_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___f_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___f_1469_; uint8_t v___x_1470_; lean_object* v___x_1471_; 
lean_dec_ref(v_b_1451_);
v_a_1456_ = lean_array_uget_borrowed(v_as_1448_, v_i_1450_);
v_selector_1457_ = lean_ctor_get(v_a_1456_, 0);
v_tryFn_1458_ = lean_ctor_get(v_selector_1457_, 0);
lean_inc_ref(v_tryFn_1458_);
v___x_1459_ = lean_apply_1(v_tryFn_1458_, lean_box(0));
v___x_1460_ = lean_unsigned_to_nat(0u);
v___x_1461_ = lean_nat_dec_eq(v___x_1447_, v___x_1460_);
v___f_1462_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__0));
v___x_1463_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__1));
v___x_1464_ = lean_box(v___x_1461_);
lean_inc(v_a_1456_);
v___f_1465_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_1465_, 0, v_a_1456_);
lean_closure_set(v___f_1465_, 1, v___x_1460_);
lean_closure_set(v___f_1465_, 2, v___x_1464_);
lean_closure_set(v___f_1465_, 3, v___f_1462_);
lean_closure_set(v___f_1465_, 4, v___x_1463_);
v___x_1466_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1460_, v___x_1461_, v___x_1459_, v___f_1465_);
v___x_1467_ = lean_box_usize(v_i_1450_);
v___x_1468_ = lean_box_usize(v_sz_1449_);
v___f_1469_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_1469_, 0, v___x_1467_);
lean_closure_set(v___f_1469_, 1, v___x_1447_);
lean_closure_set(v___f_1469_, 2, v_as_1448_);
lean_closure_set(v___f_1469_, 3, v___x_1468_);
v___x_1470_ = 0;
v___x_1471_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1460_, v___x_1470_, v___x_1466_, v___f_1469_);
return v___x_1471_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__2(size_t v_i_1472_, lean_object* v___x_1473_, lean_object* v_as_1474_, size_t v_sz_1475_, lean_object* v_x_1476_){
_start:
{
if (lean_obj_tag(v_x_1476_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1486_; 
lean_dec_ref(v_as_1474_);
lean_dec(v___x_1473_);
v_a_1478_ = lean_ctor_get(v_x_1476_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_x_1476_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1480_ = v_x_1476_;
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v_x_1476_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1484_; 
v___x_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
return v___x_1484_;
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1506_; 
v_a_1487_ = lean_ctor_get(v_x_1476_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v_x_1476_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1489_ = v_x_1476_;
v_isShared_1490_ = v_isSharedCheck_1506_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v_x_1476_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1506_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
if (lean_obj_tag(v_a_1487_) == 0)
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1501_; 
lean_dec_ref(v_as_1474_);
lean_dec(v___x_1473_);
v_a_1491_ = lean_ctor_get(v_a_1487_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_a_1487_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1493_ = v_a_1487_;
v_isShared_1494_ = v_isSharedCheck_1501_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v_a_1487_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1501_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 0, v_a_1491_);
v___x_1496_ = v___x_1489_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1498_; 
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 0, v___x_1496_);
v___x_1498_ = v___x_1493_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1496_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
else
{
lean_object* v_a_1502_; size_t v___x_1503_; size_t v___x_1504_; lean_object* v___x_1505_; 
lean_del_object(v___x_1489_);
v_a_1502_ = lean_ctor_get(v_a_1487_, 0);
lean_inc(v_a_1502_);
lean_dec_ref_known(v_a_1487_, 1);
v___x_1503_ = ((size_t)1ULL);
v___x_1504_ = lean_usize_add(v_i_1472_, v___x_1503_);
v___x_1505_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg(v___x_1473_, v_as_1474_, v_sz_1475_, v___x_1504_, v_a_1502_);
return v___x_1505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___boxed(lean_object* v___x_1507_, lean_object* v_as_1508_, lean_object* v_sz_1509_, lean_object* v_i_1510_, lean_object* v_b_1511_, lean_object* v___y_1512_){
_start:
{
size_t v_sz_boxed_1513_; size_t v_i_boxed_1514_; lean_object* v_res_1515_; 
v_sz_boxed_1513_ = lean_unbox_usize(v_sz_1509_);
lean_dec(v_sz_1509_);
v_i_boxed_1514_ = lean_unbox_usize(v_i_1510_);
lean_dec(v_i_1510_);
v_res_1515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg(v___x_1507_, v_as_1508_, v_sz_boxed_1513_, v_i_boxed_1514_, v_b_1511_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__1(lean_object* v_selectables_1516_, lean_object* v___x_1517_, lean_object* v___x_1518_, uint8_t v___x_1519_, lean_object* v___f_1520_, lean_object* v_x_1521_){
_start:
{
if (lean_obj_tag(v_x_1521_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1531_; 
lean_dec_ref(v___f_1520_);
lean_dec(v___x_1518_);
lean_dec(v___x_1517_);
lean_dec_ref(v_selectables_1516_);
v_a_1523_ = lean_ctor_get(v_x_1521_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_x_1521_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1525_ = v_x_1521_;
v_isShared_1526_ = v_isSharedCheck_1531_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v_x_1521_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1531_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1523_);
v___x_1528_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
return v___x_1529_;
}
}
}
else
{
lean_object* v_a_1532_; uint64_t v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; size_t v_sz_1538_; size_t v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v_a_1532_ = lean_ctor_get(v_x_1521_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v_x_1521_, 1);
v___x_1533_ = l_ByteArray_toUInt64LE_x21(v_a_1532_);
lean_dec(v_a_1532_);
v___x_1534_ = lean_uint64_to_nat(v___x_1533_);
v___x_1535_ = l_mkStdGen(v___x_1534_);
lean_dec(v___x_1534_);
v___x_1536_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(v_selectables_1516_, v___x_1535_);
v___x_1537_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__1));
v_sz_1538_ = lean_array_size(v___x_1536_);
v___x_1539_ = ((size_t)0ULL);
v___x_1540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg(v___x_1517_, v___x_1536_, v_sz_1538_, v___x_1539_, v___x_1537_);
v___x_1541_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1518_, v___x_1519_, v___x_1540_, v___f_1520_);
return v___x_1541_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__1___boxed(lean_object* v_selectables_1542_, lean_object* v___x_1543_, lean_object* v___x_1544_, lean_object* v___x_1545_, lean_object* v___f_1546_, lean_object* v_x_1547_, lean_object* v___y_1548_){
_start:
{
uint8_t v___x_2511__boxed_1549_; lean_object* v_res_1550_; 
v___x_2511__boxed_1549_ = lean_unbox(v___x_1545_);
v_res_1550_ = l_Std_Async_Selectable_tryOne___redArg___lam__1(v_selectables_1542_, v___x_1543_, v___x_1544_, v___x_2511__boxed_1549_, v___f_1546_, v_x_1547_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg(lean_object* v_selectables_1552_){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1554_ = lean_array_get_size(v_selectables_1552_);
v___x_1555_ = lean_unsigned_to_nat(0u);
v___x_1556_ = lean_nat_dec_eq(v___x_1554_, v___x_1555_);
if (v___x_1556_ == 0)
{
lean_object* v___f_1557_; lean_object* v___x_1558_; lean_object* v___f_1559_; lean_object* v_val_1561_; size_t v___x_1564_; lean_object* v___x_1565_; 
v___f_1557_ = ((lean_object*)(l_Std_Async_Selectable_tryOne___redArg___closed__0));
v___x_1558_ = lean_box(v___x_1556_);
v___f_1559_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_tryOne___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_1559_, 0, v_selectables_1552_);
lean_closure_set(v___f_1559_, 1, v___x_1554_);
lean_closure_set(v___f_1559_, 2, v___x_1555_);
lean_closure_set(v___f_1559_, 3, v___x_1558_);
lean_closure_set(v___f_1559_, 4, v___f_1557_);
v___x_1564_ = ((size_t)8ULL);
v___x_1565_ = lean_io_get_random_bytes(v___x_1564_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1565_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1565_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
lean_ctor_set_tag(v___x_1568_, 1);
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
v_val_1561_ = v___x_1571_;
goto v___jp_1560_;
}
}
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
v_a_1574_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1565_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1565_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
lean_ctor_set_tag(v___x_1576_, 0);
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
v_val_1561_ = v___x_1579_;
goto v___jp_1560_;
}
}
}
v___jp_1560_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1562_, 0, v_val_1561_);
v___x_1563_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1555_, v___x_1556_, v___x_1562_, v___f_1559_);
return v___x_1563_;
}
}
else
{
lean_object* v___x_1582_; 
lean_dec_ref(v_selectables_1552_);
v___x_1582_ = ((lean_object*)(l_Std_Async_Selectable_tryOne___redArg___lam__0___closed__1));
return v___x_1582_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___boxed(lean_object* v_selectables_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Std_Async_Selectable_tryOne___redArg(v_selectables_1583_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne(lean_object* v_00_u03b1_1586_, lean_object* v_selectables_1587_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Std_Async_Selectable_tryOne___redArg(v_selectables_1587_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___boxed(lean_object* v_00_u03b1_1590_, lean_object* v_selectables_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Std_Async_Selectable_tryOne(v_00_u03b1_1590_, v_selectables_1591_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0(lean_object* v_00_u03b1_1594_, lean_object* v___x_1595_, lean_object* v_as_1596_, size_t v_sz_1597_, size_t v_i_1598_, lean_object* v_b_1599_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg(v___x_1595_, v_as_1596_, v_sz_1597_, v_i_1598_, v_b_1599_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___boxed(lean_object* v_00_u03b1_1602_, lean_object* v___x_1603_, lean_object* v_as_1604_, lean_object* v_sz_1605_, lean_object* v_i_1606_, lean_object* v_b_1607_, lean_object* v___y_1608_){
_start:
{
size_t v_sz_boxed_1609_; size_t v_i_boxed_1610_; lean_object* v_res_1611_; 
v_sz_boxed_1609_ = lean_unbox_usize(v_sz_1605_);
lean_dec(v_sz_1605_);
v_i_boxed_1610_ = lean_unbox_usize(v_i_1606_);
lean_dec(v_i_1606_);
v_res_1611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0(v_00_u03b1_1602_, v___x_1603_, v_as_1604_, v_sz_boxed_1609_, v_i_boxed_1610_, v_b_1607_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1(lean_object* v_a_1612_, lean_object* v___f_1613_, lean_object* v___x_1614_, lean_object* v_x_1615_){
_start:
{
if (lean_obj_tag(v_x_1615_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1625_; 
lean_dec_ref(v___x_1614_);
lean_dec_ref(v___f_1613_);
lean_dec_ref(v_a_1612_);
v_a_1617_ = lean_ctor_get(v_x_1615_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_x_1615_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1619_ = v_x_1615_;
v_isShared_1620_ = v_isSharedCheck_1625_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v_x_1615_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1625_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
lean_object* v___x_1623_; 
v___x_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1622_);
return v___x_1623_;
}
}
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1641_; 
v_a_1626_ = lean_ctor_get(v_x_1615_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_x_1615_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1628_ = v_x_1615_;
v_isShared_1629_ = v_isSharedCheck_1641_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v_x_1615_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1641_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
if (lean_obj_tag(v_a_1626_) == 1)
{
lean_object* v_val_1630_; lean_object* v_cont_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; uint8_t v___x_1634_; lean_object* v___x_1635_; 
lean_del_object(v___x_1628_);
lean_dec_ref(v___x_1614_);
v_val_1630_ = lean_ctor_get(v_a_1626_, 0);
lean_inc(v_val_1630_);
lean_dec_ref_known(v_a_1626_, 1);
v_cont_1631_ = lean_ctor_get(v_a_1612_, 1);
lean_inc_ref(v_cont_1631_);
lean_dec_ref(v_a_1612_);
v___x_1632_ = lean_apply_2(v_cont_1631_, v_val_1630_, lean_box(0));
v___x_1633_ = lean_unsigned_to_nat(0u);
v___x_1634_ = 0;
v___x_1635_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1633_, v___x_1634_, v___x_1632_, v___f_1613_);
return v___x_1635_;
}
else
{
lean_object* v___x_1636_; lean_object* v___x_1638_; 
lean_dec(v_a_1626_);
lean_dec_ref(v___f_1613_);
lean_dec_ref(v_a_1612_);
v___x_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1614_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 0, v___x_1636_);
v___x_1638_ = v___x_1628_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1636_);
v___x_1638_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
lean_object* v___x_1639_; 
v___x_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
return v___x_1639_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1___boxed(lean_object* v_a_1642_, lean_object* v___f_1643_, lean_object* v___x_1644_, lean_object* v_x_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1(v_a_1642_, v___f_1643_, v___x_1644_, v_x_1645_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0___boxed(lean_object* v_i_1648_, lean_object* v_as_1649_, lean_object* v_sz_1650_, lean_object* v_x_1651_, lean_object* v___y_1652_){
_start:
{
size_t v_i_boxed_1653_; size_t v_sz_boxed_1654_; lean_object* v_res_1655_; 
v_i_boxed_1653_ = lean_unbox_usize(v_i_1648_);
lean_dec(v_i_1648_);
v_sz_boxed_1654_ = lean_unbox_usize(v_sz_1650_);
lean_dec(v_sz_1650_);
v_res_1655_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0(v_i_boxed_1653_, v_as_1649_, v_sz_boxed_1654_, v_x_1651_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(lean_object* v_as_1656_, size_t v_sz_1657_, size_t v_i_1658_, lean_object* v_b_1659_){
_start:
{
uint8_t v___x_1661_; 
v___x_1661_ = lean_usize_dec_lt(v_i_1658_, v_sz_1657_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
lean_dec_ref(v_as_1656_);
v___x_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1662_, 0, v_b_1659_);
v___x_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
return v___x_1663_;
}
else
{
lean_object* v_a_1664_; lean_object* v_selector_1665_; lean_object* v_tryFn_1666_; lean_object* v___x_1667_; lean_object* v___f_1668_; lean_object* v___x_1669_; lean_object* v___f_1670_; lean_object* v___x_1671_; uint8_t v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___f_1676_; lean_object* v___x_1677_; 
lean_dec_ref(v_b_1659_);
v_a_1664_ = lean_array_uget_borrowed(v_as_1656_, v_i_1658_);
v_selector_1665_ = lean_ctor_get(v_a_1664_, 0);
v_tryFn_1666_ = lean_ctor_get(v_selector_1665_, 0);
lean_inc_ref(v_tryFn_1666_);
v___x_1667_ = lean_apply_1(v_tryFn_1666_, lean_box(0));
v___f_1668_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__0));
v___x_1669_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__1));
lean_inc(v_a_1664_);
v___f_1670_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1670_, 0, v_a_1664_);
lean_closure_set(v___f_1670_, 1, v___f_1668_);
lean_closure_set(v___f_1670_, 2, v___x_1669_);
v___x_1671_ = lean_unsigned_to_nat(0u);
v___x_1672_ = 0;
v___x_1673_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1671_, v___x_1672_, v___x_1667_, v___f_1670_);
v___x_1674_ = lean_box_usize(v_i_1658_);
v___x_1675_ = lean_box_usize(v_sz_1657_);
v___f_1676_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1676_, 0, v___x_1674_);
lean_closure_set(v___f_1676_, 1, v_as_1656_);
lean_closure_set(v___f_1676_, 2, v___x_1675_);
v___x_1677_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1671_, v___x_1672_, v___x_1673_, v___f_1676_);
return v___x_1677_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0(size_t v_i_1678_, lean_object* v_as_1679_, size_t v_sz_1680_, lean_object* v_x_1681_){
_start:
{
if (lean_obj_tag(v_x_1681_) == 0)
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1691_; 
lean_dec_ref(v_as_1679_);
v_a_1683_ = lean_ctor_get(v_x_1681_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_x_1681_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1685_ = v_x_1681_;
v_isShared_1686_ = v_isSharedCheck_1691_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v_x_1681_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1691_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1689_; 
v___x_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
return v___x_1689_;
}
}
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1711_; 
v_a_1692_ = lean_ctor_get(v_x_1681_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v_x_1681_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1694_ = v_x_1681_;
v_isShared_1695_ = v_isSharedCheck_1711_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v_x_1681_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1711_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
if (lean_obj_tag(v_a_1692_) == 0)
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1706_; 
lean_dec_ref(v_as_1679_);
v_a_1696_ = lean_ctor_get(v_a_1692_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v_a_1692_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1698_ = v_a_1692_;
v_isShared_1699_ = v_isSharedCheck_1706_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v_a_1692_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1706_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 0, v_a_1696_);
v___x_1701_ = v___x_1694_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
lean_object* v___x_1703_; 
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 0, v___x_1701_);
v___x_1703_ = v___x_1698_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1701_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
else
{
lean_object* v_a_1707_; size_t v___x_1708_; size_t v___x_1709_; lean_object* v___x_1710_; 
lean_del_object(v___x_1694_);
v_a_1707_ = lean_ctor_get(v_a_1692_, 0);
lean_inc(v_a_1707_);
lean_dec_ref_known(v_a_1692_, 1);
v___x_1708_ = ((size_t)1ULL);
v___x_1709_ = lean_usize_add(v_i_1678_, v___x_1708_);
v___x_1710_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(v_as_1679_, v_sz_1680_, v___x_1709_, v_a_1707_);
return v___x_1710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___boxed(lean_object* v_as_1712_, lean_object* v_sz_1713_, lean_object* v_i_1714_, lean_object* v_b_1715_, lean_object* v___y_1716_){
_start:
{
size_t v_sz_boxed_1717_; size_t v_i_boxed_1718_; lean_object* v_res_1719_; 
v_sz_boxed_1717_ = lean_unbox_usize(v_sz_1713_);
lean_dec(v_sz_1713_);
v_i_boxed_1718_ = lean_unbox_usize(v_i_1714_);
lean_dec(v_i_1714_);
v_res_1719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(v_as_1712_, v_sz_boxed_1717_, v_i_boxed_1718_, v_b_1715_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__1(lean_object* v_selectables_1720_, lean_object* v___f_1721_, lean_object* v_x_1722_){
_start:
{
if (lean_obj_tag(v_x_1722_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1732_; 
lean_dec_ref(v___f_1721_);
lean_dec_ref(v_selectables_1720_);
v_a_1724_ = lean_ctor_get(v_x_1722_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v_x_1722_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1726_ = v_x_1722_;
v_isShared_1727_ = v_isSharedCheck_1732_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v_x_1722_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1732_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
lean_object* v___x_1730_; 
v___x_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
return v___x_1730_;
}
}
}
else
{
lean_object* v_a_1733_; uint64_t v___x_1734_; lean_object* v_seed_1735_; lean_object* v_gen_1736_; lean_object* v_selectables_1737_; lean_object* v___x_1738_; size_t v_sz_1739_; size_t v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; uint8_t v___x_1743_; lean_object* v___x_1744_; 
v_a_1733_ = lean_ctor_get(v_x_1722_, 0);
lean_inc(v_a_1733_);
lean_dec_ref_known(v_x_1722_, 1);
v___x_1734_ = l_ByteArray_toUInt64LE_x21(v_a_1733_);
lean_dec(v_a_1733_);
v_seed_1735_ = lean_uint64_to_nat(v___x_1734_);
v_gen_1736_ = l_mkStdGen(v_seed_1735_);
lean_dec(v_seed_1735_);
v_selectables_1737_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(v_selectables_1720_, v_gen_1736_);
v___x_1738_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__1));
v_sz_1739_ = lean_array_size(v_selectables_1737_);
v___x_1740_ = ((size_t)0ULL);
v___x_1741_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(v_selectables_1737_, v_sz_1739_, v___x_1740_, v___x_1738_);
v___x_1742_ = lean_unsigned_to_nat(0u);
v___x_1743_ = 0;
v___x_1744_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1742_, v___x_1743_, v___x_1741_, v___f_1721_);
return v___x_1744_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__1___boxed(lean_object* v_selectables_1745_, lean_object* v___f_1746_, lean_object* v_x_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Std_Async_Selectable_combine___redArg___lam__1(v_selectables_1745_, v___f_1746_, v_x_1747_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__0(lean_object* v___f_1750_, size_t v___x_1751_){
_start:
{
lean_object* v_val_1754_; lean_object* v___x_1759_; 
v___x_1759_ = lean_io_get_random_bytes(v___x_1751_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1759_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1759_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
lean_ctor_set_tag(v___x_1762_, 1);
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
v_val_1754_ = v___x_1765_;
goto v___jp_1753_;
}
}
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
v_a_1768_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1759_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1759_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
lean_ctor_set_tag(v___x_1770_, 0);
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
v_val_1754_ = v___x_1773_;
goto v___jp_1753_;
}
}
}
v___jp_1753_:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; lean_object* v___x_1758_; 
v___x_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1755_, 0, v_val_1754_);
v___x_1756_ = lean_unsigned_to_nat(0u);
v___x_1757_ = 0;
v___x_1758_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1756_, v___x_1757_, v___x_1755_, v___f_1750_);
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__0___boxed(lean_object* v___f_1776_, lean_object* v___x_1777_, lean_object* v___y_1778_){
_start:
{
size_t v___x_7649__boxed_1779_; lean_object* v_res_1780_; 
v___x_7649__boxed_1779_ = lean_unbox_usize(v___x_1777_);
lean_dec(v___x_1777_);
v_res_1780_ = l_Std_Async_Selectable_combine___redArg___lam__0(v___f_1776_, v___x_7649__boxed_1779_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__2(lean_object* v_a_1781_, lean_object* v_x_1782_){
_start:
{
if (lean_obj_tag(v_x_1782_) == 0)
{
lean_object* v___x_1784_; 
v___x_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1784_, 0, v_x_1782_);
return v___x_1784_;
}
else
{
lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1794_; 
v_isSharedCheck_1794_ = !lean_is_exclusive(v_x_1782_);
if (v_isSharedCheck_1794_ == 0)
{
lean_object* v_unused_1795_; 
v_unused_1795_ = lean_ctor_get(v_x_1782_, 0);
lean_dec(v_unused_1795_);
v___x_1786_ = v_x_1782_;
v_isShared_1787_ = v_isSharedCheck_1794_;
goto v_resetjp_1785_;
}
else
{
lean_dec(v_x_1782_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1794_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1791_; 
v___x_1788_ = lean_box(0);
v___x_1789_ = lean_io_promise_resolve(v___x_1788_, v_a_1781_);
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 0, v___x_1789_);
v___x_1791_ = v___x_1786_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1789_);
v___x_1791_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
lean_object* v___x_1792_; 
v___x_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1791_);
return v___x_1792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__2___boxed(lean_object* v_a_1796_, lean_object* v_x_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Std_Async_Selectable_combine___redArg___lam__2(v_a_1796_, v_x_1797_);
lean_dec(v_a_1796_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__0(lean_object* v_a_1800_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1801_, 0, v_a_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__3(lean_object* v_a_1802_, lean_object* v___f_1803_, lean_object* v_x_1804_){
_start:
{
if (lean_obj_tag(v_x_1804_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1814_; 
lean_dec_ref(v___f_1803_);
lean_dec_ref(v_a_1802_);
v_a_1806_ = lean_ctor_get(v_x_1804_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v_x_1804_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1808_ = v_x_1804_;
v_isShared_1809_ = v_isSharedCheck_1814_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v_x_1804_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1814_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
lean_object* v___x_1812_; 
v___x_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
return v___x_1812_;
}
}
}
else
{
lean_object* v_a_1815_; lean_object* v_cont_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; uint8_t v___x_1819_; lean_object* v___x_1820_; 
v_a_1815_ = lean_ctor_get(v_x_1804_, 0);
lean_inc(v_a_1815_);
lean_dec_ref_known(v_x_1804_, 1);
v_cont_1816_ = lean_ctor_get(v_a_1802_, 1);
lean_inc_ref(v_cont_1816_);
lean_dec_ref(v_a_1802_);
v___x_1817_ = lean_apply_2(v_cont_1816_, v_a_1815_, lean_box(0));
v___x_1818_ = lean_unsigned_to_nat(0u);
v___x_1819_ = 0;
v___x_1820_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1818_, v___x_1819_, v___x_1817_, v___f_1803_);
return v___x_1820_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__3___boxed(lean_object* v_a_1821_, lean_object* v___f_1822_, lean_object* v_x_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__3(v_a_1821_, v___f_1822_, v_x_1823_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__2(lean_object* v_promise_1826_, lean_object* v_x_1827_){
_start:
{
if (lean_obj_tag(v_x_1827_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1839_; 
v_a_1829_ = lean_ctor_get(v_x_1827_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v_x_1827_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1831_ = v_x_1827_;
v_isShared_1832_ = v_isSharedCheck_1839_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v_x_1827_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1839_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1835_ = lean_io_promise_resolve(v___x_1834_, v_promise_1826_);
v___x_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
v___x_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
return v___x_1837_;
}
}
}
else
{
lean_object* v___x_1840_; 
v___x_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1840_, 0, v_x_1827_);
return v___x_1840_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__2___boxed(lean_object* v_promise_1841_, lean_object* v_x_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__2(v_promise_1841_, v_x_1842_);
lean_dec(v_promise_1841_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__4(lean_object* v___f_1845_, lean_object* v___f_1846_, lean_object* v_val_1847_, lean_object* v_x_1848_){
_start:
{
lean_object* v_val_1851_; 
if (lean_obj_tag(v_x_1848_) == 0)
{
lean_object* v___x_1857_; 
lean_dec_ref(v_val_1847_);
lean_dec_ref(v___f_1846_);
lean_dec_ref(v___f_1845_);
v___x_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1857_, 0, v_x_1848_);
return v___x_1857_;
}
else
{
lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1870_; 
v_isSharedCheck_1870_ = !lean_is_exclusive(v_x_1848_);
if (v_isSharedCheck_1870_ == 0)
{
lean_object* v_unused_1871_; 
v_unused_1871_ = lean_ctor_get(v_x_1848_, 0);
lean_dec(v_unused_1871_);
v___x_1859_ = v_x_1848_;
v_isShared_1860_ = v_isSharedCheck_1870_;
goto v_resetjp_1858_;
}
else
{
lean_dec(v_x_1848_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1870_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___redArg(v_val_1847_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_a_1862_; lean_object* v___x_1864_; 
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_a_1862_);
lean_dec_ref_known(v___x_1861_, 1);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v_a_1862_);
v___x_1864_ = v___x_1859_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1862_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
v_val_1851_ = v___x_1864_;
goto v___jp_1850_;
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; 
v_a_1866_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_a_1866_);
lean_dec_ref_known(v___x_1861_, 1);
if (v_isShared_1860_ == 0)
{
lean_ctor_set_tag(v___x_1859_, 0);
lean_ctor_set(v___x_1859_, 0, v_a_1866_);
v___x_1868_ = v___x_1859_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1866_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
v_val_1851_ = v___x_1868_;
goto v___jp_1850_;
}
}
}
}
v___jp_1850_:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v_val_1851_);
v___x_1853_ = lean_unsigned_to_nat(0u);
v___x_1854_ = 0;
v___x_1855_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1853_, v___x_1854_, v___x_1852_, v___f_1845_);
v___x_1856_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1853_, v___x_1854_, v___x_1855_, v___f_1846_);
return v___x_1856_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__4___boxed(lean_object* v___f_1872_, lean_object* v___f_1873_, lean_object* v_val_1874_, lean_object* v_x_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__4(v___f_1872_, v___f_1873_, v_val_1874_, v_x_1875_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg___lam__1___boxed(lean_object* v_i_1878_, lean_object* v_as_1879_, lean_object* v_sz_1880_, lean_object* v_x_1881_, lean_object* v___y_1882_){
_start:
{
size_t v_i_boxed_1883_; size_t v_sz_boxed_1884_; lean_object* v_res_1885_; 
v_i_boxed_1883_ = lean_unbox_usize(v_i_1878_);
lean_dec(v_i_1878_);
v_sz_boxed_1884_ = lean_unbox_usize(v_sz_1880_);
lean_dec(v_sz_1880_);
v_res_1885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg___lam__1(v_i_boxed_1883_, v_as_1879_, v_sz_boxed_1884_, v_x_1881_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg(lean_object* v_as_1886_, size_t v_sz_1887_, size_t v_i_1888_, lean_object* v_b_1889_){
_start:
{
uint8_t v___x_1891_; 
v___x_1891_ = lean_usize_dec_lt(v_i_1888_, v_sz_1887_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
lean_dec_ref(v_as_1886_);
v___x_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1892_, 0, v_b_1889_);
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
return v___x_1893_;
}
else
{
lean_object* v_a_1894_; lean_object* v_selector_1895_; lean_object* v_unregisterFn_1896_; lean_object* v___x_1897_; lean_object* v___f_1898_; lean_object* v___x_1899_; uint8_t v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___f_1904_; lean_object* v___x_1905_; 
v_a_1894_ = lean_array_uget_borrowed(v_as_1886_, v_i_1888_);
v_selector_1895_ = lean_ctor_get(v_a_1894_, 0);
v_unregisterFn_1896_ = lean_ctor_get(v_selector_1895_, 2);
lean_inc_ref(v_unregisterFn_1896_);
v___x_1897_ = lean_apply_1(v_unregisterFn_1896_, lean_box(0));
v___f_1898_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___closed__0));
v___x_1899_ = lean_unsigned_to_nat(0u);
v___x_1900_ = 0;
v___x_1901_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1899_, v___x_1900_, v___x_1897_, v___f_1898_);
v___x_1902_ = lean_box_usize(v_i_1888_);
v___x_1903_ = lean_box_usize(v_sz_1887_);
v___f_1904_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1904_, 0, v___x_1902_);
lean_closure_set(v___f_1904_, 1, v_as_1886_);
lean_closure_set(v___f_1904_, 2, v___x_1903_);
v___x_1905_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1899_, v___x_1900_, v___x_1901_, v___f_1904_);
return v___x_1905_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg___lam__1(size_t v_i_1906_, lean_object* v_as_1907_, size_t v_sz_1908_, lean_object* v_x_1909_){
_start:
{
if (lean_obj_tag(v_x_1909_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1919_; 
lean_dec_ref(v_as_1907_);
v_a_1911_ = lean_ctor_get(v_x_1909_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v_x_1909_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1913_ = v_x_1909_;
v_isShared_1914_ = v_isSharedCheck_1919_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v_x_1909_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1919_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1917_; 
v___x_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1916_);
return v___x_1917_;
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1939_; 
v_a_1920_ = lean_ctor_get(v_x_1909_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v_x_1909_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1922_ = v_x_1909_;
v_isShared_1923_ = v_isSharedCheck_1939_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v_x_1909_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1939_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
if (lean_obj_tag(v_a_1920_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1934_; 
lean_dec_ref(v_as_1907_);
v_a_1924_ = lean_ctor_get(v_a_1920_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v_a_1920_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1926_ = v_a_1920_;
v_isShared_1927_ = v_isSharedCheck_1934_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v_a_1920_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1934_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1929_; 
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v_a_1924_);
v___x_1929_ = v___x_1922_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1924_);
v___x_1929_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
lean_object* v___x_1931_; 
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v___x_1929_);
v___x_1931_ = v___x_1926_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1929_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
else
{
lean_object* v_a_1935_; size_t v___x_1936_; size_t v___x_1937_; lean_object* v___x_1938_; 
lean_del_object(v___x_1922_);
v_a_1935_ = lean_ctor_get(v_a_1920_, 0);
lean_inc(v_a_1935_);
lean_dec_ref_known(v_a_1920_, 1);
v___x_1936_ = ((size_t)1ULL);
v___x_1937_ = lean_usize_add(v_i_1906_, v___x_1936_);
v___x_1938_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg(v_as_1907_, v_sz_1908_, v___x_1937_, v_a_1935_);
return v___x_1938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg___boxed(lean_object* v_as_1940_, lean_object* v_sz_1941_, lean_object* v_i_1942_, lean_object* v_b_1943_, lean_object* v___y_1944_){
_start:
{
size_t v_sz_boxed_1945_; size_t v_i_boxed_1946_; lean_object* v_res_1947_; 
v_sz_boxed_1945_ = lean_unbox_usize(v_sz_1941_);
lean_dec(v_sz_1941_);
v_i_boxed_1946_ = lean_unbox_usize(v_i_1942_);
lean_dec(v_i_1942_);
v_res_1947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg(v_as_1940_, v_sz_boxed_1945_, v_i_boxed_1946_, v_b_1943_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__5(lean_object* v___x_1948_, lean_object* v___x_1949_, lean_object* v___f_1950_, lean_object* v_x_1951_){
_start:
{
if (lean_obj_tag(v_x_1951_) == 0)
{
lean_object* v___x_1953_; 
lean_dec_ref(v___f_1950_);
lean_dec_ref(v___x_1948_);
v___x_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1953_, 0, v_x_1951_);
return v___x_1953_;
}
else
{
size_t v_sz_1954_; size_t v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; lean_object* v___x_1959_; 
lean_dec_ref_known(v_x_1951_, 1);
v_sz_1954_ = lean_array_size(v___x_1948_);
v___x_1955_ = ((size_t)0ULL);
v___x_1956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg(v___x_1948_, v_sz_1954_, v___x_1955_, v___x_1949_);
v___x_1957_ = lean_unsigned_to_nat(0u);
v___x_1958_ = 0;
v___x_1959_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1957_, v___x_1958_, v___x_1956_, v___f_1950_);
return v___x_1959_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__5___boxed(lean_object* v___x_1960_, lean_object* v___x_1961_, lean_object* v___f_1962_, lean_object* v_x_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__5(v___x_1960_, v___x_1961_, v___f_1962_, v_x_1963_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__1(lean_object* v_promise_1966_, lean_object* v_x_1967_){
_start:
{
if (lean_obj_tag(v_x_1967_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1977_; 
v_a_1969_ = lean_ctor_get(v_x_1967_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_x_1967_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1971_ = v_x_1967_;
v_isShared_1972_ = v_isSharedCheck_1977_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v_x_1967_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1977_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
lean_object* v___x_1975_; 
v___x_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
return v___x_1975_;
}
}
}
else
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1978_ = lean_io_promise_resolve(v_x_1967_, v_promise_1966_);
v___x_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
v___x_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
return v___x_1980_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__1___boxed(lean_object* v_promise_1981_, lean_object* v_x_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__1(v_promise_1981_, v_x_1982_);
lean_dec(v_promise_1981_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__6(lean_object* v___x_1985_, lean_object* v_waiter_1986_, lean_object* v_a_1987_, lean_object* v___x_1988_, lean_object* v_a_1989_, lean_object* v___f_1990_, lean_object* v_a_1991_){
_start:
{
if (lean_obj_tag(v_a_1991_) == 0)
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
lean_dec_ref(v___f_1990_);
lean_dec_ref(v___x_1988_);
lean_dec_ref(v_a_1987_);
lean_dec_ref(v_waiter_1986_);
v___x_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1985_);
v___x_1994_ = lean_task_pure(v___x_1993_);
return v___x_1994_;
}
else
{
lean_object* v_val_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2016_; 
v_val_1995_ = lean_ctor_get(v_a_1991_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_a_1991_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_1997_ = v_a_1991_;
v_isShared_1998_ = v_isSharedCheck_2016_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_val_1995_);
lean_dec(v_a_1991_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2016_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v_promise_1999_; lean_object* v___f_2000_; lean_object* v___f_2001_; lean_object* v___f_2002_; lean_object* v___f_2003_; lean_object* v___f_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; uint8_t v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2010_; 
v_promise_1999_ = lean_ctor_get(v_waiter_1986_, 1);
lean_inc_n(v_promise_1999_, 2);
lean_dec_ref(v_waiter_1986_);
v___f_2000_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2000_, 0, v_promise_1999_);
v___f_2001_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2001_, 0, v_promise_1999_);
v___f_2002_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_2002_, 0, v_a_1987_);
lean_closure_set(v___f_2002_, 1, v___f_2001_);
v___f_2003_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_2003_, 0, v___f_2002_);
lean_closure_set(v___f_2003_, 1, v___f_2000_);
lean_closure_set(v___f_2003_, 2, v_val_1995_);
v___f_2004_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_2004_, 0, v___x_1988_);
lean_closure_set(v___f_2004_, 1, v___x_1985_);
lean_closure_set(v___f_2004_, 2, v___f_2003_);
v___x_2005_ = l_IO_Promise_result_x21___redArg(v_a_1989_);
v___x_2006_ = lean_unsigned_to_nat(0u);
v___x_2007_ = 0;
v___x_2008_ = lean_task_map(v___f_1990_, v___x_2005_, v___x_2006_, v___x_2007_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2008_);
v___x_2010_ = v___x_1997_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2008_);
v___x_2010_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2011_; 
v___x_2011_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2006_, v___x_2007_, v___x_2010_, v___f_2004_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; lean_object* v___x_2013_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref_known(v___x_2011_, 1);
v___x_2013_ = lean_task_pure(v_a_2012_);
return v___x_2013_;
}
else
{
lean_object* v_a_2014_; 
v_a_2014_ = lean_ctor_get(v___x_2011_, 0);
lean_inc_ref(v_a_2014_);
lean_dec_ref_known(v___x_2011_, 1);
return v_a_2014_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__6___boxed(lean_object* v___x_2017_, lean_object* v_waiter_2018_, lean_object* v_a_2019_, lean_object* v___x_2020_, lean_object* v_a_2021_, lean_object* v___f_2022_, lean_object* v_a_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__6(v___x_2017_, v_waiter_2018_, v_a_2019_, v___x_2020_, v_a_2021_, v___f_2022_, v_a_2023_);
lean_dec(v_a_2021_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__7(lean_object* v_a_2026_, lean_object* v___f_2027_, lean_object* v___x_2028_, lean_object* v___f_2029_, lean_object* v_x_2030_){
_start:
{
if (lean_obj_tag(v_x_2030_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2040_; 
lean_dec_ref(v___f_2029_);
lean_dec_ref(v___f_2027_);
v_a_2032_ = lean_ctor_get(v_x_2030_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v_x_2030_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2034_ = v_x_2030_;
v_isShared_2035_ = v_isSharedCheck_2040_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v_x_2030_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2040_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2038_; 
v___x_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
return v___x_2038_;
}
}
}
else
{
lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2053_; 
v_isSharedCheck_2053_ = !lean_is_exclusive(v_x_2030_);
if (v_isSharedCheck_2053_ == 0)
{
lean_object* v_unused_2054_; 
v_unused_2054_ = lean_ctor_get(v_x_2030_, 0);
lean_dec(v_unused_2054_);
v___x_2042_ = v_x_2030_;
v_isShared_2043_ = v_isSharedCheck_2053_;
goto v_resetjp_2041_;
}
else
{
lean_dec(v_x_2030_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2053_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2044_ = lean_io_promise_result_opt(v_a_2026_);
v___x_2045_ = lean_unsigned_to_nat(0u);
v___x_2046_ = 0;
v___x_2047_ = lean_io_bind_task(v___x_2044_, v___f_2027_, v___x_2045_, v___x_2046_);
lean_dec_ref(v___x_2047_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v___x_2028_);
v___x_2049_ = v___x_2042_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2028_);
v___x_2049_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2049_);
v___x_2051_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2045_, v___x_2046_, v___x_2050_, v___f_2029_);
return v___x_2051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__7___boxed(lean_object* v_a_2055_, lean_object* v___f_2056_, lean_object* v___x_2057_, lean_object* v___f_2058_, lean_object* v_x_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__7(v_a_2055_, v___f_2056_, v___x_2057_, v___f_2058_, v_x_2059_);
lean_dec(v_a_2055_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__8(lean_object* v_waiter_2062_, lean_object* v_a_2063_, lean_object* v___f_2064_, lean_object* v___x_2065_, lean_object* v___f_2066_, lean_object* v_x_2067_){
_start:
{
if (lean_obj_tag(v_x_2067_) == 0)
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2077_; 
lean_dec_ref(v___f_2066_);
lean_dec_ref(v___f_2064_);
lean_dec_ref(v_a_2063_);
lean_dec_ref(v_waiter_2062_);
v_a_2069_ = lean_ctor_get(v_x_2067_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_x_2067_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2071_ = v_x_2067_;
v_isShared_2072_ = v_isSharedCheck_2077_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v_x_2067_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2077_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
lean_object* v___x_2075_; 
v___x_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2074_);
return v___x_2075_;
}
}
}
else
{
lean_object* v_selector_2078_; lean_object* v_a_2079_; lean_object* v_finished_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2093_; 
v_selector_2078_ = lean_ctor_get(v_a_2063_, 0);
lean_inc_ref(v_selector_2078_);
lean_dec_ref(v_a_2063_);
v_a_2079_ = lean_ctor_get(v_x_2067_, 0);
lean_inc(v_a_2079_);
lean_dec_ref_known(v_x_2067_, 1);
v_finished_2080_ = lean_ctor_get(v_waiter_2062_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v_waiter_2062_);
if (v_isSharedCheck_2093_ == 0)
{
lean_object* v_unused_2094_; 
v_unused_2094_ = lean_ctor_get(v_waiter_2062_, 1);
lean_dec(v_unused_2094_);
v___x_2082_ = v_waiter_2062_;
v_isShared_2083_ = v_isSharedCheck_2093_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_finished_2080_);
lean_dec(v_waiter_2062_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2093_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v_registerFn_2084_; lean_object* v___x_2086_; 
v_registerFn_2084_ = lean_ctor_get(v_selector_2078_, 1);
lean_inc_ref(v_registerFn_2084_);
lean_dec_ref(v_selector_2078_);
lean_inc(v_a_2079_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 1, v_a_2079_);
v___x_2086_ = v___x_2082_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_finished_2080_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_a_2079_);
v___x_2086_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
lean_object* v___x_2087_; lean_object* v___f_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; lean_object* v___x_2091_; 
v___x_2087_ = lean_apply_2(v_registerFn_2084_, v___x_2086_, lean_box(0));
v___f_2088_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_2088_, 0, v_a_2079_);
lean_closure_set(v___f_2088_, 1, v___f_2064_);
lean_closure_set(v___f_2088_, 2, v___x_2065_);
lean_closure_set(v___f_2088_, 3, v___f_2066_);
v___x_2089_ = lean_unsigned_to_nat(0u);
v___x_2090_ = 0;
v___x_2091_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2089_, v___x_2090_, v___x_2087_, v___f_2088_);
return v___x_2091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__8___boxed(lean_object* v_waiter_2095_, lean_object* v_a_2096_, lean_object* v___f_2097_, lean_object* v___x_2098_, lean_object* v___f_2099_, lean_object* v_x_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__8(v_waiter_2095_, v_a_2096_, v___f_2097_, v___x_2098_, v___f_2099_, v_x_2100_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__9___boxed(lean_object* v_i_2104_, lean_object* v_waiter_2105_, lean_object* v___x_2106_, lean_object* v_a_2107_, lean_object* v_as_2108_, lean_object* v_sz_2109_, lean_object* v_x_2110_, lean_object* v___y_2111_){
_start:
{
size_t v_i_boxed_2112_; size_t v_sz_boxed_2113_; lean_object* v_res_2114_; 
v_i_boxed_2112_ = lean_unbox_usize(v_i_2104_);
lean_dec(v_i_2104_);
v_sz_boxed_2113_ = lean_unbox_usize(v_sz_2109_);
lean_dec(v_sz_2109_);
v_res_2114_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__9(v_i_boxed_2112_, v_waiter_2105_, v___x_2106_, v_a_2107_, v_as_2108_, v_sz_boxed_2113_, v_x_2110_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg(lean_object* v_waiter_2115_, lean_object* v___x_2116_, lean_object* v_a_2117_, lean_object* v_as_2118_, size_t v_sz_2119_, size_t v_i_2120_, lean_object* v_b_2121_){
_start:
{
uint8_t v___x_2123_; 
v___x_2123_ = lean_usize_dec_lt(v_i_2120_, v_sz_2119_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
lean_dec_ref(v_as_2118_);
lean_dec(v_a_2117_);
lean_dec_ref(v___x_2116_);
lean_dec_ref(v_waiter_2115_);
v___x_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2124_, 0, v_b_2121_);
v___x_2125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
return v___x_2125_;
}
else
{
lean_object* v___x_2126_; lean_object* v___f_2127_; lean_object* v___x_2128_; lean_object* v___f_2129_; lean_object* v_a_2130_; lean_object* v___f_2131_; lean_object* v___f_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; uint8_t v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___f_2140_; lean_object* v___x_2141_; 
v___x_2126_ = lean_io_promise_new();
v___f_2127_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___closed__0));
v___x_2128_ = lean_box(0);
v___f_2129_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___closed__0));
v_a_2130_ = lean_array_uget_borrowed(v_as_2118_, v_i_2120_);
lean_inc(v_a_2117_);
lean_inc_ref(v___x_2116_);
lean_inc_n(v_a_2130_, 2);
lean_inc_ref_n(v_waiter_2115_, 2);
v___f_2131_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__6___boxed), 8, 6);
lean_closure_set(v___f_2131_, 0, v___x_2128_);
lean_closure_set(v___f_2131_, 1, v_waiter_2115_);
lean_closure_set(v___f_2131_, 2, v_a_2130_);
lean_closure_set(v___f_2131_, 3, v___x_2116_);
lean_closure_set(v___f_2131_, 4, v_a_2117_);
lean_closure_set(v___f_2131_, 5, v___f_2127_);
v___f_2132_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__8___boxed), 7, 5);
lean_closure_set(v___f_2132_, 0, v_waiter_2115_);
lean_closure_set(v___f_2132_, 1, v_a_2130_);
lean_closure_set(v___f_2132_, 2, v___f_2131_);
lean_closure_set(v___f_2132_, 3, v___x_2128_);
lean_closure_set(v___f_2132_, 4, v___f_2129_);
v___x_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2126_);
v___x_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
v___x_2135_ = lean_unsigned_to_nat(0u);
v___x_2136_ = 0;
v___x_2137_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2135_, v___x_2136_, v___x_2134_, v___f_2132_);
v___x_2138_ = lean_box_usize(v_i_2120_);
v___x_2139_ = lean_box_usize(v_sz_2119_);
v___f_2140_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__9___boxed), 8, 6);
lean_closure_set(v___f_2140_, 0, v___x_2138_);
lean_closure_set(v___f_2140_, 1, v_waiter_2115_);
lean_closure_set(v___f_2140_, 2, v___x_2116_);
lean_closure_set(v___f_2140_, 3, v_a_2117_);
lean_closure_set(v___f_2140_, 4, v_as_2118_);
lean_closure_set(v___f_2140_, 5, v___x_2139_);
v___x_2141_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2135_, v___x_2136_, v___x_2137_, v___f_2140_);
return v___x_2141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__9(size_t v_i_2142_, lean_object* v_waiter_2143_, lean_object* v___x_2144_, lean_object* v_a_2145_, lean_object* v_as_2146_, size_t v_sz_2147_, lean_object* v_x_2148_){
_start:
{
if (lean_obj_tag(v_x_2148_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2158_; 
lean_dec_ref(v_as_2146_);
lean_dec(v_a_2145_);
lean_dec_ref(v___x_2144_);
lean_dec_ref(v_waiter_2143_);
v_a_2150_ = lean_ctor_get(v_x_2148_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_x_2148_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2152_ = v_x_2148_;
v_isShared_2153_ = v_isSharedCheck_2158_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v_x_2148_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2158_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2150_);
v___x_2155_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
lean_object* v___x_2156_; 
v___x_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2155_);
return v___x_2156_;
}
}
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2178_; 
v_a_2159_ = lean_ctor_get(v_x_2148_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v_x_2148_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2161_ = v_x_2148_;
v_isShared_2162_ = v_isSharedCheck_2178_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v_x_2148_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2178_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
if (lean_obj_tag(v_a_2159_) == 0)
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2173_; 
lean_dec_ref(v_as_2146_);
lean_dec(v_a_2145_);
lean_dec_ref(v___x_2144_);
lean_dec_ref(v_waiter_2143_);
v_a_2163_ = lean_ctor_get(v_a_2159_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_a_2159_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2165_ = v_a_2159_;
v_isShared_2166_ = v_isSharedCheck_2173_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v_a_2159_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2173_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 0, v_a_2163_);
v___x_2168_ = v___x_2161_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2163_);
v___x_2168_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
lean_object* v___x_2170_; 
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 0, v___x_2168_);
v___x_2170_ = v___x_2165_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
else
{
lean_object* v_a_2174_; size_t v___x_2175_; size_t v___x_2176_; lean_object* v___x_2177_; 
lean_del_object(v___x_2161_);
v_a_2174_ = lean_ctor_get(v_a_2159_, 0);
lean_inc(v_a_2174_);
lean_dec_ref_known(v_a_2159_, 1);
v___x_2175_ = ((size_t)1ULL);
v___x_2176_ = lean_usize_add(v_i_2142_, v___x_2175_);
v___x_2177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg(v_waiter_2143_, v___x_2144_, v_a_2145_, v_as_2146_, v_sz_2147_, v___x_2176_, v_a_2174_);
return v___x_2177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___boxed(lean_object* v_waiter_2179_, lean_object* v___x_2180_, lean_object* v_a_2181_, lean_object* v_as_2182_, lean_object* v_sz_2183_, lean_object* v_i_2184_, lean_object* v_b_2185_, lean_object* v___y_2186_){
_start:
{
size_t v_sz_boxed_2187_; size_t v_i_boxed_2188_; lean_object* v_res_2189_; 
v_sz_boxed_2187_ = lean_unbox_usize(v_sz_2183_);
lean_dec(v_sz_2183_);
v_i_boxed_2188_ = lean_unbox_usize(v_i_2184_);
lean_dec(v_i_2184_);
v_res_2189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg(v_waiter_2179_, v___x_2180_, v_a_2181_, v_as_2182_, v_sz_boxed_2187_, v_i_boxed_2188_, v_b_2185_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__3(lean_object* v_selectables_2190_, lean_object* v_waiter_2191_, lean_object* v_a_2192_, lean_object* v___f_2193_, lean_object* v_x_2194_){
_start:
{
if (lean_obj_tag(v_x_2194_) == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2204_; 
lean_dec_ref(v___f_2193_);
lean_dec(v_a_2192_);
lean_dec_ref(v_waiter_2191_);
lean_dec_ref(v_selectables_2190_);
v_a_2196_ = lean_ctor_get(v_x_2194_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v_x_2194_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2198_ = v_x_2194_;
v_isShared_2199_ = v_isSharedCheck_2204_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v_x_2194_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2204_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2196_);
v___x_2201_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
lean_object* v___x_2202_; 
v___x_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
return v___x_2202_;
}
}
}
else
{
lean_object* v_a_2205_; uint64_t v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; size_t v_sz_2211_; size_t v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; uint8_t v___x_2215_; lean_object* v___x_2216_; 
v_a_2205_ = lean_ctor_get(v_x_2194_, 0);
lean_inc(v_a_2205_);
lean_dec_ref_known(v_x_2194_, 1);
v___x_2206_ = l_ByteArray_toUInt64LE_x21(v_a_2205_);
lean_dec(v_a_2205_);
v___x_2207_ = lean_uint64_to_nat(v___x_2206_);
v___x_2208_ = l_mkStdGen(v___x_2207_);
lean_dec(v___x_2207_);
v___x_2209_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(v_selectables_2190_, v___x_2208_);
v___x_2210_ = lean_box(0);
v_sz_2211_ = lean_array_size(v___x_2209_);
v___x_2212_ = ((size_t)0ULL);
lean_inc_ref(v___x_2209_);
v___x_2213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg(v_waiter_2191_, v___x_2209_, v_a_2192_, v___x_2209_, v_sz_2211_, v___x_2212_, v___x_2210_);
v___x_2214_ = lean_unsigned_to_nat(0u);
v___x_2215_ = 0;
v___x_2216_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2214_, v___x_2215_, v___x_2213_, v___f_2193_);
return v___x_2216_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__3___boxed(lean_object* v_selectables_2217_, lean_object* v_waiter_2218_, lean_object* v_a_2219_, lean_object* v___f_2220_, lean_object* v_x_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_Std_Async_Selectable_combine___redArg___lam__3(v_selectables_2217_, v_waiter_2218_, v_a_2219_, v___f_2220_, v_x_2221_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__4(lean_object* v_selectables_2224_, lean_object* v_waiter_2225_, size_t v___x_2226_, lean_object* v_x_2227_){
_start:
{
if (lean_obj_tag(v_x_2227_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2237_; 
lean_dec_ref(v_waiter_2225_);
lean_dec_ref(v_selectables_2224_);
v_a_2229_ = lean_ctor_get(v_x_2227_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_x_2227_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2231_ = v_x_2227_;
v_isShared_2232_ = v_isSharedCheck_2237_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v_x_2227_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2237_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2232_ == 0)
{
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2229_);
v___x_2234_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
lean_object* v___x_2235_; 
v___x_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
return v___x_2235_;
}
}
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2259_; 
v_a_2238_ = lean_ctor_get(v_x_2227_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_x_2227_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2240_ = v_x_2227_;
v_isShared_2241_ = v_isSharedCheck_2259_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v_x_2227_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2259_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___f_2242_; lean_object* v___f_2243_; lean_object* v_val_2245_; lean_object* v___x_2250_; 
lean_inc(v_a_2238_);
v___f_2242_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2242_, 0, v_a_2238_);
v___f_2243_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_2243_, 0, v_selectables_2224_);
lean_closure_set(v___f_2243_, 1, v_waiter_2225_);
lean_closure_set(v___f_2243_, 2, v_a_2238_);
lean_closure_set(v___f_2243_, 3, v___f_2242_);
v___x_2250_ = lean_io_get_random_bytes(v___x_2226_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v_a_2251_; lean_object* v___x_2253_; 
v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
lean_inc(v_a_2251_);
lean_dec_ref_known(v___x_2250_, 1);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 0, v_a_2251_);
v___x_2253_ = v___x_2240_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2251_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
v_val_2245_ = v___x_2253_;
goto v___jp_2244_;
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; 
v_a_2255_ = lean_ctor_get(v___x_2250_, 0);
lean_inc(v_a_2255_);
lean_dec_ref_known(v___x_2250_, 1);
if (v_isShared_2241_ == 0)
{
lean_ctor_set_tag(v___x_2240_, 0);
lean_ctor_set(v___x_2240_, 0, v_a_2255_);
v___x_2257_ = v___x_2240_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2255_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
v_val_2245_ = v___x_2257_;
goto v___jp_2244_;
}
}
v___jp_2244_:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; uint8_t v___x_2248_; lean_object* v___x_2249_; 
v___x_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2246_, 0, v_val_2245_);
v___x_2247_ = lean_unsigned_to_nat(0u);
v___x_2248_ = 0;
v___x_2249_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2247_, v___x_2248_, v___x_2246_, v___f_2243_);
return v___x_2249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__4___boxed(lean_object* v_selectables_2260_, lean_object* v_waiter_2261_, lean_object* v___x_2262_, lean_object* v_x_2263_, lean_object* v___y_2264_){
_start:
{
size_t v___x_8384__boxed_2265_; lean_object* v_res_2266_; 
v___x_8384__boxed_2265_ = lean_unbox_usize(v___x_2262_);
lean_dec(v___x_2262_);
v_res_2266_ = l_Std_Async_Selectable_combine___redArg___lam__4(v_selectables_2260_, v_waiter_2261_, v___x_8384__boxed_2265_, v_x_2263_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__5(lean_object* v_selectables_2267_, size_t v___x_2268_, lean_object* v_waiter_2269_){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___f_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; uint8_t v___x_2277_; lean_object* v___x_2278_; 
v___x_2271_ = lean_io_promise_new();
v___x_2272_ = lean_box_usize(v___x_2268_);
v___f_2273_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_2273_, 0, v_selectables_2267_);
lean_closure_set(v___f_2273_, 1, v_waiter_2269_);
lean_closure_set(v___f_2273_, 2, v___x_2272_);
v___x_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2271_);
v___x_2275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
v___x_2276_ = lean_unsigned_to_nat(0u);
v___x_2277_ = 0;
v___x_2278_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2276_, v___x_2277_, v___x_2275_, v___f_2273_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__5___boxed(lean_object* v_selectables_2279_, lean_object* v___x_2280_, lean_object* v_waiter_2281_, lean_object* v___y_2282_){
_start:
{
size_t v___x_8455__boxed_2283_; lean_object* v_res_2284_; 
v___x_8455__boxed_2283_ = lean_unbox_usize(v___x_2280_);
lean_dec(v___x_2280_);
v_res_2284_ = l_Std_Async_Selectable_combine___redArg___lam__5(v_selectables_2279_, v___x_8455__boxed_2283_, v_waiter_2281_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__6(lean_object* v___x_2285_, lean_object* v_x_2286_){
_start:
{
if (lean_obj_tag(v_x_2286_) == 0)
{
lean_object* v___x_2288_; 
v___x_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2288_, 0, v_x_2286_);
return v___x_2288_;
}
else
{
lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2296_; 
v_isSharedCheck_2296_ = !lean_is_exclusive(v_x_2286_);
if (v_isSharedCheck_2296_ == 0)
{
lean_object* v_unused_2297_; 
v_unused_2297_ = lean_ctor_get(v_x_2286_, 0);
lean_dec(v_unused_2297_);
v___x_2290_ = v_x_2286_;
v_isShared_2291_ = v_isSharedCheck_2296_;
goto v_resetjp_2289_;
}
else
{
lean_dec(v_x_2286_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2296_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 0, v___x_2285_);
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v___x_2285_);
v___x_2293_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
lean_object* v___x_2294_; 
v___x_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
return v___x_2294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__6___boxed(lean_object* v___x_2298_, lean_object* v_x_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Std_Async_Selectable_combine___redArg___lam__6(v___x_2298_, v_x_2299_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__7(lean_object* v_selectables_2302_, size_t v_sz_2303_, size_t v___x_2304_, lean_object* v___x_2305_, lean_object* v___f_2306_){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; lean_object* v___x_2311_; 
v___x_2308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg(v_selectables_2302_, v_sz_2303_, v___x_2304_, v___x_2305_);
v___x_2309_ = lean_unsigned_to_nat(0u);
v___x_2310_ = 0;
v___x_2311_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2309_, v___x_2310_, v___x_2308_, v___f_2306_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__7___boxed(lean_object* v_selectables_2312_, lean_object* v_sz_2313_, lean_object* v___x_2314_, lean_object* v___x_2315_, lean_object* v___f_2316_, lean_object* v___y_2317_){
_start:
{
size_t v_sz_boxed_2318_; size_t v___x_8508__boxed_2319_; lean_object* v_res_2320_; 
v_sz_boxed_2318_ = lean_unbox_usize(v_sz_2313_);
lean_dec(v_sz_2313_);
v___x_8508__boxed_2319_ = lean_unbox_usize(v___x_2314_);
lean_dec(v___x_2314_);
v_res_2320_ = l_Std_Async_Selectable_combine___redArg___lam__7(v_selectables_2312_, v_sz_boxed_2318_, v___x_8508__boxed_2319_, v___x_2315_, v___f_2316_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg(lean_object* v_selectables_2327_){
_start:
{
lean_object* v___f_2329_; lean_object* v___f_2330_; lean_object* v___x_2331_; lean_object* v___f_2332_; lean_object* v___x_2333_; lean_object* v___f_2334_; lean_object* v___x_2335_; lean_object* v___f_2336_; size_t v_sz_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___f_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___f_2329_ = ((lean_object*)(l_Std_Async_Selectable_tryOne___redArg___closed__0));
lean_inc_ref_n(v_selectables_2327_, 2);
v___f_2330_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2330_, 0, v_selectables_2327_);
lean_closure_set(v___f_2330_, 1, v___f_2329_);
v___x_2331_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___boxed__const__2));
v___f_2332_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2332_, 0, v___f_2330_);
lean_closure_set(v___f_2332_, 1, v___x_2331_);
v___x_2333_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___boxed__const__2));
v___f_2334_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_2334_, 0, v_selectables_2327_);
lean_closure_set(v___f_2334_, 1, v___x_2333_);
v___x_2335_ = lean_box(0);
v___f_2336_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___closed__0));
v_sz_2337_ = lean_array_size(v_selectables_2327_);
v___x_2338_ = lean_box_usize(v_sz_2337_);
v___x_2339_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___boxed__const__1));
v___f_2340_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_2340_, 0, v_selectables_2327_);
lean_closure_set(v___f_2340_, 1, v___x_2338_);
lean_closure_set(v___f_2340_, 2, v___x_2339_);
lean_closure_set(v___f_2340_, 3, v___x_2335_);
lean_closure_set(v___f_2340_, 4, v___f_2336_);
v___x_2341_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2341_, 0, v___f_2332_);
lean_ctor_set(v___x_2341_, 1, v___f_2334_);
lean_ctor_set(v___x_2341_, 2, v___f_2340_);
v___x_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___boxed(lean_object* v_selectables_2343_, lean_object* v_a_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Std_Async_Selectable_combine___redArg(v_selectables_2343_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine(lean_object* v_00_u03b1_2346_, lean_object* v_selectables_2347_){
_start:
{
lean_object* v___x_2349_; 
v___x_2349_ = l_Std_Async_Selectable_combine___redArg(v_selectables_2347_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___boxed(lean_object* v_00_u03b1_2350_, lean_object* v_selectables_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Std_Async_Selectable_combine(v_00_u03b1_2350_, v_selectables_2351_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0(lean_object* v_00_u03b1_2354_, lean_object* v_as_2355_, size_t v_sz_2356_, size_t v_i_2357_, lean_object* v_b_2358_){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg(v_as_2355_, v_sz_2356_, v_i_2357_, v_b_2358_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___boxed(lean_object* v_00_u03b1_2361_, lean_object* v_as_2362_, lean_object* v_sz_2363_, lean_object* v_i_2364_, lean_object* v_b_2365_, lean_object* v___y_2366_){
_start:
{
size_t v_sz_boxed_2367_; size_t v_i_boxed_2368_; lean_object* v_res_2369_; 
v_sz_boxed_2367_ = lean_unbox_usize(v_sz_2363_);
lean_dec(v_sz_2363_);
v_i_boxed_2368_ = lean_unbox_usize(v_i_2364_);
lean_dec(v_i_2364_);
v_res_2369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0(v_00_u03b1_2361_, v_as_2362_, v_sz_boxed_2367_, v_i_boxed_2368_, v_b_2365_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1(lean_object* v_00_u03b1_2370_, lean_object* v_waiter_2371_, lean_object* v___x_2372_, lean_object* v_a_2373_, lean_object* v_as_2374_, size_t v_sz_2375_, size_t v_i_2376_, lean_object* v_b_2377_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg(v_waiter_2371_, v___x_2372_, v_a_2373_, v_as_2374_, v_sz_2375_, v_i_2376_, v_b_2377_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___boxed(lean_object* v_00_u03b1_2380_, lean_object* v_waiter_2381_, lean_object* v___x_2382_, lean_object* v_a_2383_, lean_object* v_as_2384_, lean_object* v_sz_2385_, lean_object* v_i_2386_, lean_object* v_b_2387_, lean_object* v___y_2388_){
_start:
{
size_t v_sz_boxed_2389_; size_t v_i_boxed_2390_; lean_object* v_res_2391_; 
v_sz_boxed_2389_ = lean_unbox_usize(v_sz_2385_);
lean_dec(v_sz_2385_);
v_i_boxed_2390_ = lean_unbox_usize(v_i_2386_);
lean_dec(v_i_2386_);
v_res_2391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1(v_00_u03b1_2380_, v_waiter_2381_, v___x_2382_, v_a_2383_, v_as_2384_, v_sz_boxed_2389_, v_i_boxed_2390_, v_b_2387_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2(lean_object* v_00_u03b1_2392_, lean_object* v_as_2393_, size_t v_sz_2394_, size_t v_i_2395_, lean_object* v_b_2396_){
_start:
{
lean_object* v___x_2398_; 
v___x_2398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(v_as_2393_, v_sz_2394_, v_i_2395_, v_b_2396_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___boxed(lean_object* v_00_u03b1_2399_, lean_object* v_as_2400_, lean_object* v_sz_2401_, lean_object* v_i_2402_, lean_object* v_b_2403_, lean_object* v___y_2404_){
_start:
{
size_t v_sz_boxed_2405_; size_t v_i_boxed_2406_; lean_object* v_res_2407_; 
v_sz_boxed_2405_ = lean_unbox_usize(v_sz_2401_);
lean_dec(v_sz_2401_);
v_i_boxed_2406_ = lean_unbox_usize(v_i_2402_);
lean_dec(v_i_2402_);
v_res_2407_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2(v_00_u03b1_2399_, v_as_2400_, v_sz_boxed_2405_, v_i_boxed_2406_, v_b_2403_);
return v_res_2407_;
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
