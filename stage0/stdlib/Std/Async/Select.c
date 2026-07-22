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
size_t lean_array_size(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_io_promise_new();
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_IO_stdGenRef;
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__9(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Selectable_combine___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Selectable_combine___redArg___lam__8___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Async_Selectable_combine___redArg___closed__0 = (const lean_object*)&l_Std_Async_Selectable_combine___redArg___closed__0_value;
static const lean_ctor_object l_Std_Async_Selectable_combine___redArg___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Std_Async_Selectable_combine___redArg___boxed__const__1 = (const lean_object*)&l_Std_Async_Selectable_combine___redArg___boxed__const__1_value;
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
lean_object* v___x_164_; 
lean_dec(v___x_162_);
lean_dec(v_i_159_);
v___x_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_164_, 0, v_xs_157_);
lean_ctor_set(v___x_164_, 1, v_gen_158_);
return v___x_164_;
}
else
{
lean_object* v___x_165_; lean_object* v_fst_166_; lean_object* v_snd_167_; lean_object* v_xs_168_; lean_object* v___x_169_; 
v___x_165_ = l_randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0(v_gen_158_, v_i_159_, v___x_162_);
lean_dec(v___x_162_);
v_fst_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_fst_166_);
v_snd_167_ = lean_ctor_get(v___x_165_, 1);
lean_inc(v_snd_167_);
lean_dec_ref(v___x_165_);
v_xs_168_ = lean_array_swap(v_xs_157_, v_i_159_, v_fst_166_);
lean_dec(v_fst_166_);
v___x_169_ = lean_nat_add(v_i_159_, v___x_161_);
lean_dec(v_i_159_);
v_xs_157_ = v_xs_168_;
v_gen_158_ = v_snd_167_;
v_i_159_ = v___x_169_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Select_0__Std_Async_shuffleIt_go(lean_object* v_00_u03b1_171_, lean_object* v_xs_172_, lean_object* v_gen_173_, lean_object* v_i_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt_go___redArg(v_xs_172_, v_gen_173_, v_i_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Select_0__Std_Async_shuffleIt_go_match__1_splitter___redArg(lean_object* v_x_176_, lean_object* v_h__1_177_){
_start:
{
lean_object* v_fst_178_; lean_object* v_snd_179_; lean_object* v___x_180_; 
v_fst_178_ = lean_ctor_get(v_x_176_, 0);
lean_inc(v_fst_178_);
v_snd_179_ = lean_ctor_get(v_x_176_, 1);
lean_inc(v_snd_179_);
lean_dec_ref(v_x_176_);
v___x_180_ = lean_apply_2(v_h__1_177_, v_fst_178_, v_snd_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Select_0__Std_Async_shuffleIt_go_match__1_splitter(lean_object* v_motive_181_, lean_object* v_x_182_, lean_object* v_h__1_183_){
_start:
{
lean_object* v_fst_184_; lean_object* v_snd_185_; lean_object* v___x_186_; 
v_fst_184_ = lean_ctor_get(v_x_182_, 0);
lean_inc(v_fst_184_);
v_snd_185_ = lean_ctor_get(v_x_182_, 1);
lean_inc(v_snd_185_);
lean_dec_ref(v_x_182_);
v___x_186_ = lean_apply_2(v_h__1_183_, v_fst_184_, v_snd_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(lean_object* v_xs_187_, lean_object* v_gen_188_){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = lean_unsigned_to_nat(0u);
v___x_190_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt_go___redArg(v_xs_187_, v_gen_188_, v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Select_0__Std_Async_shuffleIt(lean_object* v_00_u03b1_191_, lean_object* v_xs_192_, lean_object* v_gen_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(v_xs_192_, v_gen_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___redArg(lean_object* v_e_195_){
_start:
{
if (lean_obj_tag(v_e_195_) == 0)
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_206_; 
v_a_197_ = lean_ctor_get(v_e_195_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v_e_195_);
if (v_isSharedCheck_206_ == 0)
{
v___x_199_ = v_e_195_;
v_isShared_200_ = v_isSharedCheck_206_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v_e_195_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_206_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_201_ = lean_io_error_to_string(v_a_197_);
v___x_202_ = lean_mk_io_user_error(v___x_201_);
if (v_isShared_200_ == 0)
{
lean_ctor_set_tag(v___x_199_, 1);
lean_ctor_set(v___x_199_, 0, v___x_202_);
v___x_204_ = v___x_199_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
else
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
v_a_207_ = lean_ctor_get(v_e_195_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v_e_195_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v_e_195_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v_e_195_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
lean_ctor_set_tag(v___x_209_, 0);
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_a_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___redArg___boxed(lean_object* v_e_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___redArg(v_e_215_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1(lean_object* v_00_u03b1_218_, lean_object* v_e_219_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___redArg(v_e_219_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___boxed(lean_object* v_00_u03b1_222_, lean_object* v_e_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1(v_00_u03b1_222_, v_e_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__0(lean_object* v___x_226_, lean_object* v_x_227_){
_start:
{
if (lean_obj_tag(v_x_227_) == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_mk_io_user_error(v___x_226_);
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
return v___x_229_;
}
else
{
lean_object* v_val_230_; 
lean_dec_ref(v___x_226_);
v_val_230_ = lean_ctor_get(v_x_227_, 0);
lean_inc(v_val_230_);
return v_val_230_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__0___boxed(lean_object* v___x_231_, lean_object* v_x_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Std_Async_Selectable_one___redArg___lam__0(v___x_231_, v_x_232_);
lean_dec(v_x_232_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__1(lean_object* v___f_234_, uint8_t v___x_235_, lean_object* v_x_236_){
_start:
{
if (lean_obj_tag(v_x_236_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_246_; 
lean_dec_ref(v___f_234_);
v_a_238_ = lean_ctor_get(v_x_236_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v_x_236_);
if (v_isSharedCheck_246_ == 0)
{
v___x_240_ = v_x_236_;
v_isShared_241_ = v_isSharedCheck_246_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v_x_236_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_246_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_238_);
v___x_243_ = v_reuseFailAlloc_245_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_244_; 
v___x_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
return v___x_244_;
}
}
}
else
{
lean_object* v_a_247_; 
v_a_247_ = lean_ctor_get(v_x_236_, 0);
lean_inc(v_a_247_);
lean_dec_ref_known(v_x_236_, 1);
if (lean_obj_tag(v_a_247_) == 0)
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_256_; 
lean_dec_ref(v___f_234_);
v_a_248_ = lean_ctor_get(v_a_247_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v_a_247_);
if (v_isSharedCheck_256_ == 0)
{
v___x_250_ = v_a_247_;
v_isShared_251_ = v_isSharedCheck_256_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v_a_247_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_256_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_251_ == 0)
{
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_248_);
v___x_253_ = v_reuseFailAlloc_255_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_254_; 
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
return v___x_254_;
}
}
}
else
{
lean_object* v_a_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v_a_257_ = lean_ctor_get(v_a_247_, 0);
lean_inc(v_a_257_);
lean_dec_ref_known(v_a_247_, 1);
v___x_258_ = lean_io_promise_result_opt(v_a_257_);
lean_dec(v_a_257_);
v___x_259_ = lean_unsigned_to_nat(0u);
v___x_260_ = lean_task_map(v___f_234_, v___x_258_, v___x_259_, v___x_235_);
v___x_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
return v___x_261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__1___boxed(lean_object* v___f_262_, lean_object* v___x_263_, lean_object* v_x_264_, lean_object* v___y_265_){
_start:
{
uint8_t v___x_11687__boxed_266_; lean_object* v_res_267_; 
v___x_11687__boxed_266_ = lean_unbox(v___x_263_);
v_res_267_ = l_Std_Async_Selectable_one___redArg___lam__1(v___f_262_, v___x_11687__boxed_266_, v_x_264_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__2(uint8_t v___x_271_, lean_object* v_x_272_, lean_object* v_x_273_){
_start:
{
if (lean_obj_tag(v_x_273_) == 0)
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_283_; 
lean_dec_ref(v_x_272_);
v_a_275_ = lean_ctor_get(v_x_273_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v_x_273_);
if (v_isSharedCheck_283_ == 0)
{
v___x_277_ = v_x_273_;
v_isShared_278_ = v_isSharedCheck_283_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v_x_273_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_283_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_282_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
lean_object* v___x_281_; 
v___x_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
return v___x_281_;
}
}
}
else
{
lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_296_; 
v_isSharedCheck_296_ = !lean_is_exclusive(v_x_273_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; 
v_unused_297_ = lean_ctor_get(v_x_273_, 0);
lean_dec(v_unused_297_);
v___x_285_ = v_x_273_;
v_isShared_286_ = v_isSharedCheck_296_;
goto v_resetjp_284_;
}
else
{
lean_dec(v_x_273_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_296_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___f_287_; lean_object* v___x_288_; lean_object* v___f_289_; lean_object* v___x_291_; 
v___f_287_ = ((lean_object*)(l_Std_Async_Selectable_one___redArg___lam__2___closed__1));
v___x_288_ = lean_box(v___x_271_);
v___f_289_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_289_, 0, v___f_287_);
lean_closure_set(v___f_289_, 1, v___x_288_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v_x_272_);
v___x_291_ = v___x_285_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_x_272_);
v___x_291_ = v_reuseFailAlloc_295_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_293_, v___x_271_, v___x_292_, v___f_289_);
return v___x_294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__2___boxed(lean_object* v___x_298_, lean_object* v_x_299_, lean_object* v_x_300_, lean_object* v___y_301_){
_start:
{
uint8_t v___x_11752__boxed_302_; lean_object* v_res_303_; 
v___x_11752__boxed_302_ = lean_unbox(v___x_298_);
v_res_303_ = l_Std_Async_Selectable_one___redArg___lam__2(v___x_11752__boxed_302_, v_x_299_, v_x_300_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__3(lean_object* v___x_304_, lean_object* v_a_305_, uint8_t v___x_306_, lean_object* v___f_307_, lean_object* v_x_308_){
_start:
{
if (lean_obj_tag(v_x_308_) == 0)
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_318_; 
lean_dec_ref(v___f_307_);
v_a_310_ = lean_ctor_get(v_x_308_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v_x_308_);
if (v_isSharedCheck_318_ == 0)
{
v___x_312_ = v_x_308_;
v_isShared_313_ = v_isSharedCheck_318_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v_x_308_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_318_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_310_);
v___x_315_ = v_reuseFailAlloc_317_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
lean_object* v___x_316_; 
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
}
}
else
{
lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_329_; 
v_isSharedCheck_329_ = !lean_is_exclusive(v_x_308_);
if (v_isSharedCheck_329_ == 0)
{
lean_object* v_unused_330_; 
v_unused_330_ = lean_ctor_get(v_x_308_, 0);
lean_dec(v_unused_330_);
v___x_320_ = v_x_308_;
v_isShared_321_ = v_isSharedCheck_329_;
goto v_resetjp_319_;
}
else
{
lean_dec(v_x_308_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_329_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_322_ = lean_io_promise_resolve(v___x_304_, v_a_305_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 0, v___x_322_);
v___x_324_ = v___x_320_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_322_);
v___x_324_ = v_reuseFailAlloc_328_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
v___x_326_ = lean_unsigned_to_nat(0u);
v___x_327_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_326_, v___x_306_, v___x_325_, v___f_307_);
return v___x_327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__3___boxed(lean_object* v___x_331_, lean_object* v_a_332_, lean_object* v___x_333_, lean_object* v___f_334_, lean_object* v_x_335_, lean_object* v___y_336_){
_start:
{
uint8_t v___x_11816__boxed_337_; lean_object* v_res_338_; 
v___x_11816__boxed_337_ = lean_unbox(v___x_333_);
v_res_338_ = l_Std_Async_Selectable_one___redArg___lam__3(v___x_331_, v_a_332_, v___x_11816__boxed_337_, v___f_334_, v_x_335_);
lean_dec(v_a_332_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__4(lean_object* v___x_339_, lean_object* v___y_340_){
_start:
{
if (lean_obj_tag(v___y_340_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
v_a_341_ = lean_ctor_get(v___y_340_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___y_340_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___y_340_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___y_340_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
else
{
lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
v_isSharedCheck_355_ = !lean_is_exclusive(v___y_340_);
if (v_isSharedCheck_355_ == 0)
{
lean_object* v_unused_356_; 
v_unused_356_ = lean_ctor_get(v___y_340_, 0);
lean_dec(v_unused_356_);
v___x_350_ = v___y_340_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_dec(v___y_340_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v___x_339_);
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_339_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__2(lean_object* v_a_357_, lean_object* v_x_358_){
_start:
{
if (lean_obj_tag(v_x_358_) == 0)
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_370_; 
v_a_360_ = lean_ctor_get(v_x_358_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v_x_358_);
if (v_isSharedCheck_370_ == 0)
{
v___x_362_ = v_x_358_;
v_isShared_363_ = v_isSharedCheck_370_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v_x_358_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_370_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_369_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_366_ = lean_io_promise_resolve(v___x_365_, v_a_357_);
v___x_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
}
}
else
{
lean_object* v___x_371_; 
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v_x_358_);
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__2___boxed(lean_object* v_a_372_, lean_object* v_x_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__2(v_a_372_, v_x_373_);
lean_dec(v_a_372_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__1(lean_object* v_a_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_377_, 0, v_a_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__0(lean_object* v_a_378_, lean_object* v_x_379_){
_start:
{
if (lean_obj_tag(v_x_379_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_389_; 
v_a_381_ = lean_ctor_get(v_x_379_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v_x_379_);
if (v_isSharedCheck_389_ == 0)
{
v___x_383_ = v_x_379_;
v_isShared_384_ = v_isSharedCheck_389_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v_x_379_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_389_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_381_);
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
else
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_390_ = lean_io_promise_resolve(v_x_379_, v_a_378_);
v___x_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
return v___x_392_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__0___boxed(lean_object* v_a_393_, lean_object* v_x_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__0(v_a_393_, v_x_394_);
lean_dec(v_a_393_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__8(lean_object* v_a_397_, lean_object* v___f_398_, uint8_t v___x_399_, lean_object* v___x_400_, uint8_t v_a_401_, lean_object* v___f_402_, lean_object* v_x_403_){
_start:
{
if (lean_obj_tag(v_x_403_) == 0)
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_413_; 
lean_dec_ref(v___f_402_);
lean_dec_ref(v___f_398_);
v_a_405_ = lean_ctor_get(v_x_403_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v_x_403_);
if (v_isSharedCheck_413_ == 0)
{
v___x_407_ = v_x_403_;
v_isShared_408_ = v_isSharedCheck_413_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v_x_403_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_413_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_412_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_411_; 
v___x_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
return v___x_411_;
}
}
}
else
{
lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_425_; 
v_isSharedCheck_425_ = !lean_is_exclusive(v_x_403_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; 
v_unused_426_ = lean_ctor_get(v_x_403_, 0);
lean_dec(v_unused_426_);
v___x_415_ = v_x_403_;
v_isShared_416_ = v_isSharedCheck_425_;
goto v_resetjp_414_;
}
else
{
lean_dec(v_x_403_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_425_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_417_ = lean_io_promise_result_opt(v_a_397_);
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = lean_io_bind_task(v___x_417_, v___f_398_, v___x_418_, v___x_399_);
lean_dec_ref(v___x_419_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 0, v___x_400_);
v___x_421_ = v___x_415_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_400_);
v___x_421_ = v_reuseFailAlloc_424_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
v___x_423_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_418_, v_a_401_, v___x_422_, v___f_402_);
return v___x_423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__8___boxed(lean_object* v_a_427_, lean_object* v___f_428_, lean_object* v___x_429_, lean_object* v___x_430_, lean_object* v_a_431_, lean_object* v___f_432_, lean_object* v_x_433_, lean_object* v___y_434_){
_start:
{
uint8_t v___x_11986__boxed_435_; uint8_t v_a_11988__boxed_436_; lean_object* v_res_437_; 
v___x_11986__boxed_435_ = lean_unbox(v___x_429_);
v_a_11988__boxed_436_ = lean_unbox(v_a_431_);
v_res_437_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__8(v_a_427_, v___f_428_, v___x_11986__boxed_435_, v___x_430_, v_a_11988__boxed_436_, v___f_432_, v_x_433_);
lean_dec(v_a_427_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__9(lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v___f_440_, uint8_t v___x_441_, lean_object* v___x_442_, uint8_t v_a_443_, lean_object* v___f_444_, lean_object* v_x_445_){
_start:
{
if (lean_obj_tag(v_x_445_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_455_; 
lean_dec_ref(v___f_444_);
lean_dec_ref(v___f_440_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
v_a_447_ = lean_ctor_get(v_x_445_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v_x_445_);
if (v_isSharedCheck_455_ == 0)
{
v___x_449_ = v_x_445_;
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v_x_445_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_454_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_453_; 
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
return v___x_453_;
}
}
}
else
{
lean_object* v_selector_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_471_; 
v_selector_456_ = lean_ctor_get(v_a_438_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v_a_438_);
if (v_isSharedCheck_471_ == 0)
{
lean_object* v_unused_472_; 
v_unused_472_ = lean_ctor_get(v_a_438_, 1);
lean_dec(v_unused_472_);
v___x_458_ = v_a_438_;
v_isShared_459_ = v_isSharedCheck_471_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_selector_456_);
lean_dec(v_a_438_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_471_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v_a_460_; lean_object* v_registerFn_461_; lean_object* v___x_463_; 
v_a_460_ = lean_ctor_get(v_x_445_, 0);
lean_inc_n(v_a_460_, 2);
lean_dec_ref_known(v_x_445_, 1);
v_registerFn_461_ = lean_ctor_get(v_selector_456_, 1);
lean_inc_ref(v_registerFn_461_);
lean_dec_ref(v_selector_456_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 1, v_a_460_);
lean_ctor_set(v___x_458_, 0, v_a_439_);
v___x_463_ = v___x_458_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_439_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_a_460_);
v___x_463_ = v_reuseFailAlloc_470_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___f_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_464_ = lean_apply_2(v_registerFn_461_, v___x_463_, lean_box(0));
v___x_465_ = lean_box(v___x_441_);
v___x_466_ = lean_box(v_a_443_);
v___f_467_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__8___boxed), 8, 6);
lean_closure_set(v___f_467_, 0, v_a_460_);
lean_closure_set(v___f_467_, 1, v___f_440_);
lean_closure_set(v___f_467_, 2, v___x_465_);
lean_closure_set(v___f_467_, 3, v___x_442_);
lean_closure_set(v___f_467_, 4, v___x_466_);
lean_closure_set(v___f_467_, 5, v___f_444_);
v___x_468_ = lean_unsigned_to_nat(0u);
v___x_469_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_468_, v_a_443_, v___x_464_, v___f_467_);
return v___x_469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__9___boxed(lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v___f_475_, lean_object* v___x_476_, lean_object* v___x_477_, lean_object* v_a_478_, lean_object* v___f_479_, lean_object* v_x_480_, lean_object* v___y_481_){
_start:
{
uint8_t v___x_12055__boxed_482_; uint8_t v_a_12057__boxed_483_; lean_object* v_res_484_; 
v___x_12055__boxed_482_ = lean_unbox(v___x_476_);
v_a_12057__boxed_483_ = lean_unbox(v_a_478_);
v_res_484_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__9(v_a_473_, v_a_474_, v___f_475_, v___x_12055__boxed_482_, v___x_477_, v_a_12057__boxed_483_, v___f_479_, v_x_480_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__3(lean_object* v_a_485_, lean_object* v_a_486_, uint8_t v_a_487_, lean_object* v___f_488_, lean_object* v_x_489_){
_start:
{
if (lean_obj_tag(v_x_489_) == 0)
{
lean_object* v___x_491_; 
lean_dec_ref(v___f_488_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v_x_489_);
return v___x_491_;
}
else
{
lean_object* v_cont_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
lean_dec_ref_known(v_x_489_, 1);
v_cont_492_ = lean_ctor_get(v_a_485_, 1);
lean_inc_ref(v_cont_492_);
lean_dec_ref(v_a_485_);
v___x_493_ = lean_apply_2(v_cont_492_, v_a_486_, lean_box(0));
v___x_494_ = lean_unsigned_to_nat(0u);
v___x_495_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_494_, v_a_487_, v___x_493_, v___f_488_);
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__3___boxed(lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v___f_499_, lean_object* v_x_500_, lean_object* v___y_501_){
_start:
{
uint8_t v_a_12126__boxed_502_; lean_object* v_res_503_; 
v_a_12126__boxed_502_ = lean_unbox(v_a_498_);
v_res_503_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__3(v_a_496_, v_a_497_, v_a_12126__boxed_502_, v___f_499_, v_x_500_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__0(lean_object* v___x_504_, lean_object* v_x_505_){
_start:
{
if (lean_obj_tag(v_x_505_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_515_; 
v_a_507_ = lean_ctor_get(v_x_505_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v_x_505_);
if (v_isSharedCheck_515_ == 0)
{
v___x_509_ = v_x_505_;
v_isShared_510_ = v_isSharedCheck_515_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v_x_505_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_515_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_507_);
v___x_512_ = v_reuseFailAlloc_514_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_513_; 
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
return v___x_513_;
}
}
}
else
{
lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_524_; 
v_isSharedCheck_524_ = !lean_is_exclusive(v_x_505_);
if (v_isSharedCheck_524_ == 0)
{
lean_object* v_unused_525_; 
v_unused_525_ = lean_ctor_get(v_x_505_, 0);
lean_dec(v_unused_525_);
v___x_517_ = v_x_505_;
v_isShared_518_ = v_isSharedCheck_524_;
goto v_resetjp_516_;
}
else
{
lean_dec(v_x_505_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_524_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_504_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_519_);
v___x_521_ = v___x_517_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_523_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_522_; 
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
return v___x_522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__0___boxed(lean_object* v___x_526_, lean_object* v_x_527_, lean_object* v___y_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__0(v___x_526_, v_x_527_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__1___boxed(lean_object* v_i_532_, lean_object* v_a_533_, lean_object* v_as_534_, lean_object* v_sz_535_, lean_object* v_x_536_, lean_object* v___y_537_){
_start:
{
size_t v_i_boxed_538_; uint8_t v_a_12199__boxed_539_; size_t v_sz_boxed_540_; lean_object* v_res_541_; 
v_i_boxed_538_ = lean_unbox_usize(v_i_532_);
lean_dec(v_i_532_);
v_a_12199__boxed_539_ = lean_unbox(v_a_533_);
v_sz_boxed_540_ = lean_unbox_usize(v_sz_535_);
lean_dec(v_sz_535_);
v_res_541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__1(v_i_boxed_538_, v_a_12199__boxed_539_, v_as_534_, v_sz_boxed_540_, v_x_536_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg(uint8_t v_a_542_, lean_object* v_as_543_, size_t v_sz_544_, size_t v_i_545_, lean_object* v_b_546_){
_start:
{
uint8_t v___x_548_; 
v___x_548_ = lean_usize_dec_lt(v_i_545_, v_sz_544_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; 
lean_dec_ref(v_as_543_);
v___x_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_549_, 0, v_b_546_);
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
return v___x_550_;
}
else
{
lean_object* v_a_551_; lean_object* v_selector_552_; lean_object* v_unregisterFn_553_; lean_object* v___x_554_; lean_object* v___f_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___f_561_; uint8_t v___x_562_; lean_object* v___x_563_; 
v_a_551_ = lean_array_uget_borrowed(v_as_543_, v_i_545_);
v_selector_552_ = lean_ctor_get(v_a_551_, 0);
v_unregisterFn_553_ = lean_ctor_get(v_selector_552_, 2);
lean_inc_ref(v_unregisterFn_553_);
v___x_554_ = lean_apply_1(v_unregisterFn_553_, lean_box(0));
v___f_555_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___closed__0));
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_556_, v_a_542_, v___x_554_, v___f_555_);
v___x_558_ = lean_box_usize(v_i_545_);
v___x_559_ = lean_box(v_a_542_);
v___x_560_ = lean_box_usize(v_sz_544_);
v___f_561_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__1___boxed), 6, 4);
lean_closure_set(v___f_561_, 0, v___x_558_);
lean_closure_set(v___f_561_, 1, v___x_559_);
lean_closure_set(v___f_561_, 2, v_as_543_);
lean_closure_set(v___f_561_, 3, v___x_560_);
v___x_562_ = 0;
v___x_563_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_556_, v___x_562_, v___x_557_, v___f_561_);
return v___x_563_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__1(size_t v_i_564_, uint8_t v_a_565_, lean_object* v_as_566_, size_t v_sz_567_, lean_object* v_x_568_){
_start:
{
if (lean_obj_tag(v_x_568_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_578_; 
lean_dec_ref(v_as_566_);
v_a_570_ = lean_ctor_get(v_x_568_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v_x_568_);
if (v_isSharedCheck_578_ == 0)
{
v___x_572_ = v_x_568_;
v_isShared_573_ = v_isSharedCheck_578_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v_x_568_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_578_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_577_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_576_; 
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
return v___x_576_;
}
}
}
else
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_598_; 
v_a_579_ = lean_ctor_get(v_x_568_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v_x_568_);
if (v_isSharedCheck_598_ == 0)
{
v___x_581_ = v_x_568_;
v_isShared_582_ = v_isSharedCheck_598_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v_x_568_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_598_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
if (lean_obj_tag(v_a_579_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_593_; 
lean_dec_ref(v_as_566_);
v_a_583_ = lean_ctor_get(v_a_579_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v_a_579_);
if (v_isSharedCheck_593_ == 0)
{
v___x_585_ = v_a_579_;
v_isShared_586_ = v_isSharedCheck_593_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v_a_579_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_593_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v_a_583_);
v___x_588_ = v___x_581_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_592_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_590_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_588_);
v___x_590_ = v___x_585_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
else
{
lean_object* v_a_594_; size_t v___x_595_; size_t v___x_596_; lean_object* v___x_597_; 
lean_del_object(v___x_581_);
v_a_594_ = lean_ctor_get(v_a_579_, 0);
lean_inc(v_a_594_);
lean_dec_ref_known(v_a_579_, 1);
v___x_595_ = ((size_t)1ULL);
v___x_596_ = lean_usize_add(v_i_564_, v___x_595_);
v___x_597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg(v_a_565_, v_as_566_, v_sz_567_, v___x_596_, v_a_594_);
return v___x_597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___boxed(lean_object* v_a_599_, lean_object* v_as_600_, lean_object* v_sz_601_, lean_object* v_i_602_, lean_object* v_b_603_, lean_object* v___y_604_){
_start:
{
uint8_t v_a_12215__boxed_605_; size_t v_sz_boxed_606_; size_t v_i_boxed_607_; lean_object* v_res_608_; 
v_a_12215__boxed_605_ = lean_unbox(v_a_599_);
v_sz_boxed_606_ = lean_unbox_usize(v_sz_601_);
lean_dec(v_sz_601_);
v_i_boxed_607_ = lean_unbox_usize(v_i_602_);
lean_dec(v_i_602_);
v_res_608_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg(v_a_12215__boxed_605_, v_as_600_, v_sz_boxed_606_, v_i_boxed_607_, v_b_603_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__5(lean_object* v_fst_609_, uint8_t v_a_610_, lean_object* v___x_611_, lean_object* v___f_612_, lean_object* v_x_613_){
_start:
{
if (lean_obj_tag(v_x_613_) == 0)
{
lean_object* v___x_615_; 
lean_dec_ref(v___f_612_);
lean_dec_ref(v_fst_609_);
v___x_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_615_, 0, v_x_613_);
return v___x_615_;
}
else
{
size_t v_sz_616_; size_t v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
lean_dec_ref_known(v_x_613_, 1);
v_sz_616_ = lean_array_size(v_fst_609_);
v___x_617_ = ((size_t)0ULL);
v___x_618_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg(v_a_610_, v_fst_609_, v_sz_616_, v___x_617_, v___x_611_);
v___x_619_ = lean_unsigned_to_nat(0u);
v___x_620_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_619_, v_a_610_, v___x_618_, v___f_612_);
return v___x_620_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__5___boxed(lean_object* v_fst_621_, lean_object* v_a_622_, lean_object* v___x_623_, lean_object* v___f_624_, lean_object* v_x_625_, lean_object* v___y_626_){
_start:
{
uint8_t v_a_12303__boxed_627_; lean_object* v_res_628_; 
v_a_12303__boxed_627_ = lean_unbox(v_a_622_);
v_res_628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__5(v_fst_621_, v_a_12303__boxed_627_, v___x_623_, v___f_624_, v_x_625_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__6(lean_object* v_a_629_, uint8_t v_a_630_, lean_object* v___f_631_, lean_object* v_fst_632_, lean_object* v___x_633_, lean_object* v_a_634_, lean_object* v___f_635_, lean_object* v___f_636_, lean_object* v_x_637_){
_start:
{
if (lean_obj_tag(v_x_637_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_647_; 
lean_dec_ref(v___f_636_);
lean_dec_ref(v___f_635_);
lean_dec_ref(v_fst_632_);
lean_dec_ref(v___f_631_);
lean_dec_ref(v_a_629_);
v_a_639_ = lean_ctor_get(v_x_637_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v_x_637_);
if (v_isSharedCheck_647_ == 0)
{
v___x_641_ = v_x_637_;
v_isShared_642_ = v_isSharedCheck_647_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v_x_637_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_647_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_646_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_645_; 
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
return v___x_645_;
}
}
}
else
{
lean_object* v_a_648_; lean_object* v___x_649_; lean_object* v___f_650_; lean_object* v___x_651_; lean_object* v___f_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v_a_648_ = lean_ctor_get(v_x_637_, 0);
lean_inc(v_a_648_);
lean_dec_ref_known(v_x_637_, 1);
v___x_649_ = lean_box(v_a_630_);
v___f_650_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_650_, 0, v_a_629_);
lean_closure_set(v___f_650_, 1, v_a_648_);
lean_closure_set(v___f_650_, 2, v___x_649_);
lean_closure_set(v___f_650_, 3, v___f_631_);
v___x_651_ = lean_box(v_a_630_);
v___f_652_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__5___boxed), 6, 4);
lean_closure_set(v___f_652_, 0, v_fst_632_);
lean_closure_set(v___f_652_, 1, v___x_651_);
lean_closure_set(v___f_652_, 2, v___x_633_);
lean_closure_set(v___f_652_, 3, v___f_650_);
v___x_653_ = lean_io_promise_result_opt(v_a_634_);
v___x_654_ = lean_unsigned_to_nat(0u);
v___x_655_ = lean_task_map(v___f_635_, v___x_653_, v___x_654_, v_a_630_);
v___x_656_ = lean_task_map(v___f_636_, v___x_655_, v___x_654_, v_a_630_);
v___x_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
v___x_658_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_654_, v_a_630_, v___x_657_, v___f_652_);
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__6___boxed(lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v___f_661_, lean_object* v_fst_662_, lean_object* v___x_663_, lean_object* v_a_664_, lean_object* v___f_665_, lean_object* v___f_666_, lean_object* v_x_667_, lean_object* v___y_668_){
_start:
{
uint8_t v_a_12332__boxed_669_; lean_object* v_res_670_; 
v_a_12332__boxed_669_ = lean_unbox(v_a_660_);
v_res_670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__6(v_a_659_, v_a_12332__boxed_669_, v___f_661_, v_fst_662_, v___x_663_, v_a_664_, v___f_665_, v___f_666_, v_x_667_);
lean_dec(v_a_664_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__7(lean_object* v___x_671_, uint8_t v_a_672_, lean_object* v___f_673_, lean_object* v___f_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_val_678_; 
if (lean_obj_tag(v_a_675_) == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; 
lean_dec_ref(v___f_674_);
lean_dec_ref(v___f_673_);
v___x_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_671_);
v___x_687_ = lean_task_pure(v___x_686_);
return v___x_687_;
}
else
{
lean_object* v_val_688_; lean_object* v___x_689_; 
v_val_688_ = lean_ctor_get(v_a_675_, 0);
lean_inc(v_val_688_);
lean_dec_ref_known(v_a_675_, 1);
v___x_689_ = l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___redArg(v_val_688_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set_tag(v___x_692_, 1);
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
v_val_678_ = v___x_695_;
goto v___jp_677_;
}
}
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
v_a_698_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_689_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_689_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
lean_ctor_set_tag(v___x_700_, 0);
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
v_val_678_ = v___x_703_;
goto v___jp_677_;
}
}
}
}
v___jp_677_:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v_val_678_);
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_680_, v_a_672_, v___x_679_, v___f_673_);
v___x_682_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_680_, v_a_672_, v___x_681_, v___f_674_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_684_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_a_683_);
lean_dec_ref_known(v___x_682_, 1);
v___x_684_ = lean_task_pure(v_a_683_);
return v___x_684_;
}
else
{
lean_object* v_a_685_; 
v_a_685_ = lean_ctor_get(v___x_682_, 0);
lean_inc_ref(v_a_685_);
lean_dec_ref_known(v___x_682_, 1);
return v_a_685_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__7___boxed(lean_object* v___x_706_, lean_object* v_a_707_, lean_object* v___f_708_, lean_object* v___f_709_, lean_object* v_a_710_, lean_object* v___y_711_){
_start:
{
uint8_t v_a_12400__boxed_712_; lean_object* v_res_713_; 
v_a_12400__boxed_712_ = lean_unbox(v_a_707_);
v_res_713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__7(v___x_706_, v_a_12400__boxed_712_, v___f_708_, v___f_709_, v_a_710_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__10(lean_object* v_a_714_, lean_object* v___f_715_, lean_object* v_fst_716_, lean_object* v___x_717_, lean_object* v_a_718_, lean_object* v___f_719_, lean_object* v___f_720_, lean_object* v___f_721_, lean_object* v_a_722_, uint8_t v___x_723_, lean_object* v___f_724_, lean_object* v_x_725_){
_start:
{
if (lean_obj_tag(v_x_725_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_735_; 
lean_dec_ref(v___f_724_);
lean_dec(v_a_722_);
lean_dec_ref(v___f_721_);
lean_dec_ref(v___f_720_);
lean_dec_ref(v___f_719_);
lean_dec(v_a_718_);
lean_dec_ref(v_fst_716_);
lean_dec_ref(v___f_715_);
lean_dec_ref(v_a_714_);
v_a_727_ = lean_ctor_get(v_x_725_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v_x_725_);
if (v_isSharedCheck_735_ == 0)
{
v___x_729_ = v_x_725_;
v_isShared_730_ = v_isSharedCheck_735_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v_x_725_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_735_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_734_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_733_; 
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
return v___x_733_;
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_758_; 
v_a_736_ = lean_ctor_get(v_x_725_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v_x_725_);
if (v_isSharedCheck_758_ == 0)
{
v___x_738_ = v_x_725_;
v_isShared_739_ = v_isSharedCheck_758_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v_x_725_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_758_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
uint8_t v___x_740_; 
v___x_740_ = lean_unbox(v_a_736_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; lean_object* v___f_742_; lean_object* v___f_743_; lean_object* v___x_744_; lean_object* v___f_745_; lean_object* v___x_747_; 
v___x_741_ = lean_io_promise_new();
lean_inc_n(v_a_736_, 3);
lean_inc_ref(v_a_714_);
v___f_742_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__6___boxed), 10, 8);
lean_closure_set(v___f_742_, 0, v_a_714_);
lean_closure_set(v___f_742_, 1, v_a_736_);
lean_closure_set(v___f_742_, 2, v___f_715_);
lean_closure_set(v___f_742_, 3, v_fst_716_);
lean_closure_set(v___f_742_, 4, v___x_717_);
lean_closure_set(v___f_742_, 5, v_a_718_);
lean_closure_set(v___f_742_, 6, v___f_719_);
lean_closure_set(v___f_742_, 7, v___f_720_);
v___f_743_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_743_, 0, v___x_717_);
lean_closure_set(v___f_743_, 1, v_a_736_);
lean_closure_set(v___f_743_, 2, v___f_742_);
lean_closure_set(v___f_743_, 3, v___f_721_);
v___x_744_ = lean_box(v___x_723_);
v___f_745_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__9___boxed), 9, 7);
lean_closure_set(v___f_745_, 0, v_a_714_);
lean_closure_set(v___f_745_, 1, v_a_722_);
lean_closure_set(v___f_745_, 2, v___f_743_);
lean_closure_set(v___f_745_, 3, v___x_744_);
lean_closure_set(v___f_745_, 4, v___x_717_);
lean_closure_set(v___f_745_, 5, v_a_736_);
lean_closure_set(v___f_745_, 6, v___f_724_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_741_);
v___x_747_ = v___x_738_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_741_);
v___x_747_ = v_reuseFailAlloc_752_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; lean_object* v___x_751_; 
v___x_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
v___x_749_ = lean_unsigned_to_nat(0u);
v___x_750_ = lean_unbox(v_a_736_);
lean_dec(v_a_736_);
v___x_751_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_749_, v___x_750_, v___x_748_, v___f_745_);
return v___x_751_;
}
}
else
{
lean_object* v___x_753_; lean_object* v___x_755_; 
lean_dec(v_a_736_);
lean_dec_ref(v___f_724_);
lean_dec(v_a_722_);
lean_dec_ref(v___f_721_);
lean_dec_ref(v___f_720_);
lean_dec_ref(v___f_719_);
lean_dec(v_a_718_);
lean_dec_ref(v_fst_716_);
lean_dec_ref(v___f_715_);
lean_dec_ref(v_a_714_);
v___x_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_717_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_753_);
v___x_755_ = v___x_738_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_753_);
v___x_755_ = v_reuseFailAlloc_757_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_756_; 
v___x_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
return v___x_756_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__10___boxed(lean_object* v_a_759_, lean_object* v___f_760_, lean_object* v_fst_761_, lean_object* v___x_762_, lean_object* v_a_763_, lean_object* v___f_764_, lean_object* v___f_765_, lean_object* v___f_766_, lean_object* v_a_767_, lean_object* v___x_768_, lean_object* v___f_769_, lean_object* v_x_770_, lean_object* v___y_771_){
_start:
{
uint8_t v___x_12480__boxed_772_; lean_object* v_res_773_; 
v___x_12480__boxed_772_ = lean_unbox(v___x_768_);
v_res_773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__10(v_a_759_, v___f_760_, v_fst_761_, v___x_762_, v_a_763_, v___f_764_, v___f_765_, v___f_766_, v_a_767_, v___x_12480__boxed_772_, v___f_769_, v_x_770_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__11___boxed(lean_object* v_i_777_, lean_object* v_a_778_, lean_object* v_fst_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_as_782_, lean_object* v_sz_783_, lean_object* v_x_784_, lean_object* v___y_785_){
_start:
{
size_t v_i_boxed_786_; size_t v_sz_boxed_787_; lean_object* v_res_788_; 
v_i_boxed_786_ = lean_unbox_usize(v_i_777_);
lean_dec(v_i_777_);
v_sz_boxed_787_ = lean_unbox_usize(v_sz_783_);
lean_dec(v_sz_783_);
v_res_788_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__11(v_i_boxed_786_, v_a_778_, v_fst_779_, v_a_780_, v_a_781_, v_as_782_, v_sz_boxed_787_, v_x_784_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg(lean_object* v_a_789_, lean_object* v_fst_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_as_793_, size_t v_sz_794_, size_t v_i_795_, lean_object* v_b_796_){
_start:
{
uint8_t v___x_798_; 
v___x_798_ = lean_usize_dec_lt(v_i_795_, v_sz_794_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec_ref(v_as_793_);
lean_dec(v_a_792_);
lean_dec(v_a_791_);
lean_dec_ref(v_fst_790_);
lean_dec(v_a_789_);
v___x_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_799_, 0, v_b_796_);
v___x_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
return v___x_800_;
}
else
{
lean_object* v___x_801_; lean_object* v___f_802_; lean_object* v___f_803_; lean_object* v___f_804_; lean_object* v___x_805_; lean_object* v___f_806_; lean_object* v___f_807_; uint8_t v___x_808_; lean_object* v_a_809_; lean_object* v___x_810_; lean_object* v___f_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___f_818_; lean_object* v___x_819_; 
v___x_801_ = lean_st_ref_get(v_a_792_);
lean_inc_n(v_a_789_, 2);
v___f_802_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_802_, 0, v_a_789_);
v___f_803_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___closed__0));
v___f_804_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_804_, 0, v_a_789_);
v___x_805_ = lean_box(0);
v___f_806_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___closed__0));
v___f_807_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___closed__1));
v___x_808_ = 0;
v_a_809_ = lean_array_uget_borrowed(v_as_793_, v_i_795_);
v___x_810_ = lean_box(v___x_808_);
lean_inc(v_a_792_);
lean_inc(v_a_791_);
lean_inc_ref(v_fst_790_);
lean_inc(v_a_809_);
v___f_811_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__10___boxed), 13, 11);
lean_closure_set(v___f_811_, 0, v_a_809_);
lean_closure_set(v___f_811_, 1, v___f_802_);
lean_closure_set(v___f_811_, 2, v_fst_790_);
lean_closure_set(v___f_811_, 3, v___x_805_);
lean_closure_set(v___f_811_, 4, v_a_791_);
lean_closure_set(v___f_811_, 5, v___f_803_);
lean_closure_set(v___f_811_, 6, v___f_807_);
lean_closure_set(v___f_811_, 7, v___f_804_);
lean_closure_set(v___f_811_, 8, v_a_792_);
lean_closure_set(v___f_811_, 9, v___x_810_);
lean_closure_set(v___f_811_, 10, v___f_806_);
v___x_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_801_);
v___x_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
v___x_814_ = lean_unsigned_to_nat(0u);
v___x_815_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_814_, v___x_808_, v___x_813_, v___f_811_);
v___x_816_ = lean_box_usize(v_i_795_);
v___x_817_ = lean_box_usize(v_sz_794_);
v___f_818_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__11___boxed), 9, 7);
lean_closure_set(v___f_818_, 0, v___x_816_);
lean_closure_set(v___f_818_, 1, v_a_789_);
lean_closure_set(v___f_818_, 2, v_fst_790_);
lean_closure_set(v___f_818_, 3, v_a_791_);
lean_closure_set(v___f_818_, 4, v_a_792_);
lean_closure_set(v___f_818_, 5, v_as_793_);
lean_closure_set(v___f_818_, 6, v___x_817_);
v___x_819_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_814_, v___x_808_, v___x_815_, v___f_818_);
return v___x_819_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__11(size_t v_i_820_, lean_object* v_a_821_, lean_object* v_fst_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_as_825_, size_t v_sz_826_, lean_object* v_x_827_){
_start:
{
if (lean_obj_tag(v_x_827_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_837_; 
lean_dec_ref(v_as_825_);
lean_dec(v_a_824_);
lean_dec(v_a_823_);
lean_dec_ref(v_fst_822_);
lean_dec(v_a_821_);
v_a_829_ = lean_ctor_get(v_x_827_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v_x_827_);
if (v_isSharedCheck_837_ == 0)
{
v___x_831_ = v_x_827_;
v_isShared_832_ = v_isSharedCheck_837_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v_x_827_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_837_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_836_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
lean_object* v___x_835_; 
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
}
}
else
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_857_; 
v_a_838_ = lean_ctor_get(v_x_827_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v_x_827_);
if (v_isSharedCheck_857_ == 0)
{
v___x_840_ = v_x_827_;
v_isShared_841_ = v_isSharedCheck_857_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v_x_827_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_857_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
if (lean_obj_tag(v_a_838_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_852_; 
lean_dec_ref(v_as_825_);
lean_dec(v_a_824_);
lean_dec(v_a_823_);
lean_dec_ref(v_fst_822_);
lean_dec(v_a_821_);
v_a_842_ = lean_ctor_get(v_a_838_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v_a_838_);
if (v_isSharedCheck_852_ == 0)
{
v___x_844_ = v_a_838_;
v_isShared_845_ = v_isSharedCheck_852_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v_a_838_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_852_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v_a_842_);
v___x_847_ = v___x_840_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_851_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_849_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v___x_847_);
v___x_849_ = v___x_844_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_847_);
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
else
{
lean_object* v_a_853_; size_t v___x_854_; size_t v___x_855_; lean_object* v___x_856_; 
lean_del_object(v___x_840_);
v_a_853_ = lean_ctor_get(v_a_838_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v_a_838_, 1);
v___x_854_ = ((size_t)1ULL);
v___x_855_ = lean_usize_add(v_i_820_, v___x_854_);
v___x_856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg(v_a_821_, v_fst_822_, v_a_823_, v_a_824_, v_as_825_, v_sz_826_, v___x_855_, v_a_853_);
return v___x_856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___boxed(lean_object* v_a_858_, lean_object* v_fst_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_as_862_, lean_object* v_sz_863_, lean_object* v_i_864_, lean_object* v_b_865_, lean_object* v___y_866_){
_start:
{
size_t v_sz_boxed_867_; size_t v_i_boxed_868_; lean_object* v_res_869_; 
v_sz_boxed_867_ = lean_unbox_usize(v_sz_863_);
lean_dec(v_sz_863_);
v_i_boxed_868_ = lean_unbox_usize(v_i_864_);
lean_dec(v_i_864_);
v_res_869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg(v_a_858_, v_fst_859_, v_a_860_, v_a_861_, v_as_862_, v_sz_boxed_867_, v_i_boxed_868_, v_b_865_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__4(lean_object* v_fst_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v___x_873_, uint8_t v___x_874_, lean_object* v_x_875_){
_start:
{
if (lean_obj_tag(v_x_875_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_885_; 
lean_dec(v_a_872_);
lean_dec(v_a_871_);
lean_dec_ref(v_fst_870_);
v_a_877_ = lean_ctor_get(v_x_875_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v_x_875_);
if (v_isSharedCheck_885_ == 0)
{
v___x_879_ = v_x_875_;
v_isShared_880_ = v_isSharedCheck_885_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v_x_875_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_885_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_884_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_883_; 
v___x_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
return v___x_883_;
}
}
}
else
{
lean_object* v_a_886_; size_t v_sz_887_; size_t v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___f_891_; lean_object* v___x_892_; lean_object* v___f_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v_a_886_ = lean_ctor_get(v_x_875_, 0);
v_sz_887_ = lean_array_size(v_fst_870_);
v___x_888_ = ((size_t)0ULL);
lean_inc(v_a_871_);
lean_inc_ref(v_fst_870_);
lean_inc(v_a_886_);
v___x_889_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg(v_a_886_, v_fst_870_, v_a_871_, v_a_872_, v_fst_870_, v_sz_887_, v___x_888_, v___x_873_);
v___x_890_ = lean_box(v___x_874_);
v___f_891_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_891_, 0, v___x_890_);
lean_closure_set(v___f_891_, 1, v_x_875_);
v___x_892_ = lean_box(v___x_874_);
v___f_893_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_893_, 0, v___x_873_);
lean_closure_set(v___f_893_, 1, v_a_871_);
lean_closure_set(v___f_893_, 2, v___x_892_);
lean_closure_set(v___f_893_, 3, v___f_891_);
v___x_894_ = lean_unsigned_to_nat(0u);
v___x_895_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_894_, v___x_874_, v___x_889_, v___f_893_);
return v___x_895_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__4___boxed(lean_object* v_fst_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v___x_899_, lean_object* v___x_900_, lean_object* v_x_901_, lean_object* v___y_902_){
_start:
{
uint8_t v___x_12720__boxed_903_; lean_object* v_res_904_; 
v___x_12720__boxed_903_ = lean_unbox(v___x_900_);
v_res_904_ = l_Std_Async_Selectable_one___redArg___lam__4(v_fst_896_, v_a_897_, v_a_898_, v___x_899_, v___x_12720__boxed_903_, v_x_901_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__5(lean_object* v_fst_905_, lean_object* v_a_906_, lean_object* v___x_907_, uint8_t v___x_908_, lean_object* v_x_909_){
_start:
{
if (lean_obj_tag(v_x_909_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_919_; 
lean_dec(v_a_906_);
lean_dec_ref(v_fst_905_);
v_a_911_ = lean_ctor_get(v_x_909_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v_x_909_);
if (v_isSharedCheck_919_ == 0)
{
v___x_913_ = v_x_909_;
v_isShared_914_ = v_isSharedCheck_919_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v_x_909_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_919_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_918_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_917_; 
v___x_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
return v___x_917_;
}
}
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_933_; 
v_a_920_ = lean_ctor_get(v_x_909_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v_x_909_);
if (v_isSharedCheck_933_ == 0)
{
v___x_922_ = v_x_909_;
v_isShared_923_ = v_isSharedCheck_933_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v_x_909_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_933_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___f_926_; lean_object* v___x_928_; 
v___x_924_ = lean_io_promise_new();
v___x_925_ = lean_box(v___x_908_);
v___f_926_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__4___boxed), 7, 5);
lean_closure_set(v___f_926_, 0, v_fst_905_);
lean_closure_set(v___f_926_, 1, v_a_906_);
lean_closure_set(v___f_926_, 2, v_a_920_);
lean_closure_set(v___f_926_, 3, v___x_907_);
lean_closure_set(v___f_926_, 4, v___x_925_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v___x_924_);
v___x_928_ = v___x_922_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_924_);
v___x_928_ = v_reuseFailAlloc_932_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
v___x_930_ = lean_unsigned_to_nat(0u);
v___x_931_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_930_, v___x_908_, v___x_929_, v___f_926_);
return v___x_931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__5___boxed(lean_object* v_fst_934_, lean_object* v_a_935_, lean_object* v___x_936_, lean_object* v___x_937_, lean_object* v_x_938_, lean_object* v___y_939_){
_start:
{
uint8_t v___x_12776__boxed_940_; lean_object* v_res_941_; 
v___x_12776__boxed_940_ = lean_unbox(v___x_937_);
v_res_941_ = l_Std_Async_Selectable_one___redArg___lam__5(v_fst_934_, v_a_935_, v___x_936_, v___x_12776__boxed_940_, v_x_938_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__6(lean_object* v_fst_942_, lean_object* v_a_943_, lean_object* v___x_944_, lean_object* v_x_945_){
_start:
{
if (lean_obj_tag(v_x_945_) == 0)
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_955_; 
lean_dec(v_a_943_);
lean_dec_ref(v_fst_942_);
v_a_947_ = lean_ctor_get(v_x_945_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v_x_945_);
if (v_isSharedCheck_955_ == 0)
{
v___x_949_ = v_x_945_;
v_isShared_950_ = v_isSharedCheck_955_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v_x_945_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_955_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_954_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_953_; 
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
return v___x_953_;
}
}
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_983_; 
v_a_956_ = lean_ctor_get(v_x_945_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v_x_945_);
if (v_isSharedCheck_983_ == 0)
{
v___x_958_ = v_x_945_;
v_isShared_959_ = v_isSharedCheck_983_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v_x_945_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_983_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v_fst_960_; 
v_fst_960_ = lean_ctor_get(v_a_956_, 0);
lean_inc(v_fst_960_);
lean_dec(v_a_956_);
if (lean_obj_tag(v_fst_960_) == 0)
{
uint8_t v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___f_965_; lean_object* v___x_967_; 
v___x_961_ = 0;
v___x_962_ = lean_box(v___x_961_);
v___x_963_ = lean_st_mk_ref(v___x_962_);
v___x_964_ = lean_box(v___x_961_);
v___f_965_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__5___boxed), 6, 4);
lean_closure_set(v___f_965_, 0, v_fst_942_);
lean_closure_set(v___f_965_, 1, v_a_943_);
lean_closure_set(v___f_965_, 2, v___x_944_);
lean_closure_set(v___f_965_, 3, v___x_964_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 0, v___x_963_);
v___x_967_ = v___x_958_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_963_);
v___x_967_ = v_reuseFailAlloc_971_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
v___x_969_ = lean_unsigned_to_nat(0u);
v___x_970_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_969_, v___x_961_, v___x_968_, v___f_965_);
return v___x_970_;
}
}
else
{
lean_object* v_val_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_982_; 
lean_dec(v_a_943_);
lean_dec_ref(v_fst_942_);
v_val_972_ = lean_ctor_get(v_fst_960_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v_fst_960_);
if (v_isSharedCheck_982_ == 0)
{
v___x_974_ = v_fst_960_;
v_isShared_975_ = v_isSharedCheck_982_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_val_972_);
lean_dec(v_fst_960_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_982_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 0, v_val_972_);
v___x_977_ = v___x_958_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_val_972_);
v___x_977_ = v_reuseFailAlloc_981_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_979_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set_tag(v___x_974_, 0);
lean_ctor_set(v___x_974_, 0, v___x_977_);
v___x_979_ = v___x_974_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__6___boxed(lean_object* v_fst_984_, lean_object* v_a_985_, lean_object* v___x_986_, lean_object* v_x_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Std_Async_Selectable_one___redArg___lam__6(v_fst_984_, v_a_985_, v___x_986_, v_x_987_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__1(lean_object* v_a_990_, lean_object* v___f_991_, lean_object* v___x_992_, lean_object* v_x_993_){
_start:
{
if (lean_obj_tag(v_x_993_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1003_; 
lean_dec_ref(v___x_992_);
lean_dec_ref(v___f_991_);
lean_dec_ref(v_a_990_);
v_a_995_ = lean_ctor_get(v_x_993_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_x_993_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_997_ = v_x_993_;
v_isShared_998_ = v_isSharedCheck_1003_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v_x_993_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1003_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1002_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
return v___x_1001_;
}
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1019_; 
v_a_1004_ = lean_ctor_get(v_x_993_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_x_993_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1006_ = v_x_993_;
v_isShared_1007_ = v_isSharedCheck_1019_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v_x_993_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1019_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
if (lean_obj_tag(v_a_1004_) == 1)
{
lean_object* v_val_1008_; lean_object* v_cont_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; lean_object* v___x_1013_; 
lean_del_object(v___x_1006_);
lean_dec_ref(v___x_992_);
v_val_1008_ = lean_ctor_get(v_a_1004_, 0);
lean_inc(v_val_1008_);
lean_dec_ref_known(v_a_1004_, 1);
v_cont_1009_ = lean_ctor_get(v_a_990_, 1);
lean_inc_ref(v_cont_1009_);
lean_dec_ref(v_a_990_);
v___x_1010_ = lean_apply_2(v_cont_1009_, v_val_1008_, lean_box(0));
v___x_1011_ = lean_unsigned_to_nat(0u);
v___x_1012_ = 0;
v___x_1013_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1011_, v___x_1012_, v___x_1010_, v___f_991_);
return v___x_1013_;
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1016_; 
lean_dec(v_a_1004_);
lean_dec_ref(v___f_991_);
lean_dec_ref(v_a_990_);
v___x_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_992_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v___x_1014_);
v___x_1016_ = v___x_1006_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
return v___x_1017_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__1___boxed(lean_object* v_a_1020_, lean_object* v___f_1021_, lean_object* v___x_1022_, lean_object* v_x_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__1(v_a_1020_, v___f_1021_, v___x_1022_, v_x_1023_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__0(lean_object* v___x_1026_, lean_object* v_x_1027_){
_start:
{
if (lean_obj_tag(v_x_1027_) == 0)
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1037_; 
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
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1049_; 
v_a_1038_ = lean_ctor_get(v_x_1027_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_x_1027_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1040_ = v_x_1027_;
v_isShared_1041_ = v_isSharedCheck_1049_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v_x_1027_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1049_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1042_, 0, v_a_1038_);
v___x_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
lean_ctor_set(v___x_1043_, 1, v___x_1026_);
v___x_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v___x_1044_);
v___x_1046_ = v___x_1040_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
return v___x_1047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__0___boxed(lean_object* v___x_1050_, lean_object* v_x_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__0(v___x_1050_, v_x_1051_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__2___boxed(lean_object* v_i_1059_, lean_object* v_as_1060_, lean_object* v_sz_1061_, lean_object* v_x_1062_, lean_object* v___y_1063_){
_start:
{
size_t v_i_boxed_1064_; size_t v_sz_boxed_1065_; lean_object* v_res_1066_; 
v_i_boxed_1064_ = lean_unbox_usize(v_i_1059_);
lean_dec(v_i_1059_);
v_sz_boxed_1065_ = lean_unbox_usize(v_sz_1061_);
lean_dec(v_sz_1061_);
v_res_1066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__2(v_i_boxed_1064_, v_as_1060_, v_sz_boxed_1065_, v_x_1062_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg(lean_object* v_as_1067_, size_t v_sz_1068_, size_t v_i_1069_, lean_object* v_b_1070_){
_start:
{
uint8_t v___x_1072_; 
v___x_1072_ = lean_usize_dec_lt(v_i_1069_, v_sz_1068_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
lean_dec_ref(v_as_1067_);
v___x_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1073_, 0, v_b_1070_);
v___x_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
return v___x_1074_;
}
else
{
lean_object* v_a_1075_; lean_object* v_selector_1076_; lean_object* v_tryFn_1077_; lean_object* v___x_1078_; lean_object* v___f_1079_; lean_object* v___x_1080_; lean_object* v___f_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___f_1087_; lean_object* v___x_1088_; 
lean_dec_ref(v_b_1070_);
v_a_1075_ = lean_array_uget_borrowed(v_as_1067_, v_i_1069_);
v_selector_1076_ = lean_ctor_get(v_a_1075_, 0);
v_tryFn_1077_ = lean_ctor_get(v_selector_1076_, 0);
lean_inc_ref(v_tryFn_1077_);
v___x_1078_ = lean_apply_1(v_tryFn_1077_, lean_box(0));
v___f_1079_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___closed__0));
v___x_1080_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___closed__1));
lean_inc(v_a_1075_);
v___f_1081_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1081_, 0, v_a_1075_);
lean_closure_set(v___f_1081_, 1, v___f_1079_);
lean_closure_set(v___f_1081_, 2, v___x_1080_);
v___x_1082_ = lean_unsigned_to_nat(0u);
v___x_1083_ = 0;
v___x_1084_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1082_, v___x_1083_, v___x_1078_, v___f_1081_);
v___x_1085_ = lean_box_usize(v_i_1069_);
v___x_1086_ = lean_box_usize(v_sz_1068_);
v___f_1087_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_1087_, 0, v___x_1085_);
lean_closure_set(v___f_1087_, 1, v_as_1067_);
lean_closure_set(v___f_1087_, 2, v___x_1086_);
v___x_1088_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1082_, v___x_1083_, v___x_1084_, v___f_1087_);
return v___x_1088_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__2(size_t v_i_1089_, lean_object* v_as_1090_, size_t v_sz_1091_, lean_object* v_x_1092_){
_start:
{
if (lean_obj_tag(v_x_1092_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1102_; 
lean_dec_ref(v_as_1090_);
v_a_1094_ = lean_ctor_get(v_x_1092_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_x_1092_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1096_ = v_x_1092_;
v_isShared_1097_ = v_isSharedCheck_1102_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v_x_1092_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1102_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
lean_object* v___x_1100_; 
v___x_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
return v___x_1100_;
}
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1122_; 
v_a_1103_ = lean_ctor_get(v_x_1092_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_x_1092_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1105_ = v_x_1092_;
v_isShared_1106_ = v_isSharedCheck_1122_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v_x_1092_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1122_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
if (lean_obj_tag(v_a_1103_) == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1117_; 
lean_dec_ref(v_as_1090_);
v_a_1107_ = lean_ctor_get(v_a_1103_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_a_1103_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1109_ = v_a_1103_;
v_isShared_1110_ = v_isSharedCheck_1117_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v_a_1103_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1117_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v_a_1107_);
v___x_1112_ = v___x_1105_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_object* v___x_1114_; 
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1112_);
v___x_1114_ = v___x_1109_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1112_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
else
{
lean_object* v_a_1118_; size_t v___x_1119_; size_t v___x_1120_; lean_object* v___x_1121_; 
lean_del_object(v___x_1105_);
v_a_1118_ = lean_ctor_get(v_a_1103_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v_a_1103_, 1);
v___x_1119_ = ((size_t)1ULL);
v___x_1120_ = lean_usize_add(v_i_1089_, v___x_1119_);
v___x_1121_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg(v_as_1090_, v_sz_1091_, v___x_1120_, v_a_1118_);
return v___x_1121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___boxed(lean_object* v_as_1123_, lean_object* v_sz_1124_, lean_object* v_i_1125_, lean_object* v_b_1126_, lean_object* v___y_1127_){
_start:
{
size_t v_sz_boxed_1128_; size_t v_i_boxed_1129_; lean_object* v_res_1130_; 
v_sz_boxed_1128_ = lean_unbox_usize(v_sz_1124_);
lean_dec(v_sz_1124_);
v_i_boxed_1129_ = lean_unbox_usize(v_i_1125_);
lean_dec(v_i_1125_);
v_res_1130_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg(v_as_1123_, v_sz_boxed_1128_, v_i_boxed_1129_, v_b_1126_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__7(lean_object* v_fst_1131_, lean_object* v_x_1132_){
_start:
{
if (lean_obj_tag(v_x_1132_) == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1142_; 
lean_dec_ref(v_fst_1131_);
v_a_1134_ = lean_ctor_get(v_x_1132_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_x_1132_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1136_ = v_x_1132_;
v_isShared_1137_ = v_isSharedCheck_1142_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v_x_1132_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1142_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
lean_object* v___x_1140_; 
v___x_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
return v___x_1140_;
}
}
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; size_t v_sz_1146_; size_t v___x_1147_; lean_object* v___x_1148_; lean_object* v___f_1149_; lean_object* v___x_1150_; uint8_t v___x_1151_; lean_object* v___x_1152_; 
v_a_1143_ = lean_ctor_get(v_x_1132_, 0);
lean_inc(v_a_1143_);
lean_dec_ref_known(v_x_1132_, 1);
v___x_1144_ = lean_box(0);
v___x_1145_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___closed__1));
v_sz_1146_ = lean_array_size(v_fst_1131_);
v___x_1147_ = ((size_t)0ULL);
lean_inc_ref(v_fst_1131_);
v___x_1148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg(v_fst_1131_, v_sz_1146_, v___x_1147_, v___x_1145_);
v___f_1149_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__6___boxed), 5, 3);
lean_closure_set(v___f_1149_, 0, v_fst_1131_);
lean_closure_set(v___f_1149_, 1, v_a_1143_);
lean_closure_set(v___f_1149_, 2, v___x_1144_);
v___x_1150_ = lean_unsigned_to_nat(0u);
v___x_1151_ = 0;
v___x_1152_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1150_, v___x_1151_, v___x_1148_, v___f_1149_);
return v___x_1152_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__7___boxed(lean_object* v_fst_1153_, lean_object* v_x_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Std_Async_Selectable_one___redArg___lam__7(v_fst_1153_, v_x_1154_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__8(lean_object* v___f_1157_, lean_object* v_x_1158_){
_start:
{
if (lean_obj_tag(v_x_1158_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1168_; 
lean_dec_ref(v___f_1157_);
v_a_1160_ = lean_ctor_get(v_x_1158_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_x_1158_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1162_ = v_x_1158_;
v_isShared_1163_ = v_isSharedCheck_1168_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v_x_1158_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1168_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
return v___x_1166_;
}
}
}
else
{
lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1180_; 
v_isSharedCheck_1180_ = !lean_is_exclusive(v_x_1158_);
if (v_isSharedCheck_1180_ == 0)
{
lean_object* v_unused_1181_; 
v_unused_1181_ = lean_ctor_get(v_x_1158_, 0);
lean_dec(v_unused_1181_);
v___x_1170_ = v_x_1158_;
v_isShared_1171_ = v_isSharedCheck_1180_;
goto v_resetjp_1169_;
}
else
{
lean_dec(v_x_1158_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1180_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1172_; lean_object* v___x_1174_; 
v___x_1172_ = lean_io_promise_new();
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 0, v___x_1172_);
v___x_1174_ = v___x_1170_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; lean_object* v___x_1178_; 
v___x_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
v___x_1176_ = lean_unsigned_to_nat(0u);
v___x_1177_ = 0;
v___x_1178_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1176_, v___x_1177_, v___x_1175_, v___f_1157_);
return v___x_1178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__8___boxed(lean_object* v___f_1182_, lean_object* v_x_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Std_Async_Selectable_one___redArg___lam__8(v___f_1182_, v_x_1183_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__9(lean_object* v_selectables_1186_, lean_object* v___x_1187_, lean_object* v_x_1188_){
_start:
{
if (lean_obj_tag(v_x_1188_) == 0)
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1198_; 
lean_dec_ref(v_selectables_1186_);
v_a_1190_ = lean_ctor_get(v_x_1188_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_x_1188_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1192_ = v_x_1188_;
v_isShared_1193_ = v_isSharedCheck_1198_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v_x_1188_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1198_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1190_);
v___x_1195_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
return v___x_1196_;
}
}
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1216_; 
v_a_1199_ = lean_ctor_get(v_x_1188_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_x_1188_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1201_ = v_x_1188_;
v_isShared_1202_ = v_isSharedCheck_1216_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v_x_1188_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1216_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v_fst_1204_; lean_object* v_snd_1205_; lean_object* v___x_1206_; lean_object* v___f_1207_; lean_object* v___f_1208_; lean_object* v___x_1210_; 
v___x_1203_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(v_selectables_1186_, v_a_1199_);
v_fst_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_fst_1204_);
v_snd_1205_ = lean_ctor_get(v___x_1203_, 1);
lean_inc(v_snd_1205_);
lean_dec_ref(v___x_1203_);
v___x_1206_ = lean_st_ref_set(v___x_1187_, v_snd_1205_);
v___f_1207_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_1207_, 0, v_fst_1204_);
v___f_1208_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__8___boxed), 3, 1);
lean_closure_set(v___f_1208_, 0, v___f_1207_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1206_);
v___x_1210_ = v___x_1201_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1206_);
v___x_1210_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; uint8_t v___x_1213_; lean_object* v___x_1214_; 
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
v___x_1212_ = lean_unsigned_to_nat(0u);
v___x_1213_ = 0;
v___x_1214_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1212_, v___x_1213_, v___x_1211_, v___f_1208_);
return v___x_1214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__9___boxed(lean_object* v_selectables_1217_, lean_object* v___x_1218_, lean_object* v_x_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Std_Async_Selectable_one___redArg___lam__9(v_selectables_1217_, v___x_1218_, v_x_1219_);
lean_dec(v___x_1218_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__10(lean_object* v_selectables_1222_, lean_object* v_____r_1223_){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___f_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; lean_object* v___x_1232_; 
v___x_1225_ = l_IO_stdGenRef;
v___x_1226_ = lean_st_ref_get(v___x_1225_);
v___f_1227_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__9___boxed), 4, 2);
lean_closure_set(v___f_1227_, 0, v_selectables_1222_);
lean_closure_set(v___f_1227_, 1, v___x_1225_);
v___x_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1226_);
v___x_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
v___x_1230_ = lean_unsigned_to_nat(0u);
v___x_1231_ = 0;
v___x_1232_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1230_, v___x_1231_, v___x_1229_, v___f_1227_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__10___boxed(lean_object* v_selectables_1233_, lean_object* v_____r_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Std_Async_Selectable_one___redArg___lam__10(v_selectables_1233_, v_____r_1234_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__11(lean_object* v___f_1237_, lean_object* v_x_1238_){
_start:
{
if (lean_obj_tag(v_x_1238_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1248_; 
lean_dec_ref(v___f_1237_);
v_a_1240_ = lean_ctor_get(v_x_1238_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v_x_1238_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1242_ = v_x_1238_;
v_isShared_1243_ = v_isSharedCheck_1248_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v_x_1238_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1248_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
lean_object* v___x_1246_; 
v___x_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
return v___x_1246_;
}
}
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1250_; 
v_a_1249_ = lean_ctor_get(v_x_1238_, 0);
lean_inc(v_a_1249_);
lean_dec_ref_known(v_x_1238_, 1);
v___x_1250_ = lean_apply_2(v___f_1237_, v_a_1249_, lean_box(0));
return v___x_1250_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__11___boxed(lean_object* v___f_1251_, lean_object* v_x_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Std_Async_Selectable_one___redArg___lam__11(v___f_1251_, v_x_1252_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg(lean_object* v_selectables_1262_){
_start:
{
lean_object* v___f_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
lean_inc_ref(v_selectables_1262_);
v___f_1264_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__10___boxed), 3, 1);
lean_closure_set(v___f_1264_, 0, v_selectables_1262_);
v___x_1265_ = lean_array_get_size(v_selectables_1262_);
v___x_1266_ = lean_unsigned_to_nat(0u);
v___x_1267_ = lean_nat_dec_eq(v___x_1265_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
lean_dec_ref(v___f_1264_);
v___x_1268_ = lean_box(0);
v___x_1269_ = l_Std_Async_Selectable_one___redArg___lam__10(v_selectables_1262_, v___x_1268_);
return v___x_1269_;
}
else
{
lean_object* v___f_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; lean_object* v___x_1273_; 
lean_dec_ref(v_selectables_1262_);
v___f_1270_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__11___boxed), 3, 1);
lean_closure_set(v___f_1270_, 0, v___f_1264_);
v___x_1271_ = ((lean_object*)(l_Std_Async_Selectable_one___redArg___closed__3));
v___x_1272_ = 0;
v___x_1273_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1266_, v___x_1272_, v___x_1271_, v___f_1270_);
return v___x_1273_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___boxed(lean_object* v_selectables_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Std_Async_Selectable_one___redArg(v_selectables_1274_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one(lean_object* v_00_u03b1_1277_, lean_object* v_selectables_1278_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Std_Async_Selectable_one___redArg(v_selectables_1278_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___boxed(lean_object* v_00_u03b1_1281_, lean_object* v_selectables_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Std_Async_Selectable_one(v_00_u03b1_1281_, v_selectables_1282_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0(lean_object* v_00_u03b1_1285_, uint8_t v_a_1286_, lean_object* v_as_1287_, size_t v_sz_1288_, size_t v_i_1289_, lean_object* v_b_1290_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg(v_a_1286_, v_as_1287_, v_sz_1288_, v_i_1289_, v_b_1290_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___boxed(lean_object* v_00_u03b1_1293_, lean_object* v_a_1294_, lean_object* v_as_1295_, lean_object* v_sz_1296_, lean_object* v_i_1297_, lean_object* v_b_1298_, lean_object* v___y_1299_){
_start:
{
uint8_t v_a_13413__boxed_1300_; size_t v_sz_boxed_1301_; size_t v_i_boxed_1302_; lean_object* v_res_1303_; 
v_a_13413__boxed_1300_ = lean_unbox(v_a_1294_);
v_sz_boxed_1301_ = lean_unbox_usize(v_sz_1296_);
lean_dec(v_sz_1296_);
v_i_boxed_1302_ = lean_unbox_usize(v_i_1297_);
lean_dec(v_i_1297_);
v_res_1303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0(v_00_u03b1_1293_, v_a_13413__boxed_1300_, v_as_1295_, v_sz_boxed_1301_, v_i_boxed_1302_, v_b_1298_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2(lean_object* v_00_u03b1_1304_, lean_object* v_a_1305_, lean_object* v_fst_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_as_1309_, size_t v_sz_1310_, size_t v_i_1311_, lean_object* v_b_1312_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg(v_a_1305_, v_fst_1306_, v_a_1307_, v_a_1308_, v_as_1309_, v_sz_1310_, v_i_1311_, v_b_1312_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___boxed(lean_object* v_00_u03b1_1315_, lean_object* v_a_1316_, lean_object* v_fst_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_as_1320_, lean_object* v_sz_1321_, lean_object* v_i_1322_, lean_object* v_b_1323_, lean_object* v___y_1324_){
_start:
{
size_t v_sz_boxed_1325_; size_t v_i_boxed_1326_; lean_object* v_res_1327_; 
v_sz_boxed_1325_ = lean_unbox_usize(v_sz_1321_);
lean_dec(v_sz_1321_);
v_i_boxed_1326_ = lean_unbox_usize(v_i_1322_);
lean_dec(v_i_1322_);
v_res_1327_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2(v_00_u03b1_1315_, v_a_1316_, v_fst_1317_, v_a_1318_, v_a_1319_, v_as_1320_, v_sz_boxed_1325_, v_i_boxed_1326_, v_b_1323_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3(lean_object* v_00_u03b1_1328_, lean_object* v_as_1329_, size_t v_sz_1330_, size_t v_i_1331_, lean_object* v_b_1332_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg(v_as_1329_, v_sz_1330_, v_i_1331_, v_b_1332_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___boxed(lean_object* v_00_u03b1_1335_, lean_object* v_as_1336_, lean_object* v_sz_1337_, lean_object* v_i_1338_, lean_object* v_b_1339_, lean_object* v___y_1340_){
_start:
{
size_t v_sz_boxed_1341_; size_t v_i_boxed_1342_; lean_object* v_res_1343_; 
v_sz_boxed_1341_ = lean_unbox_usize(v_sz_1337_);
lean_dec(v_sz_1337_);
v_i_boxed_1342_ = lean_unbox_usize(v_i_1338_);
lean_dec(v_i_1338_);
v_res_1343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3(v_00_u03b1_1335_, v_as_1336_, v_sz_boxed_1341_, v_i_boxed_1342_, v_b_1339_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__0(lean_object* v_x_1348_){
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
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1376_; 
v_a_1359_ = lean_ctor_get(v_x_1348_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_x_1348_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1361_ = v_x_1348_;
v_isShared_1362_ = v_isSharedCheck_1376_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v_x_1348_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1376_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v_fst_1363_; 
v_fst_1363_ = lean_ctor_get(v_a_1359_, 0);
lean_inc(v_fst_1363_);
lean_dec(v_a_1359_);
if (lean_obj_tag(v_fst_1363_) == 0)
{
lean_object* v___x_1364_; 
lean_del_object(v___x_1361_);
v___x_1364_ = ((lean_object*)(l_Std_Async_Selectable_tryOne___redArg___lam__0___closed__1));
return v___x_1364_;
}
else
{
lean_object* v_val_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1375_; 
v_val_1365_ = lean_ctor_get(v_fst_1363_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_fst_1363_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1367_ = v_fst_1363_;
v_isShared_1368_ = v_isSharedCheck_1375_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_val_1365_);
lean_dec(v_fst_1363_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1375_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v_val_1365_);
v___x_1370_ = v___x_1361_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_val_1365_);
v___x_1370_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
lean_object* v___x_1372_; 
if (v_isShared_1368_ == 0)
{
lean_ctor_set_tag(v___x_1367_, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1370_);
v___x_1372_ = v___x_1367_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__0___boxed(lean_object* v_x_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Std_Async_Selectable_tryOne___redArg___lam__0(v_x_1377_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__0(lean_object* v___x_1380_, lean_object* v_x_1381_){
_start:
{
if (lean_obj_tag(v_x_1381_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1391_; 
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
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1404_; 
v_a_1392_ = lean_ctor_get(v_x_1381_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_x_1381_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1394_ = v_x_1381_;
v_isShared_1395_ = v_isSharedCheck_1404_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v_x_1381_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1404_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1401_; 
v___x_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1396_, 0, v_a_1392_);
v___x_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
v___x_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
lean_ctor_set(v___x_1398_, 1, v___x_1380_);
v___x_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v___x_1399_);
v___x_1401_ = v___x_1394_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
lean_object* v___x_1402_; 
v___x_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
return v___x_1402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__0___boxed(lean_object* v___x_1405_, lean_object* v_x_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__0(v___x_1405_, v_x_1406_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__1(lean_object* v_a_1409_, lean_object* v___x_1410_, uint8_t v___x_1411_, lean_object* v___f_1412_, lean_object* v___x_1413_, lean_object* v_x_1414_){
_start:
{
if (lean_obj_tag(v_x_1414_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1424_; 
lean_dec_ref(v___x_1413_);
lean_dec_ref(v___f_1412_);
lean_dec(v___x_1410_);
lean_dec_ref(v_a_1409_);
v_a_1416_ = lean_ctor_get(v_x_1414_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_x_1414_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1418_ = v_x_1414_;
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v_x_1414_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1422_; 
v___x_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
return v___x_1422_;
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1438_; 
v_a_1425_ = lean_ctor_get(v_x_1414_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_x_1414_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1427_ = v_x_1414_;
v_isShared_1428_ = v_isSharedCheck_1438_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v_x_1414_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1438_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
if (lean_obj_tag(v_a_1425_) == 1)
{
lean_object* v_val_1429_; lean_object* v_cont_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
lean_del_object(v___x_1427_);
lean_dec_ref(v___x_1413_);
v_val_1429_ = lean_ctor_get(v_a_1425_, 0);
lean_inc(v_val_1429_);
lean_dec_ref_known(v_a_1425_, 1);
v_cont_1430_ = lean_ctor_get(v_a_1409_, 1);
lean_inc_ref(v_cont_1430_);
lean_dec_ref(v_a_1409_);
v___x_1431_ = lean_apply_2(v_cont_1430_, v_val_1429_, lean_box(0));
v___x_1432_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1410_, v___x_1411_, v___x_1431_, v___f_1412_);
return v___x_1432_;
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1435_; 
lean_dec(v_a_1425_);
lean_dec_ref(v___f_1412_);
lean_dec(v___x_1410_);
lean_dec_ref(v_a_1409_);
v___x_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1413_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 0, v___x_1433_);
v___x_1435_ = v___x_1427_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
return v___x_1436_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__1___boxed(lean_object* v_a_1439_, lean_object* v___x_1440_, lean_object* v___x_1441_, lean_object* v___f_1442_, lean_object* v___x_1443_, lean_object* v_x_1444_, lean_object* v___y_1445_){
_start:
{
uint8_t v___x_2726__boxed_1446_; lean_object* v_res_1447_; 
v___x_2726__boxed_1446_ = lean_unbox(v___x_1441_);
v_res_1447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__1(v_a_1439_, v___x_1440_, v___x_2726__boxed_1446_, v___f_1442_, v___x_1443_, v_x_1444_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__2___boxed(lean_object* v_i_1453_, lean_object* v___x_1454_, lean_object* v_as_1455_, lean_object* v_sz_1456_, lean_object* v_x_1457_, lean_object* v___y_1458_){
_start:
{
size_t v_i_boxed_1459_; size_t v_sz_boxed_1460_; lean_object* v_res_1461_; 
v_i_boxed_1459_ = lean_unbox_usize(v_i_1453_);
lean_dec(v_i_1453_);
v_sz_boxed_1460_ = lean_unbox_usize(v_sz_1456_);
lean_dec(v_sz_1456_);
v_res_1461_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__2(v_i_boxed_1459_, v___x_1454_, v_as_1455_, v_sz_boxed_1460_, v_x_1457_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg(lean_object* v___x_1462_, lean_object* v_as_1463_, size_t v_sz_1464_, size_t v_i_1465_, lean_object* v_b_1466_){
_start:
{
uint8_t v___x_1468_; 
v___x_1468_ = lean_usize_dec_lt(v_i_1465_, v_sz_1464_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
lean_dec_ref(v_as_1463_);
lean_dec(v___x_1462_);
v___x_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1469_, 0, v_b_1466_);
v___x_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
return v___x_1470_;
}
else
{
lean_object* v_a_1471_; lean_object* v_selector_1472_; lean_object* v_tryFn_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; uint8_t v___x_1476_; lean_object* v___f_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___f_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___f_1484_; uint8_t v___x_1485_; lean_object* v___x_1486_; 
lean_dec_ref(v_b_1466_);
v_a_1471_ = lean_array_uget_borrowed(v_as_1463_, v_i_1465_);
v_selector_1472_ = lean_ctor_get(v_a_1471_, 0);
v_tryFn_1473_ = lean_ctor_get(v_selector_1472_, 0);
lean_inc_ref(v_tryFn_1473_);
v___x_1474_ = lean_apply_1(v_tryFn_1473_, lean_box(0));
v___x_1475_ = lean_unsigned_to_nat(0u);
v___x_1476_ = lean_nat_dec_eq(v___x_1462_, v___x_1475_);
v___f_1477_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__0));
v___x_1478_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__1));
v___x_1479_ = lean_box(v___x_1476_);
lean_inc(v_a_1471_);
v___f_1480_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_1480_, 0, v_a_1471_);
lean_closure_set(v___f_1480_, 1, v___x_1475_);
lean_closure_set(v___f_1480_, 2, v___x_1479_);
lean_closure_set(v___f_1480_, 3, v___f_1477_);
lean_closure_set(v___f_1480_, 4, v___x_1478_);
v___x_1481_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1475_, v___x_1476_, v___x_1474_, v___f_1480_);
v___x_1482_ = lean_box_usize(v_i_1465_);
v___x_1483_ = lean_box_usize(v_sz_1464_);
v___f_1484_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_1484_, 0, v___x_1482_);
lean_closure_set(v___f_1484_, 1, v___x_1462_);
lean_closure_set(v___f_1484_, 2, v_as_1463_);
lean_closure_set(v___f_1484_, 3, v___x_1483_);
v___x_1485_ = 0;
v___x_1486_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1475_, v___x_1485_, v___x_1481_, v___f_1484_);
return v___x_1486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__2(size_t v_i_1487_, lean_object* v___x_1488_, lean_object* v_as_1489_, size_t v_sz_1490_, lean_object* v_x_1491_){
_start:
{
if (lean_obj_tag(v_x_1491_) == 0)
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1501_; 
lean_dec_ref(v_as_1489_);
lean_dec(v___x_1488_);
v_a_1493_ = lean_ctor_get(v_x_1491_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_x_1491_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1495_ = v_x_1491_;
v_isShared_1496_ = v_isSharedCheck_1501_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v_x_1491_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1501_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1493_);
v___x_1498_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
return v___x_1499_;
}
}
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1521_; 
v_a_1502_ = lean_ctor_get(v_x_1491_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v_x_1491_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1504_ = v_x_1491_;
v_isShared_1505_ = v_isSharedCheck_1521_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v_x_1491_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1521_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
if (lean_obj_tag(v_a_1502_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1516_; 
lean_dec_ref(v_as_1489_);
lean_dec(v___x_1488_);
v_a_1506_ = lean_ctor_get(v_a_1502_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v_a_1502_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1508_ = v_a_1502_;
v_isShared_1509_ = v_isSharedCheck_1516_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v_a_1502_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1516_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 0, v_a_1506_);
v___x_1511_ = v___x_1504_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1506_);
v___x_1511_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
lean_object* v___x_1513_; 
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 0, v___x_1511_);
v___x_1513_ = v___x_1508_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
else
{
lean_object* v_a_1517_; size_t v___x_1518_; size_t v___x_1519_; lean_object* v___x_1520_; 
lean_del_object(v___x_1504_);
v_a_1517_ = lean_ctor_get(v_a_1502_, 0);
lean_inc(v_a_1517_);
lean_dec_ref_known(v_a_1502_, 1);
v___x_1518_ = ((size_t)1ULL);
v___x_1519_ = lean_usize_add(v_i_1487_, v___x_1518_);
v___x_1520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg(v___x_1488_, v_as_1489_, v_sz_1490_, v___x_1519_, v_a_1517_);
return v___x_1520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___boxed(lean_object* v___x_1522_, lean_object* v_as_1523_, lean_object* v_sz_1524_, lean_object* v_i_1525_, lean_object* v_b_1526_, lean_object* v___y_1527_){
_start:
{
size_t v_sz_boxed_1528_; size_t v_i_boxed_1529_; lean_object* v_res_1530_; 
v_sz_boxed_1528_ = lean_unbox_usize(v_sz_1524_);
lean_dec(v_sz_1524_);
v_i_boxed_1529_ = lean_unbox_usize(v_i_1525_);
lean_dec(v_i_1525_);
v_res_1530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg(v___x_1522_, v_as_1523_, v_sz_boxed_1528_, v_i_boxed_1529_, v_b_1526_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__1(lean_object* v_fst_1531_, lean_object* v___x_1532_, lean_object* v___x_1533_, uint8_t v___x_1534_, lean_object* v___f_1535_, lean_object* v_x_1536_){
_start:
{
if (lean_obj_tag(v_x_1536_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1546_; 
lean_dec_ref(v___f_1535_);
lean_dec(v___x_1533_);
lean_dec(v___x_1532_);
lean_dec_ref(v_fst_1531_);
v_a_1538_ = lean_ctor_get(v_x_1536_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_x_1536_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1540_ = v_x_1536_;
v_isShared_1541_ = v_isSharedCheck_1546_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v_x_1536_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1546_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
return v___x_1544_;
}
}
}
else
{
lean_object* v___x_1547_; size_t v_sz_1548_; size_t v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
lean_dec_ref_known(v_x_1536_, 1);
v___x_1547_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__1));
v_sz_1548_ = lean_array_size(v_fst_1531_);
v___x_1549_ = ((size_t)0ULL);
v___x_1550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg(v___x_1532_, v_fst_1531_, v_sz_1548_, v___x_1549_, v___x_1547_);
v___x_1551_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1533_, v___x_1534_, v___x_1550_, v___f_1535_);
return v___x_1551_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__1___boxed(lean_object* v_fst_1552_, lean_object* v___x_1553_, lean_object* v___x_1554_, lean_object* v___x_1555_, lean_object* v___f_1556_, lean_object* v_x_1557_, lean_object* v___y_1558_){
_start:
{
uint8_t v___x_2913__boxed_1559_; lean_object* v_res_1560_; 
v___x_2913__boxed_1559_ = lean_unbox(v___x_1555_);
v_res_1560_ = l_Std_Async_Selectable_tryOne___redArg___lam__1(v_fst_1552_, v___x_1553_, v___x_1554_, v___x_2913__boxed_1559_, v___f_1556_, v_x_1557_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__2(lean_object* v_selectables_1561_, lean_object* v___x_1562_, lean_object* v___x_1563_, lean_object* v___x_1564_, uint8_t v___x_1565_, lean_object* v___f_1566_, lean_object* v_x_1567_){
_start:
{
if (lean_obj_tag(v_x_1567_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1577_; 
lean_dec_ref(v___f_1566_);
lean_dec(v___x_1564_);
lean_dec(v___x_1563_);
lean_dec_ref(v_selectables_1561_);
v_a_1569_ = lean_ctor_get(v_x_1567_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v_x_1567_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1571_ = v_x_1567_;
v_isShared_1572_ = v_isSharedCheck_1577_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v_x_1567_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1577_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
return v___x_1575_;
}
}
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1593_; 
v_a_1578_ = lean_ctor_get(v_x_1567_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v_x_1567_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1580_ = v_x_1567_;
v_isShared_1581_ = v_isSharedCheck_1593_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v_x_1567_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1593_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1582_; lean_object* v_fst_1583_; lean_object* v_snd_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___f_1587_; lean_object* v___x_1589_; 
v___x_1582_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(v_selectables_1561_, v_a_1578_);
v_fst_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_fst_1583_);
v_snd_1584_ = lean_ctor_get(v___x_1582_, 1);
lean_inc(v_snd_1584_);
lean_dec_ref(v___x_1582_);
v___x_1585_ = lean_st_ref_set(v___x_1562_, v_snd_1584_);
v___x_1586_ = lean_box(v___x_1565_);
lean_inc(v___x_1564_);
v___f_1587_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_tryOne___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_1587_, 0, v_fst_1583_);
lean_closure_set(v___f_1587_, 1, v___x_1563_);
lean_closure_set(v___f_1587_, 2, v___x_1564_);
lean_closure_set(v___f_1587_, 3, v___x_1586_);
lean_closure_set(v___f_1587_, 4, v___f_1566_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v___x_1585_);
v___x_1589_ = v___x_1580_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1585_);
v___x_1589_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
v___x_1591_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1564_, v___x_1565_, v___x_1590_, v___f_1587_);
return v___x_1591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__2___boxed(lean_object* v_selectables_1594_, lean_object* v___x_1595_, lean_object* v___x_1596_, lean_object* v___x_1597_, lean_object* v___x_1598_, lean_object* v___f_1599_, lean_object* v_x_1600_, lean_object* v___y_1601_){
_start:
{
uint8_t v___x_2963__boxed_1602_; lean_object* v_res_1603_; 
v___x_2963__boxed_1602_ = lean_unbox(v___x_1598_);
v_res_1603_ = l_Std_Async_Selectable_tryOne___redArg___lam__2(v_selectables_1594_, v___x_1595_, v___x_1596_, v___x_1597_, v___x_2963__boxed_1602_, v___f_1599_, v_x_1600_);
lean_dec(v___x_1595_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg(lean_object* v_selectables_1605_){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; uint8_t v___x_1609_; 
v___x_1607_ = lean_array_get_size(v_selectables_1605_);
v___x_1608_ = lean_unsigned_to_nat(0u);
v___x_1609_ = lean_nat_dec_eq(v___x_1607_, v___x_1608_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___f_1612_; lean_object* v___x_1613_; lean_object* v___f_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1610_ = l_IO_stdGenRef;
v___x_1611_ = lean_st_ref_get(v___x_1610_);
v___f_1612_ = ((lean_object*)(l_Std_Async_Selectable_tryOne___redArg___closed__0));
v___x_1613_ = lean_box(v___x_1609_);
v___f_1614_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_tryOne___redArg___lam__2___boxed), 8, 6);
lean_closure_set(v___f_1614_, 0, v_selectables_1605_);
lean_closure_set(v___f_1614_, 1, v___x_1610_);
lean_closure_set(v___f_1614_, 2, v___x_1607_);
lean_closure_set(v___f_1614_, 3, v___x_1608_);
lean_closure_set(v___f_1614_, 4, v___x_1613_);
lean_closure_set(v___f_1614_, 5, v___f_1612_);
v___x_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1611_);
v___x_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
v___x_1617_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1608_, v___x_1609_, v___x_1616_, v___f_1614_);
return v___x_1617_;
}
else
{
lean_object* v___x_1618_; 
lean_dec_ref(v_selectables_1605_);
v___x_1618_ = ((lean_object*)(l_Std_Async_Selectable_tryOne___redArg___lam__0___closed__1));
return v___x_1618_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___boxed(lean_object* v_selectables_1619_, lean_object* v_a_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Std_Async_Selectable_tryOne___redArg(v_selectables_1619_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne(lean_object* v_00_u03b1_1622_, lean_object* v_selectables_1623_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Std_Async_Selectable_tryOne___redArg(v_selectables_1623_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___boxed(lean_object* v_00_u03b1_1626_, lean_object* v_selectables_1627_, lean_object* v_a_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Std_Async_Selectable_tryOne(v_00_u03b1_1626_, v_selectables_1627_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0(lean_object* v_00_u03b1_1630_, lean_object* v___x_1631_, lean_object* v_as_1632_, size_t v_sz_1633_, size_t v_i_1634_, lean_object* v_b_1635_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg(v___x_1631_, v_as_1632_, v_sz_1633_, v_i_1634_, v_b_1635_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___boxed(lean_object* v_00_u03b1_1638_, lean_object* v___x_1639_, lean_object* v_as_1640_, lean_object* v_sz_1641_, lean_object* v_i_1642_, lean_object* v_b_1643_, lean_object* v___y_1644_){
_start:
{
size_t v_sz_boxed_1645_; size_t v_i_boxed_1646_; lean_object* v_res_1647_; 
v_sz_boxed_1645_ = lean_unbox_usize(v_sz_1641_);
lean_dec(v_sz_1641_);
v_i_boxed_1646_ = lean_unbox_usize(v_i_1642_);
lean_dec(v_i_1642_);
v_res_1647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0(v_00_u03b1_1638_, v___x_1639_, v_as_1640_, v_sz_boxed_1645_, v_i_boxed_1646_, v_b_1643_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1(lean_object* v_a_1648_, lean_object* v___f_1649_, lean_object* v___x_1650_, lean_object* v_x_1651_){
_start:
{
if (lean_obj_tag(v_x_1651_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1661_; 
lean_dec_ref(v___x_1650_);
lean_dec_ref(v___f_1649_);
lean_dec_ref(v_a_1648_);
v_a_1653_ = lean_ctor_get(v_x_1651_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v_x_1651_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1655_ = v_x_1651_;
v_isShared_1656_ = v_isSharedCheck_1661_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v_x_1651_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1661_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
lean_object* v___x_1659_; 
v___x_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
return v___x_1659_;
}
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1677_; 
v_a_1662_ = lean_ctor_get(v_x_1651_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_x_1651_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1664_ = v_x_1651_;
v_isShared_1665_ = v_isSharedCheck_1677_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v_x_1651_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1677_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
if (lean_obj_tag(v_a_1662_) == 1)
{
lean_object* v_val_1666_; lean_object* v_cont_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; uint8_t v___x_1670_; lean_object* v___x_1671_; 
lean_del_object(v___x_1664_);
lean_dec_ref(v___x_1650_);
v_val_1666_ = lean_ctor_get(v_a_1662_, 0);
lean_inc(v_val_1666_);
lean_dec_ref_known(v_a_1662_, 1);
v_cont_1667_ = lean_ctor_get(v_a_1648_, 1);
lean_inc_ref(v_cont_1667_);
lean_dec_ref(v_a_1648_);
v___x_1668_ = lean_apply_2(v_cont_1667_, v_val_1666_, lean_box(0));
v___x_1669_ = lean_unsigned_to_nat(0u);
v___x_1670_ = 0;
v___x_1671_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1669_, v___x_1670_, v___x_1668_, v___f_1649_);
return v___x_1671_;
}
else
{
lean_object* v___x_1672_; lean_object* v___x_1674_; 
lean_dec(v_a_1662_);
lean_dec_ref(v___f_1649_);
lean_dec_ref(v_a_1648_);
v___x_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1650_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1672_);
v___x_1674_ = v___x_1664_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
lean_object* v___x_1675_; 
v___x_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
return v___x_1675_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1___boxed(lean_object* v_a_1678_, lean_object* v___f_1679_, lean_object* v___x_1680_, lean_object* v_x_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1(v_a_1678_, v___f_1679_, v___x_1680_, v_x_1681_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0___boxed(lean_object* v_i_1684_, lean_object* v_as_1685_, lean_object* v_sz_1686_, lean_object* v_x_1687_, lean_object* v___y_1688_){
_start:
{
size_t v_i_boxed_1689_; size_t v_sz_boxed_1690_; lean_object* v_res_1691_; 
v_i_boxed_1689_ = lean_unbox_usize(v_i_1684_);
lean_dec(v_i_1684_);
v_sz_boxed_1690_ = lean_unbox_usize(v_sz_1686_);
lean_dec(v_sz_1686_);
v_res_1691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0(v_i_boxed_1689_, v_as_1685_, v_sz_boxed_1690_, v_x_1687_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(lean_object* v_as_1692_, size_t v_sz_1693_, size_t v_i_1694_, lean_object* v_b_1695_){
_start:
{
uint8_t v___x_1697_; 
v___x_1697_ = lean_usize_dec_lt(v_i_1694_, v_sz_1693_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
lean_dec_ref(v_as_1692_);
v___x_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1698_, 0, v_b_1695_);
v___x_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
return v___x_1699_;
}
else
{
lean_object* v_a_1700_; lean_object* v_selector_1701_; lean_object* v_tryFn_1702_; lean_object* v___x_1703_; lean_object* v___f_1704_; lean_object* v___x_1705_; lean_object* v___f_1706_; lean_object* v___x_1707_; uint8_t v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___f_1712_; lean_object* v___x_1713_; 
lean_dec_ref(v_b_1695_);
v_a_1700_ = lean_array_uget_borrowed(v_as_1692_, v_i_1694_);
v_selector_1701_ = lean_ctor_get(v_a_1700_, 0);
v_tryFn_1702_ = lean_ctor_get(v_selector_1701_, 0);
lean_inc_ref(v_tryFn_1702_);
v___x_1703_ = lean_apply_1(v_tryFn_1702_, lean_box(0));
v___f_1704_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__0));
v___x_1705_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__1));
lean_inc(v_a_1700_);
v___f_1706_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1706_, 0, v_a_1700_);
lean_closure_set(v___f_1706_, 1, v___f_1704_);
lean_closure_set(v___f_1706_, 2, v___x_1705_);
v___x_1707_ = lean_unsigned_to_nat(0u);
v___x_1708_ = 0;
v___x_1709_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1707_, v___x_1708_, v___x_1703_, v___f_1706_);
v___x_1710_ = lean_box_usize(v_i_1694_);
v___x_1711_ = lean_box_usize(v_sz_1693_);
v___f_1712_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1712_, 0, v___x_1710_);
lean_closure_set(v___f_1712_, 1, v_as_1692_);
lean_closure_set(v___f_1712_, 2, v___x_1711_);
v___x_1713_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1707_, v___x_1708_, v___x_1709_, v___f_1712_);
return v___x_1713_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0(size_t v_i_1714_, lean_object* v_as_1715_, size_t v_sz_1716_, lean_object* v_x_1717_){
_start:
{
if (lean_obj_tag(v_x_1717_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1727_; 
lean_dec_ref(v_as_1715_);
v_a_1719_ = lean_ctor_get(v_x_1717_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_x_1717_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1721_ = v_x_1717_;
v_isShared_1722_ = v_isSharedCheck_1727_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v_x_1717_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1727_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1719_);
v___x_1724_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_object* v___x_1725_; 
v___x_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1724_);
return v___x_1725_;
}
}
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1747_; 
v_a_1728_ = lean_ctor_get(v_x_1717_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v_x_1717_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1730_ = v_x_1717_;
v_isShared_1731_ = v_isSharedCheck_1747_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v_x_1717_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1747_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
if (lean_obj_tag(v_a_1728_) == 0)
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1742_; 
lean_dec_ref(v_as_1715_);
v_a_1732_ = lean_ctor_get(v_a_1728_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v_a_1728_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1734_ = v_a_1728_;
v_isShared_1735_ = v_isSharedCheck_1742_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v_a_1728_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1742_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v_a_1732_);
v___x_1737_ = v___x_1730_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
lean_object* v___x_1739_; 
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 0, v___x_1737_);
v___x_1739_ = v___x_1734_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
else
{
lean_object* v_a_1743_; size_t v___x_1744_; size_t v___x_1745_; lean_object* v___x_1746_; 
lean_del_object(v___x_1730_);
v_a_1743_ = lean_ctor_get(v_a_1728_, 0);
lean_inc(v_a_1743_);
lean_dec_ref_known(v_a_1728_, 1);
v___x_1744_ = ((size_t)1ULL);
v___x_1745_ = lean_usize_add(v_i_1714_, v___x_1744_);
v___x_1746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(v_as_1715_, v_sz_1716_, v___x_1745_, v_a_1743_);
return v___x_1746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___boxed(lean_object* v_as_1748_, lean_object* v_sz_1749_, lean_object* v_i_1750_, lean_object* v_b_1751_, lean_object* v___y_1752_){
_start:
{
size_t v_sz_boxed_1753_; size_t v_i_boxed_1754_; lean_object* v_res_1755_; 
v_sz_boxed_1753_ = lean_unbox_usize(v_sz_1749_);
lean_dec(v_sz_1749_);
v_i_boxed_1754_ = lean_unbox_usize(v_i_1750_);
lean_dec(v_i_1750_);
v_res_1755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(v_as_1748_, v_sz_boxed_1753_, v_i_boxed_1754_, v_b_1751_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__1(lean_object* v_fst_1756_, lean_object* v___f_1757_, lean_object* v_x_1758_){
_start:
{
if (lean_obj_tag(v_x_1758_) == 0)
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1768_; 
lean_dec_ref(v___f_1757_);
lean_dec_ref(v_fst_1756_);
v_a_1760_ = lean_ctor_get(v_x_1758_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v_x_1758_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1762_ = v_x_1758_;
v_isShared_1763_ = v_isSharedCheck_1768_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v_x_1758_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1768_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1760_);
v___x_1765_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
lean_object* v___x_1766_; 
v___x_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1765_);
return v___x_1766_;
}
}
}
else
{
lean_object* v___x_1769_; size_t v_sz_1770_; size_t v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; lean_object* v___x_1775_; 
lean_dec_ref_known(v_x_1758_, 1);
v___x_1769_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__1));
v_sz_1770_ = lean_array_size(v_fst_1756_);
v___x_1771_ = ((size_t)0ULL);
v___x_1772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(v_fst_1756_, v_sz_1770_, v___x_1771_, v___x_1769_);
v___x_1773_ = lean_unsigned_to_nat(0u);
v___x_1774_ = 0;
v___x_1775_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1773_, v___x_1774_, v___x_1772_, v___f_1757_);
return v___x_1775_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__1___boxed(lean_object* v_fst_1776_, lean_object* v___f_1777_, lean_object* v_x_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Std_Async_Selectable_combine___redArg___lam__1(v_fst_1776_, v___f_1777_, v_x_1778_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__0(lean_object* v_selectables_1781_, lean_object* v___x_1782_, lean_object* v___f_1783_, lean_object* v_x_1784_){
_start:
{
if (lean_obj_tag(v_x_1784_) == 0)
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1794_; 
lean_dec_ref(v___f_1783_);
lean_dec_ref(v_selectables_1781_);
v_a_1786_ = lean_ctor_get(v_x_1784_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v_x_1784_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1788_ = v_x_1784_;
v_isShared_1789_ = v_isSharedCheck_1794_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v_x_1784_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1794_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1786_);
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
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1811_; 
v_a_1795_ = lean_ctor_get(v_x_1784_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v_x_1784_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1797_ = v_x_1784_;
v_isShared_1798_ = v_isSharedCheck_1811_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v_x_1784_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1811_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1799_; lean_object* v_fst_1800_; lean_object* v_snd_1801_; lean_object* v___x_1802_; lean_object* v___f_1803_; lean_object* v___x_1805_; 
v___x_1799_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(v_selectables_1781_, v_a_1795_);
v_fst_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_fst_1800_);
v_snd_1801_ = lean_ctor_get(v___x_1799_, 1);
lean_inc(v_snd_1801_);
lean_dec_ref(v___x_1799_);
v___x_1802_ = lean_st_ref_set(v___x_1782_, v_snd_1801_);
v___f_1803_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1803_, 0, v_fst_1800_);
lean_closure_set(v___f_1803_, 1, v___f_1783_);
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 0, v___x_1802_);
v___x_1805_ = v___x_1797_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1802_);
v___x_1805_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; lean_object* v___x_1809_; 
v___x_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
v___x_1807_ = lean_unsigned_to_nat(0u);
v___x_1808_ = 0;
v___x_1809_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1807_, v___x_1808_, v___x_1806_, v___f_1803_);
return v___x_1809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__0___boxed(lean_object* v_selectables_1812_, lean_object* v___x_1813_, lean_object* v___f_1814_, lean_object* v_x_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Std_Async_Selectable_combine___redArg___lam__0(v_selectables_1812_, v___x_1813_, v___f_1814_, v_x_1815_);
lean_dec(v___x_1813_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__2(lean_object* v___x_1818_, lean_object* v___f_1819_){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; uint8_t v___x_1825_; lean_object* v___x_1826_; 
v___x_1821_ = lean_st_ref_get(v___x_1818_);
v___x_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
v___x_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
v___x_1824_ = lean_unsigned_to_nat(0u);
v___x_1825_ = 0;
v___x_1826_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1824_, v___x_1825_, v___x_1823_, v___f_1819_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__2___boxed(lean_object* v___x_1827_, lean_object* v___f_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Std_Async_Selectable_combine___redArg___lam__2(v___x_1827_, v___f_1828_);
lean_dec(v___x_1827_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__3(lean_object* v_a_1831_, lean_object* v_x_1832_){
_start:
{
if (lean_obj_tag(v_x_1832_) == 0)
{
lean_object* v___x_1834_; 
v___x_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1834_, 0, v_x_1832_);
return v___x_1834_;
}
else
{
lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1844_; 
v_isSharedCheck_1844_ = !lean_is_exclusive(v_x_1832_);
if (v_isSharedCheck_1844_ == 0)
{
lean_object* v_unused_1845_; 
v_unused_1845_ = lean_ctor_get(v_x_1832_, 0);
lean_dec(v_unused_1845_);
v___x_1836_ = v_x_1832_;
v_isShared_1837_ = v_isSharedCheck_1844_;
goto v_resetjp_1835_;
}
else
{
lean_dec(v_x_1832_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1844_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1841_; 
v___x_1838_ = lean_box(0);
v___x_1839_ = lean_io_promise_resolve(v___x_1838_, v_a_1831_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1839_);
v___x_1841_ = v___x_1836_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_object* v___x_1842_; 
v___x_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
return v___x_1842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__3___boxed(lean_object* v_a_1846_, lean_object* v_x_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Std_Async_Selectable_combine___redArg___lam__3(v_a_1846_, v_x_1847_);
lean_dec(v_a_1846_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__0(lean_object* v_a_1850_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1851_, 0, v_a_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__3(lean_object* v_a_1852_, lean_object* v___f_1853_, lean_object* v_x_1854_){
_start:
{
if (lean_obj_tag(v_x_1854_) == 0)
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1864_; 
lean_dec_ref(v___f_1853_);
lean_dec_ref(v_a_1852_);
v_a_1856_ = lean_ctor_get(v_x_1854_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_x_1854_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1858_ = v_x_1854_;
v_isShared_1859_ = v_isSharedCheck_1864_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v_x_1854_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1864_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1856_);
v___x_1861_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1862_; 
v___x_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
return v___x_1862_;
}
}
}
else
{
lean_object* v_a_1865_; lean_object* v_cont_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; uint8_t v___x_1869_; lean_object* v___x_1870_; 
v_a_1865_ = lean_ctor_get(v_x_1854_, 0);
lean_inc(v_a_1865_);
lean_dec_ref_known(v_x_1854_, 1);
v_cont_1866_ = lean_ctor_get(v_a_1852_, 1);
lean_inc_ref(v_cont_1866_);
lean_dec_ref(v_a_1852_);
v___x_1867_ = lean_apply_2(v_cont_1866_, v_a_1865_, lean_box(0));
v___x_1868_ = lean_unsigned_to_nat(0u);
v___x_1869_ = 0;
v___x_1870_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1868_, v___x_1869_, v___x_1867_, v___f_1853_);
return v___x_1870_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__3___boxed(lean_object* v_a_1871_, lean_object* v___f_1872_, lean_object* v_x_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__3(v_a_1871_, v___f_1872_, v_x_1873_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__2(lean_object* v_promise_1876_, lean_object* v_x_1877_){
_start:
{
if (lean_obj_tag(v_x_1877_) == 0)
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1889_; 
v_a_1879_ = lean_ctor_get(v_x_1877_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v_x_1877_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1881_ = v_x_1877_;
v_isShared_1882_ = v_isSharedCheck_1889_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v_x_1877_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1889_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1885_ = lean_io_promise_resolve(v___x_1884_, v_promise_1876_);
v___x_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
v___x_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
return v___x_1887_;
}
}
}
else
{
lean_object* v___x_1890_; 
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v_x_1877_);
return v___x_1890_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__2___boxed(lean_object* v_promise_1891_, lean_object* v_x_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__2(v_promise_1891_, v_x_1892_);
lean_dec(v_promise_1891_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__4(lean_object* v___f_1895_, lean_object* v___f_1896_, lean_object* v_val_1897_, lean_object* v_x_1898_){
_start:
{
lean_object* v_val_1901_; 
if (lean_obj_tag(v_x_1898_) == 0)
{
lean_object* v___x_1907_; 
lean_dec_ref(v_val_1897_);
lean_dec_ref(v___f_1896_);
lean_dec_ref(v___f_1895_);
v___x_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1907_, 0, v_x_1898_);
return v___x_1907_;
}
else
{
lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1920_; 
v_isSharedCheck_1920_ = !lean_is_exclusive(v_x_1898_);
if (v_isSharedCheck_1920_ == 0)
{
lean_object* v_unused_1921_; 
v_unused_1921_ = lean_ctor_get(v_x_1898_, 0);
lean_dec(v_unused_1921_);
v___x_1909_ = v_x_1898_;
v_isShared_1910_ = v_isSharedCheck_1920_;
goto v_resetjp_1908_;
}
else
{
lean_dec(v_x_1898_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1920_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___redArg(v_val_1897_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1914_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref_known(v___x_1911_, 1);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v_a_1912_);
v___x_1914_ = v___x_1909_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1912_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
v_val_1901_ = v___x_1914_;
goto v___jp_1900_;
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; 
v_a_1916_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1916_);
lean_dec_ref_known(v___x_1911_, 1);
if (v_isShared_1910_ == 0)
{
lean_ctor_set_tag(v___x_1909_, 0);
lean_ctor_set(v___x_1909_, 0, v_a_1916_);
v___x_1918_ = v___x_1909_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1916_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
v_val_1901_ = v___x_1918_;
goto v___jp_1900_;
}
}
}
}
v___jp_1900_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; uint8_t v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1902_, 0, v_val_1901_);
v___x_1903_ = lean_unsigned_to_nat(0u);
v___x_1904_ = 0;
v___x_1905_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1903_, v___x_1904_, v___x_1902_, v___f_1895_);
v___x_1906_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1903_, v___x_1904_, v___x_1905_, v___f_1896_);
return v___x_1906_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__4___boxed(lean_object* v___f_1922_, lean_object* v___f_1923_, lean_object* v_val_1924_, lean_object* v_x_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__4(v___f_1922_, v___f_1923_, v_val_1924_, v_x_1925_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg___lam__1___boxed(lean_object* v_i_1928_, lean_object* v_as_1929_, lean_object* v_sz_1930_, lean_object* v_x_1931_, lean_object* v___y_1932_){
_start:
{
size_t v_i_boxed_1933_; size_t v_sz_boxed_1934_; lean_object* v_res_1935_; 
v_i_boxed_1933_ = lean_unbox_usize(v_i_1928_);
lean_dec(v_i_1928_);
v_sz_boxed_1934_ = lean_unbox_usize(v_sz_1930_);
lean_dec(v_sz_1930_);
v_res_1935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg___lam__1(v_i_boxed_1933_, v_as_1929_, v_sz_boxed_1934_, v_x_1931_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg(lean_object* v_as_1936_, size_t v_sz_1937_, size_t v_i_1938_, lean_object* v_b_1939_){
_start:
{
uint8_t v___x_1941_; 
v___x_1941_ = lean_usize_dec_lt(v_i_1938_, v_sz_1937_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
lean_dec_ref(v_as_1936_);
v___x_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1942_, 0, v_b_1939_);
v___x_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
return v___x_1943_;
}
else
{
lean_object* v_a_1944_; lean_object* v_selector_1945_; lean_object* v_unregisterFn_1946_; lean_object* v___x_1947_; lean_object* v___f_1948_; lean_object* v___x_1949_; uint8_t v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___f_1954_; lean_object* v___x_1955_; 
v_a_1944_ = lean_array_uget_borrowed(v_as_1936_, v_i_1938_);
v_selector_1945_ = lean_ctor_get(v_a_1944_, 0);
v_unregisterFn_1946_ = lean_ctor_get(v_selector_1945_, 2);
lean_inc_ref(v_unregisterFn_1946_);
v___x_1947_ = lean_apply_1(v_unregisterFn_1946_, lean_box(0));
v___f_1948_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___closed__0));
v___x_1949_ = lean_unsigned_to_nat(0u);
v___x_1950_ = 0;
v___x_1951_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1949_, v___x_1950_, v___x_1947_, v___f_1948_);
v___x_1952_ = lean_box_usize(v_i_1938_);
v___x_1953_ = lean_box_usize(v_sz_1937_);
v___f_1954_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1954_, 0, v___x_1952_);
lean_closure_set(v___f_1954_, 1, v_as_1936_);
lean_closure_set(v___f_1954_, 2, v___x_1953_);
v___x_1955_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1949_, v___x_1950_, v___x_1951_, v___f_1954_);
return v___x_1955_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg___lam__1(size_t v_i_1956_, lean_object* v_as_1957_, size_t v_sz_1958_, lean_object* v_x_1959_){
_start:
{
if (lean_obj_tag(v_x_1959_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1969_; 
lean_dec_ref(v_as_1957_);
v_a_1961_ = lean_ctor_get(v_x_1959_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v_x_1959_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1963_ = v_x_1959_;
v_isShared_1964_ = v_isSharedCheck_1969_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v_x_1959_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1969_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
lean_object* v___x_1967_; 
v___x_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1966_);
return v___x_1967_;
}
}
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1989_; 
v_a_1970_ = lean_ctor_get(v_x_1959_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v_x_1959_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1972_ = v_x_1959_;
v_isShared_1973_ = v_isSharedCheck_1989_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v_x_1959_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1989_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
if (lean_obj_tag(v_a_1970_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1984_; 
lean_dec_ref(v_as_1957_);
v_a_1974_ = lean_ctor_get(v_a_1970_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v_a_1970_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1976_ = v_a_1970_;
v_isShared_1977_ = v_isSharedCheck_1984_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v_a_1970_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1984_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v_a_1974_);
v___x_1979_ = v___x_1972_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1981_; 
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v___x_1979_);
v___x_1981_ = v___x_1976_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1979_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
else
{
lean_object* v_a_1985_; size_t v___x_1986_; size_t v___x_1987_; lean_object* v___x_1988_; 
lean_del_object(v___x_1972_);
v_a_1985_ = lean_ctor_get(v_a_1970_, 0);
lean_inc(v_a_1985_);
lean_dec_ref_known(v_a_1970_, 1);
v___x_1986_ = ((size_t)1ULL);
v___x_1987_ = lean_usize_add(v_i_1956_, v___x_1986_);
v___x_1988_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg(v_as_1957_, v_sz_1958_, v___x_1987_, v_a_1985_);
return v___x_1988_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg___boxed(lean_object* v_as_1990_, lean_object* v_sz_1991_, lean_object* v_i_1992_, lean_object* v_b_1993_, lean_object* v___y_1994_){
_start:
{
size_t v_sz_boxed_1995_; size_t v_i_boxed_1996_; lean_object* v_res_1997_; 
v_sz_boxed_1995_ = lean_unbox_usize(v_sz_1991_);
lean_dec(v_sz_1991_);
v_i_boxed_1996_ = lean_unbox_usize(v_i_1992_);
lean_dec(v_i_1992_);
v_res_1997_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg(v_as_1990_, v_sz_boxed_1995_, v_i_boxed_1996_, v_b_1993_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__5(lean_object* v_fst_1998_, lean_object* v___x_1999_, lean_object* v___f_2000_, lean_object* v_x_2001_){
_start:
{
if (lean_obj_tag(v_x_2001_) == 0)
{
lean_object* v___x_2003_; 
lean_dec_ref(v___f_2000_);
lean_dec_ref(v_fst_1998_);
v___x_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2003_, 0, v_x_2001_);
return v___x_2003_;
}
else
{
size_t v_sz_2004_; size_t v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; uint8_t v___x_2008_; lean_object* v___x_2009_; 
lean_dec_ref_known(v_x_2001_, 1);
v_sz_2004_ = lean_array_size(v_fst_1998_);
v___x_2005_ = ((size_t)0ULL);
v___x_2006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg(v_fst_1998_, v_sz_2004_, v___x_2005_, v___x_1999_);
v___x_2007_ = lean_unsigned_to_nat(0u);
v___x_2008_ = 0;
v___x_2009_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2007_, v___x_2008_, v___x_2006_, v___f_2000_);
return v___x_2009_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__5___boxed(lean_object* v_fst_2010_, lean_object* v___x_2011_, lean_object* v___f_2012_, lean_object* v_x_2013_, lean_object* v___y_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__5(v_fst_2010_, v___x_2011_, v___f_2012_, v_x_2013_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__1(lean_object* v_promise_2016_, lean_object* v_x_2017_){
_start:
{
if (lean_obj_tag(v_x_2017_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2027_; 
v_a_2019_ = lean_ctor_get(v_x_2017_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v_x_2017_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2021_ = v_x_2017_;
v_isShared_2022_ = v_isSharedCheck_2027_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v_x_2017_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2027_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
lean_object* v___x_2025_; 
v___x_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2024_);
return v___x_2025_;
}
}
}
else
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2028_ = lean_io_promise_resolve(v_x_2017_, v_promise_2016_);
v___x_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2028_);
v___x_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
return v___x_2030_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__1___boxed(lean_object* v_promise_2031_, lean_object* v_x_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__1(v_promise_2031_, v_x_2032_);
lean_dec(v_promise_2031_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__6(lean_object* v___x_2035_, lean_object* v_waiter_2036_, lean_object* v_a_2037_, lean_object* v_fst_2038_, lean_object* v_a_2039_, lean_object* v___f_2040_, lean_object* v_a_2041_){
_start:
{
if (lean_obj_tag(v_a_2041_) == 0)
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
lean_dec_ref(v___f_2040_);
lean_dec_ref(v_fst_2038_);
lean_dec_ref(v_a_2037_);
lean_dec_ref(v_waiter_2036_);
v___x_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2035_);
v___x_2044_ = lean_task_pure(v___x_2043_);
return v___x_2044_;
}
else
{
lean_object* v_val_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2066_; 
v_val_2045_ = lean_ctor_get(v_a_2041_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v_a_2041_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2047_ = v_a_2041_;
v_isShared_2048_ = v_isSharedCheck_2066_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_val_2045_);
lean_dec(v_a_2041_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2066_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v_promise_2049_; lean_object* v___f_2050_; lean_object* v___f_2051_; lean_object* v___f_2052_; lean_object* v___f_2053_; lean_object* v___f_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; uint8_t v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2060_; 
v_promise_2049_ = lean_ctor_get(v_waiter_2036_, 1);
lean_inc_n(v_promise_2049_, 2);
lean_dec_ref(v_waiter_2036_);
v___f_2050_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2050_, 0, v_promise_2049_);
v___f_2051_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2051_, 0, v_promise_2049_);
v___f_2052_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_2052_, 0, v_a_2037_);
lean_closure_set(v___f_2052_, 1, v___f_2051_);
v___f_2053_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_2053_, 0, v___f_2052_);
lean_closure_set(v___f_2053_, 1, v___f_2050_);
lean_closure_set(v___f_2053_, 2, v_val_2045_);
v___f_2054_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_2054_, 0, v_fst_2038_);
lean_closure_set(v___f_2054_, 1, v___x_2035_);
lean_closure_set(v___f_2054_, 2, v___f_2053_);
v___x_2055_ = l_IO_Promise_result_x21___redArg(v_a_2039_);
v___x_2056_ = lean_unsigned_to_nat(0u);
v___x_2057_ = 0;
v___x_2058_ = lean_task_map(v___f_2040_, v___x_2055_, v___x_2056_, v___x_2057_);
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 0, v___x_2058_);
v___x_2060_ = v___x_2047_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
lean_object* v___x_2061_; 
v___x_2061_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2056_, v___x_2057_, v___x_2060_, v___f_2054_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2063_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2062_);
lean_dec_ref_known(v___x_2061_, 1);
v___x_2063_ = lean_task_pure(v_a_2062_);
return v___x_2063_;
}
else
{
lean_object* v_a_2064_; 
v_a_2064_ = lean_ctor_get(v___x_2061_, 0);
lean_inc_ref(v_a_2064_);
lean_dec_ref_known(v___x_2061_, 1);
return v_a_2064_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__6___boxed(lean_object* v___x_2067_, lean_object* v_waiter_2068_, lean_object* v_a_2069_, lean_object* v_fst_2070_, lean_object* v_a_2071_, lean_object* v___f_2072_, lean_object* v_a_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__6(v___x_2067_, v_waiter_2068_, v_a_2069_, v_fst_2070_, v_a_2071_, v___f_2072_, v_a_2073_);
lean_dec(v_a_2071_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__7(lean_object* v_a_2076_, lean_object* v___f_2077_, lean_object* v___x_2078_, lean_object* v___f_2079_, lean_object* v_x_2080_){
_start:
{
if (lean_obj_tag(v_x_2080_) == 0)
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2090_; 
lean_dec_ref(v___f_2079_);
lean_dec_ref(v___f_2077_);
v_a_2082_ = lean_ctor_get(v_x_2080_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v_x_2080_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2084_ = v_x_2080_;
v_isShared_2085_ = v_isSharedCheck_2090_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v_x_2080_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2090_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
lean_object* v___x_2088_; 
v___x_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
return v___x_2088_;
}
}
}
else
{
lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2103_; 
v_isSharedCheck_2103_ = !lean_is_exclusive(v_x_2080_);
if (v_isSharedCheck_2103_ == 0)
{
lean_object* v_unused_2104_; 
v_unused_2104_ = lean_ctor_get(v_x_2080_, 0);
lean_dec(v_unused_2104_);
v___x_2092_ = v_x_2080_;
v_isShared_2093_ = v_isSharedCheck_2103_;
goto v_resetjp_2091_;
}
else
{
lean_dec(v_x_2080_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2103_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; uint8_t v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2099_; 
v___x_2094_ = lean_io_promise_result_opt(v_a_2076_);
v___x_2095_ = lean_unsigned_to_nat(0u);
v___x_2096_ = 0;
v___x_2097_ = lean_io_bind_task(v___x_2094_, v___f_2077_, v___x_2095_, v___x_2096_);
lean_dec_ref(v___x_2097_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v___x_2078_);
v___x_2099_ = v___x_2092_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2078_);
v___x_2099_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
v___x_2101_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2095_, v___x_2096_, v___x_2100_, v___f_2079_);
return v___x_2101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__7___boxed(lean_object* v_a_2105_, lean_object* v___f_2106_, lean_object* v___x_2107_, lean_object* v___f_2108_, lean_object* v_x_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__7(v_a_2105_, v___f_2106_, v___x_2107_, v___f_2108_, v_x_2109_);
lean_dec(v_a_2105_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__8(lean_object* v_waiter_2112_, lean_object* v_a_2113_, lean_object* v___f_2114_, lean_object* v___x_2115_, lean_object* v___f_2116_, lean_object* v_x_2117_){
_start:
{
if (lean_obj_tag(v_x_2117_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2127_; 
lean_dec_ref(v___f_2116_);
lean_dec_ref(v___f_2114_);
lean_dec_ref(v_a_2113_);
lean_dec_ref(v_waiter_2112_);
v_a_2119_ = lean_ctor_get(v_x_2117_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v_x_2117_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2121_ = v_x_2117_;
v_isShared_2122_ = v_isSharedCheck_2127_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v_x_2117_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2127_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
lean_object* v___x_2125_; 
v___x_2125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
return v___x_2125_;
}
}
}
else
{
lean_object* v_selector_2128_; lean_object* v_a_2129_; lean_object* v_finished_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2143_; 
v_selector_2128_ = lean_ctor_get(v_a_2113_, 0);
lean_inc_ref(v_selector_2128_);
lean_dec_ref(v_a_2113_);
v_a_2129_ = lean_ctor_get(v_x_2117_, 0);
lean_inc(v_a_2129_);
lean_dec_ref_known(v_x_2117_, 1);
v_finished_2130_ = lean_ctor_get(v_waiter_2112_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v_waiter_2112_);
if (v_isSharedCheck_2143_ == 0)
{
lean_object* v_unused_2144_; 
v_unused_2144_ = lean_ctor_get(v_waiter_2112_, 1);
lean_dec(v_unused_2144_);
v___x_2132_ = v_waiter_2112_;
v_isShared_2133_ = v_isSharedCheck_2143_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_finished_2130_);
lean_dec(v_waiter_2112_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2143_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v_registerFn_2134_; lean_object* v___x_2136_; 
v_registerFn_2134_ = lean_ctor_get(v_selector_2128_, 1);
lean_inc_ref(v_registerFn_2134_);
lean_dec_ref(v_selector_2128_);
lean_inc(v_a_2129_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 1, v_a_2129_);
v___x_2136_ = v___x_2132_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_finished_2130_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v_a_2129_);
v___x_2136_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
lean_object* v___x_2137_; lean_object* v___f_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; lean_object* v___x_2141_; 
v___x_2137_ = lean_apply_2(v_registerFn_2134_, v___x_2136_, lean_box(0));
v___f_2138_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_2138_, 0, v_a_2129_);
lean_closure_set(v___f_2138_, 1, v___f_2114_);
lean_closure_set(v___f_2138_, 2, v___x_2115_);
lean_closure_set(v___f_2138_, 3, v___f_2116_);
v___x_2139_ = lean_unsigned_to_nat(0u);
v___x_2140_ = 0;
v___x_2141_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2139_, v___x_2140_, v___x_2137_, v___f_2138_);
return v___x_2141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__8___boxed(lean_object* v_waiter_2145_, lean_object* v_a_2146_, lean_object* v___f_2147_, lean_object* v___x_2148_, lean_object* v___f_2149_, lean_object* v_x_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__8(v_waiter_2145_, v_a_2146_, v___f_2147_, v___x_2148_, v___f_2149_, v_x_2150_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__9___boxed(lean_object* v_i_2154_, lean_object* v_waiter_2155_, lean_object* v_fst_2156_, lean_object* v_a_2157_, lean_object* v_as_2158_, lean_object* v_sz_2159_, lean_object* v_x_2160_, lean_object* v___y_2161_){
_start:
{
size_t v_i_boxed_2162_; size_t v_sz_boxed_2163_; lean_object* v_res_2164_; 
v_i_boxed_2162_ = lean_unbox_usize(v_i_2154_);
lean_dec(v_i_2154_);
v_sz_boxed_2163_ = lean_unbox_usize(v_sz_2159_);
lean_dec(v_sz_2159_);
v_res_2164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__9(v_i_boxed_2162_, v_waiter_2155_, v_fst_2156_, v_a_2157_, v_as_2158_, v_sz_boxed_2163_, v_x_2160_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg(lean_object* v_waiter_2165_, lean_object* v_fst_2166_, lean_object* v_a_2167_, lean_object* v_as_2168_, size_t v_sz_2169_, size_t v_i_2170_, lean_object* v_b_2171_){
_start:
{
uint8_t v___x_2173_; 
v___x_2173_ = lean_usize_dec_lt(v_i_2170_, v_sz_2169_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
lean_dec_ref(v_as_2168_);
lean_dec(v_a_2167_);
lean_dec_ref(v_fst_2166_);
lean_dec_ref(v_waiter_2165_);
v___x_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2174_, 0, v_b_2171_);
v___x_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2174_);
return v___x_2175_;
}
else
{
lean_object* v___x_2176_; lean_object* v___f_2177_; lean_object* v___x_2178_; lean_object* v___f_2179_; lean_object* v_a_2180_; lean_object* v___f_2181_; lean_object* v___f_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; uint8_t v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___f_2190_; lean_object* v___x_2191_; 
v___x_2176_ = lean_io_promise_new();
v___f_2177_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___closed__0));
v___x_2178_ = lean_box(0);
v___f_2179_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___closed__0));
v_a_2180_ = lean_array_uget_borrowed(v_as_2168_, v_i_2170_);
lean_inc(v_a_2167_);
lean_inc_ref(v_fst_2166_);
lean_inc_n(v_a_2180_, 2);
lean_inc_ref_n(v_waiter_2165_, 2);
v___f_2181_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__6___boxed), 8, 6);
lean_closure_set(v___f_2181_, 0, v___x_2178_);
lean_closure_set(v___f_2181_, 1, v_waiter_2165_);
lean_closure_set(v___f_2181_, 2, v_a_2180_);
lean_closure_set(v___f_2181_, 3, v_fst_2166_);
lean_closure_set(v___f_2181_, 4, v_a_2167_);
lean_closure_set(v___f_2181_, 5, v___f_2177_);
v___f_2182_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__8___boxed), 7, 5);
lean_closure_set(v___f_2182_, 0, v_waiter_2165_);
lean_closure_set(v___f_2182_, 1, v_a_2180_);
lean_closure_set(v___f_2182_, 2, v___f_2181_);
lean_closure_set(v___f_2182_, 3, v___x_2178_);
lean_closure_set(v___f_2182_, 4, v___f_2179_);
v___x_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2176_);
v___x_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2183_);
v___x_2185_ = lean_unsigned_to_nat(0u);
v___x_2186_ = 0;
v___x_2187_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2185_, v___x_2186_, v___x_2184_, v___f_2182_);
v___x_2188_ = lean_box_usize(v_i_2170_);
v___x_2189_ = lean_box_usize(v_sz_2169_);
v___f_2190_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__9___boxed), 8, 6);
lean_closure_set(v___f_2190_, 0, v___x_2188_);
lean_closure_set(v___f_2190_, 1, v_waiter_2165_);
lean_closure_set(v___f_2190_, 2, v_fst_2166_);
lean_closure_set(v___f_2190_, 3, v_a_2167_);
lean_closure_set(v___f_2190_, 4, v_as_2168_);
lean_closure_set(v___f_2190_, 5, v___x_2189_);
v___x_2191_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2185_, v___x_2186_, v___x_2187_, v___f_2190_);
return v___x_2191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__9(size_t v_i_2192_, lean_object* v_waiter_2193_, lean_object* v_fst_2194_, lean_object* v_a_2195_, lean_object* v_as_2196_, size_t v_sz_2197_, lean_object* v_x_2198_){
_start:
{
if (lean_obj_tag(v_x_2198_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2208_; 
lean_dec_ref(v_as_2196_);
lean_dec(v_a_2195_);
lean_dec_ref(v_fst_2194_);
lean_dec_ref(v_waiter_2193_);
v_a_2200_ = lean_ctor_get(v_x_2198_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v_x_2198_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2202_ = v_x_2198_;
v_isShared_2203_ = v_isSharedCheck_2208_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v_x_2198_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2208_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
lean_object* v___x_2206_; 
v___x_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
return v___x_2206_;
}
}
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2228_; 
v_a_2209_ = lean_ctor_get(v_x_2198_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v_x_2198_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2211_ = v_x_2198_;
v_isShared_2212_ = v_isSharedCheck_2228_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v_x_2198_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2228_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
if (lean_obj_tag(v_a_2209_) == 0)
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2223_; 
lean_dec_ref(v_as_2196_);
lean_dec(v_a_2195_);
lean_dec_ref(v_fst_2194_);
lean_dec_ref(v_waiter_2193_);
v_a_2213_ = lean_ctor_get(v_a_2209_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_a_2209_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2215_ = v_a_2209_;
v_isShared_2216_ = v_isSharedCheck_2223_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v_a_2209_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2223_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 0, v_a_2213_);
v___x_2218_ = v___x_2211_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
lean_object* v___x_2220_; 
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 0, v___x_2218_);
v___x_2220_ = v___x_2215_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2218_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
else
{
lean_object* v_a_2224_; size_t v___x_2225_; size_t v___x_2226_; lean_object* v___x_2227_; 
lean_del_object(v___x_2211_);
v_a_2224_ = lean_ctor_get(v_a_2209_, 0);
lean_inc(v_a_2224_);
lean_dec_ref_known(v_a_2209_, 1);
v___x_2225_ = ((size_t)1ULL);
v___x_2226_ = lean_usize_add(v_i_2192_, v___x_2225_);
v___x_2227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg(v_waiter_2193_, v_fst_2194_, v_a_2195_, v_as_2196_, v_sz_2197_, v___x_2226_, v_a_2224_);
return v___x_2227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___boxed(lean_object* v_waiter_2229_, lean_object* v_fst_2230_, lean_object* v_a_2231_, lean_object* v_as_2232_, lean_object* v_sz_2233_, lean_object* v_i_2234_, lean_object* v_b_2235_, lean_object* v___y_2236_){
_start:
{
size_t v_sz_boxed_2237_; size_t v_i_boxed_2238_; lean_object* v_res_2239_; 
v_sz_boxed_2237_ = lean_unbox_usize(v_sz_2233_);
lean_dec(v_sz_2233_);
v_i_boxed_2238_ = lean_unbox_usize(v_i_2234_);
lean_dec(v_i_2234_);
v_res_2239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg(v_waiter_2229_, v_fst_2230_, v_a_2231_, v_as_2232_, v_sz_boxed_2237_, v_i_boxed_2238_, v_b_2235_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__4(lean_object* v_fst_2240_, lean_object* v_waiter_2241_, lean_object* v_a_2242_, lean_object* v___f_2243_, lean_object* v_x_2244_){
_start:
{
if (lean_obj_tag(v_x_2244_) == 0)
{
lean_object* v___x_2246_; 
lean_dec_ref(v___f_2243_);
lean_dec(v_a_2242_);
lean_dec_ref(v_waiter_2241_);
lean_dec_ref(v_fst_2240_);
v___x_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2246_, 0, v_x_2244_);
return v___x_2246_;
}
else
{
lean_object* v___x_2247_; size_t v_sz_2248_; size_t v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; uint8_t v___x_2252_; lean_object* v___x_2253_; 
lean_dec_ref_known(v_x_2244_, 1);
v___x_2247_ = lean_box(0);
v_sz_2248_ = lean_array_size(v_fst_2240_);
v___x_2249_ = ((size_t)0ULL);
lean_inc_ref(v_fst_2240_);
v___x_2250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg(v_waiter_2241_, v_fst_2240_, v_a_2242_, v_fst_2240_, v_sz_2248_, v___x_2249_, v___x_2247_);
v___x_2251_ = lean_unsigned_to_nat(0u);
v___x_2252_ = 0;
v___x_2253_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2251_, v___x_2252_, v___x_2250_, v___f_2243_);
return v___x_2253_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__4___boxed(lean_object* v_fst_2254_, lean_object* v_waiter_2255_, lean_object* v_a_2256_, lean_object* v___f_2257_, lean_object* v_x_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Std_Async_Selectable_combine___redArg___lam__4(v_fst_2254_, v_waiter_2255_, v_a_2256_, v___f_2257_, v_x_2258_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__5(lean_object* v_selectables_2261_, lean_object* v___x_2262_, lean_object* v_waiter_2263_, lean_object* v_a_2264_, lean_object* v___f_2265_, lean_object* v_x_2266_){
_start:
{
if (lean_obj_tag(v_x_2266_) == 0)
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2276_; 
lean_dec_ref(v___f_2265_);
lean_dec(v_a_2264_);
lean_dec_ref(v_waiter_2263_);
lean_dec_ref(v_selectables_2261_);
v_a_2268_ = lean_ctor_get(v_x_2266_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v_x_2266_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2270_ = v_x_2266_;
v_isShared_2271_ = v_isSharedCheck_2276_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v_x_2266_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2276_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
lean_object* v___x_2274_; 
v___x_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
return v___x_2274_;
}
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2293_; 
v_a_2277_ = lean_ctor_get(v_x_2266_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v_x_2266_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2279_ = v_x_2266_;
v_isShared_2280_ = v_isSharedCheck_2293_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v_x_2266_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2293_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2281_; lean_object* v_fst_2282_; lean_object* v_snd_2283_; lean_object* v___x_2284_; lean_object* v___f_2285_; lean_object* v___x_2287_; 
v___x_2281_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(v_selectables_2261_, v_a_2277_);
v_fst_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_fst_2282_);
v_snd_2283_ = lean_ctor_get(v___x_2281_, 1);
lean_inc(v_snd_2283_);
lean_dec_ref(v___x_2281_);
v___x_2284_ = lean_st_ref_set(v___x_2262_, v_snd_2283_);
v___f_2285_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_2285_, 0, v_fst_2282_);
lean_closure_set(v___f_2285_, 1, v_waiter_2263_);
lean_closure_set(v___f_2285_, 2, v_a_2264_);
lean_closure_set(v___f_2285_, 3, v___f_2265_);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v___x_2284_);
v___x_2287_ = v___x_2279_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2284_);
v___x_2287_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; uint8_t v___x_2290_; lean_object* v___x_2291_; 
v___x_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
v___x_2289_ = lean_unsigned_to_nat(0u);
v___x_2290_ = 0;
v___x_2291_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2289_, v___x_2290_, v___x_2288_, v___f_2285_);
return v___x_2291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__5___boxed(lean_object* v_selectables_2294_, lean_object* v___x_2295_, lean_object* v_waiter_2296_, lean_object* v_a_2297_, lean_object* v___f_2298_, lean_object* v_x_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Std_Async_Selectable_combine___redArg___lam__5(v_selectables_2294_, v___x_2295_, v_waiter_2296_, v_a_2297_, v___f_2298_, v_x_2299_);
lean_dec(v___x_2295_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__6(lean_object* v___x_2302_, lean_object* v_selectables_2303_, lean_object* v_waiter_2304_, lean_object* v_x_2305_){
_start:
{
if (lean_obj_tag(v_x_2305_) == 0)
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2315_; 
lean_dec_ref(v_waiter_2304_);
lean_dec_ref(v_selectables_2303_);
lean_dec(v___x_2302_);
v_a_2307_ = lean_ctor_get(v_x_2305_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v_x_2305_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2309_ = v_x_2305_;
v_isShared_2310_ = v_isSharedCheck_2315_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v_x_2305_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2315_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
lean_object* v___x_2313_; 
v___x_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2312_);
return v___x_2313_;
}
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2330_; 
v_a_2316_ = lean_ctor_get(v_x_2305_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v_x_2305_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2318_ = v_x_2305_;
v_isShared_2319_ = v_isSharedCheck_2330_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v_x_2305_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2330_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2320_; lean_object* v___f_2321_; lean_object* v___f_2322_; lean_object* v___x_2324_; 
v___x_2320_ = lean_st_ref_get(v___x_2302_);
lean_inc(v_a_2316_);
v___f_2321_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2321_, 0, v_a_2316_);
v___f_2322_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__5___boxed), 7, 5);
lean_closure_set(v___f_2322_, 0, v_selectables_2303_);
lean_closure_set(v___f_2322_, 1, v___x_2302_);
lean_closure_set(v___f_2322_, 2, v_waiter_2304_);
lean_closure_set(v___f_2322_, 3, v_a_2316_);
lean_closure_set(v___f_2322_, 4, v___f_2321_);
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v___x_2320_);
v___x_2324_ = v___x_2318_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2320_);
v___x_2324_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; uint8_t v___x_2327_; lean_object* v___x_2328_; 
v___x_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2324_);
v___x_2326_ = lean_unsigned_to_nat(0u);
v___x_2327_ = 0;
v___x_2328_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2326_, v___x_2327_, v___x_2325_, v___f_2322_);
return v___x_2328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__6___boxed(lean_object* v___x_2331_, lean_object* v_selectables_2332_, lean_object* v_waiter_2333_, lean_object* v_x_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v_res_2336_; 
v_res_2336_ = l_Std_Async_Selectable_combine___redArg___lam__6(v___x_2331_, v_selectables_2332_, v_waiter_2333_, v_x_2334_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__7(lean_object* v___x_2337_, lean_object* v_selectables_2338_, lean_object* v_waiter_2339_){
_start:
{
lean_object* v___x_2341_; lean_object* v___f_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; uint8_t v___x_2346_; lean_object* v___x_2347_; 
v___x_2341_ = lean_io_promise_new();
v___f_2342_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__6___boxed), 5, 3);
lean_closure_set(v___f_2342_, 0, v___x_2337_);
lean_closure_set(v___f_2342_, 1, v_selectables_2338_);
lean_closure_set(v___f_2342_, 2, v_waiter_2339_);
v___x_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2341_);
v___x_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2343_);
v___x_2345_ = lean_unsigned_to_nat(0u);
v___x_2346_ = 0;
v___x_2347_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2345_, v___x_2346_, v___x_2344_, v___f_2342_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__7___boxed(lean_object* v___x_2348_, lean_object* v_selectables_2349_, lean_object* v_waiter_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Std_Async_Selectable_combine___redArg___lam__7(v___x_2348_, v_selectables_2349_, v_waiter_2350_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__8(lean_object* v___x_2353_, lean_object* v_x_2354_){
_start:
{
if (lean_obj_tag(v_x_2354_) == 0)
{
lean_object* v___x_2356_; 
v___x_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2356_, 0, v_x_2354_);
return v___x_2356_;
}
else
{
lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2364_; 
v_isSharedCheck_2364_ = !lean_is_exclusive(v_x_2354_);
if (v_isSharedCheck_2364_ == 0)
{
lean_object* v_unused_2365_; 
v_unused_2365_ = lean_ctor_get(v_x_2354_, 0);
lean_dec(v_unused_2365_);
v___x_2358_ = v_x_2354_;
v_isShared_2359_ = v_isSharedCheck_2364_;
goto v_resetjp_2357_;
}
else
{
lean_dec(v_x_2354_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2364_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 0, v___x_2353_);
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2353_);
v___x_2361_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
lean_object* v___x_2362_; 
v___x_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2361_);
return v___x_2362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__8___boxed(lean_object* v___x_2366_, lean_object* v_x_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Std_Async_Selectable_combine___redArg___lam__8(v___x_2366_, v_x_2367_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__9(lean_object* v_selectables_2370_, size_t v_sz_2371_, size_t v___x_2372_, lean_object* v___x_2373_, lean_object* v___f_2374_){
_start:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; uint8_t v___x_2378_; lean_object* v___x_2379_; 
v___x_2376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg(v_selectables_2370_, v_sz_2371_, v___x_2372_, v___x_2373_);
v___x_2377_ = lean_unsigned_to_nat(0u);
v___x_2378_ = 0;
v___x_2379_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2377_, v___x_2378_, v___x_2376_, v___f_2374_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__9___boxed(lean_object* v_selectables_2380_, lean_object* v_sz_2381_, lean_object* v___x_2382_, lean_object* v___x_2383_, lean_object* v___f_2384_, lean_object* v___y_2385_){
_start:
{
size_t v_sz_boxed_2386_; size_t v___x_9597__boxed_2387_; lean_object* v_res_2388_; 
v_sz_boxed_2386_ = lean_unbox_usize(v_sz_2381_);
lean_dec(v_sz_2381_);
v___x_9597__boxed_2387_ = lean_unbox_usize(v___x_2382_);
lean_dec(v___x_2382_);
v_res_2388_ = l_Std_Async_Selectable_combine___redArg___lam__9(v_selectables_2380_, v_sz_boxed_2386_, v___x_9597__boxed_2387_, v___x_2383_, v___f_2384_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg(lean_object* v_selectables_2393_){
_start:
{
lean_object* v___f_2395_; lean_object* v___x_2396_; lean_object* v___f_2397_; lean_object* v___f_2398_; lean_object* v___f_2399_; lean_object* v___x_2400_; lean_object* v___f_2401_; size_t v_sz_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___f_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___f_2395_ = ((lean_object*)(l_Std_Async_Selectable_tryOne___redArg___closed__0));
v___x_2396_ = l_IO_stdGenRef;
lean_inc_ref_n(v_selectables_2393_, 2);
v___f_2397_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2397_, 0, v_selectables_2393_);
lean_closure_set(v___f_2397_, 1, v___x_2396_);
lean_closure_set(v___f_2397_, 2, v___f_2395_);
v___f_2398_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_2398_, 0, v___x_2396_);
lean_closure_set(v___f_2398_, 1, v___f_2397_);
v___f_2399_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_2399_, 0, v___x_2396_);
lean_closure_set(v___f_2399_, 1, v_selectables_2393_);
v___x_2400_ = lean_box(0);
v___f_2401_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___closed__0));
v_sz_2402_ = lean_array_size(v_selectables_2393_);
v___x_2403_ = lean_box_usize(v_sz_2402_);
v___x_2404_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___boxed__const__1));
v___f_2405_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__9___boxed), 6, 5);
lean_closure_set(v___f_2405_, 0, v_selectables_2393_);
lean_closure_set(v___f_2405_, 1, v___x_2403_);
lean_closure_set(v___f_2405_, 2, v___x_2404_);
lean_closure_set(v___f_2405_, 3, v___x_2400_);
lean_closure_set(v___f_2405_, 4, v___f_2401_);
v___x_2406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2406_, 0, v___f_2398_);
lean_ctor_set(v___x_2406_, 1, v___f_2399_);
lean_ctor_set(v___x_2406_, 2, v___f_2405_);
v___x_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___boxed(lean_object* v_selectables_2408_, lean_object* v_a_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Std_Async_Selectable_combine___redArg(v_selectables_2408_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine(lean_object* v_00_u03b1_2411_, lean_object* v_selectables_2412_){
_start:
{
lean_object* v___x_2414_; 
v___x_2414_ = l_Std_Async_Selectable_combine___redArg(v_selectables_2412_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___boxed(lean_object* v_00_u03b1_2415_, lean_object* v_selectables_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Std_Async_Selectable_combine(v_00_u03b1_2415_, v_selectables_2416_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0(lean_object* v_00_u03b1_2419_, lean_object* v_as_2420_, size_t v_sz_2421_, size_t v_i_2422_, lean_object* v_b_2423_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg(v_as_2420_, v_sz_2421_, v_i_2422_, v_b_2423_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___boxed(lean_object* v_00_u03b1_2426_, lean_object* v_as_2427_, lean_object* v_sz_2428_, lean_object* v_i_2429_, lean_object* v_b_2430_, lean_object* v___y_2431_){
_start:
{
size_t v_sz_boxed_2432_; size_t v_i_boxed_2433_; lean_object* v_res_2434_; 
v_sz_boxed_2432_ = lean_unbox_usize(v_sz_2428_);
lean_dec(v_sz_2428_);
v_i_boxed_2433_ = lean_unbox_usize(v_i_2429_);
lean_dec(v_i_2429_);
v_res_2434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0(v_00_u03b1_2426_, v_as_2427_, v_sz_boxed_2432_, v_i_boxed_2433_, v_b_2430_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1(lean_object* v_00_u03b1_2435_, lean_object* v_waiter_2436_, lean_object* v_fst_2437_, lean_object* v_a_2438_, lean_object* v_as_2439_, size_t v_sz_2440_, size_t v_i_2441_, lean_object* v_b_2442_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg(v_waiter_2436_, v_fst_2437_, v_a_2438_, v_as_2439_, v_sz_2440_, v_i_2441_, v_b_2442_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___boxed(lean_object* v_00_u03b1_2445_, lean_object* v_waiter_2446_, lean_object* v_fst_2447_, lean_object* v_a_2448_, lean_object* v_as_2449_, lean_object* v_sz_2450_, lean_object* v_i_2451_, lean_object* v_b_2452_, lean_object* v___y_2453_){
_start:
{
size_t v_sz_boxed_2454_; size_t v_i_boxed_2455_; lean_object* v_res_2456_; 
v_sz_boxed_2454_ = lean_unbox_usize(v_sz_2450_);
lean_dec(v_sz_2450_);
v_i_boxed_2455_ = lean_unbox_usize(v_i_2451_);
lean_dec(v_i_2451_);
v_res_2456_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1(v_00_u03b1_2445_, v_waiter_2446_, v_fst_2447_, v_a_2448_, v_as_2449_, v_sz_boxed_2454_, v_i_boxed_2455_, v_b_2452_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2(lean_object* v_00_u03b1_2457_, lean_object* v_as_2458_, size_t v_sz_2459_, size_t v_i_2460_, lean_object* v_b_2461_){
_start:
{
lean_object* v___x_2463_; 
v___x_2463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(v_as_2458_, v_sz_2459_, v_i_2460_, v_b_2461_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___boxed(lean_object* v_00_u03b1_2464_, lean_object* v_as_2465_, lean_object* v_sz_2466_, lean_object* v_i_2467_, lean_object* v_b_2468_, lean_object* v___y_2469_){
_start:
{
size_t v_sz_boxed_2470_; size_t v_i_boxed_2471_; lean_object* v_res_2472_; 
v_sz_boxed_2470_ = lean_unbox_usize(v_sz_2466_);
lean_dec(v_sz_2466_);
v_i_boxed_2471_ = lean_unbox_usize(v_i_2467_);
lean_dec(v_i_2467_);
v_res_2472_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2(v_00_u03b1_2464_, v_as_2465_, v_sz_boxed_2470_, v_i_boxed_2471_, v_b_2468_);
return v_res_2472_;
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
