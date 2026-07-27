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
lean_object* lean_mk_io_user_error(lean_object*);
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_io_promise_new();
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_Selectable_combine___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_Selectable_combine___redArg___lam__0___closed__0 = (const lean_object*)&l_Std_Async_Selectable_combine___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Async_Selectable_combine___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Selectable_combine___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Std_Async_Selectable_combine___redArg___lam__0___closed__1 = (const lean_object*)&l_Std_Async_Selectable_combine___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__2(size_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__9(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__6(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__4(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__0_value;
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__3___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__1_value;
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__4___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__3_value;
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__5___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__3_value)} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__12(size_t, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Selectable_combine___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Selectable_combine___redArg___lam__4___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Async_Selectable_combine___redArg___lam__5___closed__0 = (const lean_object*)&l_Std_Async_Selectable_combine___redArg___lam__5___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__0___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___closed__0_value;
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__2(size_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__9(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Selectable_combine___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Selectable_combine___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_Selectable_combine___redArg___closed__0 = (const lean_object*)&l_Std_Async_Selectable_combine___redArg___closed__0_value;
static const lean_closure_object l_Std_Async_Selectable_combine___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Selectable_combine___redArg___lam__8___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Async_Selectable_combine___redArg___closed__1 = (const lean_object*)&l_Std_Async_Selectable_combine___redArg___closed__1_value;
static const lean_ctor_object l_Std_Async_Selectable_combine___redArg___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Std_Async_Selectable_combine___redArg___boxed__const__1 = (const lean_object*)&l_Std_Async_Selectable_combine___redArg___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Async_Selectable_one___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "the promise linked to the Async was dropped"};
static const lean_object* l_Std_Async_Selectable_one___redArg___lam__3___closed__0 = (const lean_object*)&l_Std_Async_Selectable_one___redArg___lam__3___closed__0_value;
static const lean_closure_object l_Std_Async_Selectable_one___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Selectable_one___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_Selectable_one___redArg___lam__3___closed__0_value)} };
static const lean_object* l_Std_Async_Selectable_one___redArg___lam__3___closed__1 = (const lean_object*)&l_Std_Async_Selectable_one___redArg___lam__3___closed__1_value;
static const lean_closure_object l_Std_Async_Selectable_one___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Selectable_one___redArg___lam__2___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_Selectable_one___redArg___lam__3___closed__1_value)} };
static const lean_object* l_Std_Async_Selectable_one___redArg___lam__3___closed__2 = (const lean_object*)&l_Std_Async_Selectable_one___redArg___lam__3___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__5(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Selectable_one___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Selectable_one___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_Selectable_one___redArg___closed__0 = (const lean_object*)&l_Std_Async_Selectable_one___redArg___closed__0_value;
static const lean_closure_object l_Std_Async_Selectable_one___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Selectable_one___redArg___lam__9___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_Selectable_one___redArg___closed__0_value)} };
static const lean_object* l_Std_Async_Selectable_one___redArg___closed__1 = (const lean_object*)&l_Std_Async_Selectable_one___redArg___closed__1_value;
static const lean_string_object l_Std_Async_Selectable_one___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Selectable.one requires at least one Selectable"};
static const lean_object* l_Std_Async_Selectable_one___redArg___closed__2 = (const lean_object*)&l_Std_Async_Selectable_one___redArg___closed__2_value;
static const lean_ctor_object l_Std_Async_Selectable_one___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Std_Async_Selectable_one___redArg___closed__2_value)}};
static const lean_object* l_Std_Async_Selectable_one___redArg___closed__3 = (const lean_object*)&l_Std_Async_Selectable_one___redArg___closed__3_value;
static const lean_ctor_object l_Std_Async_Selectable_one___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Selectable_one___redArg___closed__3_value)}};
static const lean_object* l_Std_Async_Selectable_one___redArg___closed__4 = (const lean_object*)&l_Std_Async_Selectable_one___redArg___closed__4_value;
static const lean_ctor_object l_Std_Async_Selectable_one___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Selectable_one___redArg___closed__4_value)}};
static const lean_object* l_Std_Async_Selectable_one___redArg___closed__5 = (const lean_object*)&l_Std_Async_Selectable_one___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Async_Selectable_tryOne___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "Selectable.tryOne requires at least one Selectable"};
static const lean_object* l_Std_Async_Selectable_tryOne___redArg___closed__0 = (const lean_object*)&l_Std_Async_Selectable_tryOne___redArg___closed__0_value;
static const lean_ctor_object l_Std_Async_Selectable_tryOne___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Std_Async_Selectable_tryOne___redArg___closed__0_value)}};
static const lean_object* l_Std_Async_Selectable_tryOne___redArg___closed__1 = (const lean_object*)&l_Std_Async_Selectable_tryOne___redArg___closed__1_value;
static const lean_ctor_object l_Std_Async_Selectable_tryOne___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Selectable_tryOne___redArg___closed__1_value)}};
static const lean_object* l_Std_Async_Selectable_tryOne___redArg___closed__2 = (const lean_object*)&l_Std_Async_Selectable_tryOne___redArg___closed__2_value;
static const lean_ctor_object l_Std_Async_Selectable_tryOne___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Selectable_tryOne___redArg___closed__2_value)}};
static const lean_object* l_Std_Async_Selectable_tryOne___redArg___closed__3 = (const lean_object*)&l_Std_Async_Selectable_tryOne___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__0___redArg___lam__0(lean_object* v_lose_195_, lean_object* v_a_196_, lean_object* v_promise_197_, lean_object* v_x_198_){
_start:
{
if (lean_obj_tag(v_x_198_) == 0)
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_208_; 
lean_dec(v_a_196_);
lean_dec_ref(v_lose_195_);
v_a_200_ = lean_ctor_get(v_x_198_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v_x_198_);
if (v_isSharedCheck_208_ == 0)
{
v___x_202_ = v_x_198_;
v_isShared_203_ = v_isSharedCheck_208_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v_x_198_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_208_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_207_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_206_; 
v___x_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
return v___x_206_;
}
}
}
else
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_221_; 
v_a_209_ = lean_ctor_get(v_x_198_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v_x_198_);
if (v_isSharedCheck_221_ == 0)
{
v___x_211_ = v_x_198_;
v_isShared_212_ = v_isSharedCheck_221_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v_x_198_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_221_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
uint8_t v___x_213_; 
v___x_213_ = lean_unbox(v_a_209_);
lean_dec(v_a_209_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; 
lean_del_object(v___x_211_);
lean_dec(v_a_196_);
v___x_214_ = lean_apply_1(v_lose_195_, lean_box(0));
return v___x_214_;
}
else
{
lean_object* v___x_216_; 
lean_dec_ref(v_lose_195_);
if (v_isShared_212_ == 0)
{
lean_ctor_set_tag(v___x_211_, 0);
lean_ctor_set(v___x_211_, 0, v_a_196_);
v___x_216_ = v___x_211_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_a_196_);
v___x_216_ = v_reuseFailAlloc_220_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_217_ = lean_io_promise_resolve(v___x_216_, v_promise_197_);
v___x_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
return v___x_219_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__0___redArg___lam__0___boxed(lean_object* v_lose_222_, lean_object* v_a_223_, lean_object* v_promise_224_, lean_object* v_x_225_, lean_object* v___y_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__0___redArg___lam__0(v_lose_222_, v_a_223_, v_promise_224_, v_x_225_);
lean_dec(v_promise_224_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__0___redArg(lean_object* v_a_228_, lean_object* v_w_229_, lean_object* v_lose_230_){
_start:
{
lean_object* v_finished_232_; lean_object* v_promise_233_; lean_object* v___x_234_; lean_object* v___f_235_; uint8_t v___y_237_; uint8_t v___x_247_; 
v_finished_232_ = lean_ctor_get(v_w_229_, 0);
lean_inc(v_finished_232_);
v_promise_233_ = lean_ctor_get(v_w_229_, 1);
lean_inc(v_promise_233_);
lean_dec_ref(v_w_229_);
v___x_234_ = lean_st_ref_take(v_finished_232_);
v___f_235_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__0___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_235_, 0, v_lose_230_);
lean_closure_set(v___f_235_, 1, v_a_228_);
lean_closure_set(v___f_235_, 2, v_promise_233_);
v___x_247_ = lean_unbox(v___x_234_);
lean_dec(v___x_234_);
if (v___x_247_ == 0)
{
uint8_t v___x_248_; 
v___x_248_ = 1;
v___y_237_ = v___x_248_;
goto v___jp_236_;
}
else
{
uint8_t v___x_249_; 
v___x_249_ = 0;
v___y_237_ = v___x_249_;
goto v___jp_236_;
}
v___jp_236_:
{
uint8_t v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; lean_object* v___x_246_; 
v___x_238_ = 1;
v___x_239_ = lean_box(v___x_238_);
v___x_240_ = lean_st_ref_set(v_finished_232_, v___x_239_);
lean_dec(v_finished_232_);
v___x_241_ = lean_box(v___y_237_);
v___x_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = 0;
v___x_246_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_244_, v___x_245_, v___x_243_, v___f_235_);
return v___x_246_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__0___redArg___boxed(lean_object* v_a_250_, lean_object* v_w_251_, lean_object* v_lose_252_, lean_object* v___y_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__0___redArg(v_a_250_, v_w_251_, v_lose_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__0(lean_object* v_00_u03b1_255_, lean_object* v_a_256_, lean_object* v_w_257_, lean_object* v_lose_258_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__0___redArg(v_a_256_, v_w_257_, v_lose_258_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__0___boxed(lean_object* v_00_u03b1_261_, lean_object* v_a_262_, lean_object* v_w_263_, lean_object* v_lose_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__0(v_00_u03b1_261_, v_a_262_, v_w_263_, v_lose_264_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__1___redArg(lean_object* v_e_267_){
_start:
{
if (lean_obj_tag(v_e_267_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_278_; 
v_a_269_ = lean_ctor_get(v_e_267_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v_e_267_);
if (v_isSharedCheck_278_ == 0)
{
v___x_271_ = v_e_267_;
v_isShared_272_ = v_isSharedCheck_278_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v_e_267_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_278_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_273_ = lean_io_error_to_string(v_a_269_);
v___x_274_ = lean_mk_io_user_error(v___x_273_);
if (v_isShared_272_ == 0)
{
lean_ctor_set_tag(v___x_271_, 1);
lean_ctor_set(v___x_271_, 0, v___x_274_);
v___x_276_ = v___x_271_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
else
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
v_a_279_ = lean_ctor_get(v_e_267_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v_e_267_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v_e_267_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v_e_267_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
lean_ctor_set_tag(v___x_281_, 0);
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__1___redArg___boxed(lean_object* v_e_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__1___redArg(v_e_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__1(lean_object* v_00_u03b1_290_, lean_object* v_e_291_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__1___redArg(v_e_291_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__1___boxed(lean_object* v_00_u03b1_294_, lean_object* v_e_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__1(v_00_u03b1_294_, v_e_295_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__0(lean_object* v_x_302_){
_start:
{
if (lean_obj_tag(v_x_302_) == 0)
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_312_; 
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
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_330_; 
v_a_313_ = lean_ctor_get(v_x_302_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v_x_302_);
if (v_isSharedCheck_330_ == 0)
{
v___x_315_ = v_x_302_;
v_isShared_316_ = v_isSharedCheck_330_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v_x_302_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_330_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v_fst_317_; 
v_fst_317_ = lean_ctor_get(v_a_313_, 0);
lean_inc(v_fst_317_);
lean_dec(v_a_313_);
if (lean_obj_tag(v_fst_317_) == 0)
{
lean_object* v___x_318_; 
lean_del_object(v___x_315_);
v___x_318_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___lam__0___closed__1));
return v___x_318_;
}
else
{
lean_object* v_val_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_329_; 
v_val_319_ = lean_ctor_get(v_fst_317_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v_fst_317_);
if (v_isSharedCheck_329_ == 0)
{
v___x_321_ = v_fst_317_;
v_isShared_322_ = v_isSharedCheck_329_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_val_319_);
lean_dec(v_fst_317_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_329_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v_val_319_);
v___x_324_ = v___x_315_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_val_319_);
v___x_324_ = v_reuseFailAlloc_328_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_326_; 
if (v_isShared_322_ == 0)
{
lean_ctor_set_tag(v___x_321_, 0);
lean_ctor_set(v___x_321_, 0, v___x_324_);
v___x_326_ = v___x_321_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_324_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__0___boxed(lean_object* v_x_331_, lean_object* v___y_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Std_Async_Selectable_combine___redArg___lam__0(v_x_331_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__0(lean_object* v___x_334_, lean_object* v_x_335_){
_start:
{
if (lean_obj_tag(v_x_335_) == 0)
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_345_; 
v_a_337_ = lean_ctor_get(v_x_335_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v_x_335_);
if (v_isSharedCheck_345_ == 0)
{
v___x_339_ = v_x_335_;
v_isShared_340_ = v_isSharedCheck_345_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v_x_335_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_345_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_a_337_);
v___x_342_ = v_reuseFailAlloc_344_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_343_; 
v___x_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
return v___x_343_;
}
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_358_; 
v_a_346_ = lean_ctor_get(v_x_335_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v_x_335_);
if (v_isSharedCheck_358_ == 0)
{
v___x_348_ = v_x_335_;
v_isShared_349_ = v_isSharedCheck_358_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v_x_335_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_358_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_350_, 0, v_a_346_);
v___x_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
v___x_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
lean_ctor_set(v___x_352_, 1, v___x_334_);
v___x_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_353_);
v___x_355_ = v___x_348_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_353_);
v___x_355_ = v_reuseFailAlloc_357_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
lean_object* v___x_356_; 
v___x_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
return v___x_356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__0___boxed(lean_object* v___x_359_, lean_object* v_x_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__0(v___x_359_, v_x_360_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__1(lean_object* v_a_363_, lean_object* v___f_364_, lean_object* v___x_365_, lean_object* v_x_366_){
_start:
{
if (lean_obj_tag(v_x_366_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_376_; 
lean_dec_ref(v___x_365_);
lean_dec_ref(v___f_364_);
lean_dec_ref(v_a_363_);
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
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_392_; 
v_a_377_ = lean_ctor_get(v_x_366_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v_x_366_);
if (v_isSharedCheck_392_ == 0)
{
v___x_379_ = v_x_366_;
v_isShared_380_ = v_isSharedCheck_392_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v_x_366_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_392_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
if (lean_obj_tag(v_a_377_) == 1)
{
lean_object* v_val_381_; lean_object* v_cont_382_; lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; lean_object* v___x_386_; 
lean_del_object(v___x_379_);
lean_dec_ref(v___x_365_);
v_val_381_ = lean_ctor_get(v_a_377_, 0);
lean_inc(v_val_381_);
lean_dec_ref_known(v_a_377_, 1);
v_cont_382_ = lean_ctor_get(v_a_363_, 1);
lean_inc_ref(v_cont_382_);
lean_dec_ref(v_a_363_);
v___x_383_ = lean_apply_2(v_cont_382_, v_val_381_, lean_box(0));
v___x_384_ = lean_unsigned_to_nat(0u);
v___x_385_ = 0;
v___x_386_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_384_, v___x_385_, v___x_383_, v___f_364_);
return v___x_386_;
}
else
{
lean_object* v___x_387_; lean_object* v___x_389_; 
lean_dec(v_a_377_);
lean_dec_ref(v___f_364_);
lean_dec_ref(v_a_363_);
v___x_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_365_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v___x_387_);
v___x_389_ = v___x_379_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_387_);
v___x_389_ = v_reuseFailAlloc_391_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v___x_390_; 
v___x_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__1___boxed(lean_object* v_a_393_, lean_object* v___f_394_, lean_object* v___x_395_, lean_object* v_x_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__1(v_a_393_, v___f_394_, v___x_395_, v_x_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__2___boxed(lean_object* v_i_404_, lean_object* v_as_405_, lean_object* v_sz_406_, lean_object* v_x_407_, lean_object* v___y_408_){
_start:
{
size_t v_i_boxed_409_; size_t v_sz_boxed_410_; lean_object* v_res_411_; 
v_i_boxed_409_ = lean_unbox_usize(v_i_404_);
lean_dec(v_i_404_);
v_sz_boxed_410_ = lean_unbox_usize(v_sz_406_);
lean_dec(v_sz_406_);
v_res_411_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__2(v_i_boxed_409_, v_as_405_, v_sz_boxed_410_, v_x_407_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg(lean_object* v_as_412_, size_t v_sz_413_, size_t v_i_414_, lean_object* v_b_415_){
_start:
{
uint8_t v___x_417_; 
v___x_417_ = lean_usize_dec_lt(v_i_414_, v_sz_413_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_419_; 
lean_dec_ref(v_as_412_);
v___x_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_418_, 0, v_b_415_);
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
return v___x_419_;
}
else
{
lean_object* v_a_420_; lean_object* v_selector_421_; lean_object* v_tryFn_422_; lean_object* v___x_423_; lean_object* v___f_424_; lean_object* v___x_425_; lean_object* v___f_426_; lean_object* v___x_427_; uint8_t v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___f_432_; lean_object* v___x_433_; 
lean_dec_ref(v_b_415_);
v_a_420_ = lean_array_uget_borrowed(v_as_412_, v_i_414_);
v_selector_421_ = lean_ctor_get(v_a_420_, 0);
v_tryFn_422_ = lean_ctor_get(v_selector_421_, 0);
lean_inc_ref(v_tryFn_422_);
v___x_423_ = lean_apply_1(v_tryFn_422_, lean_box(0));
v___f_424_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___closed__0));
v___x_425_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___closed__1));
lean_inc(v_a_420_);
v___f_426_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_426_, 0, v_a_420_);
lean_closure_set(v___f_426_, 1, v___f_424_);
lean_closure_set(v___f_426_, 2, v___x_425_);
v___x_427_ = lean_unsigned_to_nat(0u);
v___x_428_ = 0;
v___x_429_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_427_, v___x_428_, v___x_423_, v___f_426_);
v___x_430_ = lean_box_usize(v_i_414_);
v___x_431_ = lean_box_usize(v_sz_413_);
v___f_432_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_432_, 0, v___x_430_);
lean_closure_set(v___f_432_, 1, v_as_412_);
lean_closure_set(v___f_432_, 2, v___x_431_);
v___x_433_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_427_, v___x_428_, v___x_429_, v___f_432_);
return v___x_433_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__2(size_t v_i_434_, lean_object* v_as_435_, size_t v_sz_436_, lean_object* v_x_437_){
_start:
{
if (lean_obj_tag(v_x_437_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_447_; 
lean_dec_ref(v_as_435_);
v_a_439_ = lean_ctor_get(v_x_437_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v_x_437_);
if (v_isSharedCheck_447_ == 0)
{
v___x_441_ = v_x_437_;
v_isShared_442_ = v_isSharedCheck_447_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v_x_437_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_447_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_439_);
v___x_444_ = v_reuseFailAlloc_446_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_445_; 
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
return v___x_445_;
}
}
}
else
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_467_; 
v_a_448_ = lean_ctor_get(v_x_437_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v_x_437_);
if (v_isSharedCheck_467_ == 0)
{
v___x_450_ = v_x_437_;
v_isShared_451_ = v_isSharedCheck_467_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v_x_437_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_467_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
if (lean_obj_tag(v_a_448_) == 0)
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_462_; 
lean_dec_ref(v_as_435_);
v_a_452_ = lean_ctor_get(v_a_448_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v_a_448_);
if (v_isSharedCheck_462_ == 0)
{
v___x_454_ = v_a_448_;
v_isShared_455_ = v_isSharedCheck_462_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v_a_448_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_462_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v_a_452_);
v___x_457_ = v___x_450_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_461_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_459_; 
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_457_);
v___x_459_ = v___x_454_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
else
{
lean_object* v_a_463_; size_t v___x_464_; size_t v___x_465_; lean_object* v___x_466_; 
lean_del_object(v___x_450_);
v_a_463_ = lean_ctor_get(v_a_448_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v_a_448_, 1);
v___x_464_ = ((size_t)1ULL);
v___x_465_ = lean_usize_add(v_i_434_, v___x_464_);
v___x_466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg(v_as_435_, v_sz_436_, v___x_465_, v_a_463_);
return v___x_466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___boxed(lean_object* v_as_468_, lean_object* v_sz_469_, lean_object* v_i_470_, lean_object* v_b_471_, lean_object* v___y_472_){
_start:
{
size_t v_sz_boxed_473_; size_t v_i_boxed_474_; lean_object* v_res_475_; 
v_sz_boxed_473_ = lean_unbox_usize(v_sz_469_);
lean_dec(v_sz_469_);
v_i_boxed_474_ = lean_unbox_usize(v_i_470_);
lean_dec(v_i_470_);
v_res_475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg(v_as_468_, v_sz_boxed_473_, v_i_boxed_474_, v_b_471_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__1(lean_object* v_fst_476_, lean_object* v___f_477_, lean_object* v_x_478_){
_start:
{
if (lean_obj_tag(v_x_478_) == 0)
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_488_; 
lean_dec_ref(v___f_477_);
lean_dec_ref(v_fst_476_);
v_a_480_ = lean_ctor_get(v_x_478_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v_x_478_);
if (v_isSharedCheck_488_ == 0)
{
v___x_482_ = v_x_478_;
v_isShared_483_ = v_isSharedCheck_488_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v_x_478_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_488_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_487_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_486_; 
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
}
}
else
{
lean_object* v___x_489_; size_t v_sz_490_; size_t v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; lean_object* v___x_495_; 
lean_dec_ref_known(v_x_478_, 1);
v___x_489_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___closed__1));
v_sz_490_ = lean_array_size(v_fst_476_);
v___x_491_ = ((size_t)0ULL);
v___x_492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg(v_fst_476_, v_sz_490_, v___x_491_, v___x_489_);
v___x_493_ = lean_unsigned_to_nat(0u);
v___x_494_ = 0;
v___x_495_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_493_, v___x_494_, v___x_492_, v___f_477_);
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__1___boxed(lean_object* v_fst_496_, lean_object* v___f_497_, lean_object* v_x_498_, lean_object* v___y_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Std_Async_Selectable_combine___redArg___lam__1(v_fst_496_, v___f_497_, v_x_498_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__2(lean_object* v_selectables_501_, lean_object* v___x_502_, lean_object* v___f_503_, lean_object* v_x_504_){
_start:
{
if (lean_obj_tag(v_x_504_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_514_; 
lean_dec_ref(v___f_503_);
lean_dec_ref(v_selectables_501_);
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
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_531_; 
v_a_515_ = lean_ctor_get(v_x_504_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v_x_504_);
if (v_isSharedCheck_531_ == 0)
{
v___x_517_ = v_x_504_;
v_isShared_518_ = v_isSharedCheck_531_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v_x_504_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_531_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; lean_object* v_fst_520_; lean_object* v_snd_521_; lean_object* v___x_522_; lean_object* v___f_523_; lean_object* v___x_525_; 
v___x_519_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(v_selectables_501_, v_a_515_);
v_fst_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_fst_520_);
v_snd_521_ = lean_ctor_get(v___x_519_, 1);
lean_inc(v_snd_521_);
lean_dec_ref(v___x_519_);
v___x_522_ = lean_st_ref_set(v___x_502_, v_snd_521_);
v___f_523_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_523_, 0, v_fst_520_);
lean_closure_set(v___f_523_, 1, v___f_503_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_522_);
v___x_525_ = v___x_517_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_522_);
v___x_525_ = v_reuseFailAlloc_530_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; lean_object* v___x_529_; 
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
v___x_527_ = lean_unsigned_to_nat(0u);
v___x_528_ = 0;
v___x_529_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_527_, v___x_528_, v___x_526_, v___f_523_);
return v___x_529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__2___boxed(lean_object* v_selectables_532_, lean_object* v___x_533_, lean_object* v___f_534_, lean_object* v_x_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Std_Async_Selectable_combine___redArg___lam__2(v_selectables_532_, v___x_533_, v___f_534_, v_x_535_);
lean_dec(v___x_533_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__3(lean_object* v___x_538_, lean_object* v___f_539_){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; lean_object* v___x_546_; 
v___x_541_ = lean_st_ref_get(v___x_538_);
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = 0;
v___x_546_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_544_, v___x_545_, v___x_543_, v___f_539_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__3___boxed(lean_object* v___x_547_, lean_object* v___f_548_, lean_object* v___y_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Std_Async_Selectable_combine___redArg___lam__3(v___x_547_, v___f_548_);
lean_dec(v___x_547_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__4(lean_object* v___x_551_, lean_object* v_x_552_){
_start:
{
if (lean_obj_tag(v_x_552_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_562_; 
v_a_554_ = lean_ctor_get(v_x_552_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v_x_552_);
if (v_isSharedCheck_562_ == 0)
{
v___x_556_ = v_x_552_;
v_isShared_557_ = v_isSharedCheck_562_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v_x_552_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_562_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_561_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; 
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
return v___x_560_;
}
}
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_583_; 
v_a_563_ = lean_ctor_get(v_x_552_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v_x_552_);
if (v_isSharedCheck_583_ == 0)
{
v___x_565_ = v_x_552_;
v_isShared_566_ = v_isSharedCheck_583_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v_x_552_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_583_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v_fst_567_; 
v_fst_567_ = lean_ctor_get(v_a_563_, 0);
lean_inc(v_fst_567_);
lean_dec(v_a_563_);
if (lean_obj_tag(v_fst_567_) == 0)
{
lean_object* v___x_569_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_551_);
v___x_569_ = v___x_565_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_551_);
v___x_569_ = v_reuseFailAlloc_571_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_570_; 
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
}
else
{
lean_object* v_val_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_582_; 
v_val_572_ = lean_ctor_get(v_fst_567_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v_fst_567_);
if (v_isSharedCheck_582_ == 0)
{
v___x_574_ = v_fst_567_;
v_isShared_575_ = v_isSharedCheck_582_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_val_572_);
lean_dec(v_fst_567_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_582_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v_val_572_);
v___x_577_ = v___x_565_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_val_572_);
v___x_577_ = v_reuseFailAlloc_581_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_579_; 
if (v_isShared_575_ == 0)
{
lean_ctor_set_tag(v___x_574_, 0);
lean_ctor_set(v___x_574_, 0, v___x_577_);
v___x_579_ = v___x_574_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_577_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__4___boxed(lean_object* v___x_584_, lean_object* v_x_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Std_Async_Selectable_combine___redArg___lam__4(v___x_584_, v_x_585_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__9(lean_object* v___x_588_, lean_object* v_a_589_, lean_object* v___f_590_, uint8_t v_a_591_, lean_object* v___f_592_, lean_object* v_x_593_){
_start:
{
if (lean_obj_tag(v_x_593_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_603_; 
lean_dec_ref(v___f_592_);
lean_dec_ref(v___f_590_);
v_a_595_ = lean_ctor_get(v_x_593_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v_x_593_);
if (v_isSharedCheck_603_ == 0)
{
v___x_597_ = v_x_593_;
v_isShared_598_ = v_isSharedCheck_603_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v_x_593_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_603_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_602_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_601_; 
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
return v___x_601_;
}
}
}
else
{
lean_object* v_a_604_; 
v_a_604_ = lean_ctor_get(v_x_593_, 0);
lean_inc(v_a_604_);
lean_dec_ref_known(v_x_593_, 1);
if (lean_obj_tag(v_a_604_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_616_; 
lean_dec_ref(v___f_592_);
lean_dec_ref(v___f_590_);
v_a_605_ = lean_ctor_get(v_a_604_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v_a_604_);
if (v_isSharedCheck_616_ == 0)
{
v___x_607_ = v_a_604_;
v_isShared_608_ = v_isSharedCheck_616_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v_a_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_616_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_609_, 0, v_a_605_);
v___x_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v___x_588_);
v___x_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
if (v_isShared_608_ == 0)
{
lean_ctor_set_tag(v___x_607_, 1);
lean_ctor_set(v___x_607_, 0, v___x_611_);
v___x_613_ = v___x_607_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_611_);
v___x_613_ = v_reuseFailAlloc_615_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_614_; 
v___x_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
return v___x_614_;
}
}
}
else
{
lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_628_; 
v_isSharedCheck_628_ = !lean_is_exclusive(v_a_604_);
if (v_isSharedCheck_628_ == 0)
{
lean_object* v_unused_629_; 
v_unused_629_ = lean_ctor_get(v_a_604_, 0);
lean_dec(v_unused_629_);
v___x_618_ = v_a_604_;
v_isShared_619_ = v_isSharedCheck_628_;
goto v_resetjp_617_;
}
else
{
lean_dec(v_a_604_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_628_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_620_ = lean_io_promise_result_opt(v_a_589_);
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = lean_io_bind_task(v___x_620_, v___f_590_, v___x_621_, v_a_591_);
lean_dec_ref(v___x_622_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_588_);
v___x_624_ = v___x_618_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_588_);
v___x_624_ = v_reuseFailAlloc_627_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
v___x_626_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_621_, v_a_591_, v___x_625_, v___f_592_);
return v___x_626_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__9___boxed(lean_object* v___x_630_, lean_object* v_a_631_, lean_object* v___f_632_, lean_object* v_a_633_, lean_object* v___f_634_, lean_object* v_x_635_, lean_object* v___y_636_){
_start:
{
uint8_t v_a_11463__boxed_637_; lean_object* v_res_638_; 
v_a_11463__boxed_637_ = lean_unbox(v_a_633_);
v_res_638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__9(v___x_630_, v_a_631_, v___f_632_, v_a_11463__boxed_637_, v___f_634_, v_x_635_);
lean_dec(v_a_631_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__10(lean_object* v_a_639_, lean_object* v_finished_640_, uint8_t v_a_641_, lean_object* v___f_642_, lean_object* v___f_643_, lean_object* v___x_644_, lean_object* v___f_645_, lean_object* v___f_646_, lean_object* v_x_647_){
_start:
{
if (lean_obj_tag(v_x_647_) == 0)
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_657_; 
lean_dec_ref(v___f_646_);
lean_dec_ref(v___f_645_);
lean_dec_ref(v___f_643_);
lean_dec_ref(v___f_642_);
lean_dec(v_finished_640_);
lean_dec_ref(v_a_639_);
v_a_649_ = lean_ctor_get(v_x_647_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v_x_647_);
if (v_isSharedCheck_657_ == 0)
{
v___x_651_ = v_x_647_;
v_isShared_652_ = v_isSharedCheck_657_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v_x_647_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_657_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_656_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_655_; 
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
return v___x_655_;
}
}
}
else
{
lean_object* v_selector_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_674_; 
v_selector_658_ = lean_ctor_get(v_a_639_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v_a_639_);
if (v_isSharedCheck_674_ == 0)
{
lean_object* v_unused_675_; 
v_unused_675_ = lean_ctor_get(v_a_639_, 1);
lean_dec(v_unused_675_);
v___x_660_ = v_a_639_;
v_isShared_661_ = v_isSharedCheck_674_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_selector_658_);
lean_dec(v_a_639_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_674_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v_a_662_; lean_object* v_registerFn_663_; lean_object* v___x_665_; 
v_a_662_ = lean_ctor_get(v_x_647_, 0);
lean_inc_n(v_a_662_, 2);
lean_dec_ref_known(v_x_647_, 1);
v_registerFn_663_ = lean_ctor_get(v_selector_658_, 1);
lean_inc_ref(v_registerFn_663_);
lean_dec_ref(v_selector_658_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 1, v_a_662_);
lean_ctor_set(v___x_660_, 0, v_finished_640_);
v___x_665_ = v___x_660_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_finished_640_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_a_662_);
v___x_665_ = v_reuseFailAlloc_673_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___f_671_; lean_object* v___x_672_; 
v___x_666_ = lean_apply_2(v_registerFn_663_, v___x_665_, lean_box(0));
v___x_667_ = lean_unsigned_to_nat(0u);
v___x_668_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_667_, v_a_641_, v___x_666_, v___f_642_);
v___x_669_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_667_, v_a_641_, v___x_668_, v___f_643_);
v___x_670_ = lean_box(v_a_641_);
v___f_671_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__9___boxed), 7, 5);
lean_closure_set(v___f_671_, 0, v___x_644_);
lean_closure_set(v___f_671_, 1, v_a_662_);
lean_closure_set(v___f_671_, 2, v___f_645_);
lean_closure_set(v___f_671_, 3, v___x_670_);
lean_closure_set(v___f_671_, 4, v___f_646_);
v___x_672_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_667_, v_a_641_, v___x_669_, v___f_671_);
return v___x_672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__10___boxed(lean_object* v_a_676_, lean_object* v_finished_677_, lean_object* v_a_678_, lean_object* v___f_679_, lean_object* v___f_680_, lean_object* v___x_681_, lean_object* v___f_682_, lean_object* v___f_683_, lean_object* v_x_684_, lean_object* v___y_685_){
_start:
{
uint8_t v_a_11552__boxed_686_; lean_object* v_res_687_; 
v_a_11552__boxed_686_ = lean_unbox(v_a_678_);
v_res_687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__10(v_a_676_, v_finished_677_, v_a_11552__boxed_686_, v___f_679_, v___f_680_, v___x_681_, v___f_682_, v___f_683_, v_x_684_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__7(lean_object* v___x_688_, uint8_t v_a_689_, lean_object* v___f_690_, lean_object* v___f_691_, lean_object* v_a_692_){
_start:
{
lean_object* v_val_695_; 
if (lean_obj_tag(v_a_692_) == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; 
lean_dec_ref(v___f_691_);
lean_dec_ref(v___f_690_);
v___x_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_688_);
v___x_704_ = lean_task_pure(v___x_703_);
return v___x_704_;
}
else
{
lean_object* v_val_705_; lean_object* v___x_706_; 
v_val_705_ = lean_ctor_get(v_a_692_, 0);
lean_inc(v_val_705_);
lean_dec_ref_known(v_a_692_, 1);
v___x_706_ = l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__1___redArg(v_val_705_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_706_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
lean_ctor_set_tag(v___x_709_, 1);
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
v_val_695_ = v___x_712_;
goto v___jp_694_;
}
}
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
v_a_715_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_706_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_706_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
lean_ctor_set_tag(v___x_717_, 0);
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
v_val_695_ = v___x_720_;
goto v___jp_694_;
}
}
}
}
v___jp_694_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v_val_695_);
v___x_697_ = lean_unsigned_to_nat(0u);
v___x_698_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_697_, v_a_689_, v___x_696_, v___f_690_);
v___x_699_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_697_, v_a_689_, v___x_698_, v___f_691_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_701_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
lean_dec_ref_known(v___x_699_, 1);
v___x_701_ = lean_task_pure(v_a_700_);
return v___x_701_;
}
else
{
lean_object* v_a_702_; 
v_a_702_ = lean_ctor_get(v___x_699_, 0);
lean_inc_ref(v_a_702_);
lean_dec_ref_known(v___x_699_, 1);
return v_a_702_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__7___boxed(lean_object* v___x_723_, lean_object* v_a_724_, lean_object* v___f_725_, lean_object* v___f_726_, lean_object* v_a_727_, lean_object* v___y_728_){
_start:
{
uint8_t v_a_11627__boxed_729_; lean_object* v_res_730_; 
v_a_11627__boxed_729_ = lean_unbox(v_a_724_);
v_res_730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__7(v___x_723_, v_a_11627__boxed_729_, v___f_725_, v___f_726_, v_a_727_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__6(lean_object* v_a_731_, uint8_t v_a_732_, lean_object* v___f_733_, lean_object* v_x_734_){
_start:
{
if (lean_obj_tag(v_x_734_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_744_; 
lean_dec_ref(v___f_733_);
lean_dec_ref(v_a_731_);
v_a_736_ = lean_ctor_get(v_x_734_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v_x_734_);
if (v_isSharedCheck_744_ == 0)
{
v___x_738_ = v_x_734_;
v_isShared_739_ = v_isSharedCheck_744_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v_x_734_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_744_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_743_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_742_; 
v___x_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
return v___x_742_;
}
}
}
else
{
lean_object* v_a_745_; lean_object* v_cont_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v_a_745_ = lean_ctor_get(v_x_734_, 0);
lean_inc(v_a_745_);
lean_dec_ref_known(v_x_734_, 1);
v_cont_746_ = lean_ctor_get(v_a_731_, 1);
lean_inc_ref(v_cont_746_);
lean_dec_ref(v_a_731_);
v___x_747_ = lean_apply_2(v_cont_746_, v_a_745_, lean_box(0));
v___x_748_ = lean_unsigned_to_nat(0u);
v___x_749_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_748_, v_a_732_, v___x_747_, v___f_733_);
return v___x_749_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__6___boxed(lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v___f_752_, lean_object* v_x_753_, lean_object* v___y_754_){
_start:
{
uint8_t v_a_11699__boxed_755_; lean_object* v_res_756_; 
v_a_11699__boxed_755_ = lean_unbox(v_a_751_);
v_res_756_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__6(v_a_750_, v_a_11699__boxed_755_, v___f_752_, v_x_753_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__8(lean_object* v_waiter_757_, lean_object* v___f_758_, uint8_t v_a_759_, lean_object* v___f_760_, lean_object* v_x_761_){
_start:
{
if (lean_obj_tag(v_x_761_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v_a_763_ = lean_ctor_get(v_x_761_, 0);
lean_inc(v_a_763_);
lean_dec_ref_known(v_x_761_, 1);
v___x_764_ = l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__0___redArg(v_a_763_, v_waiter_757_, v___f_758_);
v___x_765_ = lean_unsigned_to_nat(0u);
v___x_766_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_765_, v_a_759_, v___x_764_, v___f_760_);
return v___x_766_;
}
else
{
lean_object* v___x_767_; 
lean_dec_ref(v___f_760_);
lean_dec_ref(v___f_758_);
lean_dec_ref(v_waiter_757_);
v___x_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_767_, 0, v_x_761_);
return v___x_767_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__8___boxed(lean_object* v_waiter_768_, lean_object* v___f_769_, lean_object* v_a_770_, lean_object* v___f_771_, lean_object* v_x_772_, lean_object* v___y_773_){
_start:
{
uint8_t v_a_11738__boxed_774_; lean_object* v_res_775_; 
v_a_11738__boxed_774_ = lean_unbox(v_a_770_);
v_res_775_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__8(v_waiter_768_, v___f_769_, v_a_11738__boxed_774_, v___f_771_, v_x_772_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__11(lean_object* v_a_776_, lean_object* v___f_777_, lean_object* v___x_778_, lean_object* v___f_779_, lean_object* v_waiter_780_, lean_object* v___f_781_, lean_object* v___f_782_, lean_object* v_finished_783_, lean_object* v___f_784_, lean_object* v___f_785_, lean_object* v_x_786_){
_start:
{
if (lean_obj_tag(v_x_786_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_796_; 
lean_dec_ref(v___f_785_);
lean_dec_ref(v___f_784_);
lean_dec(v_finished_783_);
lean_dec_ref(v___f_782_);
lean_dec_ref(v___f_781_);
lean_dec_ref(v_waiter_780_);
lean_dec_ref(v___f_779_);
lean_dec_ref(v___f_777_);
lean_dec_ref(v_a_776_);
v_a_788_ = lean_ctor_get(v_x_786_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v_x_786_);
if (v_isSharedCheck_796_ == 0)
{
v___x_790_ = v_x_786_;
v_isShared_791_ = v_isSharedCheck_796_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v_x_786_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_796_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_795_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_794_; 
v___x_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
return v___x_794_;
}
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_821_; 
v_a_797_ = lean_ctor_get(v_x_786_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v_x_786_);
if (v_isSharedCheck_821_ == 0)
{
v___x_799_ = v_x_786_;
v_isShared_800_ = v_isSharedCheck_821_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v_x_786_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_821_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
uint8_t v___x_801_; 
v___x_801_ = lean_unbox(v_a_797_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; lean_object* v___f_803_; lean_object* v___f_804_; lean_object* v___f_805_; lean_object* v___f_806_; lean_object* v___x_808_; 
v___x_802_ = lean_io_promise_new();
lean_inc_n(v_a_797_, 4);
lean_inc_ref(v_a_776_);
v___f_803_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__6___boxed), 5, 3);
lean_closure_set(v___f_803_, 0, v_a_776_);
lean_closure_set(v___f_803_, 1, v_a_797_);
lean_closure_set(v___f_803_, 2, v___f_777_);
v___f_804_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_804_, 0, v___x_778_);
lean_closure_set(v___f_804_, 1, v_a_797_);
lean_closure_set(v___f_804_, 2, v___f_803_);
lean_closure_set(v___f_804_, 3, v___f_779_);
v___f_805_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_805_, 0, v_waiter_780_);
lean_closure_set(v___f_805_, 1, v___f_781_);
lean_closure_set(v___f_805_, 2, v_a_797_);
lean_closure_set(v___f_805_, 3, v___f_782_);
v___f_806_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__10___boxed), 10, 8);
lean_closure_set(v___f_806_, 0, v_a_776_);
lean_closure_set(v___f_806_, 1, v_finished_783_);
lean_closure_set(v___f_806_, 2, v_a_797_);
lean_closure_set(v___f_806_, 3, v___f_784_);
lean_closure_set(v___f_806_, 4, v___f_805_);
lean_closure_set(v___f_806_, 5, v___x_778_);
lean_closure_set(v___f_806_, 6, v___f_804_);
lean_closure_set(v___f_806_, 7, v___f_785_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_802_);
v___x_808_ = v___x_799_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_802_);
v___x_808_ = v_reuseFailAlloc_813_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_809_; lean_object* v___x_810_; uint8_t v___x_811_; lean_object* v___x_812_; 
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
v___x_810_ = lean_unsigned_to_nat(0u);
v___x_811_ = lean_unbox(v_a_797_);
lean_dec(v_a_797_);
v___x_812_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_810_, v___x_811_, v___x_809_, v___f_806_);
return v___x_812_;
}
}
else
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_818_; 
lean_dec(v_a_797_);
lean_dec_ref(v___f_785_);
lean_dec_ref(v___f_784_);
lean_dec(v_finished_783_);
lean_dec_ref(v___f_782_);
lean_dec_ref(v___f_781_);
lean_dec_ref(v_waiter_780_);
lean_dec_ref(v___f_779_);
lean_dec_ref(v___f_777_);
lean_dec_ref(v_a_776_);
v___x_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_778_);
v___x_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
lean_ctor_set(v___x_815_, 1, v___x_778_);
v___x_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_816_);
v___x_818_ = v___x_799_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_820_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_819_; 
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
return v___x_819_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__11___boxed(lean_object* v_a_822_, lean_object* v___f_823_, lean_object* v___x_824_, lean_object* v___f_825_, lean_object* v_waiter_826_, lean_object* v___f_827_, lean_object* v___f_828_, lean_object* v_finished_829_, lean_object* v___f_830_, lean_object* v___f_831_, lean_object* v_x_832_, lean_object* v___y_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__11(v_a_822_, v___f_823_, v___x_824_, v___f_825_, v_waiter_826_, v___f_827_, v___f_828_, v_finished_829_, v___f_830_, v___f_831_, v_x_832_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__4(lean_object* v___x_835_){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_837_, 0, v___x_835_);
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__4___boxed(lean_object* v___x_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__4(v___x_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__2(lean_object* v_promise_842_, lean_object* v_x_843_){
_start:
{
if (lean_obj_tag(v_x_843_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_853_; 
v_a_845_ = lean_ctor_get(v_x_843_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v_x_843_);
if (v_isSharedCheck_853_ == 0)
{
v___x_847_ = v_x_843_;
v_isShared_848_ = v_isSharedCheck_853_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v_x_843_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_853_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_852_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
lean_object* v___x_851_; 
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
return v___x_851_;
}
}
}
else
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_854_ = lean_io_promise_resolve(v_x_843_, v_promise_842_);
v___x_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
v___x_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
return v___x_856_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__2___boxed(lean_object* v_promise_857_, lean_object* v_x_858_, lean_object* v___y_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__2(v_promise_857_, v_x_858_);
lean_dec(v_promise_857_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__5(lean_object* v___x_861_, lean_object* v_x_862_){
_start:
{
if (lean_obj_tag(v_x_862_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_872_; 
lean_dec_ref(v___x_861_);
v_a_864_ = lean_ctor_get(v_x_862_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v_x_862_);
if (v_isSharedCheck_872_ == 0)
{
v___x_866_ = v_x_862_;
v_isShared_867_ = v_isSharedCheck_872_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v_x_862_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_872_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_871_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_870_; 
v___x_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
return v___x_870_;
}
}
}
else
{
lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_881_; 
v_isSharedCheck_881_ = !lean_is_exclusive(v_x_862_);
if (v_isSharedCheck_881_ == 0)
{
lean_object* v_unused_882_; 
v_unused_882_ = lean_ctor_get(v_x_862_, 0);
lean_dec(v_unused_882_);
v___x_874_ = v_x_862_;
v_isShared_875_ = v_isSharedCheck_881_;
goto v_resetjp_873_;
}
else
{
lean_dec(v_x_862_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_881_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_876_, 0, v___x_861_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_876_);
v___x_878_ = v___x_874_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__5___boxed(lean_object* v___x_883_, lean_object* v_x_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__5(v___x_883_, v_x_884_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0(lean_object* v_x_887_){
_start:
{
if (lean_obj_tag(v_x_887_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_897_; 
v_a_889_ = lean_ctor_get(v_x_887_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v_x_887_);
if (v_isSharedCheck_897_ == 0)
{
v___x_891_ = v_x_887_;
v_isShared_892_ = v_isSharedCheck_897_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v_x_887_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_897_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_896_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_895_; 
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
return v___x_895_;
}
}
}
else
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_907_; 
v_a_898_ = lean_ctor_get(v_x_887_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v_x_887_);
if (v_isSharedCheck_907_ == 0)
{
v___x_900_ = v_x_887_;
v_isShared_901_ = v_isSharedCheck_907_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v_x_887_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_907_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_906_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
return v___x_905_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0___boxed(lean_object* v_x_908_, lean_object* v___y_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0(v_x_908_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__3(lean_object* v___x_911_, lean_object* v_x_912_){
_start:
{
if (lean_obj_tag(v_x_912_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_922_; 
v_a_914_ = lean_ctor_get(v_x_912_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v_x_912_);
if (v_isSharedCheck_922_ == 0)
{
v___x_916_ = v_x_912_;
v_isShared_917_ = v_isSharedCheck_922_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v_x_912_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_922_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_921_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_920_; 
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
return v___x_920_;
}
}
}
else
{
lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_931_; 
v_isSharedCheck_931_ = !lean_is_exclusive(v_x_912_);
if (v_isSharedCheck_931_ == 0)
{
lean_object* v_unused_932_; 
v_unused_932_ = lean_ctor_get(v_x_912_, 0);
lean_dec(v_unused_932_);
v___x_924_ = v_x_912_;
v_isShared_925_ = v_isSharedCheck_931_;
goto v_resetjp_923_;
}
else
{
lean_dec(v_x_912_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_931_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
lean_ctor_set_tag(v___x_924_, 0);
lean_ctor_set(v___x_924_, 0, v___x_911_);
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_911_);
v___x_927_ = v_reuseFailAlloc_930_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
v___x_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
return v___x_929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__3___boxed(lean_object* v___x_933_, lean_object* v_x_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__3(v___x_933_, v_x_934_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1(lean_object* v_promise_937_, lean_object* v_x_938_){
_start:
{
if (lean_obj_tag(v_x_938_) == 0)
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_950_; 
v_a_940_ = lean_ctor_get(v_x_938_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v_x_938_);
if (v_isSharedCheck_950_ == 0)
{
v___x_942_ = v_x_938_;
v_isShared_943_ = v_isSharedCheck_950_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v_x_938_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_950_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_949_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_946_ = lean_io_promise_resolve(v___x_945_, v_promise_937_);
v___x_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
return v___x_948_;
}
}
}
else
{
lean_object* v___x_951_; 
v___x_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_951_, 0, v_x_938_);
return v___x_951_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1___boxed(lean_object* v_promise_952_, lean_object* v_x_953_, lean_object* v___y_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1(v_promise_952_, v_x_953_);
lean_dec(v_promise_952_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__12___boxed(lean_object* v_i_966_, lean_object* v_waiter_967_, lean_object* v_as_968_, lean_object* v_sz_969_, lean_object* v_x_970_, lean_object* v___y_971_){
_start:
{
size_t v_i_boxed_972_; size_t v_sz_boxed_973_; lean_object* v_res_974_; 
v_i_boxed_972_ = lean_unbox_usize(v_i_966_);
lean_dec(v_i_966_);
v_sz_boxed_973_ = lean_unbox_usize(v_sz_969_);
lean_dec(v_sz_969_);
v_res_974_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__12(v_i_boxed_972_, v_waiter_967_, v_as_968_, v_sz_boxed_973_, v_x_970_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(lean_object* v_waiter_975_, lean_object* v_as_976_, size_t v_sz_977_, size_t v_i_978_, lean_object* v_b_979_){
_start:
{
uint8_t v___x_981_; 
v___x_981_ = lean_usize_dec_lt(v_i_978_, v_sz_977_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; lean_object* v___x_983_; 
lean_dec_ref(v_as_976_);
lean_dec_ref(v_waiter_975_);
v___x_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_982_, 0, v_b_979_);
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
return v___x_983_;
}
else
{
lean_object* v_finished_984_; lean_object* v_promise_985_; lean_object* v___x_986_; lean_object* v___f_987_; lean_object* v___f_988_; lean_object* v___f_989_; lean_object* v___x_990_; lean_object* v___f_991_; lean_object* v___f_992_; lean_object* v___f_993_; lean_object* v_a_994_; lean_object* v___f_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___f_1003_; lean_object* v___x_1004_; 
lean_dec_ref(v_b_979_);
v_finished_984_ = lean_ctor_get(v_waiter_975_, 0);
v_promise_985_ = lean_ctor_get(v_waiter_975_, 1);
v___x_986_ = lean_st_ref_get(v_finished_984_);
v___f_987_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__0));
lean_inc_n(v_promise_985_, 2);
v___f_988_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_988_, 0, v_promise_985_);
v___f_989_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_989_, 0, v_promise_985_);
v___x_990_ = lean_box(0);
v___f_991_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__1));
v___f_992_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__2));
v___f_993_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__4));
v_a_994_ = lean_array_uget_borrowed(v_as_976_, v_i_978_);
lean_inc(v_finished_984_);
lean_inc_ref(v_waiter_975_);
lean_inc(v_a_994_);
v___f_995_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__11___boxed), 12, 10);
lean_closure_set(v___f_995_, 0, v_a_994_);
lean_closure_set(v___f_995_, 1, v___f_989_);
lean_closure_set(v___f_995_, 2, v___x_990_);
lean_closure_set(v___f_995_, 3, v___f_988_);
lean_closure_set(v___f_995_, 4, v_waiter_975_);
lean_closure_set(v___f_995_, 5, v___f_992_);
lean_closure_set(v___f_995_, 6, v___f_991_);
lean_closure_set(v___f_995_, 7, v_finished_984_);
lean_closure_set(v___f_995_, 8, v___f_987_);
lean_closure_set(v___f_995_, 9, v___f_993_);
v___x_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_996_, 0, v___x_986_);
v___x_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
v___x_998_ = lean_unsigned_to_nat(0u);
v___x_999_ = 0;
v___x_1000_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_998_, v___x_999_, v___x_997_, v___f_995_);
v___x_1001_ = lean_box_usize(v_i_978_);
v___x_1002_ = lean_box_usize(v_sz_977_);
v___f_1003_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_1003_, 0, v___x_1001_);
lean_closure_set(v___f_1003_, 1, v_waiter_975_);
lean_closure_set(v___f_1003_, 2, v_as_976_);
lean_closure_set(v___f_1003_, 3, v___x_1002_);
v___x_1004_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_998_, v___x_999_, v___x_1000_, v___f_1003_);
return v___x_1004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__12(size_t v_i_1005_, lean_object* v_waiter_1006_, lean_object* v_as_1007_, size_t v_sz_1008_, lean_object* v_x_1009_){
_start:
{
if (lean_obj_tag(v_x_1009_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1019_; 
lean_dec_ref(v_as_1007_);
lean_dec_ref(v_waiter_1006_);
v_a_1011_ = lean_ctor_get(v_x_1009_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_x_1009_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1013_ = v_x_1009_;
v_isShared_1014_ = v_isSharedCheck_1019_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v_x_1009_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1019_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1011_);
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
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1039_; 
v_a_1020_ = lean_ctor_get(v_x_1009_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_x_1009_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1022_ = v_x_1009_;
v_isShared_1023_ = v_isSharedCheck_1039_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v_x_1009_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1039_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
if (lean_obj_tag(v_a_1020_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1034_; 
lean_dec_ref(v_as_1007_);
lean_dec_ref(v_waiter_1006_);
v_a_1024_ = lean_ctor_get(v_a_1020_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_a_1020_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1026_ = v_a_1020_;
v_isShared_1027_ = v_isSharedCheck_1034_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v_a_1020_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1034_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v_a_1024_);
v___x_1029_ = v___x_1022_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
lean_object* v___x_1031_; 
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1029_);
v___x_1031_ = v___x_1026_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
else
{
lean_object* v_a_1035_; size_t v___x_1036_; size_t v___x_1037_; lean_object* v___x_1038_; 
lean_del_object(v___x_1022_);
v_a_1035_ = lean_ctor_get(v_a_1020_, 0);
lean_inc(v_a_1035_);
lean_dec_ref_known(v_a_1020_, 1);
v___x_1036_ = ((size_t)1ULL);
v___x_1037_ = lean_usize_add(v_i_1005_, v___x_1036_);
v___x_1038_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(v_waiter_1006_, v_as_1007_, v_sz_1008_, v___x_1037_, v_a_1035_);
return v___x_1038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___boxed(lean_object* v_waiter_1040_, lean_object* v_as_1041_, lean_object* v_sz_1042_, lean_object* v_i_1043_, lean_object* v_b_1044_, lean_object* v___y_1045_){
_start:
{
size_t v_sz_boxed_1046_; size_t v_i_boxed_1047_; lean_object* v_res_1048_; 
v_sz_boxed_1046_ = lean_unbox_usize(v_sz_1042_);
lean_dec(v_sz_1042_);
v_i_boxed_1047_ = lean_unbox_usize(v_i_1043_);
lean_dec(v_i_1043_);
v_res_1048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(v_waiter_1040_, v_as_1041_, v_sz_boxed_1046_, v_i_boxed_1047_, v_b_1044_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__5(lean_object* v_fst_1051_, lean_object* v_waiter_1052_, lean_object* v_x_1053_){
_start:
{
if (lean_obj_tag(v_x_1053_) == 0)
{
lean_object* v___x_1055_; 
lean_dec_ref(v_waiter_1052_);
lean_dec_ref(v_fst_1051_);
v___x_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1055_, 0, v_x_1053_);
return v___x_1055_;
}
else
{
lean_object* v___x_1056_; size_t v_sz_1057_; size_t v___x_1058_; lean_object* v___x_1059_; lean_object* v___f_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; lean_object* v___x_1063_; 
lean_dec_ref_known(v_x_1053_, 1);
v___x_1056_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__3));
v_sz_1057_ = lean_array_size(v_fst_1051_);
v___x_1058_ = ((size_t)0ULL);
v___x_1059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(v_waiter_1052_, v_fst_1051_, v_sz_1057_, v___x_1058_, v___x_1056_);
v___f_1060_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___lam__5___closed__0));
v___x_1061_ = lean_unsigned_to_nat(0u);
v___x_1062_ = 0;
v___x_1063_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1061_, v___x_1062_, v___x_1059_, v___f_1060_);
return v___x_1063_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__5___boxed(lean_object* v_fst_1064_, lean_object* v_waiter_1065_, lean_object* v_x_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Std_Async_Selectable_combine___redArg___lam__5(v_fst_1064_, v_waiter_1065_, v_x_1066_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__6(lean_object* v_selectables_1069_, lean_object* v___x_1070_, lean_object* v_waiter_1071_, lean_object* v_x_1072_){
_start:
{
if (lean_obj_tag(v_x_1072_) == 0)
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1082_; 
lean_dec_ref(v_waiter_1071_);
lean_dec_ref(v_selectables_1069_);
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
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1099_; 
v_a_1083_ = lean_ctor_get(v_x_1072_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_x_1072_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1085_ = v_x_1072_;
v_isShared_1086_ = v_isSharedCheck_1099_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v_x_1072_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1099_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v_fst_1088_; lean_object* v_snd_1089_; lean_object* v___x_1090_; lean_object* v___f_1091_; lean_object* v___x_1093_; 
v___x_1087_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(v_selectables_1069_, v_a_1083_);
v_fst_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_fst_1088_);
v_snd_1089_ = lean_ctor_get(v___x_1087_, 1);
lean_inc(v_snd_1089_);
lean_dec_ref(v___x_1087_);
v___x_1090_ = lean_st_ref_set(v___x_1070_, v_snd_1089_);
v___f_1091_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_1091_, 0, v_fst_1088_);
lean_closure_set(v___f_1091_, 1, v_waiter_1071_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1090_);
v___x_1093_ = v___x_1085_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1090_);
v___x_1093_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; uint8_t v___x_1096_; lean_object* v___x_1097_; 
v___x_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
v___x_1095_ = lean_unsigned_to_nat(0u);
v___x_1096_ = 0;
v___x_1097_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1095_, v___x_1096_, v___x_1094_, v___f_1091_);
return v___x_1097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__6___boxed(lean_object* v_selectables_1100_, lean_object* v___x_1101_, lean_object* v_waiter_1102_, lean_object* v_x_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Std_Async_Selectable_combine___redArg___lam__6(v_selectables_1100_, v___x_1101_, v_waiter_1102_, v_x_1103_);
lean_dec(v___x_1101_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__7(lean_object* v___x_1106_, lean_object* v_selectables_1107_, lean_object* v_waiter_1108_){
_start:
{
lean_object* v___x_1110_; lean_object* v___f_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; lean_object* v___x_1116_; 
v___x_1110_ = lean_st_ref_get(v___x_1106_);
v___f_1111_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__6___boxed), 5, 3);
lean_closure_set(v___f_1111_, 0, v_selectables_1107_);
lean_closure_set(v___f_1111_, 1, v___x_1106_);
lean_closure_set(v___f_1111_, 2, v_waiter_1108_);
v___x_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1110_);
v___x_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
v___x_1114_ = lean_unsigned_to_nat(0u);
v___x_1115_ = 0;
v___x_1116_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1114_, v___x_1115_, v___x_1113_, v___f_1111_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__7___boxed(lean_object* v___x_1117_, lean_object* v_selectables_1118_, lean_object* v_waiter_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Std_Async_Selectable_combine___redArg___lam__7(v___x_1117_, v_selectables_1118_, v_waiter_1119_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__8(lean_object* v___x_1122_, lean_object* v_x_1123_){
_start:
{
if (lean_obj_tag(v_x_1123_) == 0)
{
lean_object* v___x_1125_; 
v___x_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1125_, 0, v_x_1123_);
return v___x_1125_;
}
else
{
lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1133_; 
v_isSharedCheck_1133_ = !lean_is_exclusive(v_x_1123_);
if (v_isSharedCheck_1133_ == 0)
{
lean_object* v_unused_1134_; 
v_unused_1134_ = lean_ctor_get(v_x_1123_, 0);
lean_dec(v_unused_1134_);
v___x_1127_ = v_x_1123_;
v_isShared_1128_ = v_isSharedCheck_1133_;
goto v_resetjp_1126_;
}
else
{
lean_dec(v_x_1123_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1133_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1122_);
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1122_);
v___x_1130_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1131_; 
v___x_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
return v___x_1131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__8___boxed(lean_object* v___x_1135_, lean_object* v_x_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Std_Async_Selectable_combine___redArg___lam__8(v___x_1135_, v_x_1136_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__1(lean_object* v___x_1139_, lean_object* v_x_1140_){
_start:
{
if (lean_obj_tag(v_x_1140_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1150_; 
v_a_1142_ = lean_ctor_get(v_x_1140_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_x_1140_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1144_ = v_x_1140_;
v_isShared_1145_ = v_isSharedCheck_1150_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v_x_1140_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1150_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
return v___x_1148_;
}
}
}
else
{
lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1159_; 
v_isSharedCheck_1159_ = !lean_is_exclusive(v_x_1140_);
if (v_isSharedCheck_1159_ == 0)
{
lean_object* v_unused_1160_; 
v_unused_1160_ = lean_ctor_get(v_x_1140_, 0);
lean_dec(v_unused_1160_);
v___x_1152_ = v_x_1140_;
v_isShared_1153_ = v_isSharedCheck_1159_;
goto v_resetjp_1151_;
}
else
{
lean_dec(v_x_1140_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1159_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1139_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1154_);
v___x_1156_ = v___x_1152_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
return v___x_1157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__1___boxed(lean_object* v___x_1161_, lean_object* v_x_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__1(v___x_1161_, v_x_1162_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__0(lean_object* v_x_1169_){
_start:
{
if (lean_obj_tag(v_x_1169_) == 0)
{
lean_object* v___x_1171_; 
lean_dec_ref_known(v_x_1169_, 1);
v___x_1171_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__0___closed__1));
return v___x_1171_;
}
else
{
lean_object* v___x_1172_; 
v___x_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1172_, 0, v_x_1169_);
return v___x_1172_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__0___boxed(lean_object* v_x_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__0(v_x_1173_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__2___boxed(lean_object* v_i_1179_, lean_object* v_as_1180_, lean_object* v_sz_1181_, lean_object* v_x_1182_, lean_object* v___y_1183_){
_start:
{
size_t v_i_boxed_1184_; size_t v_sz_boxed_1185_; lean_object* v_res_1186_; 
v_i_boxed_1184_ = lean_unbox_usize(v_i_1179_);
lean_dec(v_i_1179_);
v_sz_boxed_1185_ = lean_unbox_usize(v_sz_1181_);
lean_dec(v_sz_1181_);
v_res_1186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__2(v_i_boxed_1184_, v_as_1180_, v_sz_boxed_1185_, v_x_1182_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg(lean_object* v_as_1187_, size_t v_sz_1188_, size_t v_i_1189_, lean_object* v_b_1190_){
_start:
{
uint8_t v___x_1192_; 
v___x_1192_ = lean_usize_dec_lt(v_i_1189_, v_sz_1188_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
lean_dec_ref(v_as_1187_);
v___x_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1193_, 0, v_b_1190_);
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
return v___x_1194_;
}
else
{
lean_object* v_a_1195_; lean_object* v_selector_1196_; lean_object* v_unregisterFn_1197_; lean_object* v___x_1198_; lean_object* v___f_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; lean_object* v___x_1202_; lean_object* v___f_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___f_1207_; lean_object* v___x_1208_; 
v_a_1195_ = lean_array_uget_borrowed(v_as_1187_, v_i_1189_);
v_selector_1196_ = lean_ctor_get(v_a_1195_, 0);
v_unregisterFn_1197_ = lean_ctor_get(v_selector_1196_, 2);
lean_inc_ref(v_unregisterFn_1197_);
v___x_1198_ = lean_apply_1(v_unregisterFn_1197_, lean_box(0));
v___f_1199_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___closed__0));
v___x_1200_ = lean_unsigned_to_nat(0u);
v___x_1201_ = 0;
v___x_1202_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1200_, v___x_1201_, v___x_1198_, v___f_1199_);
v___f_1203_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___closed__1));
v___x_1204_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1200_, v___x_1201_, v___x_1202_, v___f_1203_);
v___x_1205_ = lean_box_usize(v_i_1189_);
v___x_1206_ = lean_box_usize(v_sz_1188_);
v___f_1207_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_1207_, 0, v___x_1205_);
lean_closure_set(v___f_1207_, 1, v_as_1187_);
lean_closure_set(v___f_1207_, 2, v___x_1206_);
v___x_1208_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1200_, v___x_1201_, v___x_1204_, v___f_1207_);
return v___x_1208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__2(size_t v_i_1209_, lean_object* v_as_1210_, size_t v_sz_1211_, lean_object* v_x_1212_){
_start:
{
if (lean_obj_tag(v_x_1212_) == 0)
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1222_; 
lean_dec_ref(v_as_1210_);
v_a_1214_ = lean_ctor_get(v_x_1212_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_x_1212_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1216_ = v_x_1212_;
v_isShared_1217_ = v_isSharedCheck_1222_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v_x_1212_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1222_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1214_);
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
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1242_; 
v_a_1223_ = lean_ctor_get(v_x_1212_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_x_1212_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1225_ = v_x_1212_;
v_isShared_1226_ = v_isSharedCheck_1242_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v_x_1212_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1242_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
if (lean_obj_tag(v_a_1223_) == 0)
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1237_; 
lean_dec_ref(v_as_1210_);
v_a_1227_ = lean_ctor_get(v_a_1223_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_a_1223_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1229_ = v_a_1223_;
v_isShared_1230_ = v_isSharedCheck_1237_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v_a_1223_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1237_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v_a_1227_);
v___x_1232_ = v___x_1225_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_object* v___x_1234_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v___x_1232_);
v___x_1234_ = v___x_1229_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1232_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
else
{
lean_object* v_a_1238_; size_t v___x_1239_; size_t v___x_1240_; lean_object* v___x_1241_; 
lean_del_object(v___x_1225_);
v_a_1238_ = lean_ctor_get(v_a_1223_, 0);
lean_inc(v_a_1238_);
lean_dec_ref_known(v_a_1223_, 1);
v___x_1239_ = ((size_t)1ULL);
v___x_1240_ = lean_usize_add(v_i_1209_, v___x_1239_);
v___x_1241_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg(v_as_1210_, v_sz_1211_, v___x_1240_, v_a_1238_);
return v___x_1241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___boxed(lean_object* v_as_1243_, lean_object* v_sz_1244_, lean_object* v_i_1245_, lean_object* v_b_1246_, lean_object* v___y_1247_){
_start:
{
size_t v_sz_boxed_1248_; size_t v_i_boxed_1249_; lean_object* v_res_1250_; 
v_sz_boxed_1248_ = lean_unbox_usize(v_sz_1244_);
lean_dec(v_sz_1244_);
v_i_boxed_1249_ = lean_unbox_usize(v_i_1245_);
lean_dec(v_i_1245_);
v_res_1250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg(v_as_1243_, v_sz_boxed_1248_, v_i_boxed_1249_, v_b_1246_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__9(lean_object* v_selectables_1251_, size_t v_sz_1252_, size_t v___x_1253_, lean_object* v___x_1254_, lean_object* v___f_1255_){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; lean_object* v___x_1260_; 
v___x_1257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg(v_selectables_1251_, v_sz_1252_, v___x_1253_, v___x_1254_);
v___x_1258_ = lean_unsigned_to_nat(0u);
v___x_1259_ = 0;
v___x_1260_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1258_, v___x_1259_, v___x_1257_, v___f_1255_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__9___boxed(lean_object* v_selectables_1261_, lean_object* v_sz_1262_, lean_object* v___x_1263_, lean_object* v___x_1264_, lean_object* v___f_1265_, lean_object* v___y_1266_){
_start:
{
size_t v_sz_boxed_1267_; size_t v___x_12533__boxed_1268_; lean_object* v_res_1269_; 
v_sz_boxed_1267_ = lean_unbox_usize(v_sz_1262_);
lean_dec(v_sz_1262_);
v___x_12533__boxed_1268_ = lean_unbox_usize(v___x_1263_);
lean_dec(v___x_1263_);
v_res_1269_ = l_Std_Async_Selectable_combine___redArg___lam__9(v_selectables_1261_, v_sz_boxed_1267_, v___x_12533__boxed_1268_, v___x_1264_, v___f_1265_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg(lean_object* v_selectables_1275_){
_start:
{
lean_object* v___f_1277_; lean_object* v___x_1278_; lean_object* v___f_1279_; lean_object* v___f_1280_; lean_object* v___f_1281_; lean_object* v___x_1282_; lean_object* v___f_1283_; size_t v_sz_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___f_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___f_1277_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___closed__0));
v___x_1278_ = l_IO_stdGenRef;
lean_inc_ref_n(v_selectables_1275_, 2);
v___f_1279_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_1279_, 0, v_selectables_1275_);
lean_closure_set(v___f_1279_, 1, v___x_1278_);
lean_closure_set(v___f_1279_, 2, v___f_1277_);
v___f_1280_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_1280_, 0, v___x_1278_);
lean_closure_set(v___f_1280_, 1, v___f_1279_);
v___f_1281_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_1281_, 0, v___x_1278_);
lean_closure_set(v___f_1281_, 1, v_selectables_1275_);
v___x_1282_ = lean_box(0);
v___f_1283_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___closed__1));
v_sz_1284_ = lean_array_size(v_selectables_1275_);
v___x_1285_ = lean_box_usize(v_sz_1284_);
v___x_1286_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___boxed__const__1));
v___f_1287_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__9___boxed), 6, 5);
lean_closure_set(v___f_1287_, 0, v_selectables_1275_);
lean_closure_set(v___f_1287_, 1, v___x_1285_);
lean_closure_set(v___f_1287_, 2, v___x_1286_);
lean_closure_set(v___f_1287_, 3, v___x_1282_);
lean_closure_set(v___f_1287_, 4, v___f_1283_);
v___x_1288_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1288_, 0, v___f_1280_);
lean_ctor_set(v___x_1288_, 1, v___f_1281_);
lean_ctor_set(v___x_1288_, 2, v___f_1287_);
v___x_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___boxed(lean_object* v_selectables_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Std_Async_Selectable_combine___redArg(v_selectables_1290_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine(lean_object* v_00_u03b1_1293_, lean_object* v_selectables_1294_){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = l_Std_Async_Selectable_combine___redArg(v_selectables_1294_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___boxed(lean_object* v_00_u03b1_1297_, lean_object* v_selectables_1298_, lean_object* v_a_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Std_Async_Selectable_combine(v_00_u03b1_1297_, v_selectables_1298_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2(lean_object* v_00_u03b1_1301_, lean_object* v_waiter_1302_, lean_object* v_as_1303_, size_t v_sz_1304_, size_t v_i_1305_, lean_object* v_b_1306_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(v_waiter_1302_, v_as_1303_, v_sz_1304_, v_i_1305_, v_b_1306_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___boxed(lean_object* v_00_u03b1_1309_, lean_object* v_waiter_1310_, lean_object* v_as_1311_, lean_object* v_sz_1312_, lean_object* v_i_1313_, lean_object* v_b_1314_, lean_object* v___y_1315_){
_start:
{
size_t v_sz_boxed_1316_; size_t v_i_boxed_1317_; lean_object* v_res_1318_; 
v_sz_boxed_1316_ = lean_unbox_usize(v_sz_1312_);
lean_dec(v_sz_1312_);
v_i_boxed_1317_ = lean_unbox_usize(v_i_1313_);
lean_dec(v_i_1313_);
v_res_1318_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2(v_00_u03b1_1309_, v_waiter_1310_, v_as_1311_, v_sz_boxed_1316_, v_i_boxed_1317_, v_b_1314_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3(lean_object* v_00_u03b1_1319_, lean_object* v_as_1320_, size_t v_sz_1321_, size_t v_i_1322_, lean_object* v_b_1323_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg(v_as_1320_, v_sz_1321_, v_i_1322_, v_b_1323_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___boxed(lean_object* v_00_u03b1_1326_, lean_object* v_as_1327_, lean_object* v_sz_1328_, lean_object* v_i_1329_, lean_object* v_b_1330_, lean_object* v___y_1331_){
_start:
{
size_t v_sz_boxed_1332_; size_t v_i_boxed_1333_; lean_object* v_res_1334_; 
v_sz_boxed_1332_ = lean_unbox_usize(v_sz_1328_);
lean_dec(v_sz_1328_);
v_i_boxed_1333_ = lean_unbox_usize(v_i_1329_);
lean_dec(v_i_1329_);
v_res_1334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3(v_00_u03b1_1326_, v_as_1327_, v_sz_boxed_1332_, v_i_boxed_1333_, v_b_1330_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4(lean_object* v_00_u03b1_1335_, lean_object* v_as_1336_, size_t v_sz_1337_, size_t v_i_1338_, lean_object* v_b_1339_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg(v_as_1336_, v_sz_1337_, v_i_1338_, v_b_1339_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___boxed(lean_object* v_00_u03b1_1342_, lean_object* v_as_1343_, lean_object* v_sz_1344_, lean_object* v_i_1345_, lean_object* v_b_1346_, lean_object* v___y_1347_){
_start:
{
size_t v_sz_boxed_1348_; size_t v_i_boxed_1349_; lean_object* v_res_1350_; 
v_sz_boxed_1348_ = lean_unbox_usize(v_sz_1344_);
lean_dec(v_sz_1344_);
v_i_boxed_1349_ = lean_unbox_usize(v_i_1345_);
lean_dec(v_i_1345_);
v_res_1350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4(v_00_u03b1_1342_, v_as_1343_, v_sz_boxed_1348_, v_i_boxed_1349_, v_b_1346_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__0(lean_object* v___y_1351_){
_start:
{
if (lean_obj_tag(v___y_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
v_a_1352_ = lean_ctor_get(v___y_1351_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___y_1351_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___y_1351_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___y_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1368_; 
v_a_1360_ = lean_ctor_get(v___y_1351_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___y_1351_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1362_ = v___y_1351_;
v_isShared_1363_ = v_isSharedCheck_1368_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___y_1351_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1368_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v_fst_1364_; lean_object* v___x_1366_; 
v_fst_1364_ = lean_ctor_get(v_a_1360_, 0);
lean_inc(v_fst_1364_);
lean_dec(v_a_1360_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v_fst_1364_);
v___x_1366_ = v___x_1362_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_fst_1364_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__1(lean_object* v___x_1369_, lean_object* v_x_1370_){
_start:
{
if (lean_obj_tag(v_x_1370_) == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = lean_mk_io_user_error(v___x_1369_);
v___x_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
return v___x_1372_;
}
else
{
lean_object* v_val_1373_; 
lean_dec_ref(v___x_1369_);
v_val_1373_ = lean_ctor_get(v_x_1370_, 0);
lean_inc(v_val_1373_);
return v_val_1373_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__1___boxed(lean_object* v___x_1374_, lean_object* v_x_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Std_Async_Selectable_one___redArg___lam__1(v___x_1374_, v_x_1375_);
lean_dec(v_x_1375_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__2(lean_object* v___f_1377_, lean_object* v_x_1378_){
_start:
{
if (lean_obj_tag(v_x_1378_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1388_; 
lean_dec_ref(v___f_1377_);
v_a_1380_ = lean_ctor_get(v_x_1378_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v_x_1378_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1382_ = v_x_1378_;
v_isShared_1383_ = v_isSharedCheck_1388_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v_x_1378_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1388_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
lean_object* v___x_1386_; 
v___x_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
return v___x_1386_;
}
}
}
else
{
lean_object* v_a_1389_; 
v_a_1389_ = lean_ctor_get(v_x_1378_, 0);
lean_inc(v_a_1389_);
lean_dec_ref_known(v_x_1378_, 1);
if (lean_obj_tag(v_a_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1398_; 
lean_dec_ref(v___f_1377_);
v_a_1390_ = lean_ctor_get(v_a_1389_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_a_1389_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1392_ = v_a_1389_;
v_isShared_1393_ = v_isSharedCheck_1398_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v_a_1389_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1398_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_object* v___x_1396_; 
v___x_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1395_);
return v___x_1396_;
}
}
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v_a_1399_ = lean_ctor_get(v_a_1389_, 0);
lean_inc(v_a_1399_);
lean_dec_ref_known(v_a_1389_, 1);
v___x_1400_ = lean_io_promise_result_opt(v_a_1399_);
lean_dec(v_a_1399_);
v___x_1401_ = lean_unsigned_to_nat(0u);
v___x_1402_ = 0;
v___x_1403_ = lean_task_map(v___f_1377_, v___x_1400_, v___x_1401_, v___x_1402_);
v___x_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
return v___x_1404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__2___boxed(lean_object* v___f_1405_, lean_object* v_x_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Std_Async_Selectable_one___redArg___lam__2(v___f_1405_, v_x_1406_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__3(lean_object* v_x_1414_, lean_object* v_x_1415_){
_start:
{
if (lean_obj_tag(v_x_1415_) == 0)
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1425_; 
lean_dec_ref(v_x_1414_);
v_a_1417_ = lean_ctor_get(v_x_1415_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_x_1415_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1419_ = v_x_1415_;
v_isShared_1420_ = v_isSharedCheck_1425_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v_x_1415_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1425_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
lean_object* v___x_1423_; 
v___x_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
return v___x_1423_;
}
}
}
else
{
lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1437_; 
v_isSharedCheck_1437_ = !lean_is_exclusive(v_x_1415_);
if (v_isSharedCheck_1437_ == 0)
{
lean_object* v_unused_1438_; 
v_unused_1438_ = lean_ctor_get(v_x_1415_, 0);
lean_dec(v_unused_1438_);
v___x_1427_ = v_x_1415_;
v_isShared_1428_ = v_isSharedCheck_1437_;
goto v_resetjp_1426_;
}
else
{
lean_dec(v_x_1415_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1437_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___f_1429_; lean_object* v___x_1431_; 
v___f_1429_ = ((lean_object*)(l_Std_Async_Selectable_one___redArg___lam__3___closed__2));
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 0, v_x_1414_);
v___x_1431_ = v___x_1427_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_x_1414_);
v___x_1431_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; lean_object* v___x_1435_; 
v___x_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
v___x_1433_ = lean_unsigned_to_nat(0u);
v___x_1434_ = 0;
v___x_1435_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1433_, v___x_1434_, v___x_1432_, v___f_1429_);
return v___x_1435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__3___boxed(lean_object* v_x_1439_, lean_object* v_x_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Std_Async_Selectable_one___redArg___lam__3(v_x_1439_, v_x_1440_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__4(lean_object* v_a_1443_, lean_object* v_registerFn_1444_, uint8_t v___x_1445_, lean_object* v___f_1446_, lean_object* v_x_1447_){
_start:
{
if (lean_obj_tag(v_x_1447_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1457_; 
lean_dec_ref(v___f_1446_);
lean_dec_ref(v_registerFn_1444_);
lean_dec(v_a_1443_);
v_a_1449_ = lean_ctor_get(v_x_1447_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_x_1447_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1451_ = v_x_1447_;
v_isShared_1452_ = v_isSharedCheck_1457_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v_x_1447_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1457_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v___x_1455_; 
v___x_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
return v___x_1455_;
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v_a_1458_ = lean_ctor_get(v_x_1447_, 0);
lean_inc(v_a_1458_);
lean_dec_ref_known(v_x_1447_, 1);
v___x_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1459_, 0, v_a_1458_);
lean_ctor_set(v___x_1459_, 1, v_a_1443_);
v___x_1460_ = lean_apply_2(v_registerFn_1444_, v___x_1459_, lean_box(0));
v___x_1461_ = lean_unsigned_to_nat(0u);
v___x_1462_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1461_, v___x_1445_, v___x_1460_, v___f_1446_);
return v___x_1462_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__4___boxed(lean_object* v_a_1463_, lean_object* v_registerFn_1464_, lean_object* v___x_1465_, lean_object* v___f_1466_, lean_object* v_x_1467_, lean_object* v___y_1468_){
_start:
{
uint8_t v___x_1885__boxed_1469_; lean_object* v_res_1470_; 
v___x_1885__boxed_1469_ = lean_unbox(v___x_1465_);
v_res_1470_ = l_Std_Async_Selectable_one___redArg___lam__4(v_a_1463_, v_registerFn_1464_, v___x_1885__boxed_1469_, v___f_1466_, v_x_1467_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__5(uint8_t v___x_1471_, lean_object* v___f_1472_){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1474_ = lean_box(v___x_1471_);
v___x_1475_ = lean_st_mk_ref(v___x_1474_);
v___x_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
v___x_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
v___x_1478_ = lean_unsigned_to_nat(0u);
v___x_1479_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1478_, v___x_1471_, v___x_1477_, v___f_1472_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__5___boxed(lean_object* v___x_1480_, lean_object* v___f_1481_, lean_object* v___y_1482_){
_start:
{
uint8_t v___x_1927__boxed_1483_; lean_object* v_res_1484_; 
v___x_1927__boxed_1483_ = lean_unbox(v___x_1480_);
v_res_1484_ = l_Std_Async_Selectable_one___redArg___lam__5(v___x_1927__boxed_1483_, v___f_1481_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__6(lean_object* v_unregisterFn_1485_, lean_object* v_x_1486_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = lean_apply_1(v_unregisterFn_1485_, lean_box(0));
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__6___boxed(lean_object* v_unregisterFn_1489_, lean_object* v_x_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Std_Async_Selectable_one___redArg___lam__6(v_unregisterFn_1489_, v_x_1490_);
lean_dec(v_x_1490_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__7(lean_object* v_registerFn_1493_, lean_object* v_unregisterFn_1494_, lean_object* v___f_1495_, lean_object* v_x_1496_){
_start:
{
if (lean_obj_tag(v_x_1496_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1506_; 
lean_dec_ref(v___f_1495_);
lean_dec_ref(v_unregisterFn_1494_);
lean_dec_ref(v_registerFn_1493_);
v_a_1498_ = lean_ctor_get(v_x_1496_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v_x_1496_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1500_ = v_x_1496_;
v_isShared_1501_ = v_isSharedCheck_1506_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v_x_1496_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1506_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1504_; 
v___x_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
return v___x_1504_;
}
}
}
else
{
lean_object* v_a_1507_; lean_object* v___f_1508_; uint8_t v___x_1509_; lean_object* v___x_1510_; lean_object* v___f_1511_; lean_object* v___x_1512_; lean_object* v___f_1513_; lean_object* v___f_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___y_1518_; 
v_a_1507_ = lean_ctor_get(v_x_1496_, 0);
lean_inc(v_a_1507_);
v___f_1508_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1508_, 0, v_x_1496_);
v___x_1509_ = 0;
v___x_1510_ = lean_box(v___x_1509_);
v___f_1511_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_1511_, 0, v_a_1507_);
lean_closure_set(v___f_1511_, 1, v_registerFn_1493_);
lean_closure_set(v___f_1511_, 2, v___x_1510_);
lean_closure_set(v___f_1511_, 3, v___f_1508_);
v___x_1512_ = lean_box(v___x_1509_);
v___f_1513_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__5___boxed), 3, 2);
lean_closure_set(v___f_1513_, 0, v___x_1512_);
lean_closure_set(v___f_1513_, 1, v___f_1511_);
v___f_1514_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__6___boxed), 3, 1);
lean_closure_set(v___f_1514_, 0, v_unregisterFn_1494_);
v___x_1515_ = lean_unsigned_to_nat(0u);
v___x_1516_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_1513_, v___f_1514_, v___x_1515_, v___x_1509_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1520_; 
lean_dec_ref(v___f_1495_);
v_a_1520_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1520_);
lean_dec_ref_known(v___x_1516_, 1);
if (lean_obj_tag(v_a_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
v_a_1521_ = lean_ctor_get(v_a_1520_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v_a_1520_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v_a_1520_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v_a_1520_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
v___y_1518_ = v___x_1526_;
goto v___jp_1517_;
}
}
}
else
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1537_; 
v_a_1529_ = lean_ctor_get(v_a_1520_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_a_1520_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1531_ = v_a_1520_;
v_isShared_1532_ = v_isSharedCheck_1537_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v_a_1520_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1537_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v_fst_1533_; lean_object* v___x_1535_; 
v_fst_1533_ = lean_ctor_get(v_a_1529_, 0);
lean_inc(v_fst_1533_);
lean_dec(v_a_1529_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v_fst_1533_);
v___x_1535_ = v___x_1531_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_fst_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
v___y_1518_ = v___x_1535_;
goto v___jp_1517_;
}
}
}
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1546_; 
v_a_1538_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1540_ = v___x_1516_;
v_isShared_1541_ = v_isSharedCheck_1546_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1516_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1546_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1542_ = lean_task_map(v___f_1495_, v_a_1538_, v___x_1515_, v___x_1509_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1542_);
v___x_1544_ = v___x_1540_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
v___jp_1517_:
{
lean_object* v___x_1519_; 
v___x_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1519_, 0, v___y_1518_);
return v___x_1519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__7___boxed(lean_object* v_registerFn_1547_, lean_object* v_unregisterFn_1548_, lean_object* v___f_1549_, lean_object* v_x_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Std_Async_Selectable_one___redArg___lam__7(v_registerFn_1547_, v_unregisterFn_1548_, v___f_1549_, v_x_1550_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__8(lean_object* v___f_1553_, lean_object* v_x_1554_){
_start:
{
if (lean_obj_tag(v_x_1554_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1564_; 
lean_dec_ref(v___f_1553_);
v_a_1556_ = lean_ctor_get(v_x_1554_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v_x_1554_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1558_ = v_x_1554_;
v_isShared_1559_ = v_isSharedCheck_1564_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v_x_1554_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1564_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
lean_object* v___x_1562_; 
v___x_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
return v___x_1562_;
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1588_; 
v_a_1565_ = lean_ctor_get(v_x_1554_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v_x_1554_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1567_ = v_x_1554_;
v_isShared_1568_ = v_isSharedCheck_1588_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v_x_1554_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1588_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
if (lean_obj_tag(v_a_1565_) == 1)
{
lean_object* v_val_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1579_; 
lean_dec_ref(v___f_1553_);
v_val_1569_ = lean_ctor_get(v_a_1565_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_a_1565_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1571_ = v_a_1565_;
v_isShared_1572_ = v_isSharedCheck_1579_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_val_1569_);
lean_dec(v_a_1565_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1579_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 0, v_val_1569_);
v___x_1574_ = v___x_1567_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_val_1569_);
v___x_1574_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1576_; 
if (v_isShared_1572_ == 0)
{
lean_ctor_set_tag(v___x_1571_, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1574_);
v___x_1576_ = v___x_1571_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
else
{
lean_object* v___x_1580_; lean_object* v___x_1582_; 
lean_dec(v_a_1565_);
v___x_1580_ = lean_io_promise_new();
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 0, v___x_1580_);
v___x_1582_ = v___x_1567_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1580_);
v___x_1582_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; uint8_t v___x_1585_; lean_object* v___x_1586_; 
v___x_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
v___x_1584_ = lean_unsigned_to_nat(0u);
v___x_1585_ = 0;
v___x_1586_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1584_, v___x_1585_, v___x_1583_, v___f_1553_);
return v___x_1586_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__8___boxed(lean_object* v___f_1589_, lean_object* v_x_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Std_Async_Selectable_one___redArg___lam__8(v___f_1589_, v_x_1590_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__9(lean_object* v___f_1593_, lean_object* v_x_1594_){
_start:
{
if (lean_obj_tag(v_x_1594_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1604_; 
lean_dec_ref(v___f_1593_);
v_a_1596_ = lean_ctor_get(v_x_1594_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v_x_1594_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1598_ = v_x_1594_;
v_isShared_1599_ = v_isSharedCheck_1604_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v_x_1594_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1604_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
lean_object* v___x_1602_; 
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
return v___x_1602_;
}
}
}
else
{
lean_object* v_a_1605_; lean_object* v_tryFn_1606_; lean_object* v_registerFn_1607_; lean_object* v_unregisterFn_1608_; lean_object* v___x_1609_; lean_object* v___f_1610_; lean_object* v___f_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; lean_object* v___x_1614_; 
v_a_1605_ = lean_ctor_get(v_x_1594_, 0);
lean_inc(v_a_1605_);
lean_dec_ref_known(v_x_1594_, 1);
v_tryFn_1606_ = lean_ctor_get(v_a_1605_, 0);
lean_inc_ref(v_tryFn_1606_);
v_registerFn_1607_ = lean_ctor_get(v_a_1605_, 1);
lean_inc_ref(v_registerFn_1607_);
v_unregisterFn_1608_ = lean_ctor_get(v_a_1605_, 2);
lean_inc_ref(v_unregisterFn_1608_);
lean_dec(v_a_1605_);
v___x_1609_ = lean_apply_1(v_tryFn_1606_, lean_box(0));
v___f_1610_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__7___boxed), 5, 3);
lean_closure_set(v___f_1610_, 0, v_registerFn_1607_);
lean_closure_set(v___f_1610_, 1, v_unregisterFn_1608_);
lean_closure_set(v___f_1610_, 2, v___f_1593_);
v___f_1611_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__8___boxed), 3, 1);
lean_closure_set(v___f_1611_, 0, v___f_1610_);
v___x_1612_ = lean_unsigned_to_nat(0u);
v___x_1613_ = 0;
v___x_1614_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1612_, v___x_1613_, v___x_1609_, v___f_1611_);
return v___x_1614_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__9___boxed(lean_object* v___f_1615_, lean_object* v_x_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Std_Async_Selectable_one___redArg___lam__9(v___f_1615_, v_x_1616_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__10(lean_object* v___f_1619_, lean_object* v_selectables_1620_, lean_object* v_____r_1621_){
_start:
{
lean_object* v_val_1624_; lean_object* v___x_1629_; lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
v___x_1629_ = l_Std_Async_Selectable_combine___redArg(v_selectables_1620_);
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1629_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1629_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v___jp_1623_:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; uint8_t v___x_1627_; lean_object* v___x_1628_; 
v___x_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1625_, 0, v_val_1624_);
v___x_1626_ = lean_unsigned_to_nat(0u);
v___x_1627_ = 0;
v___x_1628_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1626_, v___x_1627_, v___x_1625_, v___f_1619_);
return v___x_1628_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
lean_ctor_set_tag(v___x_1632_, 1);
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
v_val_1624_ = v___x_1635_;
goto v___jp_1623_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__10___boxed(lean_object* v___f_1638_, lean_object* v_selectables_1639_, lean_object* v_____r_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Std_Async_Selectable_one___redArg___lam__10(v___f_1638_, v_selectables_1639_, v_____r_1640_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__11(lean_object* v___f_1643_, lean_object* v_x_1644_){
_start:
{
if (lean_obj_tag(v_x_1644_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1654_; 
lean_dec_ref(v___f_1643_);
v_a_1646_ = lean_ctor_get(v_x_1644_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v_x_1644_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1648_ = v_x_1644_;
v_isShared_1649_ = v_isSharedCheck_1654_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v_x_1644_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1654_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
lean_object* v___x_1652_; 
v___x_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
return v___x_1652_;
}
}
}
else
{
lean_object* v_a_1655_; lean_object* v___x_1656_; 
v_a_1655_ = lean_ctor_get(v_x_1644_, 0);
lean_inc(v_a_1655_);
lean_dec_ref_known(v_x_1644_, 1);
v___x_1656_ = lean_apply_2(v___f_1643_, v_a_1655_, lean_box(0));
return v___x_1656_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__11___boxed(lean_object* v___f_1657_, lean_object* v_x_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Std_Async_Selectable_one___redArg___lam__11(v___f_1657_, v_x_1658_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg(lean_object* v_selectables_1671_){
_start:
{
lean_object* v___f_1673_; lean_object* v___f_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; uint8_t v___x_1677_; 
v___f_1673_ = ((lean_object*)(l_Std_Async_Selectable_one___redArg___closed__1));
lean_inc_ref(v_selectables_1671_);
v___f_1674_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__10___boxed), 4, 2);
lean_closure_set(v___f_1674_, 0, v___f_1673_);
lean_closure_set(v___f_1674_, 1, v_selectables_1671_);
v___x_1675_ = lean_array_get_size(v_selectables_1671_);
v___x_1676_ = lean_unsigned_to_nat(0u);
v___x_1677_ = lean_nat_dec_eq(v___x_1675_, v___x_1676_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
lean_dec_ref(v___f_1674_);
v___x_1678_ = lean_box(0);
v___x_1679_ = l_Std_Async_Selectable_one___redArg___lam__10(v___f_1673_, v_selectables_1671_, v___x_1678_);
return v___x_1679_;
}
else
{
lean_object* v___f_1680_; lean_object* v___x_1681_; uint8_t v___x_1682_; lean_object* v___x_1683_; 
lean_dec_ref(v_selectables_1671_);
v___f_1680_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__11___boxed), 3, 1);
lean_closure_set(v___f_1680_, 0, v___f_1674_);
v___x_1681_ = ((lean_object*)(l_Std_Async_Selectable_one___redArg___closed__5));
v___x_1682_ = 0;
v___x_1683_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1676_, v___x_1682_, v___x_1681_, v___f_1680_);
return v___x_1683_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___boxed(lean_object* v_selectables_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Std_Async_Selectable_one___redArg(v_selectables_1684_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one(lean_object* v_00_u03b1_1687_, lean_object* v_selectables_1688_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Std_Async_Selectable_one___redArg(v_selectables_1688_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___boxed(lean_object* v_00_u03b1_1691_, lean_object* v_selectables_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Std_Async_Selectable_one(v_00_u03b1_1691_, v_selectables_1692_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__3(lean_object* v_selectables_1695_, lean_object* v___f_1696_, lean_object* v_____r_1697_){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___f_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; lean_object* v___x_1706_; 
v___x_1699_ = l_IO_stdGenRef;
v___x_1700_ = lean_st_ref_get(v___x_1699_);
v___f_1701_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_1701_, 0, v_selectables_1695_);
lean_closure_set(v___f_1701_, 1, v___x_1699_);
lean_closure_set(v___f_1701_, 2, v___f_1696_);
v___x_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1700_);
v___x_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1702_);
v___x_1704_ = lean_unsigned_to_nat(0u);
v___x_1705_ = 0;
v___x_1706_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1704_, v___x_1705_, v___x_1703_, v___f_1701_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__3___boxed(lean_object* v_selectables_1707_, lean_object* v___f_1708_, lean_object* v_____r_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Std_Async_Selectable_tryOne___redArg___lam__3(v_selectables_1707_, v___f_1708_, v_____r_1709_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__0(lean_object* v___f_1712_, lean_object* v_x_1713_){
_start:
{
if (lean_obj_tag(v_x_1713_) == 0)
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1723_; 
lean_dec_ref(v___f_1712_);
v_a_1715_ = lean_ctor_get(v_x_1713_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v_x_1713_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1717_ = v_x_1713_;
v_isShared_1718_ = v_isSharedCheck_1723_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v_x_1713_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1723_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
return v___x_1721_;
}
}
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1725_; 
v_a_1724_ = lean_ctor_get(v_x_1713_, 0);
lean_inc(v_a_1724_);
lean_dec_ref_known(v_x_1713_, 1);
v___x_1725_ = lean_apply_2(v___f_1712_, v_a_1724_, lean_box(0));
return v___x_1725_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__0___boxed(lean_object* v___f_1726_, lean_object* v_x_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Std_Async_Selectable_tryOne___redArg___lam__0(v___f_1726_, v_x_1727_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg(lean_object* v_selectables_1737_){
_start:
{
lean_object* v___f_1739_; lean_object* v___f_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; uint8_t v___x_1743_; 
v___f_1739_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___closed__0));
lean_inc_ref(v_selectables_1737_);
v___f_1740_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_tryOne___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1740_, 0, v_selectables_1737_);
lean_closure_set(v___f_1740_, 1, v___f_1739_);
v___x_1741_ = lean_array_get_size(v_selectables_1737_);
v___x_1742_ = lean_unsigned_to_nat(0u);
v___x_1743_ = lean_nat_dec_eq(v___x_1741_, v___x_1742_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
lean_dec_ref(v___f_1740_);
v___x_1744_ = lean_box(0);
v___x_1745_ = l_Std_Async_Selectable_tryOne___redArg___lam__3(v_selectables_1737_, v___f_1739_, v___x_1744_);
return v___x_1745_;
}
else
{
lean_object* v___f_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; lean_object* v___x_1749_; 
lean_dec_ref(v_selectables_1737_);
v___f_1746_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_tryOne___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1746_, 0, v___f_1740_);
v___x_1747_ = ((lean_object*)(l_Std_Async_Selectable_tryOne___redArg___closed__3));
v___x_1748_ = 0;
v___x_1749_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1742_, v___x_1748_, v___x_1747_, v___f_1746_);
return v___x_1749_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___boxed(lean_object* v_selectables_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Std_Async_Selectable_tryOne___redArg(v_selectables_1750_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne(lean_object* v_00_u03b1_1753_, lean_object* v_selectables_1754_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Std_Async_Selectable_tryOne___redArg(v_selectables_1754_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___boxed(lean_object* v_00_u03b1_1757_, lean_object* v_selectables_1758_, lean_object* v_a_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Std_Async_Selectable_tryOne(v_00_u03b1_1757_, v_selectables_1758_);
return v_res_1760_;
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
