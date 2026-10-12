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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_io_promise_new();
lean_object* lean_st_ref_get(lean_object*);
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
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
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
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_Selectable_combine___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_Selectable_combine___redArg___lam__0___closed__0 = (const lean_object*)&l_Std_Async_Selectable_combine___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Async_Selectable_combine___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Selectable_combine___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Std_Async_Selectable_combine___redArg___lam__0___closed__1 = (const lean_object*)&l_Std_Async_Selectable_combine___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__0(size_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_Selectable_combine___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_Selectable_combine___redArg___lam__2___closed__0 = (const lean_object*)&l_Std_Async_Selectable_combine___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Std_Async_Selectable_combine___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Selectable_combine___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Std_Async_Selectable_combine___redArg___lam__2___closed__1 = (const lean_object*)&l_Std_Async_Selectable_combine___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__5(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__0_value;
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__4___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__1_value;
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__5___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__3_value;
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__6___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__3_value)} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0(size_t, lean_object*, lean_object*, size_t, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___closed__0_value;
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__2___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__0(size_t, lean_object*, size_t, lean_object*);
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
lean_object* l_Std_Async_Waiter_race___redArg___lam__0(uint8_t v_s_25_){
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
LEAN_EXPORT void l_Std_Async_Waiter_race___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_s_25_ = stack[0].m_num;
lean_object* v_res_34_;
v_res_34_ = l_Std_Async_Waiter_race___redArg___lam__0(v_s_25_);
stack->m_obj
 = v_res_34_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___redArg___lam__0___boxed(lean_object* v_s_35_){
_start:
{
uint8_t v_s_boxed_36_; lean_object* v_res_37_; 
v_s_boxed_36_ = lean_unbox(v_s_35_);
v_res_37_ = l_Std_Async_Waiter_race___redArg___lam__0(v_s_boxed_36_);
return v_res_37_;
}
}
lean_object* l_Std_Async_Waiter_race___redArg___lam__1(lean_object* v_lose_38_, lean_object* v_win_39_, lean_object* v_promise_40_, uint8_t v_first_41_){
_start:
{
if (v_first_41_ == 0)
{
lean_dec(v_promise_40_);
lean_dec(v_win_39_);
lean_inc(v_lose_38_);
return v_lose_38_;
}
else
{
lean_object* v___x_42_; 
v___x_42_ = lean_apply_1(v_win_39_, v_promise_40_);
return v___x_42_;
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_lose_38_ = stack[0].m_obj;
lean_object* v_win_39_ = stack[1].m_obj;
lean_object* v_promise_40_ = stack[2].m_obj;
uint8_t v_first_41_ = stack[3].m_num;
lean_object* v_res_43_;
v_res_43_ = l_Std_Async_Waiter_race___redArg___lam__1(v_lose_38_, v_win_39_, v_promise_40_, v_first_41_);
stack->m_obj
 = v_res_43_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___redArg___lam__1___boxed(lean_object* v_lose_44_, lean_object* v_win_45_, lean_object* v_promise_46_, lean_object* v_first_47_){
_start:
{
uint8_t v_first_boxed_48_; lean_object* v_res_49_; 
v_first_boxed_48_ = lean_unbox(v_first_47_);
v_res_49_ = l_Std_Async_Waiter_race___redArg___lam__1(v_lose_44_, v_win_45_, v_promise_46_, v_first_boxed_48_);
lean_dec(v_lose_44_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___redArg(lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_w_53_, lean_object* v_lose_54_, lean_object* v_win_55_){
_start:
{
lean_object* v_toBind_56_; lean_object* v_finished_57_; lean_object* v_promise_58_; lean_object* v___f_59_; lean_object* v___f_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v_toBind_56_ = lean_ctor_get(v_inst_51_, 1);
lean_inc(v_toBind_56_);
lean_dec_ref(v_inst_51_);
v_finished_57_ = lean_ctor_get(v_w_53_, 0);
lean_inc(v_finished_57_);
v_promise_58_ = lean_ctor_get(v_w_53_, 1);
lean_inc(v_promise_58_);
lean_dec_ref(v_w_53_);
v___f_59_ = ((lean_object*)(l_Std_Async_Waiter_race___redArg___closed__0));
v___f_60_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_60_, 0, v_lose_54_);
lean_closure_set(v___f_60_, 1, v_win_55_);
lean_closure_set(v___f_60_, 2, v_promise_58_);
v___x_61_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_61_, 0, lean_box(0));
lean_closure_set(v___x_61_, 1, lean_box(0));
lean_closure_set(v___x_61_, 2, lean_box(0));
lean_closure_set(v___x_61_, 3, v_finished_57_);
lean_closure_set(v___x_61_, 4, v___f_59_);
v___x_62_ = lean_apply_2(v_inst_52_, lean_box(0), v___x_61_);
v___x_63_ = lean_apply_4(v_toBind_56_, lean_box(0), lean_box(0), v___x_62_, v___f_60_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race(lean_object* v_m_64_, lean_object* v_00_u03b1_65_, lean_object* v_00_u03b2_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_w_69_, lean_object* v_lose_70_, lean_object* v_win_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Std_Async_Waiter_race___redArg(v_inst_67_, v_inst_68_, v_w_69_, v_lose_70_, v_win_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_checkFinished___redArg(lean_object* v_inst_73_, lean_object* v_w_74_){
_start:
{
lean_object* v_finished_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v_finished_75_ = lean_ctor_get(v_w_74_, 0);
lean_inc(v_finished_75_);
lean_dec_ref(v_w_74_);
v___x_76_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_76_, 0, lean_box(0));
lean_closure_set(v___x_76_, 1, lean_box(0));
lean_closure_set(v___x_76_, 2, v_finished_75_);
v___x_77_ = lean_apply_2(v_inst_73_, lean_box(0), v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_checkFinished(lean_object* v_m_78_, lean_object* v_00_u03b1_79_, lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_w_82_){
_start:
{
lean_object* v_finished_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v_finished_83_ = lean_ctor_get(v_w_82_, 0);
lean_inc(v_finished_83_);
lean_dec_ref(v_w_82_);
v___x_84_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_84_, 0, lean_box(0));
lean_closure_set(v___x_84_, 1, lean_box(0));
lean_closure_set(v___x_84_, 2, v_finished_83_);
v___x_85_ = lean_apply_2(v_inst_81_, lean_box(0), v___x_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_checkFinished___boxed(lean_object* v_m_86_, lean_object* v_00_u03b1_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_w_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Std_Async_Waiter_checkFinished(v_m_86_, v_00_u03b1_87_, v_inst_88_, v_inst_89_, v_w_90_);
lean_dec_ref(v_inst_88_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0_spec__0(lean_object* v_genLo_92_, lean_object* v_genMag_93_, lean_object* v_x_94_, lean_object* v_x_95_){
_start:
{
lean_object* v_zero_96_; uint8_t v_isZero_97_; 
v_zero_96_ = lean_unsigned_to_nat(0u);
v_isZero_97_ = lean_nat_dec_eq(v_x_94_, v_zero_96_);
if (v_isZero_97_ == 1)
{
lean_dec(v_x_94_);
return v_x_95_;
}
else
{
lean_object* v_fst_98_; lean_object* v_snd_99_; lean_object* v___x_100_; lean_object* v_fst_101_; lean_object* v_snd_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_116_; 
v_fst_98_ = lean_ctor_get(v_x_95_, 0);
lean_inc(v_fst_98_);
v_snd_99_ = lean_ctor_get(v_x_95_, 1);
lean_inc(v_snd_99_);
lean_dec_ref(v_x_95_);
v___x_100_ = l_stdNext(v_snd_99_);
v_fst_101_ = lean_ctor_get(v___x_100_, 0);
v_snd_102_ = lean_ctor_get(v___x_100_, 1);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_116_ == 0)
{
v___x_104_ = v___x_100_;
v_isShared_105_ = v_isSharedCheck_116_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_snd_102_);
lean_inc(v_fst_101_);
lean_dec(v___x_100_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_116_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v_v_x27_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_113_; 
v___x_106_ = lean_nat_mul(v_fst_98_, v_genMag_93_);
lean_dec(v_fst_98_);
v___x_107_ = lean_nat_sub(v_fst_101_, v_genLo_92_);
lean_dec(v_fst_101_);
v_v_x27_108_ = lean_nat_add(v___x_106_, v___x_107_);
lean_dec(v___x_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_nat_div(v_x_94_, v_genMag_93_);
lean_dec(v_x_94_);
v___x_110_ = lean_unsigned_to_nat(1u);
v___x_111_ = lean_nat_sub(v___x_109_, v___x_110_);
lean_dec(v___x_109_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v_v_x27_108_);
v___x_113_ = v___x_104_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_v_x27_108_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v_snd_102_);
v___x_113_ = v_reuseFailAlloc_115_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
v_x_94_ = v___x_111_;
v_x_95_ = v___x_113_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0_spec__0___boxed(lean_object* v_genLo_117_, lean_object* v_genMag_118_, lean_object* v_x_119_, lean_object* v_x_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0_spec__0(v_genLo_117_, v_genMag_118_, v_x_119_, v_x_120_);
lean_dec(v_genMag_118_);
lean_dec(v_genLo_117_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0(lean_object* v_g_122_, lean_object* v_lo_123_, lean_object* v_hi_124_){
_start:
{
lean_object* v___y_126_; lean_object* v___y_127_; uint8_t v___x_152_; lean_object* v___y_154_; 
v___x_152_ = lean_nat_dec_lt(v_hi_124_, v_lo_123_);
if (v___x_152_ == 0)
{
v___y_154_ = v_lo_123_;
goto v___jp_153_;
}
else
{
v___y_154_ = v_hi_124_;
goto v___jp_153_;
}
v___jp_125_:
{
lean_object* v___x_128_; lean_object* v_fst_129_; lean_object* v_snd_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v_genMag_133_; lean_object* v_q_134_; lean_object* v___x_135_; lean_object* v_k_136_; lean_object* v_tgtMag_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v_fst_141_; lean_object* v_snd_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_151_; 
v___x_128_ = l_stdRange;
v_fst_129_ = lean_ctor_get(v___x_128_, 0);
v_snd_130_ = lean_ctor_get(v___x_128_, 1);
v___x_131_ = lean_nat_sub(v_snd_130_, v_fst_129_);
v___x_132_ = lean_unsigned_to_nat(1u);
v_genMag_133_ = lean_nat_add(v___x_131_, v___x_132_);
lean_dec(v___x_131_);
v_q_134_ = lean_unsigned_to_nat(1000u);
v___x_135_ = lean_nat_sub(v___y_127_, v___y_126_);
v_k_136_ = lean_nat_add(v___x_135_, v___x_132_);
lean_dec(v___x_135_);
v_tgtMag_137_ = lean_nat_mul(v_k_136_, v_q_134_);
v___x_138_ = lean_unsigned_to_nat(0u);
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v_g_122_);
v___x_140_ = l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0_spec__0(v_fst_129_, v_genMag_133_, v_tgtMag_137_, v___x_139_);
lean_dec(v_genMag_133_);
v_fst_141_ = lean_ctor_get(v___x_140_, 0);
v_snd_142_ = lean_ctor_get(v___x_140_, 1);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_151_ == 0)
{
v___x_144_ = v___x_140_;
v_isShared_145_ = v_isSharedCheck_151_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_snd_142_);
lean_inc(v_fst_141_);
lean_dec(v___x_140_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_151_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_146_; lean_object* v_v_x27_147_; lean_object* v___x_149_; 
v___x_146_ = lean_nat_mod(v_fst_141_, v_k_136_);
lean_dec(v_k_136_);
lean_dec(v_fst_141_);
v_v_x27_147_ = lean_nat_add(v___y_126_, v___x_146_);
lean_dec(v___x_146_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 0, v_v_x27_147_);
v___x_149_ = v___x_144_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_v_x27_147_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_snd_142_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
v___jp_153_:
{
if (v___x_152_ == 0)
{
v___y_126_ = v___y_154_;
v___y_127_ = v_hi_124_;
goto v___jp_125_;
}
else
{
v___y_126_ = v___y_154_;
v___y_127_ = v_lo_123_;
goto v___jp_125_;
}
}
}
}
LEAN_EXPORT lean_object* l_randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0___boxed(lean_object* v_g_155_, lean_object* v_lo_156_, lean_object* v_hi_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0(v_g_155_, v_lo_156_, v_hi_157_);
lean_dec(v_hi_157_);
lean_dec(v_lo_156_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Select_0__Std_Async_shuffleIt_go___redArg(lean_object* v_xs_159_, lean_object* v_gen_160_, lean_object* v_i_161_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_162_ = lean_array_get_size(v_xs_159_);
v___x_163_ = lean_unsigned_to_nat(1u);
v___x_164_ = lean_nat_sub(v___x_162_, v___x_163_);
v___x_165_ = lean_nat_dec_lt(v_i_161_, v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; 
lean_dec(v___x_164_);
lean_dec(v_i_161_);
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v_xs_159_);
lean_ctor_set(v___x_166_, 1, v_gen_160_);
return v___x_166_;
}
else
{
lean_object* v___x_167_; lean_object* v_fst_168_; lean_object* v_snd_169_; lean_object* v_xs_170_; lean_object* v___x_171_; 
v___x_167_ = l_randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0(v_gen_160_, v_i_161_, v___x_164_);
lean_dec(v___x_164_);
v_fst_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_fst_168_);
v_snd_169_ = lean_ctor_get(v___x_167_, 1);
lean_inc(v_snd_169_);
lean_dec_ref(v___x_167_);
v_xs_170_ = lean_array_swap(v_xs_159_, v_i_161_, v_fst_168_);
lean_dec(v_fst_168_);
v___x_171_ = lean_nat_add(v_i_161_, v___x_163_);
lean_dec(v_i_161_);
v_xs_159_ = v_xs_170_;
v_gen_160_ = v_snd_169_;
v_i_161_ = v___x_171_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Select_0__Std_Async_shuffleIt_go(lean_object* v_00_u03b1_173_, lean_object* v_xs_174_, lean_object* v_gen_175_, lean_object* v_i_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt_go___redArg(v_xs_174_, v_gen_175_, v_i_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Select_0__Std_Async_shuffleIt_go_match__1_splitter___redArg(lean_object* v_x_178_, lean_object* v_h__1_179_){
_start:
{
lean_object* v_fst_180_; lean_object* v_snd_181_; lean_object* v___x_182_; 
v_fst_180_ = lean_ctor_get(v_x_178_, 0);
lean_inc(v_fst_180_);
v_snd_181_ = lean_ctor_get(v_x_178_, 1);
lean_inc(v_snd_181_);
lean_dec_ref(v_x_178_);
v___x_182_ = lean_apply_2(v_h__1_179_, v_fst_180_, v_snd_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Select_0__Std_Async_shuffleIt_go_match__1_splitter(lean_object* v_motive_183_, lean_object* v_x_184_, lean_object* v_h__1_185_){
_start:
{
lean_object* v_fst_186_; lean_object* v_snd_187_; lean_object* v___x_188_; 
v_fst_186_ = lean_ctor_get(v_x_184_, 0);
lean_inc(v_fst_186_);
v_snd_187_ = lean_ctor_get(v_x_184_, 1);
lean_inc(v_snd_187_);
lean_dec_ref(v_x_184_);
v___x_188_ = lean_apply_2(v_h__1_185_, v_fst_186_, v_snd_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(lean_object* v_xs_189_, lean_object* v_gen_190_){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_unsigned_to_nat(0u);
v___x_192_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt_go___redArg(v_xs_189_, v_gen_190_, v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Select_0__Std_Async_shuffleIt(lean_object* v_00_u03b1_193_, lean_object* v_xs_194_, lean_object* v_gen_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(v_xs_194_, v_gen_195_);
return v___x_196_;
}
}
lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__0___redArg(lean_object* v_e_197_){
_start:
{
if (lean_obj_tag(v_e_197_) == 0)
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_208_; 
v_a_199_ = lean_ctor_get(v_e_197_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v_e_197_);
if (v_isSharedCheck_208_ == 0)
{
v___x_201_ = v_e_197_;
v_isShared_202_ = v_isSharedCheck_208_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v_e_197_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_208_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_206_; 
v___x_203_ = lean_io_error_to_string(v_a_199_);
v___x_204_ = lean_mk_io_user_error(v___x_203_);
if (v_isShared_202_ == 0)
{
lean_ctor_set_tag(v___x_201_, 1);
lean_ctor_set(v___x_201_, 0, v___x_204_);
v___x_206_ = v___x_201_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_204_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
else
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_216_; 
v_a_209_ = lean_ctor_get(v_e_197_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v_e_197_);
if (v_isSharedCheck_216_ == 0)
{
v___x_211_ = v_e_197_;
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v_e_197_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
lean_ctor_set_tag(v___x_211_, 0);
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_a_209_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_197_ = stack[0].m_obj;
lean_object* v_res_217_;
v_res_217_ = l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__0___redArg(v_e_197_);
stack->m_obj
 = v_res_217_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__0___redArg___boxed(lean_object* v_e_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__0___redArg(v_e_218_);
return v_res_220_;
}
}
lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__0(lean_object* v_00_u03b1_221_, lean_object* v_e_222_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__0___redArg(v_e_222_);
return v___x_224_;
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_222_ = stack[1].m_obj;
lean_object* v_res_225_;
v_res_225_ = l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__0(lean_box(0), v_e_222_);
stack->m_obj
 = v_res_225_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__0___boxed(lean_object* v_00_u03b1_226_, lean_object* v_e_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__0(v_00_u03b1_226_, v_e_227_);
return v_res_229_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__0(lean_object* v_lose_230_, lean_object* v_a_231_, lean_object* v_promise_232_, lean_object* v_x_233_){
_start:
{
if (lean_obj_tag(v_x_233_) == 0)
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_243_; 
lean_dec(v_a_231_);
lean_dec_ref(v_lose_230_);
v_a_235_ = lean_ctor_get(v_x_233_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v_x_233_);
if (v_isSharedCheck_243_ == 0)
{
v___x_237_ = v_x_233_;
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v_x_233_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_235_);
v___x_240_ = v_reuseFailAlloc_242_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_241_; 
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
}
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_256_; 
v_a_244_ = lean_ctor_get(v_x_233_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v_x_233_);
if (v_isSharedCheck_256_ == 0)
{
v___x_246_ = v_x_233_;
v_isShared_247_ = v_isSharedCheck_256_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v_x_233_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_256_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
uint8_t v___x_248_; 
v___x_248_ = lean_unbox(v_a_244_);
lean_dec(v_a_244_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; 
lean_del_object(v___x_246_);
lean_dec(v_a_231_);
v___x_249_ = lean_apply_1(v_lose_230_, lean_box(0));
return v___x_249_;
}
else
{
lean_object* v___x_251_; 
lean_dec_ref(v_lose_230_);
if (v_isShared_247_ == 0)
{
lean_ctor_set_tag(v___x_246_, 0);
lean_ctor_set(v___x_246_, 0, v_a_231_);
v___x_251_ = v___x_246_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_231_);
v___x_251_ = v_reuseFailAlloc_255_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = lean_io_promise_resolve(v___x_251_, v_promise_232_);
v___x_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
return v___x_254_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_lose_230_ = stack[0].m_obj;
lean_object* v_a_231_ = stack[1].m_obj;
lean_object* v_promise_232_ = stack[2].m_obj;
lean_object* v_x_233_ = stack[3].m_obj;
lean_object* v_res_257_;
v_res_257_ = l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__0(v_lose_230_, v_a_231_, v_promise_232_, v_x_233_);
stack->m_obj
 = v_res_257_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__0___boxed(lean_object* v_lose_258_, lean_object* v_a_259_, lean_object* v_promise_260_, lean_object* v_x_261_, lean_object* v___y_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__0(v_lose_258_, v_a_259_, v_promise_260_, v_x_261_);
lean_dec(v_promise_260_);
return v_res_263_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___redArg(lean_object* v_a_264_, lean_object* v_w_265_, lean_object* v_lose_266_){
_start:
{
lean_object* v_finished_268_; lean_object* v_promise_269_; lean_object* v___f_270_; lean_object* v___x_271_; uint8_t v___x_272_; lean_object* v___x_273_; uint8_t v___y_275_; uint8_t v___x_283_; 
v_finished_268_ = lean_ctor_get(v_w_265_, 0);
lean_inc(v_finished_268_);
v_promise_269_ = lean_ctor_get(v_w_265_, 1);
lean_inc(v_promise_269_);
lean_dec_ref(v_w_265_);
v___f_270_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_270_, 0, v_lose_266_);
lean_closure_set(v___f_270_, 1, v_a_264_);
lean_closure_set(v___f_270_, 2, v_promise_269_);
v___x_271_ = lean_unsigned_to_nat(0u);
v___x_272_ = 0;
v___x_273_ = lean_st_ref_take(v_finished_268_);
v___x_283_ = lean_unbox(v___x_273_);
lean_dec(v___x_273_);
if (v___x_283_ == 0)
{
uint8_t v___x_284_; 
v___x_284_ = 1;
v___y_275_ = v___x_284_;
goto v___jp_274_;
}
else
{
v___y_275_ = v___x_272_;
goto v___jp_274_;
}
v___jp_274_:
{
uint8_t v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_276_ = 1;
v___x_277_ = lean_box(v___x_276_);
v___x_278_ = lean_st_ref_put(v_finished_268_, v___x_277_);
lean_dec(v_finished_268_);
v___x_279_ = lean_box(v___y_275_);
v___x_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
v___x_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
v___x_282_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_271_, v___x_272_, v___x_281_, v___f_270_);
return v___x_282_;
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_264_ = stack[0].m_obj;
lean_object* v_w_265_ = stack[1].m_obj;
lean_object* v_lose_266_ = stack[2].m_obj;
lean_object* v_res_285_;
v_res_285_ = l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___redArg(v_a_264_, v_w_265_, v_lose_266_);
stack->m_obj
 = v_res_285_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___redArg___boxed(lean_object* v_a_286_, lean_object* v_w_287_, lean_object* v_lose_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___redArg(v_a_286_, v_w_287_, v_lose_288_);
return v_res_290_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1(lean_object* v_00_u03b1_291_, lean_object* v_a_292_, lean_object* v_w_293_, lean_object* v_lose_294_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___redArg(v_a_292_, v_w_293_, v_lose_294_);
return v___x_296_;
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_292_ = stack[1].m_obj;
lean_object* v_w_293_ = stack[2].m_obj;
lean_object* v_lose_294_ = stack[3].m_obj;
lean_object* v_res_297_;
v_res_297_ = l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1(lean_box(0), v_a_292_, v_w_293_, v_lose_294_);
stack->m_obj
 = v_res_297_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___boxed(lean_object* v_00_u03b1_298_, lean_object* v_a_299_, lean_object* v_w_300_, lean_object* v_lose_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1(v_00_u03b1_298_, v_a_299_, v_w_300_, v_lose_301_);
return v_res_303_;
}
}
lean_object* l_Std_Async_Selectable_combine___redArg___lam__0(lean_object* v_x_308_){
_start:
{
if (lean_obj_tag(v_x_308_) == 0)
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_318_; 
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
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_336_; 
v_a_319_ = lean_ctor_get(v_x_308_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v_x_308_);
if (v_isSharedCheck_336_ == 0)
{
v___x_321_ = v_x_308_;
v_isShared_322_ = v_isSharedCheck_336_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v_x_308_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_336_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v_fst_323_; 
v_fst_323_ = lean_ctor_get(v_a_319_, 0);
lean_inc(v_fst_323_);
lean_dec(v_a_319_);
if (lean_obj_tag(v_fst_323_) == 0)
{
lean_object* v___x_324_; 
lean_del_object(v___x_321_);
v___x_324_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___lam__0___closed__1));
return v___x_324_;
}
else
{
lean_object* v_val_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_335_; 
v_val_325_ = lean_ctor_get(v_fst_323_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v_fst_323_);
if (v_isSharedCheck_335_ == 0)
{
v___x_327_ = v_fst_323_;
v_isShared_328_ = v_isSharedCheck_335_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_val_325_);
lean_dec(v_fst_323_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_335_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v_val_325_);
v___x_330_ = v___x_321_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_val_325_);
v___x_330_ = v_reuseFailAlloc_334_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_332_; 
if (v_isShared_328_ == 0)
{
lean_ctor_set_tag(v___x_327_, 0);
lean_ctor_set(v___x_327_, 0, v___x_330_);
v___x_332_ = v___x_327_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Selectable_combine___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_308_ = stack[0].m_obj;
lean_object* v_res_337_;
v_res_337_ = l_Std_Async_Selectable_combine___redArg___lam__0(v_x_308_);
stack->m_obj
 = v_res_337_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__0___boxed(lean_object* v_x_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Std_Async_Selectable_combine___redArg___lam__0(v_x_338_);
return v_res_340_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__2(lean_object* v_a_341_, lean_object* v___x_342_, uint8_t v___x_343_, lean_object* v___f_344_, lean_object* v___x_345_, lean_object* v_x_346_){
_start:
{
if (lean_obj_tag(v_x_346_) == 0)
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_356_; 
lean_dec_ref(v___x_345_);
lean_dec_ref(v___f_344_);
lean_dec(v___x_342_);
lean_dec_ref(v_a_341_);
v_a_348_ = lean_ctor_get(v_x_346_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v_x_346_);
if (v_isSharedCheck_356_ == 0)
{
v___x_350_ = v_x_346_;
v_isShared_351_ = v_isSharedCheck_356_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v_x_346_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_356_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_355_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_354_; 
v___x_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
}
}
else
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_370_; 
v_a_357_ = lean_ctor_get(v_x_346_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v_x_346_);
if (v_isSharedCheck_370_ == 0)
{
v___x_359_ = v_x_346_;
v_isShared_360_ = v_isSharedCheck_370_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v_x_346_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_370_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
if (lean_obj_tag(v_a_357_) == 1)
{
lean_object* v_val_361_; lean_object* v_cont_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
lean_del_object(v___x_359_);
lean_dec_ref(v___x_345_);
v_val_361_ = lean_ctor_get(v_a_357_, 0);
lean_inc(v_val_361_);
lean_dec_ref_known(v_a_357_, 1);
v_cont_362_ = lean_ctor_get(v_a_341_, 1);
lean_inc_ref(v_cont_362_);
lean_dec_ref(v_a_341_);
v___x_363_ = lean_apply_2(v_cont_362_, v_val_361_, lean_box(0));
v___x_364_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_342_, v___x_343_, v___x_363_, v___f_344_);
return v___x_364_;
}
else
{
lean_object* v___x_365_; lean_object* v___x_367_; 
lean_dec(v_a_357_);
lean_dec_ref(v___f_344_);
lean_dec(v___x_342_);
lean_dec_ref(v_a_341_);
v___x_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_365_, 0, v___x_345_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_365_);
v___x_367_ = v___x_359_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_365_);
v___x_367_ = v_reuseFailAlloc_369_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_368_; 
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_341_ = stack[0].m_obj;
lean_object* v___x_342_ = stack[1].m_obj;
uint8_t v___x_343_ = stack[2].m_num;
lean_object* v___f_344_ = stack[3].m_obj;
lean_object* v___x_345_ = stack[4].m_obj;
lean_object* v_x_346_ = stack[5].m_obj;
lean_object* v_res_371_;
v_res_371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__2(v_a_341_, v___x_342_, v___x_343_, v___f_344_, v___x_345_, v_x_346_);
stack->m_obj
 = v_res_371_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__2___boxed(lean_object* v_a_372_, lean_object* v___x_373_, lean_object* v___x_374_, lean_object* v___f_375_, lean_object* v___x_376_, lean_object* v_x_377_, lean_object* v___y_378_){
_start:
{
uint8_t v___x_10550__boxed_379_; lean_object* v_res_380_; 
v___x_10550__boxed_379_ = lean_unbox(v___x_374_);
v_res_380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__2(v_a_372_, v___x_373_, v___x_10550__boxed_379_, v___f_375_, v___x_376_, v_x_377_);
return v_res_380_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__1(lean_object* v___x_381_, lean_object* v_x_382_){
_start:
{
if (lean_obj_tag(v_x_382_) == 0)
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_392_; 
v_a_384_ = lean_ctor_get(v_x_382_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v_x_382_);
if (v_isSharedCheck_392_ == 0)
{
v___x_386_ = v_x_382_;
v_isShared_387_ = v_isSharedCheck_392_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v_x_382_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_392_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_384_);
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
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_405_; 
v_a_393_ = lean_ctor_get(v_x_382_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v_x_382_);
if (v_isSharedCheck_405_ == 0)
{
v___x_395_ = v_x_382_;
v_isShared_396_ = v_isSharedCheck_405_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v_x_382_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_405_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_397_, 0, v_a_393_);
v___x_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set(v___x_399_, 1, v___x_381_);
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_400_);
v___x_402_ = v___x_395_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_404_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_403_; 
v___x_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
return v___x_403_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_381_ = stack[0].m_obj;
lean_object* v_x_382_ = stack[1].m_obj;
lean_object* v_res_406_;
v_res_406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__1(v___x_381_, v_x_382_);
stack->m_obj
 = v_res_406_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__1___boxed(lean_object* v___x_407_, lean_object* v_x_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__1(v___x_407_, v_x_408_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__0___boxed(lean_object* v_i_411_, lean_object* v_as_412_, lean_object* v_sz_413_, lean_object* v_x_414_, lean_object* v___y_415_){
_start:
{
size_t v_i_boxed_416_; size_t v_sz_boxed_417_; lean_object* v_res_418_; 
v_i_boxed_416_ = lean_unbox_usize(v_i_411_);
lean_dec(v_i_411_);
v_sz_boxed_417_ = lean_unbox_usize(v_sz_413_);
lean_dec(v_sz_413_);
v_res_418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__0(v_i_boxed_416_, v_as_412_, v_sz_boxed_417_, v_x_414_);
return v_res_418_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg(lean_object* v_as_424_, size_t v_sz_425_, size_t v_i_426_, lean_object* v_b_427_){
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
lean_object* v_a_432_; lean_object* v_selector_433_; lean_object* v_tryFn_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___f_437_; lean_object* v___f_438_; lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; lean_object* v___x_442_; lean_object* v___f_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec_ref(v_b_427_);
v_a_432_ = lean_array_uget(v_as_424_, v_i_426_);
v_selector_433_ = lean_ctor_get(v_a_432_, 0);
v_tryFn_434_ = lean_ctor_get(v_selector_433_, 0);
lean_inc_ref(v_tryFn_434_);
v___x_435_ = lean_box_usize(v_i_426_);
v___x_436_ = lean_box_usize(v_sz_425_);
v___f_437_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_437_, 0, v___x_435_);
lean_closure_set(v___f_437_, 1, v_as_424_);
lean_closure_set(v___f_437_, 2, v___x_436_);
v___f_438_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___closed__0));
v___x_439_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___closed__1));
v___x_440_ = lean_unsigned_to_nat(0u);
v___x_441_ = 0;
v___x_442_ = lean_box(v___x_441_);
v___f_443_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__2___boxed), 7, 5);
lean_closure_set(v___f_443_, 0, v_a_432_);
lean_closure_set(v___f_443_, 1, v___x_440_);
lean_closure_set(v___f_443_, 2, v___x_442_);
lean_closure_set(v___f_443_, 3, v___f_438_);
lean_closure_set(v___f_443_, 4, v___x_439_);
v___x_444_ = lean_apply_1(v_tryFn_434_, lean_box(0));
v___x_445_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_440_, v___x_441_, v___x_444_, v___f_443_);
v___x_446_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_440_, v___x_441_, v___x_445_, v___f_437_);
return v___x_446_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_424_ = stack[0].m_obj;
size_t v_sz_425_ = stack[1].m_num;
size_t v_i_426_ = stack[2].m_num;
lean_object* v_b_427_ = stack[3].m_obj;
lean_object* v_res_447_;
v_res_447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg(v_as_424_, v_sz_425_, v_i_426_, v_b_427_);
stack->m_obj
 = v_res_447_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__0(size_t v_i_448_, lean_object* v_as_449_, size_t v_sz_450_, lean_object* v_x_451_){
_start:
{
if (lean_obj_tag(v_x_451_) == 0)
{
lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_461_; 
lean_dec_ref(v_as_449_);
v_a_453_ = lean_ctor_get(v_x_451_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v_x_451_);
if (v_isSharedCheck_461_ == 0)
{
v___x_455_ = v_x_451_;
v_isShared_456_ = v_isSharedCheck_461_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v_x_451_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_461_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_453_);
v___x_458_ = v_reuseFailAlloc_460_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_459_; 
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
return v___x_459_;
}
}
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_481_; 
v_a_462_ = lean_ctor_get(v_x_451_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v_x_451_);
if (v_isSharedCheck_481_ == 0)
{
v___x_464_ = v_x_451_;
v_isShared_465_ = v_isSharedCheck_481_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v_x_451_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_481_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
if (lean_obj_tag(v_a_462_) == 0)
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_476_; 
lean_dec_ref(v_as_449_);
v_a_466_ = lean_ctor_get(v_a_462_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v_a_462_);
if (v_isSharedCheck_476_ == 0)
{
v___x_468_ = v_a_462_;
v_isShared_469_ = v_isSharedCheck_476_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v_a_462_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_476_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v_a_466_);
v___x_471_ = v___x_464_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_475_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_473_; 
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v___x_471_);
v___x_473_ = v___x_468_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
else
{
lean_object* v_a_477_; size_t v___x_478_; size_t v___x_479_; lean_object* v___x_480_; 
lean_del_object(v___x_464_);
v_a_477_ = lean_ctor_get(v_a_462_, 0);
lean_inc(v_a_477_);
lean_dec_ref_known(v_a_462_, 1);
v___x_478_ = ((size_t)1ULL);
v___x_479_ = lean_usize_add(v_i_448_, v___x_478_);
v___x_480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg(v_as_449_, v_sz_450_, v___x_479_, v_a_477_);
return v___x_480_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_i_448_ = stack[0].m_num;
lean_object* v_as_449_ = stack[1].m_obj;
size_t v_sz_450_ = stack[2].m_num;
lean_object* v_x_451_ = stack[3].m_obj;
lean_object* v_res_482_;
v_res_482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__0(v_i_448_, v_as_449_, v_sz_450_, v_x_451_);
stack->m_obj
 = v_res_482_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___boxed(lean_object* v_as_483_, lean_object* v_sz_484_, lean_object* v_i_485_, lean_object* v_b_486_, lean_object* v___y_487_){
_start:
{
size_t v_sz_boxed_488_; size_t v_i_boxed_489_; lean_object* v_res_490_; 
v_sz_boxed_488_ = lean_unbox_usize(v_sz_484_);
lean_dec(v_sz_484_);
v_i_boxed_489_ = lean_unbox_usize(v_i_485_);
lean_dec(v_i_485_);
v_res_490_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg(v_as_483_, v_sz_boxed_488_, v_i_boxed_489_, v_b_486_);
return v_res_490_;
}
}
lean_object* l_Std_Async_Selectable_combine___redArg___lam__1(lean_object* v_fst_491_, lean_object* v___f_492_, lean_object* v_x_493_){
_start:
{
if (lean_obj_tag(v_x_493_) == 0)
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_503_; 
lean_dec_ref(v___f_492_);
lean_dec_ref(v_fst_491_);
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
lean_object* v___x_504_; size_t v_sz_505_; size_t v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
lean_dec_ref_known(v_x_493_, 1);
v___x_504_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___closed__1));
v_sz_505_ = lean_array_size(v_fst_491_);
v___x_506_ = ((size_t)0ULL);
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = 0;
v___x_509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg(v_fst_491_, v_sz_505_, v___x_506_, v___x_504_);
v___x_510_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_507_, v___x_508_, v___x_509_, v___f_492_);
return v___x_510_;
}
}
}
LEAN_EXPORT void l_Std_Async_Selectable_combine___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_491_ = stack[0].m_obj;
lean_object* v___f_492_ = stack[1].m_obj;
lean_object* v_x_493_ = stack[2].m_obj;
lean_object* v_res_511_;
v_res_511_ = l_Std_Async_Selectable_combine___redArg___lam__1(v_fst_491_, v___f_492_, v_x_493_);
stack->m_obj
 = v_res_511_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__1___boxed(lean_object* v_fst_512_, lean_object* v___f_513_, lean_object* v_x_514_, lean_object* v___y_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Std_Async_Selectable_combine___redArg___lam__1(v_fst_512_, v___f_513_, v_x_514_);
return v_res_516_;
}
}
lean_object* l_Std_Async_Selectable_combine___redArg___lam__2(lean_object* v_selectables_521_, lean_object* v___f_522_, lean_object* v___x_523_, lean_object* v_x_524_){
_start:
{
if (lean_obj_tag(v_x_524_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_534_; 
lean_dec_ref(v___f_522_);
lean_dec_ref(v_selectables_521_);
v_a_526_ = lean_ctor_get(v_x_524_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v_x_524_);
if (v_isSharedCheck_534_ == 0)
{
v___x_528_ = v_x_524_;
v_isShared_529_ = v_isSharedCheck_534_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v_x_524_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_534_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_533_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_532_; 
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_536_; lean_object* v_fst_537_; lean_object* v_snd_538_; lean_object* v___f_539_; lean_object* v___x_540_; uint8_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_a_535_ = lean_ctor_get(v_x_524_, 0);
lean_inc(v_a_535_);
lean_dec_ref_known(v_x_524_, 1);
v___x_536_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(v_selectables_521_, v_a_535_);
v_fst_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_fst_537_);
v_snd_538_ = lean_ctor_get(v___x_536_, 1);
lean_inc(v_snd_538_);
lean_dec_ref(v___x_536_);
v___f_539_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_539_, 0, v_fst_537_);
lean_closure_set(v___f_539_, 1, v___f_522_);
v___x_540_ = lean_unsigned_to_nat(0u);
v___x_541_ = 0;
v___x_542_ = lean_st_ref_swap(v___x_523_, v_snd_538_);
lean_dec(v___x_542_);
v___x_543_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___lam__2___closed__1));
v___x_544_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_540_, v___x_541_, v___x_543_, v___f_539_);
return v___x_544_;
}
}
}
LEAN_EXPORT void l_Std_Async_Selectable_combine___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_selectables_521_ = stack[0].m_obj;
lean_object* v___f_522_ = stack[1].m_obj;
lean_object* v___x_523_ = stack[2].m_obj;
lean_object* v_x_524_ = stack[3].m_obj;
lean_object* v_res_545_;
v_res_545_ = l_Std_Async_Selectable_combine___redArg___lam__2(v_selectables_521_, v___f_522_, v___x_523_, v_x_524_);
stack->m_obj
 = v_res_545_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__2___boxed(lean_object* v_selectables_546_, lean_object* v___f_547_, lean_object* v___x_548_, lean_object* v_x_549_, lean_object* v___y_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Std_Async_Selectable_combine___redArg___lam__2(v_selectables_546_, v___f_547_, v___x_548_, v_x_549_);
lean_dec(v___x_548_);
return v_res_551_;
}
}
lean_object* l_Std_Async_Selectable_combine___redArg___lam__3(lean_object* v___x_552_, lean_object* v___f_553_){
_start:
{
lean_object* v___x_555_; uint8_t v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_555_ = lean_unsigned_to_nat(0u);
v___x_556_ = 0;
v___x_557_ = lean_st_ref_get(v___x_552_);
v___x_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
v___x_560_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_555_, v___x_556_, v___x_559_, v___f_553_);
return v___x_560_;
}
}
LEAN_EXPORT void l_Std_Async_Selectable_combine___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_552_ = stack[0].m_obj;
lean_object* v___f_553_ = stack[1].m_obj;
lean_object* v_res_561_;
v_res_561_ = l_Std_Async_Selectable_combine___redArg___lam__3(v___x_552_, v___f_553_);
stack->m_obj
 = v_res_561_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__3___boxed(lean_object* v___x_562_, lean_object* v___f_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Std_Async_Selectable_combine___redArg___lam__3(v___x_562_, v___f_563_);
lean_dec(v___x_562_);
return v_res_565_;
}
}
lean_object* l_Std_Async_Selectable_combine___redArg___lam__4(lean_object* v___x_566_, lean_object* v_x_567_){
_start:
{
if (lean_obj_tag(v_x_567_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_577_; 
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
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_598_; 
v_a_578_ = lean_ctor_get(v_x_567_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v_x_567_);
if (v_isSharedCheck_598_ == 0)
{
v___x_580_ = v_x_567_;
v_isShared_581_ = v_isSharedCheck_598_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v_x_567_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_598_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v_fst_582_; 
v_fst_582_ = lean_ctor_get(v_a_578_, 0);
lean_inc(v_fst_582_);
lean_dec(v_a_578_);
if (lean_obj_tag(v_fst_582_) == 0)
{
lean_object* v___x_584_; 
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v___x_566_);
v___x_584_ = v___x_580_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_566_);
v___x_584_ = v_reuseFailAlloc_586_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_585_; 
v___x_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
return v___x_585_;
}
}
else
{
lean_object* v_val_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_597_; 
v_val_587_ = lean_ctor_get(v_fst_582_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v_fst_582_);
if (v_isSharedCheck_597_ == 0)
{
v___x_589_ = v_fst_582_;
v_isShared_590_ = v_isSharedCheck_597_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_val_587_);
lean_dec(v_fst_582_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_597_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v_val_587_);
v___x_592_ = v___x_580_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_val_587_);
v___x_592_ = v_reuseFailAlloc_596_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_594_; 
if (v_isShared_590_ == 0)
{
lean_ctor_set_tag(v___x_589_, 0);
lean_ctor_set(v___x_589_, 0, v___x_592_);
v___x_594_ = v___x_589_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Selectable_combine___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_566_ = stack[0].m_obj;
lean_object* v_x_567_ = stack[1].m_obj;
lean_object* v_res_599_;
v_res_599_ = l_Std_Async_Selectable_combine___redArg___lam__4(v___x_566_, v_x_567_);
stack->m_obj
 = v_res_599_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__4___boxed(lean_object* v___x_600_, lean_object* v_x_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Std_Async_Selectable_combine___redArg___lam__4(v___x_600_, v_x_601_);
return v_res_603_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__4(lean_object* v___x_604_, lean_object* v_x_605_){
_start:
{
if (lean_obj_tag(v_x_605_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_615_; 
v_a_607_ = lean_ctor_get(v_x_605_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v_x_605_);
if (v_isSharedCheck_615_ == 0)
{
v___x_609_ = v_x_605_;
v_isShared_610_ = v_isSharedCheck_615_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v_x_605_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_615_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_607_);
v___x_612_ = v_reuseFailAlloc_614_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_613_; 
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
return v___x_613_;
}
}
}
else
{
lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_624_; 
v_isSharedCheck_624_ = !lean_is_exclusive(v_x_605_);
if (v_isSharedCheck_624_ == 0)
{
lean_object* v_unused_625_; 
v_unused_625_ = lean_ctor_get(v_x_605_, 0);
lean_dec(v_unused_625_);
v___x_617_ = v_x_605_;
v_isShared_618_ = v_isSharedCheck_624_;
goto v_resetjp_616_;
}
else
{
lean_dec(v_x_605_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_624_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set_tag(v___x_617_, 0);
lean_ctor_set(v___x_617_, 0, v___x_604_);
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_604_);
v___x_620_ = v_reuseFailAlloc_623_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
v___x_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
return v___x_622_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_604_ = stack[0].m_obj;
lean_object* v_x_605_ = stack[1].m_obj;
lean_object* v_res_626_;
v_res_626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__4(v___x_604_, v_x_605_);
stack->m_obj
 = v_res_626_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__4___boxed(lean_object* v___x_627_, lean_object* v_x_628_, lean_object* v___y_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__4(v___x_627_, v_x_628_);
return v_res_630_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__10(lean_object* v___x_631_, lean_object* v_a_632_, lean_object* v___f_633_, lean_object* v___x_634_, uint8_t v_a_635_, lean_object* v___f_636_, lean_object* v_x_637_){
_start:
{
if (lean_obj_tag(v_x_637_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_647_; 
lean_dec_ref(v___f_636_);
lean_dec(v___x_634_);
lean_dec_ref(v___f_633_);
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
lean_object* v_a_648_; 
v_a_648_ = lean_ctor_get(v_x_637_, 0);
lean_inc(v_a_648_);
lean_dec_ref_known(v_x_637_, 1);
if (lean_obj_tag(v_a_648_) == 0)
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_660_; 
lean_dec_ref(v___f_636_);
lean_dec(v___x_634_);
lean_dec_ref(v___f_633_);
v_a_649_ = lean_ctor_get(v_a_648_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v_a_648_);
if (v_isSharedCheck_660_ == 0)
{
v___x_651_ = v_a_648_;
v_isShared_652_ = v_isSharedCheck_660_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v_a_648_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_660_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_657_; 
v___x_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_653_, 0, v_a_649_);
v___x_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v___x_631_);
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
if (v_isShared_652_ == 0)
{
lean_ctor_set_tag(v___x_651_, 1);
lean_ctor_set(v___x_651_, 0, v___x_655_);
v___x_657_ = v___x_651_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_655_);
v___x_657_ = v_reuseFailAlloc_659_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_658_; 
v___x_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
return v___x_658_;
}
}
}
else
{
lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_671_; 
v_isSharedCheck_671_ = !lean_is_exclusive(v_a_648_);
if (v_isSharedCheck_671_ == 0)
{
lean_object* v_unused_672_; 
v_unused_672_ = lean_ctor_get(v_a_648_, 0);
lean_dec(v_unused_672_);
v___x_662_ = v_a_648_;
v_isShared_663_ = v_isSharedCheck_671_;
goto v_resetjp_661_;
}
else
{
lean_dec(v_a_648_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_671_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_664_ = lean_io_promise_result_opt(v_a_632_);
lean_inc(v___x_634_);
v___x_665_ = lean_io_bind_task(v___x_664_, v___f_633_, v___x_634_, v_a_635_);
lean_dec_ref(v___x_665_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v___x_631_);
v___x_667_ = v___x_662_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_631_);
v___x_667_ = v_reuseFailAlloc_670_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
v___x_669_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_634_, v_a_635_, v___x_668_, v___f_636_);
return v___x_669_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_631_ = stack[0].m_obj;
lean_object* v_a_632_ = stack[1].m_obj;
lean_object* v___f_633_ = stack[2].m_obj;
lean_object* v___x_634_ = stack[3].m_obj;
uint8_t v_a_635_ = stack[4].m_num;
lean_object* v___f_636_ = stack[5].m_obj;
lean_object* v_x_637_ = stack[6].m_obj;
lean_object* v_res_673_;
v_res_673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__10(v___x_631_, v_a_632_, v___f_633_, v___x_634_, v_a_635_, v___f_636_, v_x_637_);
stack->m_obj
 = v_res_673_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__10___boxed(lean_object* v___x_674_, lean_object* v_a_675_, lean_object* v___f_676_, lean_object* v___x_677_, lean_object* v_a_678_, lean_object* v___f_679_, lean_object* v_x_680_, lean_object* v___y_681_){
_start:
{
uint8_t v_a_11269__boxed_682_; lean_object* v_res_683_; 
v_a_11269__boxed_682_ = lean_unbox(v_a_678_);
v_res_683_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__10(v___x_674_, v_a_675_, v___f_676_, v___x_677_, v_a_11269__boxed_682_, v___f_679_, v_x_680_);
lean_dec(v_a_675_);
return v_res_683_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__11(lean_object* v_a_684_, lean_object* v___x_685_, lean_object* v___f_686_, lean_object* v___x_687_, uint8_t v_a_688_, lean_object* v___f_689_, lean_object* v_finished_690_, lean_object* v___f_691_, lean_object* v___f_692_, lean_object* v_x_693_){
_start:
{
if (lean_obj_tag(v_x_693_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_703_; 
lean_dec_ref(v___f_692_);
lean_dec_ref(v___f_691_);
lean_dec(v_finished_690_);
lean_dec_ref(v___f_689_);
lean_dec(v___x_687_);
lean_dec_ref(v___f_686_);
lean_dec_ref(v_a_684_);
v_a_695_ = lean_ctor_get(v_x_693_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v_x_693_);
if (v_isSharedCheck_703_ == 0)
{
v___x_697_ = v_x_693_;
v_isShared_698_ = v_isSharedCheck_703_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v_x_693_);
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
v___x_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
return v___x_701_;
}
}
}
else
{
lean_object* v_selector_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_719_; 
v_selector_704_ = lean_ctor_get(v_a_684_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v_a_684_);
if (v_isSharedCheck_719_ == 0)
{
lean_object* v_unused_720_; 
v_unused_720_ = lean_ctor_get(v_a_684_, 1);
lean_dec(v_unused_720_);
v___x_706_ = v_a_684_;
v_isShared_707_ = v_isSharedCheck_719_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_selector_704_);
lean_dec(v_a_684_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_719_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v_a_708_; lean_object* v_registerFn_709_; lean_object* v___x_710_; lean_object* v___f_711_; lean_object* v___x_713_; 
v_a_708_ = lean_ctor_get(v_x_693_, 0);
lean_inc_n(v_a_708_, 2);
lean_dec_ref_known(v_x_693_, 1);
v_registerFn_709_ = lean_ctor_get(v_selector_704_, 1);
lean_inc_ref(v_registerFn_709_);
lean_dec_ref(v_selector_704_);
v___x_710_ = lean_box(v_a_688_);
lean_inc(v___x_687_);
v___f_711_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__10___boxed), 8, 6);
lean_closure_set(v___f_711_, 0, v___x_685_);
lean_closure_set(v___f_711_, 1, v_a_708_);
lean_closure_set(v___f_711_, 2, v___f_686_);
lean_closure_set(v___f_711_, 3, v___x_687_);
lean_closure_set(v___f_711_, 4, v___x_710_);
lean_closure_set(v___f_711_, 5, v___f_689_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 1, v_a_708_);
lean_ctor_set(v___x_706_, 0, v_finished_690_);
v___x_713_ = v___x_706_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_finished_690_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_a_708_);
v___x_713_ = v_reuseFailAlloc_718_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_714_ = lean_apply_2(v_registerFn_709_, v___x_713_, lean_box(0));
lean_inc_n(v___x_687_, 2);
v___x_715_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_687_, v_a_688_, v___x_714_, v___f_691_);
v___x_716_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_687_, v_a_688_, v___x_715_, v___f_692_);
v___x_717_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_687_, v_a_688_, v___x_716_, v___f_711_);
return v___x_717_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_684_ = stack[0].m_obj;
lean_object* v___x_685_ = stack[1].m_obj;
lean_object* v___f_686_ = stack[2].m_obj;
lean_object* v___x_687_ = stack[3].m_obj;
uint8_t v_a_688_ = stack[4].m_num;
lean_object* v___f_689_ = stack[5].m_obj;
lean_object* v_finished_690_ = stack[6].m_obj;
lean_object* v___f_691_ = stack[7].m_obj;
lean_object* v___f_692_ = stack[8].m_obj;
lean_object* v_x_693_ = stack[9].m_obj;
lean_object* v_res_721_;
v_res_721_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__11(v_a_684_, v___x_685_, v___f_686_, v___x_687_, v_a_688_, v___f_689_, v_finished_690_, v___f_691_, v___f_692_, v_x_693_);
stack->m_obj
 = v_res_721_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__11___boxed(lean_object* v_a_722_, lean_object* v___x_723_, lean_object* v___f_724_, lean_object* v___x_725_, lean_object* v_a_726_, lean_object* v___f_727_, lean_object* v_finished_728_, lean_object* v___f_729_, lean_object* v___f_730_, lean_object* v_x_731_, lean_object* v___y_732_){
_start:
{
uint8_t v_a_11411__boxed_733_; lean_object* v_res_734_; 
v_a_11411__boxed_733_ = lean_unbox(v_a_726_);
v_res_734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__11(v_a_722_, v___x_723_, v___f_724_, v___x_725_, v_a_11411__boxed_733_, v___f_727_, v_finished_728_, v___f_729_, v___f_730_, v_x_731_);
return v_res_734_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__7(lean_object* v_waiter_735_, lean_object* v___f_736_, lean_object* v___x_737_, uint8_t v_a_738_, lean_object* v___f_739_, lean_object* v_x_740_){
_start:
{
if (lean_obj_tag(v_x_740_) == 0)
{
lean_object* v_a_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v_a_742_ = lean_ctor_get(v_x_740_, 0);
lean_inc(v_a_742_);
lean_dec_ref_known(v_x_740_, 1);
v___x_743_ = l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___redArg(v_a_742_, v_waiter_735_, v___f_736_);
v___x_744_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_737_, v_a_738_, v___x_743_, v___f_739_);
return v___x_744_;
}
else
{
lean_object* v___x_745_; 
lean_dec_ref(v___f_739_);
lean_dec(v___x_737_);
lean_dec_ref(v___f_736_);
lean_dec_ref(v_waiter_735_);
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v_x_740_);
return v___x_745_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_waiter_735_ = stack[0].m_obj;
lean_object* v___f_736_ = stack[1].m_obj;
lean_object* v___x_737_ = stack[2].m_obj;
uint8_t v_a_738_ = stack[3].m_num;
lean_object* v___f_739_ = stack[4].m_obj;
lean_object* v_x_740_ = stack[5].m_obj;
lean_object* v_res_746_;
v_res_746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__7(v_waiter_735_, v___f_736_, v___x_737_, v_a_738_, v___f_739_, v_x_740_);
stack->m_obj
 = v_res_746_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__7___boxed(lean_object* v_waiter_747_, lean_object* v___f_748_, lean_object* v___x_749_, lean_object* v_a_750_, lean_object* v___f_751_, lean_object* v_x_752_, lean_object* v___y_753_){
_start:
{
uint8_t v_a_11527__boxed_754_; lean_object* v_res_755_; 
v_a_11527__boxed_754_ = lean_unbox(v_a_750_);
v_res_755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__7(v_waiter_747_, v___f_748_, v___x_749_, v_a_11527__boxed_754_, v___f_751_, v_x_752_);
return v_res_755_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__8(lean_object* v_a_756_, lean_object* v___x_757_, uint8_t v_a_758_, lean_object* v___f_759_, lean_object* v_x_760_){
_start:
{
if (lean_obj_tag(v_x_760_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_770_; 
lean_dec_ref(v___f_759_);
lean_dec(v___x_757_);
lean_dec_ref(v_a_756_);
v_a_762_ = lean_ctor_get(v_x_760_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v_x_760_);
if (v_isSharedCheck_770_ == 0)
{
v___x_764_ = v_x_760_;
v_isShared_765_ = v_isSharedCheck_770_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v_x_760_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_770_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_769_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_768_; 
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
return v___x_768_;
}
}
}
else
{
lean_object* v_a_771_; lean_object* v_cont_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_a_771_ = lean_ctor_get(v_x_760_, 0);
lean_inc(v_a_771_);
lean_dec_ref_known(v_x_760_, 1);
v_cont_772_ = lean_ctor_get(v_a_756_, 1);
lean_inc_ref(v_cont_772_);
lean_dec_ref(v_a_756_);
v___x_773_ = lean_apply_2(v_cont_772_, v_a_771_, lean_box(0));
v___x_774_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_757_, v_a_758_, v___x_773_, v___f_759_);
return v___x_774_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_756_ = stack[0].m_obj;
lean_object* v___x_757_ = stack[1].m_obj;
uint8_t v_a_758_ = stack[2].m_num;
lean_object* v___f_759_ = stack[3].m_obj;
lean_object* v_x_760_ = stack[4].m_obj;
lean_object* v_res_775_;
v_res_775_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__8(v_a_756_, v___x_757_, v_a_758_, v___f_759_, v_x_760_);
stack->m_obj
 = v_res_775_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__8___boxed(lean_object* v_a_776_, lean_object* v___x_777_, lean_object* v_a_778_, lean_object* v___f_779_, lean_object* v_x_780_, lean_object* v___y_781_){
_start:
{
uint8_t v_a_11569__boxed_782_; lean_object* v_res_783_; 
v_a_11569__boxed_782_ = lean_unbox(v_a_778_);
v_res_783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__8(v_a_776_, v___x_777_, v_a_11569__boxed_782_, v___f_779_, v_x_780_);
return v_res_783_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__9(lean_object* v___x_784_, lean_object* v___x_785_, uint8_t v_a_786_, lean_object* v___f_787_, lean_object* v___f_788_, lean_object* v_a_789_){
_start:
{
lean_object* v_val_792_; 
if (lean_obj_tag(v_a_789_) == 0)
{
lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec_ref(v___f_788_);
lean_dec_ref(v___f_787_);
lean_dec(v___x_785_);
v___x_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_784_);
v___x_800_ = lean_task_pure(v___x_799_);
return v___x_800_;
}
else
{
lean_object* v_val_801_; lean_object* v___x_802_; 
v_val_801_ = lean_ctor_get(v_a_789_, 0);
lean_inc(v_val_801_);
lean_dec_ref_known(v_a_789_, 1);
v___x_802_ = l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__0___redArg(v_val_801_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___x_802_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_802_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
lean_ctor_set_tag(v___x_805_, 1);
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_803_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
v_val_792_ = v___x_808_;
goto v___jp_791_;
}
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
v_a_811_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_802_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_802_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
lean_ctor_set_tag(v___x_813_, 0);
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
v_val_792_ = v___x_816_;
goto v___jp_791_;
}
}
}
}
v___jp_791_:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_793_, 0, v_val_792_);
lean_inc(v___x_785_);
v___x_794_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_785_, v_a_786_, v___x_793_, v___f_787_);
v___x_795_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_785_, v_a_786_, v___x_794_, v___f_788_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_797_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_a_796_);
lean_dec_ref_known(v___x_795_, 1);
v___x_797_ = lean_task_pure(v_a_796_);
return v___x_797_;
}
else
{
lean_object* v_a_798_; 
v_a_798_ = lean_ctor_get(v___x_795_, 0);
lean_inc_ref(v_a_798_);
lean_dec_ref_known(v___x_795_, 1);
return v_a_798_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_784_ = stack[0].m_obj;
lean_object* v___x_785_ = stack[1].m_obj;
uint8_t v_a_786_ = stack[2].m_num;
lean_object* v___f_787_ = stack[3].m_obj;
lean_object* v___f_788_ = stack[4].m_obj;
lean_object* v_a_789_ = stack[5].m_obj;
lean_object* v_res_819_;
v_res_819_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__9(v___x_784_, v___x_785_, v_a_786_, v___f_787_, v___f_788_, v_a_789_);
stack->m_obj
 = v_res_819_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__9___boxed(lean_object* v___x_820_, lean_object* v___x_821_, lean_object* v_a_822_, lean_object* v___f_823_, lean_object* v___f_824_, lean_object* v_a_825_, lean_object* v___y_826_){
_start:
{
uint8_t v_a_11631__boxed_827_; lean_object* v_res_828_; 
v_a_11631__boxed_827_ = lean_unbox(v_a_822_);
v_res_828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__9(v___x_820_, v___x_821_, v_a_11631__boxed_827_, v___f_823_, v___f_824_, v_a_825_);
return v_res_828_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__12(lean_object* v_waiter_829_, lean_object* v___f_830_, lean_object* v___x_831_, lean_object* v___f_832_, lean_object* v_a_833_, lean_object* v___f_834_, lean_object* v___x_835_, lean_object* v___f_836_, lean_object* v___f_837_, lean_object* v_finished_838_, lean_object* v___f_839_, lean_object* v_x_840_){
_start:
{
if (lean_obj_tag(v_x_840_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_850_; 
lean_dec_ref(v___f_839_);
lean_dec(v_finished_838_);
lean_dec_ref(v___f_837_);
lean_dec_ref(v___f_836_);
lean_dec_ref(v___f_834_);
lean_dec_ref(v_a_833_);
lean_dec_ref(v___f_832_);
lean_dec(v___x_831_);
lean_dec_ref(v___f_830_);
lean_dec_ref(v_waiter_829_);
v_a_842_ = lean_ctor_get(v_x_840_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v_x_840_);
if (v_isSharedCheck_850_ == 0)
{
v___x_844_ = v_x_840_;
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v_x_840_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_849_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_848_; 
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
return v___x_848_;
}
}
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_874_; 
v_a_851_ = lean_ctor_get(v_x_840_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v_x_840_);
if (v_isSharedCheck_874_ == 0)
{
v___x_853_ = v_x_840_;
v_isShared_854_ = v_isSharedCheck_874_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v_x_840_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_874_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
uint8_t v___x_855_; 
v___x_855_ = lean_unbox(v_a_851_);
if (v___x_855_ == 0)
{
lean_object* v___f_856_; lean_object* v___f_857_; lean_object* v___f_858_; lean_object* v___f_859_; lean_object* v___x_860_; lean_object* v___x_862_; 
lean_inc_n(v_a_851_, 4);
lean_inc_n(v___x_831_, 4);
v___f_856_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__7___boxed), 7, 5);
lean_closure_set(v___f_856_, 0, v_waiter_829_);
lean_closure_set(v___f_856_, 1, v___f_830_);
lean_closure_set(v___f_856_, 2, v___x_831_);
lean_closure_set(v___f_856_, 3, v_a_851_);
lean_closure_set(v___f_856_, 4, v___f_832_);
lean_inc_ref(v_a_833_);
v___f_857_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_857_, 0, v_a_833_);
lean_closure_set(v___f_857_, 1, v___x_831_);
lean_closure_set(v___f_857_, 2, v_a_851_);
lean_closure_set(v___f_857_, 3, v___f_834_);
v___f_858_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__9___boxed), 7, 5);
lean_closure_set(v___f_858_, 0, v___x_835_);
lean_closure_set(v___f_858_, 1, v___x_831_);
lean_closure_set(v___f_858_, 2, v_a_851_);
lean_closure_set(v___f_858_, 3, v___f_857_);
lean_closure_set(v___f_858_, 4, v___f_836_);
v___f_859_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__11___boxed), 11, 9);
lean_closure_set(v___f_859_, 0, v_a_833_);
lean_closure_set(v___f_859_, 1, v___x_835_);
lean_closure_set(v___f_859_, 2, v___f_858_);
lean_closure_set(v___f_859_, 3, v___x_831_);
lean_closure_set(v___f_859_, 4, v_a_851_);
lean_closure_set(v___f_859_, 5, v___f_837_);
lean_closure_set(v___f_859_, 6, v_finished_838_);
lean_closure_set(v___f_859_, 7, v___f_839_);
lean_closure_set(v___f_859_, 8, v___f_856_);
v___x_860_ = lean_io_promise_new();
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_860_);
v___x_862_ = v___x_853_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_860_);
v___x_862_ = v_reuseFailAlloc_866_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v___x_863_; uint8_t v___x_864_; lean_object* v___x_865_; 
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
v___x_864_ = lean_unbox(v_a_851_);
lean_dec(v_a_851_);
v___x_865_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_831_, v___x_864_, v___x_863_, v___f_859_);
return v___x_865_;
}
}
else
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
lean_dec(v_a_851_);
lean_dec_ref(v___f_839_);
lean_dec(v_finished_838_);
lean_dec_ref(v___f_837_);
lean_dec_ref(v___f_836_);
lean_dec_ref(v___f_834_);
lean_dec_ref(v_a_833_);
lean_dec_ref(v___f_832_);
lean_dec(v___x_831_);
lean_dec_ref(v___f_830_);
lean_dec_ref(v_waiter_829_);
v___x_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_835_);
v___x_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
lean_ctor_set(v___x_868_, 1, v___x_835_);
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_869_);
v___x_871_ = v___x_853_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_869_);
v___x_871_ = v_reuseFailAlloc_873_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_872_; 
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
return v___x_872_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_waiter_829_ = stack[0].m_obj;
lean_object* v___f_830_ = stack[1].m_obj;
lean_object* v___x_831_ = stack[2].m_obj;
lean_object* v___f_832_ = stack[3].m_obj;
lean_object* v_a_833_ = stack[4].m_obj;
lean_object* v___f_834_ = stack[5].m_obj;
lean_object* v___x_835_ = stack[6].m_obj;
lean_object* v___f_836_ = stack[7].m_obj;
lean_object* v___f_837_ = stack[8].m_obj;
lean_object* v_finished_838_ = stack[9].m_obj;
lean_object* v___f_839_ = stack[10].m_obj;
lean_object* v_x_840_ = stack[11].m_obj;
lean_object* v_res_875_;
v_res_875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__12(v_waiter_829_, v___f_830_, v___x_831_, v___f_832_, v_a_833_, v___f_834_, v___x_835_, v___f_836_, v___f_837_, v_finished_838_, v___f_839_, v_x_840_);
stack->m_obj
 = v_res_875_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__12___boxed(lean_object* v_waiter_876_, lean_object* v___f_877_, lean_object* v___x_878_, lean_object* v___f_879_, lean_object* v_a_880_, lean_object* v___f_881_, lean_object* v___x_882_, lean_object* v___f_883_, lean_object* v___f_884_, lean_object* v_finished_885_, lean_object* v___f_886_, lean_object* v_x_887_, lean_object* v___y_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__12(v_waiter_876_, v___f_877_, v___x_878_, v___f_879_, v_a_880_, v___f_881_, v___x_882_, v___f_883_, v___f_884_, v_finished_885_, v___f_886_, v_x_887_);
return v_res_889_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__6(lean_object* v___x_890_, lean_object* v_x_891_){
_start:
{
if (lean_obj_tag(v_x_891_) == 0)
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_901_; 
lean_dec_ref(v___x_890_);
v_a_893_ = lean_ctor_get(v_x_891_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v_x_891_);
if (v_isSharedCheck_901_ == 0)
{
v___x_895_ = v_x_891_;
v_isShared_896_ = v_isSharedCheck_901_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v_x_891_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_901_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_900_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_899_; 
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
return v___x_899_;
}
}
}
else
{
lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_910_; 
v_isSharedCheck_910_ = !lean_is_exclusive(v_x_891_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; 
v_unused_911_ = lean_ctor_get(v_x_891_, 0);
lean_dec(v_unused_911_);
v___x_903_ = v_x_891_;
v_isShared_904_ = v_isSharedCheck_910_;
goto v_resetjp_902_;
}
else
{
lean_dec(v_x_891_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_910_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_890_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 0, v___x_905_);
v___x_907_ = v___x_903_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_905_);
v___x_907_ = v_reuseFailAlloc_909_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_908_; 
v___x_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
return v___x_908_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_890_ = stack[0].m_obj;
lean_object* v_x_891_ = stack[1].m_obj;
lean_object* v_res_912_;
v_res_912_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__6(v___x_890_, v_x_891_);
stack->m_obj
 = v_res_912_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__6___boxed(lean_object* v___x_913_, lean_object* v_x_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__6(v___x_913_, v_x_914_);
return v_res_916_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__2(lean_object* v_promise_917_, lean_object* v_x_918_){
_start:
{
if (lean_obj_tag(v_x_918_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_930_; 
v_a_920_ = lean_ctor_get(v_x_918_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v_x_918_);
if (v_isSharedCheck_930_ == 0)
{
v___x_922_ = v_x_918_;
v_isShared_923_ = v_isSharedCheck_930_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v_x_918_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_930_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_929_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_926_ = lean_io_promise_resolve(v___x_925_, v_promise_917_);
v___x_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
v___x_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
return v___x_928_;
}
}
}
else
{
lean_object* v___x_931_; 
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v_x_918_);
return v___x_931_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_promise_917_ = stack[0].m_obj;
lean_object* v_x_918_ = stack[1].m_obj;
lean_object* v_res_932_;
v_res_932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__2(v_promise_917_, v_x_918_);
stack->m_obj
 = v_res_932_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__2___boxed(lean_object* v_promise_933_, lean_object* v_x_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__2(v_promise_933_, v_x_934_);
lean_dec(v_promise_933_);
return v_res_936_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__5(lean_object* v___x_937_){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_937_);
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_937_ = stack[0].m_obj;
lean_object* v_res_941_;
v_res_941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__5(v___x_937_);
stack->m_obj
 = v_res_941_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__5___boxed(lean_object* v___x_942_, lean_object* v___y_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__5(v___x_942_);
return v_res_944_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__3(lean_object* v_promise_945_, lean_object* v_x_946_){
_start:
{
if (lean_obj_tag(v_x_946_) == 0)
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_956_; 
v_a_948_ = lean_ctor_get(v_x_946_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v_x_946_);
if (v_isSharedCheck_956_ == 0)
{
v___x_950_ = v_x_946_;
v_isShared_951_ = v_isSharedCheck_956_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v_x_946_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_956_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_955_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_954_; 
v___x_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
return v___x_954_;
}
}
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_957_ = lean_io_promise_resolve(v_x_946_, v_promise_945_);
v___x_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_promise_945_ = stack[0].m_obj;
lean_object* v_x_946_ = stack[1].m_obj;
lean_object* v_res_960_;
v_res_960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__3(v_promise_945_, v_x_946_);
stack->m_obj
 = v_res_960_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__3___boxed(lean_object* v_promise_961_, lean_object* v_x_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__3(v_promise_961_, v_x_962_);
lean_dec(v_promise_961_);
return v_res_964_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1(lean_object* v_x_965_){
_start:
{
if (lean_obj_tag(v_x_965_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_975_; 
v_a_967_ = lean_ctor_get(v_x_965_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v_x_965_);
if (v_isSharedCheck_975_ == 0)
{
v___x_969_ = v_x_965_;
v_isShared_970_ = v_isSharedCheck_975_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v_x_965_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_975_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_974_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
lean_object* v___x_973_; 
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
return v___x_973_;
}
}
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_985_; 
v_a_976_ = lean_ctor_get(v_x_965_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v_x_965_);
if (v_isSharedCheck_985_ == 0)
{
v___x_978_ = v_x_965_;
v_isShared_979_ = v_isSharedCheck_985_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v_x_965_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_985_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_984_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
return v___x_983_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_965_ = stack[0].m_obj;
lean_object* v_res_986_;
v_res_986_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1(v_x_965_);
stack->m_obj
 = v_res_986_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1___boxed(lean_object* v_x_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1(v_x_987_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0___boxed(lean_object* v_i_990_, lean_object* v_waiter_991_, lean_object* v_as_992_, lean_object* v_sz_993_, lean_object* v_x_994_, lean_object* v___y_995_){
_start:
{
size_t v_i_boxed_996_; size_t v_sz_boxed_997_; lean_object* v_res_998_; 
v_i_boxed_996_ = lean_unbox_usize(v_i_990_);
lean_dec(v_i_990_);
v_sz_boxed_997_ = lean_unbox_usize(v_sz_993_);
lean_dec(v_sz_993_);
v_res_998_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0(v_i_boxed_996_, v_waiter_991_, v_as_992_, v_sz_boxed_997_, v_x_994_);
return v_res_998_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(lean_object* v_waiter_1009_, lean_object* v_as_1010_, size_t v_sz_1011_, size_t v_i_1012_, lean_object* v_b_1013_){
_start:
{
uint8_t v___x_1015_; 
v___x_1015_ = lean_usize_dec_lt(v_i_1012_, v_sz_1011_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_dec_ref(v_as_1010_);
lean_dec_ref(v_waiter_1009_);
v___x_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1016_, 0, v_b_1013_);
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
return v___x_1017_;
}
else
{
lean_object* v_finished_1018_; lean_object* v_promise_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___f_1022_; lean_object* v___f_1023_; lean_object* v___f_1024_; lean_object* v___f_1025_; lean_object* v___x_1026_; lean_object* v___f_1027_; lean_object* v___f_1028_; lean_object* v___f_1029_; lean_object* v_a_1030_; lean_object* v___x_1031_; lean_object* v___f_1032_; uint8_t v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
lean_dec_ref(v_b_1013_);
v_finished_1018_ = lean_ctor_get(v_waiter_1009_, 0);
lean_inc_n(v_finished_1018_, 2);
v_promise_1019_ = lean_ctor_get(v_waiter_1009_, 1);
v___x_1020_ = lean_box_usize(v_i_1012_);
v___x_1021_ = lean_box_usize(v_sz_1011_);
lean_inc_ref(v_as_1010_);
lean_inc_ref(v_waiter_1009_);
v___f_1022_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1022_, 0, v___x_1020_);
lean_closure_set(v___f_1022_, 1, v_waiter_1009_);
lean_closure_set(v___f_1022_, 2, v_as_1010_);
lean_closure_set(v___f_1022_, 3, v___x_1021_);
v___f_1023_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__0));
lean_inc_n(v_promise_1019_, 2);
v___f_1024_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1024_, 0, v_promise_1019_);
v___f_1025_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1025_, 0, v_promise_1019_);
v___x_1026_ = lean_box(0);
v___f_1027_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__1));
v___f_1028_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__2));
v___f_1029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__4));
v_a_1030_ = lean_array_uget(v_as_1010_, v_i_1012_);
lean_dec_ref(v_as_1010_);
v___x_1031_ = lean_unsigned_to_nat(0u);
v___f_1032_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__12___boxed), 13, 11);
lean_closure_set(v___f_1032_, 0, v_waiter_1009_);
lean_closure_set(v___f_1032_, 1, v___f_1028_);
lean_closure_set(v___f_1032_, 2, v___x_1031_);
lean_closure_set(v___f_1032_, 3, v___f_1027_);
lean_closure_set(v___f_1032_, 4, v_a_1030_);
lean_closure_set(v___f_1032_, 5, v___f_1025_);
lean_closure_set(v___f_1032_, 6, v___x_1026_);
lean_closure_set(v___f_1032_, 7, v___f_1024_);
lean_closure_set(v___f_1032_, 8, v___f_1029_);
lean_closure_set(v___f_1032_, 9, v_finished_1018_);
lean_closure_set(v___f_1032_, 10, v___f_1023_);
v___x_1033_ = 0;
v___x_1034_ = lean_st_ref_get(v_finished_1018_);
lean_dec(v_finished_1018_);
v___x_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
v___x_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
v___x_1037_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1031_, v___x_1033_, v___x_1036_, v___f_1032_);
v___x_1038_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1031_, v___x_1033_, v___x_1037_, v___f_1022_);
return v___x_1038_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_waiter_1009_ = stack[0].m_obj;
lean_object* v_as_1010_ = stack[1].m_obj;
size_t v_sz_1011_ = stack[2].m_num;
size_t v_i_1012_ = stack[3].m_num;
lean_object* v_b_1013_ = stack[4].m_obj;
lean_object* v_res_1039_;
v_res_1039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(v_waiter_1009_, v_as_1010_, v_sz_1011_, v_i_1012_, v_b_1013_);
stack->m_obj
 = v_res_1039_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0(size_t v_i_1040_, lean_object* v_waiter_1041_, lean_object* v_as_1042_, size_t v_sz_1043_, lean_object* v_x_1044_){
_start:
{
if (lean_obj_tag(v_x_1044_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1054_; 
lean_dec_ref(v_as_1042_);
lean_dec_ref(v_waiter_1041_);
v_a_1046_ = lean_ctor_get(v_x_1044_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_x_1044_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1048_ = v_x_1044_;
v_isShared_1049_ = v_isSharedCheck_1054_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v_x_1044_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1054_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1052_; 
v___x_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
return v___x_1052_;
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1074_; 
v_a_1055_ = lean_ctor_get(v_x_1044_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_x_1044_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1057_ = v_x_1044_;
v_isShared_1058_ = v_isSharedCheck_1074_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v_x_1044_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1074_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
if (lean_obj_tag(v_a_1055_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1069_; 
lean_dec_ref(v_as_1042_);
lean_dec_ref(v_waiter_1041_);
v_a_1059_ = lean_ctor_get(v_a_1055_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_a_1055_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1061_ = v_a_1055_;
v_isShared_1062_ = v_isSharedCheck_1069_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v_a_1055_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1069_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v_a_1059_);
v___x_1064_ = v___x_1057_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
lean_object* v___x_1066_; 
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1064_);
v___x_1066_ = v___x_1061_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
else
{
lean_object* v_a_1070_; size_t v___x_1071_; size_t v___x_1072_; lean_object* v___x_1073_; 
lean_del_object(v___x_1057_);
v_a_1070_ = lean_ctor_get(v_a_1055_, 0);
lean_inc(v_a_1070_);
lean_dec_ref_known(v_a_1055_, 1);
v___x_1071_ = ((size_t)1ULL);
v___x_1072_ = lean_usize_add(v_i_1040_, v___x_1071_);
v___x_1073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(v_waiter_1041_, v_as_1042_, v_sz_1043_, v___x_1072_, v_a_1070_);
return v___x_1073_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_i_1040_ = stack[0].m_num;
lean_object* v_waiter_1041_ = stack[1].m_obj;
lean_object* v_as_1042_ = stack[2].m_obj;
size_t v_sz_1043_ = stack[3].m_num;
lean_object* v_x_1044_ = stack[4].m_obj;
lean_object* v_res_1075_;
v_res_1075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0(v_i_1040_, v_waiter_1041_, v_as_1042_, v_sz_1043_, v_x_1044_);
stack->m_obj
 = v_res_1075_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___boxed(lean_object* v_waiter_1076_, lean_object* v_as_1077_, lean_object* v_sz_1078_, lean_object* v_i_1079_, lean_object* v_b_1080_, lean_object* v___y_1081_){
_start:
{
size_t v_sz_boxed_1082_; size_t v_i_boxed_1083_; lean_object* v_res_1084_; 
v_sz_boxed_1082_ = lean_unbox_usize(v_sz_1078_);
lean_dec(v_sz_1078_);
v_i_boxed_1083_ = lean_unbox_usize(v_i_1079_);
lean_dec(v_i_1079_);
v_res_1084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(v_waiter_1076_, v_as_1077_, v_sz_boxed_1082_, v_i_boxed_1083_, v_b_1080_);
return v_res_1084_;
}
}
lean_object* l_Std_Async_Selectable_combine___redArg___lam__5(lean_object* v_fst_1087_, lean_object* v_waiter_1088_, lean_object* v_x_1089_){
_start:
{
if (lean_obj_tag(v_x_1089_) == 0)
{
lean_object* v___x_1091_; 
lean_dec_ref(v_waiter_1088_);
lean_dec_ref(v_fst_1087_);
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v_x_1089_);
return v___x_1091_;
}
else
{
lean_object* v___f_1092_; lean_object* v___x_1093_; size_t v_sz_1094_; size_t v___x_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_dec_ref_known(v_x_1089_, 1);
v___f_1092_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___lam__5___closed__0));
v___x_1093_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__3));
v_sz_1094_ = lean_array_size(v_fst_1087_);
v___x_1095_ = ((size_t)0ULL);
v___x_1096_ = lean_unsigned_to_nat(0u);
v___x_1097_ = 0;
v___x_1098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(v_waiter_1088_, v_fst_1087_, v_sz_1094_, v___x_1095_, v___x_1093_);
v___x_1099_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1096_, v___x_1097_, v___x_1098_, v___f_1092_);
return v___x_1099_;
}
}
}
LEAN_EXPORT void l_Std_Async_Selectable_combine___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_1087_ = stack[0].m_obj;
lean_object* v_waiter_1088_ = stack[1].m_obj;
lean_object* v_x_1089_ = stack[2].m_obj;
lean_object* v_res_1100_;
v_res_1100_ = l_Std_Async_Selectable_combine___redArg___lam__5(v_fst_1087_, v_waiter_1088_, v_x_1089_);
stack->m_obj
 = v_res_1100_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__5___boxed(lean_object* v_fst_1101_, lean_object* v_waiter_1102_, lean_object* v_x_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Std_Async_Selectable_combine___redArg___lam__5(v_fst_1101_, v_waiter_1102_, v_x_1103_);
return v_res_1105_;
}
}
lean_object* l_Std_Async_Selectable_combine___redArg___lam__6(lean_object* v_selectables_1106_, lean_object* v_waiter_1107_, lean_object* v___x_1108_, lean_object* v_x_1109_){
_start:
{
if (lean_obj_tag(v_x_1109_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1119_; 
lean_dec_ref(v_waiter_1107_);
lean_dec_ref(v_selectables_1106_);
v_a_1111_ = lean_ctor_get(v_x_1109_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_x_1109_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1113_ = v_x_1109_;
v_isShared_1114_ = v_isSharedCheck_1119_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v_x_1109_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1119_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
return v___x_1117_;
}
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1121_; lean_object* v_fst_1122_; lean_object* v_snd_1123_; lean_object* v___f_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v_a_1120_ = lean_ctor_get(v_x_1109_, 0);
lean_inc(v_a_1120_);
lean_dec_ref_known(v_x_1109_, 1);
v___x_1121_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(v_selectables_1106_, v_a_1120_);
v_fst_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_fst_1122_);
v_snd_1123_ = lean_ctor_get(v___x_1121_, 1);
lean_inc(v_snd_1123_);
lean_dec_ref(v___x_1121_);
v___f_1124_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_1124_, 0, v_fst_1122_);
lean_closure_set(v___f_1124_, 1, v_waiter_1107_);
v___x_1125_ = lean_unsigned_to_nat(0u);
v___x_1126_ = 0;
v___x_1127_ = lean_st_ref_swap(v___x_1108_, v_snd_1123_);
lean_dec(v___x_1127_);
v___x_1128_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___lam__2___closed__1));
v___x_1129_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1125_, v___x_1126_, v___x_1128_, v___f_1124_);
return v___x_1129_;
}
}
}
LEAN_EXPORT void l_Std_Async_Selectable_combine___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_selectables_1106_ = stack[0].m_obj;
lean_object* v_waiter_1107_ = stack[1].m_obj;
lean_object* v___x_1108_ = stack[2].m_obj;
lean_object* v_x_1109_ = stack[3].m_obj;
lean_object* v_res_1130_;
v_res_1130_ = l_Std_Async_Selectable_combine___redArg___lam__6(v_selectables_1106_, v_waiter_1107_, v___x_1108_, v_x_1109_);
stack->m_obj
 = v_res_1130_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__6___boxed(lean_object* v_selectables_1131_, lean_object* v_waiter_1132_, lean_object* v___x_1133_, lean_object* v_x_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Std_Async_Selectable_combine___redArg___lam__6(v_selectables_1131_, v_waiter_1132_, v___x_1133_, v_x_1134_);
lean_dec(v___x_1133_);
return v_res_1136_;
}
}
lean_object* l_Std_Async_Selectable_combine___redArg___lam__7(lean_object* v_selectables_1137_, lean_object* v___x_1138_, lean_object* v_waiter_1139_){
_start:
{
lean_object* v___f_1141_; lean_object* v___x_1142_; uint8_t v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
lean_inc(v___x_1138_);
v___f_1141_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__6___boxed), 5, 3);
lean_closure_set(v___f_1141_, 0, v_selectables_1137_);
lean_closure_set(v___f_1141_, 1, v_waiter_1139_);
lean_closure_set(v___f_1141_, 2, v___x_1138_);
v___x_1142_ = lean_unsigned_to_nat(0u);
v___x_1143_ = 0;
v___x_1144_ = lean_st_ref_get(v___x_1138_);
lean_dec(v___x_1138_);
v___x_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
v___x_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
v___x_1147_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1142_, v___x_1143_, v___x_1146_, v___f_1141_);
return v___x_1147_;
}
}
LEAN_EXPORT void l_Std_Async_Selectable_combine___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_selectables_1137_ = stack[0].m_obj;
lean_object* v___x_1138_ = stack[1].m_obj;
lean_object* v_waiter_1139_ = stack[2].m_obj;
lean_object* v_res_1148_;
v_res_1148_ = l_Std_Async_Selectable_combine___redArg___lam__7(v_selectables_1137_, v___x_1138_, v_waiter_1139_);
stack->m_obj
 = v_res_1148_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__7___boxed(lean_object* v_selectables_1149_, lean_object* v___x_1150_, lean_object* v_waiter_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Std_Async_Selectable_combine___redArg___lam__7(v_selectables_1149_, v___x_1150_, v_waiter_1151_);
return v_res_1153_;
}
}
lean_object* l_Std_Async_Selectable_combine___redArg___lam__8(lean_object* v___x_1154_, lean_object* v_x_1155_){
_start:
{
if (lean_obj_tag(v_x_1155_) == 0)
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v_x_1155_);
return v___x_1157_;
}
else
{
lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1165_; 
v_isSharedCheck_1165_ = !lean_is_exclusive(v_x_1155_);
if (v_isSharedCheck_1165_ == 0)
{
lean_object* v_unused_1166_; 
v_unused_1166_ = lean_ctor_get(v_x_1155_, 0);
lean_dec(v_unused_1166_);
v___x_1159_ = v_x_1155_;
v_isShared_1160_ = v_isSharedCheck_1165_;
goto v_resetjp_1158_;
}
else
{
lean_dec(v_x_1155_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1165_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1154_);
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1154_);
v___x_1162_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
lean_object* v___x_1163_; 
v___x_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
return v___x_1163_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Selectable_combine___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1154_ = stack[0].m_obj;
lean_object* v_x_1155_ = stack[1].m_obj;
lean_object* v_res_1167_;
v_res_1167_ = l_Std_Async_Selectable_combine___redArg___lam__8(v___x_1154_, v_x_1155_);
stack->m_obj
 = v_res_1167_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__8___boxed(lean_object* v___x_1168_, lean_object* v_x_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Std_Async_Selectable_combine___redArg___lam__8(v___x_1168_, v_x_1169_);
return v_res_1171_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__1(lean_object* v_x_1172_){
_start:
{
if (lean_obj_tag(v_x_1172_) == 0)
{
lean_object* v___x_1174_; 
lean_dec_ref_known(v_x_1172_, 1);
v___x_1174_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___lam__2___closed__1));
return v___x_1174_;
}
else
{
lean_object* v___x_1175_; 
v___x_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1175_, 0, v_x_1172_);
return v___x_1175_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1172_ = stack[0].m_obj;
lean_object* v_res_1176_;
v_res_1176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__1(v_x_1172_);
stack->m_obj
 = v_res_1176_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__1___boxed(lean_object* v_x_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__1(v_x_1177_);
return v_res_1179_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__2(lean_object* v___x_1180_, lean_object* v_x_1181_){
_start:
{
if (lean_obj_tag(v_x_1181_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1191_; 
v_a_1183_ = lean_ctor_get(v_x_1181_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_x_1181_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1185_ = v_x_1181_;
v_isShared_1186_ = v_isSharedCheck_1191_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v_x_1181_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1191_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1189_; 
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
return v___x_1189_;
}
}
}
else
{
lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1200_; 
v_isSharedCheck_1200_ = !lean_is_exclusive(v_x_1181_);
if (v_isSharedCheck_1200_ == 0)
{
lean_object* v_unused_1201_; 
v_unused_1201_ = lean_ctor_get(v_x_1181_, 0);
lean_dec(v_unused_1201_);
v___x_1193_ = v_x_1181_;
v_isShared_1194_ = v_isSharedCheck_1200_;
goto v_resetjp_1192_;
}
else
{
lean_dec(v_x_1181_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1200_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1180_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v___x_1195_);
v___x_1197_ = v___x_1193_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1198_; 
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
return v___x_1198_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1180_ = stack[0].m_obj;
lean_object* v_x_1181_ = stack[1].m_obj;
lean_object* v_res_1202_;
v_res_1202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__2(v___x_1180_, v_x_1181_);
stack->m_obj
 = v_res_1202_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__2___boxed(lean_object* v___x_1203_, lean_object* v_x_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__2(v___x_1203_, v_x_1204_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__0___boxed(lean_object* v_i_1207_, lean_object* v_as_1208_, lean_object* v_sz_1209_, lean_object* v_x_1210_, lean_object* v___y_1211_){
_start:
{
size_t v_i_boxed_1212_; size_t v_sz_boxed_1213_; lean_object* v_res_1214_; 
v_i_boxed_1212_ = lean_unbox_usize(v_i_1207_);
lean_dec(v_i_1207_);
v_sz_boxed_1213_ = lean_unbox_usize(v_sz_1209_);
lean_dec(v_sz_1209_);
v_res_1214_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__0(v_i_boxed_1212_, v_as_1208_, v_sz_boxed_1213_, v_x_1210_);
return v_res_1214_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg(lean_object* v_as_1218_, size_t v_sz_1219_, size_t v_i_1220_, lean_object* v_b_1221_){
_start:
{
uint8_t v___x_1223_; 
v___x_1223_ = lean_usize_dec_lt(v_i_1220_, v_sz_1219_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
lean_dec_ref(v_as_1218_);
v___x_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1224_, 0, v_b_1221_);
v___x_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
return v___x_1225_;
}
else
{
lean_object* v_a_1226_; lean_object* v_selector_1227_; lean_object* v_unregisterFn_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___f_1231_; lean_object* v___f_1232_; lean_object* v___f_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v_a_1226_ = lean_array_uget_borrowed(v_as_1218_, v_i_1220_);
v_selector_1227_ = lean_ctor_get(v_a_1226_, 0);
v_unregisterFn_1228_ = lean_ctor_get(v_selector_1227_, 2);
lean_inc_ref(v_unregisterFn_1228_);
v___x_1229_ = lean_box_usize(v_i_1220_);
v___x_1230_ = lean_box_usize(v_sz_1219_);
v___f_1231_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1231_, 0, v___x_1229_);
lean_closure_set(v___f_1231_, 1, v_as_1218_);
lean_closure_set(v___f_1231_, 2, v___x_1230_);
v___f_1232_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___closed__0));
v___f_1233_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___closed__1));
v___x_1234_ = lean_unsigned_to_nat(0u);
v___x_1235_ = 0;
v___x_1236_ = lean_apply_1(v_unregisterFn_1228_, lean_box(0));
v___x_1237_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1234_, v___x_1235_, v___x_1236_, v___f_1232_);
v___x_1238_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1234_, v___x_1235_, v___x_1237_, v___f_1233_);
v___x_1239_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1234_, v___x_1235_, v___x_1238_, v___f_1231_);
return v___x_1239_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1218_ = stack[0].m_obj;
size_t v_sz_1219_ = stack[1].m_num;
size_t v_i_1220_ = stack[2].m_num;
lean_object* v_b_1221_ = stack[3].m_obj;
lean_object* v_res_1240_;
v_res_1240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg(v_as_1218_, v_sz_1219_, v_i_1220_, v_b_1221_);
stack->m_obj
 = v_res_1240_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__0(size_t v_i_1241_, lean_object* v_as_1242_, size_t v_sz_1243_, lean_object* v_x_1244_){
_start:
{
if (lean_obj_tag(v_x_1244_) == 0)
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1254_; 
lean_dec_ref(v_as_1242_);
v_a_1246_ = lean_ctor_get(v_x_1244_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_x_1244_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1248_ = v_x_1244_;
v_isShared_1249_ = v_isSharedCheck_1254_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v_x_1244_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1254_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1252_; 
v___x_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
return v___x_1252_;
}
}
}
else
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1274_; 
v_a_1255_ = lean_ctor_get(v_x_1244_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_x_1244_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1257_ = v_x_1244_;
v_isShared_1258_ = v_isSharedCheck_1274_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v_x_1244_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1274_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
if (lean_obj_tag(v_a_1255_) == 0)
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1269_; 
lean_dec_ref(v_as_1242_);
v_a_1259_ = lean_ctor_get(v_a_1255_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v_a_1255_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1261_ = v_a_1255_;
v_isShared_1262_ = v_isSharedCheck_1269_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v_a_1255_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1269_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v_a_1259_);
v___x_1264_ = v___x_1257_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1266_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 0, v___x_1264_);
v___x_1266_ = v___x_1261_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
else
{
lean_object* v_a_1270_; size_t v___x_1271_; size_t v___x_1272_; lean_object* v___x_1273_; 
lean_del_object(v___x_1257_);
v_a_1270_ = lean_ctor_get(v_a_1255_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v_a_1255_, 1);
v___x_1271_ = ((size_t)1ULL);
v___x_1272_ = lean_usize_add(v_i_1241_, v___x_1271_);
v___x_1273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg(v_as_1242_, v_sz_1243_, v___x_1272_, v_a_1270_);
return v___x_1273_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_i_1241_ = stack[0].m_num;
lean_object* v_as_1242_ = stack[1].m_obj;
size_t v_sz_1243_ = stack[2].m_num;
lean_object* v_x_1244_ = stack[3].m_obj;
lean_object* v_res_1275_;
v_res_1275_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__0(v_i_1241_, v_as_1242_, v_sz_1243_, v_x_1244_);
stack->m_obj
 = v_res_1275_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___boxed(lean_object* v_as_1276_, lean_object* v_sz_1277_, lean_object* v_i_1278_, lean_object* v_b_1279_, lean_object* v___y_1280_){
_start:
{
size_t v_sz_boxed_1281_; size_t v_i_boxed_1282_; lean_object* v_res_1283_; 
v_sz_boxed_1281_ = lean_unbox_usize(v_sz_1277_);
lean_dec(v_sz_1277_);
v_i_boxed_1282_ = lean_unbox_usize(v_i_1278_);
lean_dec(v_i_1278_);
v_res_1283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg(v_as_1276_, v_sz_boxed_1281_, v_i_boxed_1282_, v_b_1279_);
return v_res_1283_;
}
}
lean_object* l_Std_Async_Selectable_combine___redArg___lam__9(lean_object* v_selectables_1284_, size_t v_sz_1285_, size_t v___x_1286_, lean_object* v___x_1287_, lean_object* v___f_1288_){
_start:
{
lean_object* v___x_1290_; uint8_t v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1290_ = lean_unsigned_to_nat(0u);
v___x_1291_ = 0;
v___x_1292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg(v_selectables_1284_, v_sz_1285_, v___x_1286_, v___x_1287_);
v___x_1293_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1290_, v___x_1291_, v___x_1292_, v___f_1288_);
return v___x_1293_;
}
}
LEAN_EXPORT void l_Std_Async_Selectable_combine___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_selectables_1284_ = stack[0].m_obj;
size_t v_sz_1285_ = stack[1].m_num;
size_t v___x_1286_ = stack[2].m_num;
lean_object* v___x_1287_ = stack[3].m_obj;
lean_object* v___f_1288_ = stack[4].m_obj;
lean_object* v_res_1294_;
v_res_1294_ = l_Std_Async_Selectable_combine___redArg___lam__9(v_selectables_1284_, v_sz_1285_, v___x_1286_, v___x_1287_, v___f_1288_);
stack->m_obj
 = v_res_1294_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__9___boxed(lean_object* v_selectables_1295_, lean_object* v_sz_1296_, lean_object* v___x_1297_, lean_object* v___x_1298_, lean_object* v___f_1299_, lean_object* v___y_1300_){
_start:
{
size_t v_sz_boxed_1301_; size_t v___x_12808__boxed_1302_; lean_object* v_res_1303_; 
v_sz_boxed_1301_ = lean_unbox_usize(v_sz_1296_);
lean_dec(v_sz_1296_);
v___x_12808__boxed_1302_ = lean_unbox_usize(v___x_1297_);
lean_dec(v___x_1297_);
v_res_1303_ = l_Std_Async_Selectable_combine___redArg___lam__9(v_selectables_1295_, v_sz_boxed_1301_, v___x_12808__boxed_1302_, v___x_1298_, v___f_1299_);
return v_res_1303_;
}
}
lean_object* l_Std_Async_Selectable_combine___redArg(lean_object* v_selectables_1309_){
_start:
{
lean_object* v___f_1311_; lean_object* v___x_1312_; lean_object* v___f_1313_; lean_object* v___f_1314_; lean_object* v___f_1315_; lean_object* v___x_1316_; lean_object* v___f_1317_; size_t v_sz_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___f_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___f_1311_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___closed__0));
v___x_1312_ = l_IO_stdGenRef;
lean_inc_ref_n(v_selectables_1309_, 2);
v___f_1313_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_1313_, 0, v_selectables_1309_);
lean_closure_set(v___f_1313_, 1, v___f_1311_);
lean_closure_set(v___f_1313_, 2, v___x_1312_);
v___f_1314_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_1314_, 0, v___x_1312_);
lean_closure_set(v___f_1314_, 1, v___f_1313_);
v___f_1315_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_1315_, 0, v_selectables_1309_);
lean_closure_set(v___f_1315_, 1, v___x_1312_);
v___x_1316_ = lean_box(0);
v___f_1317_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___closed__1));
v_sz_1318_ = lean_array_size(v_selectables_1309_);
v___x_1319_ = lean_box_usize(v_sz_1318_);
v___x_1320_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___boxed__const__1));
v___f_1321_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__9___boxed), 6, 5);
lean_closure_set(v___f_1321_, 0, v_selectables_1309_);
lean_closure_set(v___f_1321_, 1, v___x_1319_);
lean_closure_set(v___f_1321_, 2, v___x_1320_);
lean_closure_set(v___f_1321_, 3, v___x_1316_);
lean_closure_set(v___f_1321_, 4, v___f_1317_);
v___x_1322_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1322_, 0, v___f_1314_);
lean_ctor_set(v___x_1322_, 1, v___f_1315_);
lean_ctor_set(v___x_1322_, 2, v___f_1321_);
v___x_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT void l_Std_Async_Selectable_combine___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_selectables_1309_ = stack[0].m_obj;
lean_object* v_res_1324_;
v_res_1324_ = l_Std_Async_Selectable_combine___redArg(v_selectables_1309_);
stack->m_obj
 = v_res_1324_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___boxed(lean_object* v_selectables_1325_, lean_object* v_a_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Std_Async_Selectable_combine___redArg(v_selectables_1325_);
return v_res_1327_;
}
}
lean_object* l_Std_Async_Selectable_combine(lean_object* v_00_u03b1_1328_, lean_object* v_selectables_1329_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Std_Async_Selectable_combine___redArg(v_selectables_1329_);
return v___x_1331_;
}
}
LEAN_EXPORT void l_Std_Async_Selectable_combine_0interp(lean_interpreter_value* stack)
{
lean_object* v_selectables_1329_ = stack[1].m_obj;
lean_object* v_res_1332_;
v_res_1332_ = l_Std_Async_Selectable_combine(lean_box(0), v_selectables_1329_);
stack->m_obj
 = v_res_1332_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___boxed(lean_object* v_00_u03b1_1333_, lean_object* v_selectables_1334_, lean_object* v_a_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Std_Async_Selectable_combine(v_00_u03b1_1333_, v_selectables_1334_);
return v_res_1336_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2(lean_object* v_00_u03b1_1337_, lean_object* v_waiter_1338_, lean_object* v_as_1339_, size_t v_sz_1340_, size_t v_i_1341_, lean_object* v_b_1342_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(v_waiter_1338_, v_as_1339_, v_sz_1340_, v_i_1341_, v_b_1342_);
return v___x_1344_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_waiter_1338_ = stack[1].m_obj;
lean_object* v_as_1339_ = stack[2].m_obj;
size_t v_sz_1340_ = stack[3].m_num;
size_t v_i_1341_ = stack[4].m_num;
lean_object* v_b_1342_ = stack[5].m_obj;
lean_object* v_res_1345_;
v_res_1345_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2(lean_box(0), v_waiter_1338_, v_as_1339_, v_sz_1340_, v_i_1341_, v_b_1342_);
stack->m_obj
 = v_res_1345_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___boxed(lean_object* v_00_u03b1_1346_, lean_object* v_waiter_1347_, lean_object* v_as_1348_, lean_object* v_sz_1349_, lean_object* v_i_1350_, lean_object* v_b_1351_, lean_object* v___y_1352_){
_start:
{
size_t v_sz_boxed_1353_; size_t v_i_boxed_1354_; lean_object* v_res_1355_; 
v_sz_boxed_1353_ = lean_unbox_usize(v_sz_1349_);
lean_dec(v_sz_1349_);
v_i_boxed_1354_ = lean_unbox_usize(v_i_1350_);
lean_dec(v_i_1350_);
v_res_1355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2(v_00_u03b1_1346_, v_waiter_1347_, v_as_1348_, v_sz_boxed_1353_, v_i_boxed_1354_, v_b_1351_);
return v_res_1355_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3(lean_object* v_00_u03b1_1356_, lean_object* v_as_1357_, size_t v_sz_1358_, size_t v_i_1359_, lean_object* v_b_1360_){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg(v_as_1357_, v_sz_1358_, v_i_1359_, v_b_1360_);
return v___x_1362_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1357_ = stack[1].m_obj;
size_t v_sz_1358_ = stack[2].m_num;
size_t v_i_1359_ = stack[3].m_num;
lean_object* v_b_1360_ = stack[4].m_obj;
lean_object* v_res_1363_;
v_res_1363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3(lean_box(0), v_as_1357_, v_sz_1358_, v_i_1359_, v_b_1360_);
stack->m_obj
 = v_res_1363_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___boxed(lean_object* v_00_u03b1_1364_, lean_object* v_as_1365_, lean_object* v_sz_1366_, lean_object* v_i_1367_, lean_object* v_b_1368_, lean_object* v___y_1369_){
_start:
{
size_t v_sz_boxed_1370_; size_t v_i_boxed_1371_; lean_object* v_res_1372_; 
v_sz_boxed_1370_ = lean_unbox_usize(v_sz_1366_);
lean_dec(v_sz_1366_);
v_i_boxed_1371_ = lean_unbox_usize(v_i_1367_);
lean_dec(v_i_1367_);
v_res_1372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3(v_00_u03b1_1364_, v_as_1365_, v_sz_boxed_1370_, v_i_boxed_1371_, v_b_1368_);
return v_res_1372_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4(lean_object* v_00_u03b1_1373_, lean_object* v_as_1374_, size_t v_sz_1375_, size_t v_i_1376_, lean_object* v_b_1377_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg(v_as_1374_, v_sz_1375_, v_i_1376_, v_b_1377_);
return v___x_1379_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1374_ = stack[1].m_obj;
size_t v_sz_1375_ = stack[2].m_num;
size_t v_i_1376_ = stack[3].m_num;
lean_object* v_b_1377_ = stack[4].m_obj;
lean_object* v_res_1380_;
v_res_1380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4(lean_box(0), v_as_1374_, v_sz_1375_, v_i_1376_, v_b_1377_);
stack->m_obj
 = v_res_1380_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___boxed(lean_object* v_00_u03b1_1381_, lean_object* v_as_1382_, lean_object* v_sz_1383_, lean_object* v_i_1384_, lean_object* v_b_1385_, lean_object* v___y_1386_){
_start:
{
size_t v_sz_boxed_1387_; size_t v_i_boxed_1388_; lean_object* v_res_1389_; 
v_sz_boxed_1387_ = lean_unbox_usize(v_sz_1383_);
lean_dec(v_sz_1383_);
v_i_boxed_1388_ = lean_unbox_usize(v_i_1384_);
lean_dec(v_i_1384_);
v_res_1389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4(v_00_u03b1_1381_, v_as_1382_, v_sz_boxed_1387_, v_i_boxed_1388_, v_b_1385_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__0(lean_object* v___y_1390_){
_start:
{
if (lean_obj_tag(v___y_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
v_a_1391_ = lean_ctor_get(v___y_1390_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___y_1390_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___y_1390_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___y_1390_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1407_; 
v_a_1399_ = lean_ctor_get(v___y_1390_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___y_1390_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1401_ = v___y_1390_;
v_isShared_1402_ = v_isSharedCheck_1407_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___y_1390_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1407_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v_fst_1403_; lean_object* v___x_1405_; 
v_fst_1403_ = lean_ctor_get(v_a_1399_, 0);
lean_inc(v_fst_1403_);
lean_dec(v_a_1399_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 0, v_fst_1403_);
v___x_1405_ = v___x_1401_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_fst_1403_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__1(lean_object* v___x_1408_, lean_object* v_x_1409_){
_start:
{
if (lean_obj_tag(v_x_1409_) == 0)
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = lean_mk_io_user_error(v___x_1408_);
v___x_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
return v___x_1411_;
}
else
{
lean_object* v_val_1412_; 
lean_dec_ref(v___x_1408_);
v_val_1412_ = lean_ctor_get(v_x_1409_, 0);
lean_inc(v_val_1412_);
return v_val_1412_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__1___boxed(lean_object* v___x_1413_, lean_object* v_x_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Std_Async_Selectable_one___redArg___lam__1(v___x_1413_, v_x_1414_);
lean_dec(v_x_1414_);
return v_res_1415_;
}
}
lean_object* l_Std_Async_Selectable_one___redArg___lam__2(lean_object* v___f_1416_, lean_object* v_x_1417_){
_start:
{
if (lean_obj_tag(v_x_1417_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1427_; 
lean_dec_ref(v___f_1416_);
v_a_1419_ = lean_ctor_get(v_x_1417_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_x_1417_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1421_ = v_x_1417_;
v_isShared_1422_ = v_isSharedCheck_1427_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v_x_1417_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1427_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
return v___x_1425_;
}
}
}
else
{
lean_object* v_a_1428_; 
v_a_1428_ = lean_ctor_get(v_x_1417_, 0);
lean_inc(v_a_1428_);
lean_dec_ref_known(v_x_1417_, 1);
if (lean_obj_tag(v_a_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1437_; 
lean_dec_ref(v___f_1416_);
v_a_1429_ = lean_ctor_get(v_a_1428_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_a_1428_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1431_ = v_a_1428_;
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v_a_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1434_);
return v___x_1435_;
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v_a_1438_ = lean_ctor_get(v_a_1428_, 0);
lean_inc(v_a_1438_);
lean_dec_ref_known(v_a_1428_, 1);
v___x_1439_ = lean_io_promise_result_opt(v_a_1438_);
lean_dec(v_a_1438_);
v___x_1440_ = lean_unsigned_to_nat(0u);
v___x_1441_ = 0;
v___x_1442_ = lean_task_map(v___f_1416_, v___x_1439_, v___x_1440_, v___x_1441_);
v___x_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
return v___x_1443_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_Selectable_one___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1416_ = stack[0].m_obj;
lean_object* v_x_1417_ = stack[1].m_obj;
lean_object* v_res_1444_;
v_res_1444_ = l_Std_Async_Selectable_one___redArg___lam__2(v___f_1416_, v_x_1417_);
stack->m_obj
 = v_res_1444_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__2___boxed(lean_object* v___f_1445_, lean_object* v_x_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Std_Async_Selectable_one___redArg___lam__2(v___f_1445_, v_x_1446_);
return v_res_1448_;
}
}
lean_object* l_Std_Async_Selectable_one___redArg___lam__3(lean_object* v_x_1454_, lean_object* v_x_1455_){
_start:
{
if (lean_obj_tag(v_x_1455_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1465_; 
lean_dec_ref(v_x_1454_);
v_a_1457_ = lean_ctor_get(v_x_1455_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_x_1455_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1459_ = v_x_1455_;
v_isShared_1460_ = v_isSharedCheck_1465_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v_x_1455_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1465_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1463_; 
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
return v___x_1463_;
}
}
}
else
{
lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1477_; 
v_isSharedCheck_1477_ = !lean_is_exclusive(v_x_1455_);
if (v_isSharedCheck_1477_ == 0)
{
lean_object* v_unused_1478_; 
v_unused_1478_ = lean_ctor_get(v_x_1455_, 0);
lean_dec(v_unused_1478_);
v___x_1467_ = v_x_1455_;
v_isShared_1468_ = v_isSharedCheck_1477_;
goto v_resetjp_1466_;
}
else
{
lean_dec(v_x_1455_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1477_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___f_1469_; lean_object* v___x_1470_; uint8_t v___x_1471_; lean_object* v___x_1473_; 
v___f_1469_ = ((lean_object*)(l_Std_Async_Selectable_one___redArg___lam__3___closed__2));
v___x_1470_ = lean_unsigned_to_nat(0u);
v___x_1471_ = 0;
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v_x_1454_);
v___x_1473_ = v___x_1467_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_x_1454_);
v___x_1473_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
v___x_1475_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1470_, v___x_1471_, v___x_1474_, v___f_1469_);
return v___x_1475_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Selectable_one___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1454_ = stack[0].m_obj;
lean_object* v_x_1455_ = stack[1].m_obj;
lean_object* v_res_1479_;
v_res_1479_ = l_Std_Async_Selectable_one___redArg___lam__3(v_x_1454_, v_x_1455_);
stack->m_obj
 = v_res_1479_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__3___boxed(lean_object* v_x_1480_, lean_object* v_x_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Std_Async_Selectable_one___redArg___lam__3(v_x_1480_, v_x_1481_);
return v_res_1483_;
}
}
lean_object* l_Std_Async_Selectable_one___redArg___lam__4(lean_object* v_a_1484_, lean_object* v_registerFn_1485_, uint8_t v___x_1486_, lean_object* v___f_1487_, lean_object* v_x_1488_){
_start:
{
if (lean_obj_tag(v_x_1488_) == 0)
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1498_; 
lean_dec_ref(v___f_1487_);
lean_dec_ref(v_registerFn_1485_);
lean_dec(v_a_1484_);
v_a_1490_ = lean_ctor_get(v_x_1488_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v_x_1488_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1492_ = v_x_1488_;
v_isShared_1493_ = v_isSharedCheck_1498_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v_x_1488_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1498_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
return v___x_1496_;
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v_a_1499_ = lean_ctor_get(v_x_1488_, 0);
lean_inc(v_a_1499_);
lean_dec_ref_known(v_x_1488_, 1);
v___x_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1500_, 0, v_a_1499_);
lean_ctor_set(v___x_1500_, 1, v_a_1484_);
v___x_1501_ = lean_unsigned_to_nat(0u);
v___x_1502_ = lean_apply_2(v_registerFn_1485_, v___x_1500_, lean_box(0));
v___x_1503_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1501_, v___x_1486_, v___x_1502_, v___f_1487_);
return v___x_1503_;
}
}
}
LEAN_EXPORT void l_Std_Async_Selectable_one___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1484_ = stack[0].m_obj;
lean_object* v_registerFn_1485_ = stack[1].m_obj;
uint8_t v___x_1486_ = stack[2].m_num;
lean_object* v___f_1487_ = stack[3].m_obj;
lean_object* v_x_1488_ = stack[4].m_obj;
lean_object* v_res_1504_;
v_res_1504_ = l_Std_Async_Selectable_one___redArg___lam__4(v_a_1484_, v_registerFn_1485_, v___x_1486_, v___f_1487_, v_x_1488_);
stack->m_obj
 = v_res_1504_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__4___boxed(lean_object* v_a_1505_, lean_object* v_registerFn_1506_, lean_object* v___x_1507_, lean_object* v___f_1508_, lean_object* v_x_1509_, lean_object* v___y_1510_){
_start:
{
uint8_t v___x_1935__boxed_1511_; lean_object* v_res_1512_; 
v___x_1935__boxed_1511_ = lean_unbox(v___x_1507_);
v_res_1512_ = l_Std_Async_Selectable_one___redArg___lam__4(v_a_1505_, v_registerFn_1506_, v___x_1935__boxed_1511_, v___f_1508_, v_x_1509_);
return v_res_1512_;
}
}
lean_object* l_Std_Async_Selectable_one___redArg___lam__5(uint8_t v___x_1513_, lean_object* v___f_1514_){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1516_ = lean_unsigned_to_nat(0u);
v___x_1517_ = lean_box(v___x_1513_);
v___x_1518_ = lean_st_mk_ref(v___x_1517_);
v___x_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
v___x_1521_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1516_, v___x_1513_, v___x_1520_, v___f_1514_);
return v___x_1521_;
}
}
LEAN_EXPORT void l_Std_Async_Selectable_one___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1513_ = stack[0].m_num;
lean_object* v___f_1514_ = stack[1].m_obj;
lean_object* v_res_1522_;
v_res_1522_ = l_Std_Async_Selectable_one___redArg___lam__5(v___x_1513_, v___f_1514_);
stack->m_obj
 = v_res_1522_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__5___boxed(lean_object* v___x_1523_, lean_object* v___f_1524_, lean_object* v___y_1525_){
_start:
{
uint8_t v___x_2001__boxed_1526_; lean_object* v_res_1527_; 
v___x_2001__boxed_1526_ = lean_unbox(v___x_1523_);
v_res_1527_ = l_Std_Async_Selectable_one___redArg___lam__5(v___x_2001__boxed_1526_, v___f_1524_);
return v_res_1527_;
}
}
lean_object* l_Std_Async_Selectable_one___redArg___lam__6(lean_object* v_unregisterFn_1528_, lean_object* v_x_1529_){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = lean_apply_1(v_unregisterFn_1528_, lean_box(0));
return v___x_1531_;
}
}
LEAN_EXPORT void l_Std_Async_Selectable_one___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_unregisterFn_1528_ = stack[0].m_obj;
lean_object* v_x_1529_ = stack[1].m_obj;
lean_object* v_res_1532_;
v_res_1532_ = l_Std_Async_Selectable_one___redArg___lam__6(v_unregisterFn_1528_, v_x_1529_);
stack->m_obj
 = v_res_1532_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__6___boxed(lean_object* v_unregisterFn_1533_, lean_object* v_x_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Std_Async_Selectable_one___redArg___lam__6(v_unregisterFn_1533_, v_x_1534_);
lean_dec(v_x_1534_);
return v_res_1536_;
}
}
lean_object* l_Std_Async_Selectable_one___redArg___lam__7(lean_object* v_registerFn_1537_, lean_object* v_unregisterFn_1538_, lean_object* v___f_1539_, lean_object* v_x_1540_){
_start:
{
if (lean_obj_tag(v_x_1540_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1550_; 
lean_dec_ref(v___f_1539_);
lean_dec_ref(v_unregisterFn_1538_);
lean_dec_ref(v_registerFn_1537_);
v_a_1542_ = lean_ctor_get(v_x_1540_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_x_1540_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1544_ = v_x_1540_;
v_isShared_1545_ = v_isSharedCheck_1550_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v_x_1540_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1550_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1542_);
v___x_1547_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
lean_object* v___x_1548_; 
v___x_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1547_);
return v___x_1548_;
}
}
}
else
{
lean_object* v_a_1551_; lean_object* v___f_1552_; uint8_t v___x_1553_; lean_object* v___x_1554_; lean_object* v___f_1555_; lean_object* v___x_1556_; lean_object* v___f_1557_; lean_object* v___f_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___y_1562_; 
v_a_1551_ = lean_ctor_get(v_x_1540_, 0);
lean_inc(v_a_1551_);
v___f_1552_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1552_, 0, v_x_1540_);
v___x_1553_ = 0;
v___x_1554_ = lean_box(v___x_1553_);
v___f_1555_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_1555_, 0, v_a_1551_);
lean_closure_set(v___f_1555_, 1, v_registerFn_1537_);
lean_closure_set(v___f_1555_, 2, v___x_1554_);
lean_closure_set(v___f_1555_, 3, v___f_1552_);
v___x_1556_ = lean_box(v___x_1553_);
v___f_1557_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__5___boxed), 3, 2);
lean_closure_set(v___f_1557_, 0, v___x_1556_);
lean_closure_set(v___f_1557_, 1, v___f_1555_);
v___f_1558_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__6___boxed), 3, 1);
lean_closure_set(v___f_1558_, 0, v_unregisterFn_1538_);
v___x_1559_ = lean_unsigned_to_nat(0u);
v___x_1560_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_1557_, v___f_1558_, v___x_1559_, v___x_1553_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1564_; 
lean_dec_ref(v___f_1539_);
v_a_1564_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1560_, 1);
if (lean_obj_tag(v_a_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
v_a_1565_ = lean_ctor_get(v_a_1564_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_a_1564_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v_a_1564_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v_a_1564_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
v___y_1562_ = v___x_1570_;
goto v___jp_1561_;
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1581_; 
v_a_1573_ = lean_ctor_get(v_a_1564_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_a_1564_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1575_ = v_a_1564_;
v_isShared_1576_ = v_isSharedCheck_1581_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v_a_1564_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1581_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v_fst_1577_; lean_object* v___x_1579_; 
v_fst_1577_ = lean_ctor_get(v_a_1573_, 0);
lean_inc(v_fst_1577_);
lean_dec(v_a_1573_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v_fst_1577_);
v___x_1579_ = v___x_1575_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_fst_1577_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
v___y_1562_ = v___x_1579_;
goto v___jp_1561_;
}
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1590_; 
v_a_1582_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1584_ = v___x_1560_;
v_isShared_1585_ = v_isSharedCheck_1590_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1560_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1590_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1586_ = lean_task_map(v___f_1539_, v_a_1582_, v___x_1559_, v___x_1553_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v___x_1586_);
v___x_1588_ = v___x_1584_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
v___jp_1561_:
{
lean_object* v___x_1563_; 
v___x_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___y_1562_);
return v___x_1563_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_Selectable_one___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_registerFn_1537_ = stack[0].m_obj;
lean_object* v_unregisterFn_1538_ = stack[1].m_obj;
lean_object* v___f_1539_ = stack[2].m_obj;
lean_object* v_x_1540_ = stack[3].m_obj;
lean_object* v_res_1591_;
v_res_1591_ = l_Std_Async_Selectable_one___redArg___lam__7(v_registerFn_1537_, v_unregisterFn_1538_, v___f_1539_, v_x_1540_);
stack->m_obj
 = v_res_1591_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__7___boxed(lean_object* v_registerFn_1592_, lean_object* v_unregisterFn_1593_, lean_object* v___f_1594_, lean_object* v_x_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Std_Async_Selectable_one___redArg___lam__7(v_registerFn_1592_, v_unregisterFn_1593_, v___f_1594_, v_x_1595_);
return v_res_1597_;
}
}
lean_object* l_Std_Async_Selectable_one___redArg___lam__8(lean_object* v___f_1598_, lean_object* v_x_1599_){
_start:
{
if (lean_obj_tag(v_x_1599_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1609_; 
lean_dec_ref(v___f_1598_);
v_a_1601_ = lean_ctor_get(v_x_1599_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_x_1599_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1603_ = v_x_1599_;
v_isShared_1604_ = v_isSharedCheck_1609_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v_x_1599_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1609_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_object* v___x_1607_; 
v___x_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1606_);
return v___x_1607_;
}
}
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1633_; 
v_a_1610_ = lean_ctor_get(v_x_1599_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v_x_1599_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1612_ = v_x_1599_;
v_isShared_1613_ = v_isSharedCheck_1633_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v_x_1599_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1633_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
if (lean_obj_tag(v_a_1610_) == 1)
{
lean_object* v_val_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1624_; 
lean_dec_ref(v___f_1598_);
v_val_1614_ = lean_ctor_get(v_a_1610_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v_a_1610_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1616_ = v_a_1610_;
v_isShared_1617_ = v_isSharedCheck_1624_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_val_1614_);
lean_dec(v_a_1610_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1624_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 0, v_val_1614_);
v___x_1619_ = v___x_1612_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_val_1614_);
v___x_1619_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
lean_object* v___x_1621_; 
if (v_isShared_1617_ == 0)
{
lean_ctor_set_tag(v___x_1616_, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1619_);
v___x_1621_ = v___x_1616_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
else
{
lean_object* v___x_1625_; uint8_t v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1629_; 
lean_dec(v_a_1610_);
v___x_1625_ = lean_unsigned_to_nat(0u);
v___x_1626_ = 0;
v___x_1627_ = lean_io_promise_new();
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 0, v___x_1627_);
v___x_1629_ = v___x_1612_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1627_);
v___x_1629_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
v___x_1631_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1625_, v___x_1626_, v___x_1630_, v___f_1598_);
return v___x_1631_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Selectable_one___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1598_ = stack[0].m_obj;
lean_object* v_x_1599_ = stack[1].m_obj;
lean_object* v_res_1634_;
v_res_1634_ = l_Std_Async_Selectable_one___redArg___lam__8(v___f_1598_, v_x_1599_);
stack->m_obj
 = v_res_1634_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__8___boxed(lean_object* v___f_1635_, lean_object* v_x_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Std_Async_Selectable_one___redArg___lam__8(v___f_1635_, v_x_1636_);
return v_res_1638_;
}
}
lean_object* l_Std_Async_Selectable_one___redArg___lam__9(lean_object* v___f_1639_, lean_object* v_x_1640_){
_start:
{
if (lean_obj_tag(v_x_1640_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1650_; 
lean_dec_ref(v___f_1639_);
v_a_1642_ = lean_ctor_get(v_x_1640_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_x_1640_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1644_ = v_x_1640_;
v_isShared_1645_ = v_isSharedCheck_1650_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v_x_1640_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1650_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1648_; 
v___x_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
return v___x_1648_;
}
}
}
else
{
lean_object* v_a_1651_; lean_object* v_tryFn_1652_; lean_object* v_registerFn_1653_; lean_object* v_unregisterFn_1654_; lean_object* v___f_1655_; lean_object* v___f_1656_; lean_object* v___x_1657_; uint8_t v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v_a_1651_ = lean_ctor_get(v_x_1640_, 0);
lean_inc(v_a_1651_);
lean_dec_ref_known(v_x_1640_, 1);
v_tryFn_1652_ = lean_ctor_get(v_a_1651_, 0);
lean_inc_ref(v_tryFn_1652_);
v_registerFn_1653_ = lean_ctor_get(v_a_1651_, 1);
lean_inc_ref(v_registerFn_1653_);
v_unregisterFn_1654_ = lean_ctor_get(v_a_1651_, 2);
lean_inc_ref(v_unregisterFn_1654_);
lean_dec(v_a_1651_);
v___f_1655_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__7___boxed), 5, 3);
lean_closure_set(v___f_1655_, 0, v_registerFn_1653_);
lean_closure_set(v___f_1655_, 1, v_unregisterFn_1654_);
lean_closure_set(v___f_1655_, 2, v___f_1639_);
v___f_1656_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__8___boxed), 3, 1);
lean_closure_set(v___f_1656_, 0, v___f_1655_);
v___x_1657_ = lean_unsigned_to_nat(0u);
v___x_1658_ = 0;
v___x_1659_ = lean_apply_1(v_tryFn_1652_, lean_box(0));
v___x_1660_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1657_, v___x_1658_, v___x_1659_, v___f_1656_);
return v___x_1660_;
}
}
}
LEAN_EXPORT void l_Std_Async_Selectable_one___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1639_ = stack[0].m_obj;
lean_object* v_x_1640_ = stack[1].m_obj;
lean_object* v_res_1661_;
v_res_1661_ = l_Std_Async_Selectable_one___redArg___lam__9(v___f_1639_, v_x_1640_);
stack->m_obj
 = v_res_1661_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__9___boxed(lean_object* v___f_1662_, lean_object* v_x_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Std_Async_Selectable_one___redArg___lam__9(v___f_1662_, v_x_1663_);
return v_res_1665_;
}
}
lean_object* l_Std_Async_Selectable_one___redArg___lam__10(lean_object* v___f_1666_, lean_object* v_selectables_1667_, lean_object* v_____r_1668_){
_start:
{
lean_object* v___x_1670_; uint8_t v___x_1671_; lean_object* v_val_1673_; lean_object* v___x_1676_; lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
v___x_1670_ = lean_unsigned_to_nat(0u);
v___x_1671_ = 0;
v___x_1676_ = l_Std_Async_Selectable_combine___redArg(v_selectables_1667_);
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1676_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1676_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v___jp_1672_:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1674_, 0, v_val_1673_);
v___x_1675_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1670_, v___x_1671_, v___x_1674_, v___f_1666_);
return v___x_1675_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
lean_ctor_set_tag(v___x_1679_, 1);
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
v_val_1673_ = v___x_1682_;
goto v___jp_1672_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_Selectable_one___redArg___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1666_ = stack[0].m_obj;
lean_object* v_selectables_1667_ = stack[1].m_obj;
lean_object* v_____r_1668_ = stack[2].m_obj;
lean_object* v_res_1685_;
v_res_1685_ = l_Std_Async_Selectable_one___redArg___lam__10(v___f_1666_, v_selectables_1667_, v_____r_1668_);
stack->m_obj
 = v_res_1685_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__10___boxed(lean_object* v___f_1686_, lean_object* v_selectables_1687_, lean_object* v_____r_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Std_Async_Selectable_one___redArg___lam__10(v___f_1686_, v_selectables_1687_, v_____r_1688_);
return v_res_1690_;
}
}
lean_object* l_Std_Async_Selectable_one___redArg___lam__11(lean_object* v___f_1691_, lean_object* v_x_1692_){
_start:
{
if (lean_obj_tag(v_x_1692_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1702_; 
lean_dec_ref(v___f_1691_);
v_a_1694_ = lean_ctor_get(v_x_1692_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v_x_1692_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1696_ = v_x_1692_;
v_isShared_1697_ = v_isSharedCheck_1702_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v_x_1692_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1702_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
lean_object* v___x_1700_; 
v___x_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1699_);
return v___x_1700_;
}
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1704_; 
v_a_1703_ = lean_ctor_get(v_x_1692_, 0);
lean_inc(v_a_1703_);
lean_dec_ref_known(v_x_1692_, 1);
v___x_1704_ = lean_apply_2(v___f_1691_, v_a_1703_, lean_box(0));
return v___x_1704_;
}
}
}
LEAN_EXPORT void l_Std_Async_Selectable_one___redArg___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1691_ = stack[0].m_obj;
lean_object* v_x_1692_ = stack[1].m_obj;
lean_object* v_res_1705_;
v_res_1705_ = l_Std_Async_Selectable_one___redArg___lam__11(v___f_1691_, v_x_1692_);
stack->m_obj
 = v_res_1705_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__11___boxed(lean_object* v___f_1706_, lean_object* v_x_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Std_Async_Selectable_one___redArg___lam__11(v___f_1706_, v_x_1707_);
return v_res_1709_;
}
}
lean_object* l_Std_Async_Selectable_one___redArg(lean_object* v_selectables_1720_){
_start:
{
lean_object* v___f_1722_; lean_object* v___f_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; 
v___f_1722_ = ((lean_object*)(l_Std_Async_Selectable_one___redArg___closed__1));
lean_inc_ref(v_selectables_1720_);
v___f_1723_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__10___boxed), 4, 2);
lean_closure_set(v___f_1723_, 0, v___f_1722_);
lean_closure_set(v___f_1723_, 1, v_selectables_1720_);
v___x_1724_ = lean_array_get_size(v_selectables_1720_);
v___x_1725_ = lean_unsigned_to_nat(0u);
v___x_1726_ = lean_nat_dec_eq(v___x_1724_, v___x_1725_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
lean_dec_ref(v___f_1723_);
v___x_1727_ = lean_box(0);
v___x_1728_ = l_Std_Async_Selectable_one___redArg___lam__10(v___f_1722_, v_selectables_1720_, v___x_1727_);
return v___x_1728_;
}
else
{
lean_object* v___f_1729_; uint8_t v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
lean_dec_ref(v_selectables_1720_);
v___f_1729_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__11___boxed), 3, 1);
lean_closure_set(v___f_1729_, 0, v___f_1723_);
v___x_1730_ = 0;
v___x_1731_ = ((lean_object*)(l_Std_Async_Selectable_one___redArg___closed__5));
v___x_1732_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1725_, v___x_1730_, v___x_1731_, v___f_1729_);
return v___x_1732_;
}
}
}
LEAN_EXPORT void l_Std_Async_Selectable_one___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_selectables_1720_ = stack[0].m_obj;
lean_object* v_res_1733_;
v_res_1733_ = l_Std_Async_Selectable_one___redArg(v_selectables_1720_);
stack->m_obj
 = v_res_1733_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___boxed(lean_object* v_selectables_1734_, lean_object* v_a_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Std_Async_Selectable_one___redArg(v_selectables_1734_);
return v_res_1736_;
}
}
lean_object* l_Std_Async_Selectable_one(lean_object* v_00_u03b1_1737_, lean_object* v_selectables_1738_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Std_Async_Selectable_one___redArg(v_selectables_1738_);
return v___x_1740_;
}
}
LEAN_EXPORT void l_Std_Async_Selectable_one_0interp(lean_interpreter_value* stack)
{
lean_object* v_selectables_1738_ = stack[1].m_obj;
lean_object* v_res_1741_;
v_res_1741_ = l_Std_Async_Selectable_one(lean_box(0), v_selectables_1738_);
stack->m_obj
 = v_res_1741_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___boxed(lean_object* v_00_u03b1_1742_, lean_object* v_selectables_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Std_Async_Selectable_one(v_00_u03b1_1742_, v_selectables_1743_);
return v_res_1745_;
}
}
lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__3(lean_object* v_selectables_1746_, lean_object* v___f_1747_, lean_object* v_____r_1748_){
_start:
{
lean_object* v___x_1750_; lean_object* v___f_1751_; lean_object* v___x_1752_; uint8_t v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1750_ = l_IO_stdGenRef;
v___f_1751_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_1751_, 0, v_selectables_1746_);
lean_closure_set(v___f_1751_, 1, v___f_1747_);
lean_closure_set(v___f_1751_, 2, v___x_1750_);
v___x_1752_ = lean_unsigned_to_nat(0u);
v___x_1753_ = 0;
v___x_1754_ = lean_st_ref_get(v___x_1750_);
v___x_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
v___x_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
v___x_1757_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1752_, v___x_1753_, v___x_1756_, v___f_1751_);
return v___x_1757_;
}
}
LEAN_EXPORT void l_Std_Async_Selectable_tryOne___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_selectables_1746_ = stack[0].m_obj;
lean_object* v___f_1747_ = stack[1].m_obj;
lean_object* v_____r_1748_ = stack[2].m_obj;
lean_object* v_res_1758_;
v_res_1758_ = l_Std_Async_Selectable_tryOne___redArg___lam__3(v_selectables_1746_, v___f_1747_, v_____r_1748_);
stack->m_obj
 = v_res_1758_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__3___boxed(lean_object* v_selectables_1759_, lean_object* v___f_1760_, lean_object* v_____r_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Std_Async_Selectable_tryOne___redArg___lam__3(v_selectables_1759_, v___f_1760_, v_____r_1761_);
return v_res_1763_;
}
}
lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__0(lean_object* v___f_1764_, lean_object* v_x_1765_){
_start:
{
if (lean_obj_tag(v_x_1765_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1775_; 
lean_dec_ref(v___f_1764_);
v_a_1767_ = lean_ctor_get(v_x_1765_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v_x_1765_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1769_ = v_x_1765_;
v_isShared_1770_ = v_isSharedCheck_1775_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v_x_1765_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1775_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1773_; 
v___x_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
return v___x_1773_;
}
}
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1777_; 
v_a_1776_ = lean_ctor_get(v_x_1765_, 0);
lean_inc(v_a_1776_);
lean_dec_ref_known(v_x_1765_, 1);
v___x_1777_ = lean_apply_2(v___f_1764_, v_a_1776_, lean_box(0));
return v___x_1777_;
}
}
}
LEAN_EXPORT void l_Std_Async_Selectable_tryOne___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1764_ = stack[0].m_obj;
lean_object* v_x_1765_ = stack[1].m_obj;
lean_object* v_res_1778_;
v_res_1778_ = l_Std_Async_Selectable_tryOne___redArg___lam__0(v___f_1764_, v_x_1765_);
stack->m_obj
 = v_res_1778_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__0___boxed(lean_object* v___f_1779_, lean_object* v_x_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Std_Async_Selectable_tryOne___redArg___lam__0(v___f_1779_, v_x_1780_);
return v_res_1782_;
}
}
lean_object* l_Std_Async_Selectable_tryOne___redArg(lean_object* v_selectables_1790_){
_start:
{
lean_object* v___f_1792_; lean_object* v___f_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___f_1792_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___closed__0));
lean_inc_ref(v_selectables_1790_);
v___f_1793_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_tryOne___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1793_, 0, v_selectables_1790_);
lean_closure_set(v___f_1793_, 1, v___f_1792_);
v___x_1794_ = lean_array_get_size(v_selectables_1790_);
v___x_1795_ = lean_unsigned_to_nat(0u);
v___x_1796_ = lean_nat_dec_eq(v___x_1794_, v___x_1795_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
lean_dec_ref(v___f_1793_);
v___x_1797_ = lean_box(0);
v___x_1798_ = l_Std_Async_Selectable_tryOne___redArg___lam__3(v_selectables_1790_, v___f_1792_, v___x_1797_);
return v___x_1798_;
}
else
{
lean_object* v___f_1799_; uint8_t v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
lean_dec_ref(v_selectables_1790_);
v___f_1799_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_tryOne___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1799_, 0, v___f_1793_);
v___x_1800_ = 0;
v___x_1801_ = ((lean_object*)(l_Std_Async_Selectable_tryOne___redArg___closed__3));
v___x_1802_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1795_, v___x_1800_, v___x_1801_, v___f_1799_);
return v___x_1802_;
}
}
}
LEAN_EXPORT void l_Std_Async_Selectable_tryOne___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_selectables_1790_ = stack[0].m_obj;
lean_object* v_res_1803_;
v_res_1803_ = l_Std_Async_Selectable_tryOne___redArg(v_selectables_1790_);
stack->m_obj
 = v_res_1803_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___boxed(lean_object* v_selectables_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Std_Async_Selectable_tryOne___redArg(v_selectables_1804_);
return v_res_1806_;
}
}
lean_object* l_Std_Async_Selectable_tryOne(lean_object* v_00_u03b1_1807_, lean_object* v_selectables_1808_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Std_Async_Selectable_tryOne___redArg(v_selectables_1808_);
return v___x_1810_;
}
}
LEAN_EXPORT void l_Std_Async_Selectable_tryOne_0interp(lean_interpreter_value* stack)
{
lean_object* v_selectables_1808_ = stack[1].m_obj;
lean_object* v_res_1811_;
v_res_1811_ = l_Std_Async_Selectable_tryOne(lean_box(0), v_selectables_1808_);
stack->m_obj
 = v_res_1811_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___boxed(lean_object* v_00_u03b1_1812_, lean_object* v_selectables_1813_, lean_object* v_a_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Std_Async_Selectable_tryOne(v_00_u03b1_1812_, v_selectables_1813_);
return v_res_1815_;
}
}
lean_object* runtime_initialize_Init_Data_Random(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray_Extra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Async_Select(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
