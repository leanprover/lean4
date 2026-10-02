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
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__0___redArg(lean_object* v_e_195_){
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
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__0___redArg___boxed(lean_object* v_e_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__0___redArg(v_e_215_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__0(lean_object* v_00_u03b1_218_, lean_object* v_e_219_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__0___redArg(v_e_219_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__0___boxed(lean_object* v_00_u03b1_222_, lean_object* v_e_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__0(v_00_u03b1_222_, v_e_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__0(lean_object* v_lose_226_, lean_object* v_a_227_, lean_object* v_promise_228_, lean_object* v_x_229_){
_start:
{
if (lean_obj_tag(v_x_229_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_239_; 
lean_dec(v_a_227_);
lean_dec_ref(v_lose_226_);
v_a_231_ = lean_ctor_get(v_x_229_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v_x_229_);
if (v_isSharedCheck_239_ == 0)
{
v___x_233_ = v_x_229_;
v_isShared_234_ = v_isSharedCheck_239_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v_x_229_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_239_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_238_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_237_; 
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
}
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_252_; 
v_a_240_ = lean_ctor_get(v_x_229_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v_x_229_);
if (v_isSharedCheck_252_ == 0)
{
v___x_242_ = v_x_229_;
v_isShared_243_ = v_isSharedCheck_252_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v_x_229_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_252_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
uint8_t v___x_244_; 
v___x_244_ = lean_unbox(v_a_240_);
lean_dec(v_a_240_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; 
lean_del_object(v___x_242_);
lean_dec(v_a_227_);
v___x_245_ = lean_apply_1(v_lose_226_, lean_box(0));
return v___x_245_;
}
else
{
lean_object* v___x_247_; 
lean_dec_ref(v_lose_226_);
if (v_isShared_243_ == 0)
{
lean_ctor_set_tag(v___x_242_, 0);
lean_ctor_set(v___x_242_, 0, v_a_227_);
v___x_247_ = v___x_242_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_227_);
v___x_247_ = v_reuseFailAlloc_251_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_248_ = lean_io_promise_resolve(v___x_247_, v_promise_228_);
v___x_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
v___x_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
return v___x_250_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__0___boxed(lean_object* v_lose_253_, lean_object* v_a_254_, lean_object* v_promise_255_, lean_object* v_x_256_, lean_object* v___y_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__0(v_lose_253_, v_a_254_, v_promise_255_, v_x_256_);
lean_dec(v_promise_255_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___redArg(lean_object* v_a_259_, lean_object* v_w_260_, lean_object* v_lose_261_){
_start:
{
lean_object* v_finished_263_; lean_object* v_promise_264_; lean_object* v___f_265_; lean_object* v___x_266_; uint8_t v___x_267_; lean_object* v___x_268_; uint8_t v___y_270_; uint8_t v___x_278_; 
v_finished_263_ = lean_ctor_get(v_w_260_, 0);
lean_inc(v_finished_263_);
v_promise_264_ = lean_ctor_get(v_w_260_, 1);
lean_inc(v_promise_264_);
lean_dec_ref(v_w_260_);
v___f_265_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_265_, 0, v_lose_261_);
lean_closure_set(v___f_265_, 1, v_a_259_);
lean_closure_set(v___f_265_, 2, v_promise_264_);
v___x_266_ = lean_unsigned_to_nat(0u);
v___x_267_ = 0;
v___x_268_ = lean_st_ref_take(v_finished_263_);
v___x_278_ = lean_unbox(v___x_268_);
lean_dec(v___x_268_);
if (v___x_278_ == 0)
{
uint8_t v___x_279_; 
v___x_279_ = 1;
v___y_270_ = v___x_279_;
goto v___jp_269_;
}
else
{
v___y_270_ = v___x_267_;
goto v___jp_269_;
}
v___jp_269_:
{
uint8_t v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_271_ = 1;
v___x_272_ = lean_box(v___x_271_);
v___x_273_ = lean_st_ref_put(v_finished_263_, v___x_272_);
lean_dec(v_finished_263_);
v___x_274_ = lean_box(v___y_270_);
v___x_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
v___x_277_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_266_, v___x_267_, v___x_276_, v___f_265_);
return v___x_277_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___redArg___boxed(lean_object* v_a_280_, lean_object* v_w_281_, lean_object* v_lose_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___redArg(v_a_280_, v_w_281_, v_lose_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1(lean_object* v_00_u03b1_285_, lean_object* v_a_286_, lean_object* v_w_287_, lean_object* v_lose_288_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___redArg(v_a_286_, v_w_287_, v_lose_288_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___boxed(lean_object* v_00_u03b1_291_, lean_object* v_a_292_, lean_object* v_w_293_, lean_object* v_lose_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1(v_00_u03b1_291_, v_a_292_, v_w_293_, v_lose_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__0(lean_object* v_x_301_){
_start:
{
if (lean_obj_tag(v_x_301_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_311_; 
v_a_303_ = lean_ctor_get(v_x_301_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v_x_301_);
if (v_isSharedCheck_311_ == 0)
{
v___x_305_ = v_x_301_;
v_isShared_306_ = v_isSharedCheck_311_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v_x_301_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_311_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_310_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_309_; 
v___x_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
return v___x_309_;
}
}
}
else
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_329_; 
v_a_312_ = lean_ctor_get(v_x_301_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v_x_301_);
if (v_isSharedCheck_329_ == 0)
{
v___x_314_ = v_x_301_;
v_isShared_315_ = v_isSharedCheck_329_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v_x_301_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_329_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v_fst_316_; 
v_fst_316_ = lean_ctor_get(v_a_312_, 0);
lean_inc(v_fst_316_);
lean_dec(v_a_312_);
if (lean_obj_tag(v_fst_316_) == 0)
{
lean_object* v___x_317_; 
lean_del_object(v___x_314_);
v___x_317_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___lam__0___closed__1));
return v___x_317_;
}
else
{
lean_object* v_val_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_328_; 
v_val_318_ = lean_ctor_get(v_fst_316_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v_fst_316_);
if (v_isSharedCheck_328_ == 0)
{
v___x_320_ = v_fst_316_;
v_isShared_321_ = v_isSharedCheck_328_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_val_318_);
lean_dec(v_fst_316_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_328_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v_val_318_);
v___x_323_ = v___x_314_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_val_318_);
v___x_323_ = v_reuseFailAlloc_327_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_325_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set_tag(v___x_320_, 0);
lean_ctor_set(v___x_320_, 0, v___x_323_);
v___x_325_ = v___x_320_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__0___boxed(lean_object* v_x_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Std_Async_Selectable_combine___redArg___lam__0(v_x_330_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__2(lean_object* v_a_333_, lean_object* v___x_334_, uint8_t v___x_335_, lean_object* v___f_336_, lean_object* v___x_337_, lean_object* v_x_338_){
_start:
{
if (lean_obj_tag(v_x_338_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_348_; 
lean_dec_ref(v___x_337_);
lean_dec_ref(v___f_336_);
lean_dec(v___x_334_);
lean_dec_ref(v_a_333_);
v_a_340_ = lean_ctor_get(v_x_338_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v_x_338_);
if (v_isSharedCheck_348_ == 0)
{
v___x_342_ = v_x_338_;
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v_x_338_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_348_;
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
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_340_);
v___x_345_ = v_reuseFailAlloc_347_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_object* v___x_346_; 
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_362_; 
v_a_349_ = lean_ctor_get(v_x_338_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v_x_338_);
if (v_isSharedCheck_362_ == 0)
{
v___x_351_ = v_x_338_;
v_isShared_352_ = v_isSharedCheck_362_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v_x_338_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_362_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
if (lean_obj_tag(v_a_349_) == 1)
{
lean_object* v_val_353_; lean_object* v_cont_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
lean_del_object(v___x_351_);
lean_dec_ref(v___x_337_);
v_val_353_ = lean_ctor_get(v_a_349_, 0);
lean_inc(v_val_353_);
lean_dec_ref_known(v_a_349_, 1);
v_cont_354_ = lean_ctor_get(v_a_333_, 1);
lean_inc_ref(v_cont_354_);
lean_dec_ref(v_a_333_);
v___x_355_ = lean_apply_2(v_cont_354_, v_val_353_, lean_box(0));
v___x_356_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_334_, v___x_335_, v___x_355_, v___f_336_);
return v___x_356_;
}
else
{
lean_object* v___x_357_; lean_object* v___x_359_; 
lean_dec(v_a_349_);
lean_dec_ref(v___f_336_);
lean_dec(v___x_334_);
lean_dec_ref(v_a_333_);
v___x_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_337_);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_357_);
v___x_359_ = v___x_351_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_357_);
v___x_359_ = v_reuseFailAlloc_361_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_360_; 
v___x_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
return v___x_360_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__2___boxed(lean_object* v_a_363_, lean_object* v___x_364_, lean_object* v___x_365_, lean_object* v___f_366_, lean_object* v___x_367_, lean_object* v_x_368_, lean_object* v___y_369_){
_start:
{
uint8_t v___x_10441__boxed_370_; lean_object* v_res_371_; 
v___x_10441__boxed_370_ = lean_unbox(v___x_365_);
v_res_371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__2(v_a_363_, v___x_364_, v___x_10441__boxed_370_, v___f_366_, v___x_367_, v_x_368_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__1(lean_object* v___x_372_, lean_object* v_x_373_){
_start:
{
if (lean_obj_tag(v_x_373_) == 0)
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_383_; 
v_a_375_ = lean_ctor_get(v_x_373_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v_x_373_);
if (v_isSharedCheck_383_ == 0)
{
v___x_377_ = v_x_373_;
v_isShared_378_ = v_isSharedCheck_383_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v_x_373_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_383_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_382_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
lean_object* v___x_381_; 
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
return v___x_381_;
}
}
}
else
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_396_; 
v_a_384_ = lean_ctor_get(v_x_373_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v_x_373_);
if (v_isSharedCheck_396_ == 0)
{
v___x_386_ = v_x_373_;
v_isShared_387_ = v_isSharedCheck_396_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v_x_373_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_396_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_388_, 0, v_a_384_);
v___x_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v___x_372_);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 0, v___x_391_);
v___x_393_ = v___x_386_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_391_);
v___x_393_ = v_reuseFailAlloc_395_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_394_; 
v___x_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
return v___x_394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__1___boxed(lean_object* v___x_397_, lean_object* v_x_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__1(v___x_397_, v_x_398_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__0___boxed(lean_object* v_i_401_, lean_object* v_as_402_, lean_object* v_sz_403_, lean_object* v_x_404_, lean_object* v___y_405_){
_start:
{
size_t v_i_boxed_406_; size_t v_sz_boxed_407_; lean_object* v_res_408_; 
v_i_boxed_406_ = lean_unbox_usize(v_i_401_);
lean_dec(v_i_401_);
v_sz_boxed_407_ = lean_unbox_usize(v_sz_403_);
lean_dec(v_sz_403_);
v_res_408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__0(v_i_boxed_406_, v_as_402_, v_sz_boxed_407_, v_x_404_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg(lean_object* v_as_414_, size_t v_sz_415_, size_t v_i_416_, lean_object* v_b_417_){
_start:
{
uint8_t v___x_419_; 
v___x_419_ = lean_usize_dec_lt(v_i_416_, v_sz_415_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; lean_object* v___x_421_; 
lean_dec_ref(v_as_414_);
v___x_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_420_, 0, v_b_417_);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
return v___x_421_;
}
else
{
lean_object* v_a_422_; lean_object* v_selector_423_; lean_object* v_tryFn_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___f_427_; lean_object* v___f_428_; lean_object* v___x_429_; lean_object* v___x_430_; uint8_t v___x_431_; lean_object* v___x_432_; lean_object* v___f_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec_ref(v_b_417_);
v_a_422_ = lean_array_uget(v_as_414_, v_i_416_);
v_selector_423_ = lean_ctor_get(v_a_422_, 0);
v_tryFn_424_ = lean_ctor_get(v_selector_423_, 0);
lean_inc_ref(v_tryFn_424_);
v___x_425_ = lean_box_usize(v_i_416_);
v___x_426_ = lean_box_usize(v_sz_415_);
v___f_427_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_427_, 0, v___x_425_);
lean_closure_set(v___f_427_, 1, v_as_414_);
lean_closure_set(v___f_427_, 2, v___x_426_);
v___f_428_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___closed__0));
v___x_429_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___closed__1));
v___x_430_ = lean_unsigned_to_nat(0u);
v___x_431_ = 0;
v___x_432_ = lean_box(v___x_431_);
v___f_433_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__2___boxed), 7, 5);
lean_closure_set(v___f_433_, 0, v_a_422_);
lean_closure_set(v___f_433_, 1, v___x_430_);
lean_closure_set(v___f_433_, 2, v___x_432_);
lean_closure_set(v___f_433_, 3, v___f_428_);
lean_closure_set(v___f_433_, 4, v___x_429_);
v___x_434_ = lean_apply_1(v_tryFn_424_, lean_box(0));
v___x_435_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_430_, v___x_431_, v___x_434_, v___f_433_);
v___x_436_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_430_, v___x_431_, v___x_435_, v___f_427_);
return v___x_436_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___lam__0(size_t v_i_437_, lean_object* v_as_438_, size_t v_sz_439_, lean_object* v_x_440_){
_start:
{
if (lean_obj_tag(v_x_440_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_450_; 
lean_dec_ref(v_as_438_);
v_a_442_ = lean_ctor_get(v_x_440_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v_x_440_);
if (v_isSharedCheck_450_ == 0)
{
v___x_444_ = v_x_440_;
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v_x_440_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_442_);
v___x_447_ = v_reuseFailAlloc_449_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_448_; 
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
return v___x_448_;
}
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_470_; 
v_a_451_ = lean_ctor_get(v_x_440_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v_x_440_);
if (v_isSharedCheck_470_ == 0)
{
v___x_453_ = v_x_440_;
v_isShared_454_ = v_isSharedCheck_470_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v_x_440_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_470_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
if (lean_obj_tag(v_a_451_) == 0)
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_465_; 
lean_dec_ref(v_as_438_);
v_a_455_ = lean_ctor_get(v_a_451_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v_a_451_);
if (v_isSharedCheck_465_ == 0)
{
v___x_457_ = v_a_451_;
v_isShared_458_ = v_isSharedCheck_465_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v_a_451_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_465_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v_a_455_);
v___x_460_ = v___x_453_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_464_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_462_; 
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_460_);
v___x_462_ = v___x_457_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
else
{
lean_object* v_a_466_; size_t v___x_467_; size_t v___x_468_; lean_object* v___x_469_; 
lean_del_object(v___x_453_);
v_a_466_ = lean_ctor_get(v_a_451_, 0);
lean_inc(v_a_466_);
lean_dec_ref_known(v_a_451_, 1);
v___x_467_ = ((size_t)1ULL);
v___x_468_ = lean_usize_add(v_i_437_, v___x_467_);
v___x_469_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg(v_as_438_, v_sz_439_, v___x_468_, v_a_466_);
return v___x_469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___boxed(lean_object* v_as_471_, lean_object* v_sz_472_, lean_object* v_i_473_, lean_object* v_b_474_, lean_object* v___y_475_){
_start:
{
size_t v_sz_boxed_476_; size_t v_i_boxed_477_; lean_object* v_res_478_; 
v_sz_boxed_476_ = lean_unbox_usize(v_sz_472_);
lean_dec(v_sz_472_);
v_i_boxed_477_ = lean_unbox_usize(v_i_473_);
lean_dec(v_i_473_);
v_res_478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg(v_as_471_, v_sz_boxed_476_, v_i_boxed_477_, v_b_474_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__1(lean_object* v_fst_479_, lean_object* v___f_480_, lean_object* v_x_481_){
_start:
{
if (lean_obj_tag(v_x_481_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_491_; 
lean_dec_ref(v___f_480_);
lean_dec_ref(v_fst_479_);
v_a_483_ = lean_ctor_get(v_x_481_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v_x_481_);
if (v_isSharedCheck_491_ == 0)
{
v___x_485_ = v_x_481_;
v_isShared_486_ = v_isSharedCheck_491_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v_x_481_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_491_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_490_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_489_; 
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
return v___x_489_;
}
}
}
else
{
lean_object* v___x_492_; size_t v_sz_493_; size_t v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
lean_dec_ref_known(v_x_481_, 1);
v___x_492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg___closed__1));
v_sz_493_ = lean_array_size(v_fst_479_);
v___x_494_ = ((size_t)0ULL);
v___x_495_ = lean_unsigned_to_nat(0u);
v___x_496_ = 0;
v___x_497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg(v_fst_479_, v_sz_493_, v___x_494_, v___x_492_);
v___x_498_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_495_, v___x_496_, v___x_497_, v___f_480_);
return v___x_498_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__1___boxed(lean_object* v_fst_499_, lean_object* v___f_500_, lean_object* v_x_501_, lean_object* v___y_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Std_Async_Selectable_combine___redArg___lam__1(v_fst_499_, v___f_500_, v_x_501_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__2(lean_object* v_selectables_508_, lean_object* v___f_509_, lean_object* v___x_510_, lean_object* v_x_511_){
_start:
{
if (lean_obj_tag(v_x_511_) == 0)
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_521_; 
lean_dec_ref(v___f_509_);
lean_dec_ref(v_selectables_508_);
v_a_513_ = lean_ctor_get(v_x_511_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v_x_511_);
if (v_isSharedCheck_521_ == 0)
{
v___x_515_ = v_x_511_;
v_isShared_516_ = v_isSharedCheck_521_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v_x_511_);
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
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
}
}
else
{
lean_object* v_a_522_; lean_object* v___x_523_; lean_object* v_fst_524_; lean_object* v_snd_525_; lean_object* v___f_526_; lean_object* v___x_527_; uint8_t v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v_a_522_ = lean_ctor_get(v_x_511_, 0);
lean_inc(v_a_522_);
lean_dec_ref_known(v_x_511_, 1);
v___x_523_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(v_selectables_508_, v_a_522_);
v_fst_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_fst_524_);
v_snd_525_ = lean_ctor_get(v___x_523_, 1);
lean_inc(v_snd_525_);
lean_dec_ref(v___x_523_);
v___f_526_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_526_, 0, v_fst_524_);
lean_closure_set(v___f_526_, 1, v___f_509_);
v___x_527_ = lean_unsigned_to_nat(0u);
v___x_528_ = 0;
v___x_529_ = lean_st_ref_swap(v___x_510_, v_snd_525_);
lean_dec(v___x_529_);
v___x_530_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___lam__2___closed__1));
v___x_531_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_527_, v___x_528_, v___x_530_, v___f_526_);
return v___x_531_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__2___boxed(lean_object* v_selectables_532_, lean_object* v___f_533_, lean_object* v___x_534_, lean_object* v_x_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Std_Async_Selectable_combine___redArg___lam__2(v_selectables_532_, v___f_533_, v___x_534_, v_x_535_);
lean_dec(v___x_534_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__3(lean_object* v___x_538_, lean_object* v___f_539_){
_start:
{
lean_object* v___x_541_; uint8_t v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_542_ = 0;
v___x_543_ = lean_st_ref_get(v___x_538_);
v___x_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
v___x_546_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_541_, v___x_542_, v___x_545_, v___f_539_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__4(lean_object* v___x_588_, lean_object* v_x_589_){
_start:
{
if (lean_obj_tag(v_x_589_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_599_; 
v_a_591_ = lean_ctor_get(v_x_589_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v_x_589_);
if (v_isSharedCheck_599_ == 0)
{
v___x_593_ = v_x_589_;
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v_x_589_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_598_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_597_; 
v___x_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
return v___x_597_;
}
}
}
else
{
lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_608_; 
v_isSharedCheck_608_ = !lean_is_exclusive(v_x_589_);
if (v_isSharedCheck_608_ == 0)
{
lean_object* v_unused_609_; 
v_unused_609_ = lean_ctor_get(v_x_589_, 0);
lean_dec(v_unused_609_);
v___x_601_ = v_x_589_;
v_isShared_602_ = v_isSharedCheck_608_;
goto v_resetjp_600_;
}
else
{
lean_dec(v_x_589_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_608_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set_tag(v___x_601_, 0);
lean_ctor_set(v___x_601_, 0, v___x_588_);
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_588_);
v___x_604_ = v_reuseFailAlloc_607_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
return v___x_606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__4___boxed(lean_object* v___x_610_, lean_object* v_x_611_, lean_object* v___y_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__4(v___x_610_, v_x_611_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__10(lean_object* v___x_614_, lean_object* v_a_615_, lean_object* v___f_616_, lean_object* v___x_617_, uint8_t v_a_618_, lean_object* v___f_619_, lean_object* v_x_620_){
_start:
{
if (lean_obj_tag(v_x_620_) == 0)
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_630_; 
lean_dec_ref(v___f_619_);
lean_dec(v___x_617_);
lean_dec_ref(v___f_616_);
v_a_622_ = lean_ctor_get(v_x_620_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v_x_620_);
if (v_isSharedCheck_630_ == 0)
{
v___x_624_ = v_x_620_;
v_isShared_625_ = v_isSharedCheck_630_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v_x_620_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_630_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_629_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_628_; 
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
return v___x_628_;
}
}
}
else
{
lean_object* v_a_631_; 
v_a_631_ = lean_ctor_get(v_x_620_, 0);
lean_inc(v_a_631_);
lean_dec_ref_known(v_x_620_, 1);
if (lean_obj_tag(v_a_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_643_; 
lean_dec_ref(v___f_619_);
lean_dec(v___x_617_);
lean_dec_ref(v___f_616_);
v_a_632_ = lean_ctor_get(v_a_631_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v_a_631_);
if (v_isSharedCheck_643_ == 0)
{
v___x_634_ = v_a_631_;
v_isShared_635_ = v_isSharedCheck_643_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v_a_631_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_643_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_636_, 0, v_a_632_);
v___x_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v___x_614_);
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
if (v_isShared_635_ == 0)
{
lean_ctor_set_tag(v___x_634_, 1);
lean_ctor_set(v___x_634_, 0, v___x_638_);
v___x_640_ = v___x_634_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_638_);
v___x_640_ = v_reuseFailAlloc_642_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_641_; 
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
return v___x_641_;
}
}
}
else
{
lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_654_; 
v_isSharedCheck_654_ = !lean_is_exclusive(v_a_631_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; 
v_unused_655_ = lean_ctor_get(v_a_631_, 0);
lean_dec(v_unused_655_);
v___x_645_ = v_a_631_;
v_isShared_646_ = v_isSharedCheck_654_;
goto v_resetjp_644_;
}
else
{
lean_dec(v_a_631_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_654_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_650_; 
v___x_647_ = lean_io_promise_result_opt(v_a_615_);
lean_inc(v___x_617_);
v___x_648_ = lean_io_bind_task(v___x_647_, v___f_616_, v___x_617_, v_a_618_);
lean_dec_ref(v___x_648_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v___x_614_);
v___x_650_ = v___x_645_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_614_);
v___x_650_ = v_reuseFailAlloc_653_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
v___x_652_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_617_, v_a_618_, v___x_651_, v___f_619_);
return v___x_652_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__10___boxed(lean_object* v___x_656_, lean_object* v_a_657_, lean_object* v___f_658_, lean_object* v___x_659_, lean_object* v_a_660_, lean_object* v___f_661_, lean_object* v_x_662_, lean_object* v___y_663_){
_start:
{
uint8_t v_a_10917__boxed_664_; lean_object* v_res_665_; 
v_a_10917__boxed_664_ = lean_unbox(v_a_660_);
v_res_665_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__10(v___x_656_, v_a_657_, v___f_658_, v___x_659_, v_a_10917__boxed_664_, v___f_661_, v_x_662_);
lean_dec(v_a_657_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__11(lean_object* v_a_666_, lean_object* v___x_667_, lean_object* v___f_668_, lean_object* v___x_669_, uint8_t v_a_670_, lean_object* v___f_671_, lean_object* v_finished_672_, lean_object* v___f_673_, lean_object* v___f_674_, lean_object* v_x_675_){
_start:
{
if (lean_obj_tag(v_x_675_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_685_; 
lean_dec_ref(v___f_674_);
lean_dec_ref(v___f_673_);
lean_dec(v_finished_672_);
lean_dec_ref(v___f_671_);
lean_dec(v___x_669_);
lean_dec_ref(v___f_668_);
lean_dec_ref(v_a_666_);
v_a_677_ = lean_ctor_get(v_x_675_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v_x_675_);
if (v_isSharedCheck_685_ == 0)
{
v___x_679_ = v_x_675_;
v_isShared_680_ = v_isSharedCheck_685_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v_x_675_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_685_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_677_);
v___x_682_ = v_reuseFailAlloc_684_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_683_; 
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
}
}
else
{
lean_object* v_selector_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_701_; 
v_selector_686_ = lean_ctor_get(v_a_666_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v_a_666_);
if (v_isSharedCheck_701_ == 0)
{
lean_object* v_unused_702_; 
v_unused_702_ = lean_ctor_get(v_a_666_, 1);
lean_dec(v_unused_702_);
v___x_688_ = v_a_666_;
v_isShared_689_ = v_isSharedCheck_701_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_selector_686_);
lean_dec(v_a_666_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_701_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_a_690_; lean_object* v_registerFn_691_; lean_object* v___x_692_; lean_object* v___f_693_; lean_object* v___x_695_; 
v_a_690_ = lean_ctor_get(v_x_675_, 0);
lean_inc_n(v_a_690_, 2);
lean_dec_ref_known(v_x_675_, 1);
v_registerFn_691_ = lean_ctor_get(v_selector_686_, 1);
lean_inc_ref(v_registerFn_691_);
lean_dec_ref(v_selector_686_);
v___x_692_ = lean_box(v_a_670_);
lean_inc(v___x_669_);
v___f_693_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__10___boxed), 8, 6);
lean_closure_set(v___f_693_, 0, v___x_667_);
lean_closure_set(v___f_693_, 1, v_a_690_);
lean_closure_set(v___f_693_, 2, v___f_668_);
lean_closure_set(v___f_693_, 3, v___x_669_);
lean_closure_set(v___f_693_, 4, v___x_692_);
lean_closure_set(v___f_693_, 5, v___f_671_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v_a_690_);
lean_ctor_set(v___x_688_, 0, v_finished_672_);
v___x_695_ = v___x_688_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_finished_672_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_a_690_);
v___x_695_ = v_reuseFailAlloc_700_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_696_ = lean_apply_2(v_registerFn_691_, v___x_695_, lean_box(0));
lean_inc_n(v___x_669_, 2);
v___x_697_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_669_, v_a_670_, v___x_696_, v___f_673_);
v___x_698_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_669_, v_a_670_, v___x_697_, v___f_674_);
v___x_699_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_669_, v_a_670_, v___x_698_, v___f_693_);
return v___x_699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__11___boxed(lean_object* v_a_703_, lean_object* v___x_704_, lean_object* v___f_705_, lean_object* v___x_706_, lean_object* v_a_707_, lean_object* v___f_708_, lean_object* v_finished_709_, lean_object* v___f_710_, lean_object* v___f_711_, lean_object* v_x_712_, lean_object* v___y_713_){
_start:
{
uint8_t v_a_11009__boxed_714_; lean_object* v_res_715_; 
v_a_11009__boxed_714_ = lean_unbox(v_a_707_);
v_res_715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__11(v_a_703_, v___x_704_, v___f_705_, v___x_706_, v_a_11009__boxed_714_, v___f_708_, v_finished_709_, v___f_710_, v___f_711_, v_x_712_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__7(lean_object* v_waiter_716_, lean_object* v___f_717_, lean_object* v___x_718_, uint8_t v_a_719_, lean_object* v___f_720_, lean_object* v_x_721_){
_start:
{
if (lean_obj_tag(v_x_721_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v_a_723_ = lean_ctor_get(v_x_721_, 0);
lean_inc(v_a_723_);
lean_dec_ref_known(v_x_721_, 1);
v___x_724_ = l_Std_Async_Waiter_race___at___00Std_Async_Selectable_combine_spec__1___redArg(v_a_723_, v_waiter_716_, v___f_717_);
v___x_725_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_718_, v_a_719_, v___x_724_, v___f_720_);
return v___x_725_;
}
else
{
lean_object* v___x_726_; 
lean_dec_ref(v___f_720_);
lean_dec(v___x_718_);
lean_dec_ref(v___f_717_);
lean_dec_ref(v_waiter_716_);
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v_x_721_);
return v___x_726_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__7___boxed(lean_object* v_waiter_727_, lean_object* v___f_728_, lean_object* v___x_729_, lean_object* v_a_730_, lean_object* v___f_731_, lean_object* v_x_732_, lean_object* v___y_733_){
_start:
{
uint8_t v_a_11083__boxed_734_; lean_object* v_res_735_; 
v_a_11083__boxed_734_ = lean_unbox(v_a_730_);
v_res_735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__7(v_waiter_727_, v___f_728_, v___x_729_, v_a_11083__boxed_734_, v___f_731_, v_x_732_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__8(lean_object* v_a_736_, lean_object* v___x_737_, uint8_t v_a_738_, lean_object* v___f_739_, lean_object* v_x_740_){
_start:
{
if (lean_obj_tag(v_x_740_) == 0)
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_750_; 
lean_dec_ref(v___f_739_);
lean_dec(v___x_737_);
lean_dec_ref(v_a_736_);
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
lean_object* v_a_751_; lean_object* v_cont_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v_a_751_ = lean_ctor_get(v_x_740_, 0);
lean_inc(v_a_751_);
lean_dec_ref_known(v_x_740_, 1);
v_cont_752_ = lean_ctor_get(v_a_736_, 1);
lean_inc_ref(v_cont_752_);
lean_dec_ref(v_a_736_);
v___x_753_ = lean_apply_2(v_cont_752_, v_a_751_, lean_box(0));
v___x_754_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_737_, v_a_738_, v___x_753_, v___f_739_);
return v___x_754_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__8___boxed(lean_object* v_a_755_, lean_object* v___x_756_, lean_object* v_a_757_, lean_object* v___f_758_, lean_object* v_x_759_, lean_object* v___y_760_){
_start:
{
uint8_t v_a_11109__boxed_761_; lean_object* v_res_762_; 
v_a_11109__boxed_761_ = lean_unbox(v_a_757_);
v_res_762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__8(v_a_755_, v___x_756_, v_a_11109__boxed_761_, v___f_758_, v_x_759_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__9(lean_object* v___x_763_, lean_object* v___x_764_, uint8_t v_a_765_, lean_object* v___f_766_, lean_object* v___f_767_, lean_object* v_a_768_){
_start:
{
lean_object* v_val_771_; 
if (lean_obj_tag(v_a_768_) == 0)
{
lean_object* v___x_778_; lean_object* v___x_779_; 
lean_dec_ref(v___f_767_);
lean_dec_ref(v___f_766_);
lean_dec(v___x_764_);
v___x_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_763_);
v___x_779_ = lean_task_pure(v___x_778_);
return v___x_779_;
}
else
{
lean_object* v_val_780_; lean_object* v___x_781_; 
v_val_780_ = lean_ctor_get(v_a_768_, 0);
lean_inc(v_val_780_);
lean_dec_ref_known(v_a_768_, 1);
v___x_781_ = l_IO_ofExcept___at___00Std_Async_Selectable_combine_spec__0___redArg(v_val_780_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_781_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_781_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
lean_ctor_set_tag(v___x_784_, 1);
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_782_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
v_val_771_ = v___x_787_;
goto v___jp_770_;
}
}
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
v_a_790_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_781_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_781_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set_tag(v___x_792_, 0);
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
v_val_771_ = v___x_795_;
goto v___jp_770_;
}
}
}
}
v___jp_770_:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_772_, 0, v_val_771_);
lean_inc(v___x_764_);
v___x_773_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_764_, v_a_765_, v___x_772_, v___f_766_);
v___x_774_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_764_, v_a_765_, v___x_773_, v___f_767_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v___x_776_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_775_);
lean_dec_ref_known(v___x_774_, 1);
v___x_776_ = lean_task_pure(v_a_775_);
return v___x_776_;
}
else
{
lean_object* v_a_777_; 
v_a_777_ = lean_ctor_get(v___x_774_, 0);
lean_inc_ref(v_a_777_);
lean_dec_ref_known(v___x_774_, 1);
return v_a_777_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__9___boxed(lean_object* v___x_798_, lean_object* v___x_799_, lean_object* v_a_800_, lean_object* v___f_801_, lean_object* v___f_802_, lean_object* v_a_803_, lean_object* v___y_804_){
_start:
{
uint8_t v_a_11149__boxed_805_; lean_object* v_res_806_; 
v_a_11149__boxed_805_ = lean_unbox(v_a_800_);
v_res_806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__9(v___x_798_, v___x_799_, v_a_11149__boxed_805_, v___f_801_, v___f_802_, v_a_803_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__12(lean_object* v_waiter_807_, lean_object* v___f_808_, lean_object* v___x_809_, lean_object* v___f_810_, lean_object* v_a_811_, lean_object* v___f_812_, lean_object* v___x_813_, lean_object* v___f_814_, lean_object* v___f_815_, lean_object* v_finished_816_, lean_object* v___f_817_, lean_object* v_x_818_){
_start:
{
if (lean_obj_tag(v_x_818_) == 0)
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_828_; 
lean_dec_ref(v___f_817_);
lean_dec(v_finished_816_);
lean_dec_ref(v___f_815_);
lean_dec_ref(v___f_814_);
lean_dec_ref(v___f_812_);
lean_dec_ref(v_a_811_);
lean_dec_ref(v___f_810_);
lean_dec(v___x_809_);
lean_dec_ref(v___f_808_);
lean_dec_ref(v_waiter_807_);
v_a_820_ = lean_ctor_get(v_x_818_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v_x_818_);
if (v_isSharedCheck_828_ == 0)
{
v___x_822_ = v_x_818_;
v_isShared_823_ = v_isSharedCheck_828_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v_x_818_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_828_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_827_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
lean_object* v___x_826_; 
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
return v___x_826_;
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_852_; 
v_a_829_ = lean_ctor_get(v_x_818_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v_x_818_);
if (v_isSharedCheck_852_ == 0)
{
v___x_831_ = v_x_818_;
v_isShared_832_ = v_isSharedCheck_852_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v_x_818_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_852_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
uint8_t v___x_833_; 
v___x_833_ = lean_unbox(v_a_829_);
if (v___x_833_ == 0)
{
lean_object* v___f_834_; lean_object* v___f_835_; lean_object* v___f_836_; lean_object* v___f_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
lean_inc_n(v_a_829_, 4);
lean_inc_n(v___x_809_, 4);
v___f_834_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__7___boxed), 7, 5);
lean_closure_set(v___f_834_, 0, v_waiter_807_);
lean_closure_set(v___f_834_, 1, v___f_808_);
lean_closure_set(v___f_834_, 2, v___x_809_);
lean_closure_set(v___f_834_, 3, v_a_829_);
lean_closure_set(v___f_834_, 4, v___f_810_);
lean_inc_ref(v_a_811_);
v___f_835_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_835_, 0, v_a_811_);
lean_closure_set(v___f_835_, 1, v___x_809_);
lean_closure_set(v___f_835_, 2, v_a_829_);
lean_closure_set(v___f_835_, 3, v___f_812_);
v___f_836_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__9___boxed), 7, 5);
lean_closure_set(v___f_836_, 0, v___x_813_);
lean_closure_set(v___f_836_, 1, v___x_809_);
lean_closure_set(v___f_836_, 2, v_a_829_);
lean_closure_set(v___f_836_, 3, v___f_835_);
lean_closure_set(v___f_836_, 4, v___f_814_);
v___f_837_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__11___boxed), 11, 9);
lean_closure_set(v___f_837_, 0, v_a_811_);
lean_closure_set(v___f_837_, 1, v___x_813_);
lean_closure_set(v___f_837_, 2, v___f_836_);
lean_closure_set(v___f_837_, 3, v___x_809_);
lean_closure_set(v___f_837_, 4, v_a_829_);
lean_closure_set(v___f_837_, 5, v___f_815_);
lean_closure_set(v___f_837_, 6, v_finished_816_);
lean_closure_set(v___f_837_, 7, v___f_817_);
lean_closure_set(v___f_837_, 8, v___f_834_);
v___x_838_ = lean_io_promise_new();
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_838_);
v___x_840_ = v___x_831_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_844_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v___x_841_; uint8_t v___x_842_; lean_object* v___x_843_; 
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
v___x_842_ = lean_unbox(v_a_829_);
lean_dec(v_a_829_);
v___x_843_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_809_, v___x_842_, v___x_841_, v___f_837_);
return v___x_843_;
}
}
else
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
lean_dec(v_a_829_);
lean_dec_ref(v___f_817_);
lean_dec(v_finished_816_);
lean_dec_ref(v___f_815_);
lean_dec_ref(v___f_814_);
lean_dec_ref(v___f_812_);
lean_dec_ref(v_a_811_);
lean_dec_ref(v___f_810_);
lean_dec(v___x_809_);
lean_dec_ref(v___f_808_);
lean_dec_ref(v_waiter_807_);
v___x_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_813_);
v___x_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
lean_ctor_set(v___x_846_, 1, v___x_813_);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_847_);
v___x_849_ = v___x_831_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_847_);
v___x_849_ = v_reuseFailAlloc_851_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_850_; 
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
return v___x_850_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__12___boxed(lean_object* v_waiter_853_, lean_object* v___f_854_, lean_object* v___x_855_, lean_object* v___f_856_, lean_object* v_a_857_, lean_object* v___f_858_, lean_object* v___x_859_, lean_object* v___f_860_, lean_object* v___f_861_, lean_object* v_finished_862_, lean_object* v___f_863_, lean_object* v_x_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__12(v_waiter_853_, v___f_854_, v___x_855_, v___f_856_, v_a_857_, v___f_858_, v___x_859_, v___f_860_, v___f_861_, v_finished_862_, v___f_863_, v_x_864_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__6(lean_object* v___x_867_, lean_object* v_x_868_){
_start:
{
if (lean_obj_tag(v_x_868_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_878_; 
lean_dec_ref(v___x_867_);
v_a_870_ = lean_ctor_get(v_x_868_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v_x_868_);
if (v_isSharedCheck_878_ == 0)
{
v___x_872_ = v_x_868_;
v_isShared_873_ = v_isSharedCheck_878_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v_x_868_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_878_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_877_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_876_; 
v___x_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
return v___x_876_;
}
}
}
else
{
lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_887_; 
v_isSharedCheck_887_ = !lean_is_exclusive(v_x_868_);
if (v_isSharedCheck_887_ == 0)
{
lean_object* v_unused_888_; 
v_unused_888_ = lean_ctor_get(v_x_868_, 0);
lean_dec(v_unused_888_);
v___x_880_ = v_x_868_;
v_isShared_881_ = v_isSharedCheck_887_;
goto v_resetjp_879_;
}
else
{
lean_dec(v_x_868_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_887_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_867_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_882_);
v___x_884_ = v___x_880_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_882_);
v___x_884_ = v_reuseFailAlloc_886_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_885_; 
v___x_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
return v___x_885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__6___boxed(lean_object* v___x_889_, lean_object* v_x_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__6(v___x_889_, v_x_890_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__2(lean_object* v_promise_893_, lean_object* v_x_894_){
_start:
{
if (lean_obj_tag(v_x_894_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_906_; 
v_a_896_ = lean_ctor_get(v_x_894_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v_x_894_);
if (v_isSharedCheck_906_ == 0)
{
v___x_898_ = v_x_894_;
v_isShared_899_ = v_isSharedCheck_906_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v_x_894_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_906_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_905_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_902_ = lean_io_promise_resolve(v___x_901_, v_promise_893_);
v___x_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
v___x_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
return v___x_904_;
}
}
}
else
{
lean_object* v___x_907_; 
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v_x_894_);
return v___x_907_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__2___boxed(lean_object* v_promise_908_, lean_object* v_x_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__2(v_promise_908_, v_x_909_);
lean_dec(v_promise_908_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__5(lean_object* v___x_912_){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_912_);
v___x_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__5___boxed(lean_object* v___x_916_, lean_object* v___y_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__5(v___x_916_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__3(lean_object* v_promise_919_, lean_object* v_x_920_){
_start:
{
if (lean_obj_tag(v_x_920_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_930_; 
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
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_931_ = lean_io_promise_resolve(v_x_920_, v_promise_919_);
v___x_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__3___boxed(lean_object* v_promise_934_, lean_object* v_x_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__3(v_promise_934_, v_x_935_);
lean_dec(v_promise_934_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1(lean_object* v_x_938_){
_start:
{
if (lean_obj_tag(v_x_938_) == 0)
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_948_; 
v_a_940_ = lean_ctor_get(v_x_938_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v_x_938_);
if (v_isSharedCheck_948_ == 0)
{
v___x_942_ = v_x_938_;
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v_x_938_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_948_;
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
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_947_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_946_; 
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
return v___x_946_;
}
}
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_958_; 
v_a_949_ = lean_ctor_get(v_x_938_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v_x_938_);
if (v_isSharedCheck_958_ == 0)
{
v___x_951_ = v_x_938_;
v_isShared_952_ = v_isSharedCheck_958_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v_x_938_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_958_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_957_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
v___x_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
return v___x_956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1___boxed(lean_object* v_x_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__1(v_x_959_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0___boxed(lean_object* v_i_962_, lean_object* v_waiter_963_, lean_object* v_as_964_, lean_object* v_sz_965_, lean_object* v_x_966_, lean_object* v___y_967_){
_start:
{
size_t v_i_boxed_968_; size_t v_sz_boxed_969_; lean_object* v_res_970_; 
v_i_boxed_968_ = lean_unbox_usize(v_i_962_);
lean_dec(v_i_962_);
v_sz_boxed_969_ = lean_unbox_usize(v_sz_965_);
lean_dec(v_sz_965_);
v_res_970_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0(v_i_boxed_968_, v_waiter_963_, v_as_964_, v_sz_boxed_969_, v_x_966_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(lean_object* v_waiter_981_, lean_object* v_as_982_, size_t v_sz_983_, size_t v_i_984_, lean_object* v_b_985_){
_start:
{
uint8_t v___x_987_; 
v___x_987_ = lean_usize_dec_lt(v_i_984_, v_sz_983_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; lean_object* v___x_989_; 
lean_dec_ref(v_as_982_);
lean_dec_ref(v_waiter_981_);
v___x_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_988_, 0, v_b_985_);
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
else
{
lean_object* v_finished_990_; lean_object* v_promise_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___f_994_; lean_object* v___f_995_; lean_object* v___f_996_; lean_object* v___f_997_; lean_object* v___x_998_; lean_object* v___f_999_; lean_object* v___f_1000_; lean_object* v___f_1001_; lean_object* v_a_1002_; lean_object* v___x_1003_; lean_object* v___f_1004_; uint8_t v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
lean_dec_ref(v_b_985_);
v_finished_990_ = lean_ctor_get(v_waiter_981_, 0);
lean_inc_n(v_finished_990_, 2);
v_promise_991_ = lean_ctor_get(v_waiter_981_, 1);
v___x_992_ = lean_box_usize(v_i_984_);
v___x_993_ = lean_box_usize(v_sz_983_);
lean_inc_ref(v_as_982_);
lean_inc_ref(v_waiter_981_);
v___f_994_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_994_, 0, v___x_992_);
lean_closure_set(v___f_994_, 1, v_waiter_981_);
lean_closure_set(v___f_994_, 2, v_as_982_);
lean_closure_set(v___f_994_, 3, v___x_993_);
v___f_995_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__0));
lean_inc_n(v_promise_991_, 2);
v___f_996_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_996_, 0, v_promise_991_);
v___f_997_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_997_, 0, v_promise_991_);
v___x_998_ = lean_box(0);
v___f_999_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__1));
v___f_1000_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__2));
v___f_1001_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__4));
v_a_1002_ = lean_array_uget(v_as_982_, v_i_984_);
lean_dec_ref(v_as_982_);
v___x_1003_ = lean_unsigned_to_nat(0u);
v___f_1004_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__12___boxed), 13, 11);
lean_closure_set(v___f_1004_, 0, v_waiter_981_);
lean_closure_set(v___f_1004_, 1, v___f_1000_);
lean_closure_set(v___f_1004_, 2, v___x_1003_);
lean_closure_set(v___f_1004_, 3, v___f_999_);
lean_closure_set(v___f_1004_, 4, v_a_1002_);
lean_closure_set(v___f_1004_, 5, v___f_997_);
lean_closure_set(v___f_1004_, 6, v___x_998_);
lean_closure_set(v___f_1004_, 7, v___f_996_);
lean_closure_set(v___f_1004_, 8, v___f_1001_);
lean_closure_set(v___f_1004_, 9, v_finished_990_);
lean_closure_set(v___f_1004_, 10, v___f_995_);
v___x_1005_ = 0;
v___x_1006_ = lean_st_ref_get(v_finished_990_);
lean_dec(v_finished_990_);
v___x_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
v___x_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
v___x_1009_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1003_, v___x_1005_, v___x_1008_, v___f_1004_);
v___x_1010_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1003_, v___x_1005_, v___x_1009_, v___f_994_);
return v___x_1010_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___lam__0(size_t v_i_1011_, lean_object* v_waiter_1012_, lean_object* v_as_1013_, size_t v_sz_1014_, lean_object* v_x_1015_){
_start:
{
if (lean_obj_tag(v_x_1015_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1025_; 
lean_dec_ref(v_as_1013_);
lean_dec_ref(v_waiter_1012_);
v_a_1017_ = lean_ctor_get(v_x_1015_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_x_1015_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1019_ = v_x_1015_;
v_isShared_1020_ = v_isSharedCheck_1025_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v_x_1015_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1025_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1023_; 
v___x_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
return v___x_1023_;
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1045_; 
v_a_1026_ = lean_ctor_get(v_x_1015_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_x_1015_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1028_ = v_x_1015_;
v_isShared_1029_ = v_isSharedCheck_1045_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v_x_1015_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1045_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
if (lean_obj_tag(v_a_1026_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1040_; 
lean_dec_ref(v_as_1013_);
lean_dec_ref(v_waiter_1012_);
v_a_1030_ = lean_ctor_get(v_a_1026_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_a_1026_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1032_ = v_a_1026_;
v_isShared_1033_ = v_isSharedCheck_1040_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v_a_1026_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1040_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v_a_1030_);
v___x_1035_ = v___x_1028_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1037_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 0, v___x_1035_);
v___x_1037_ = v___x_1032_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1041_; size_t v___x_1042_; size_t v___x_1043_; lean_object* v___x_1044_; 
lean_del_object(v___x_1028_);
v_a_1041_ = lean_ctor_get(v_a_1026_, 0);
lean_inc(v_a_1041_);
lean_dec_ref_known(v_a_1026_, 1);
v___x_1042_ = ((size_t)1ULL);
v___x_1043_ = lean_usize_add(v_i_1011_, v___x_1042_);
v___x_1044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(v_waiter_1012_, v_as_1013_, v_sz_1014_, v___x_1043_, v_a_1041_);
return v___x_1044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___boxed(lean_object* v_waiter_1046_, lean_object* v_as_1047_, lean_object* v_sz_1048_, lean_object* v_i_1049_, lean_object* v_b_1050_, lean_object* v___y_1051_){
_start:
{
size_t v_sz_boxed_1052_; size_t v_i_boxed_1053_; lean_object* v_res_1054_; 
v_sz_boxed_1052_ = lean_unbox_usize(v_sz_1048_);
lean_dec(v_sz_1048_);
v_i_boxed_1053_ = lean_unbox_usize(v_i_1049_);
lean_dec(v_i_1049_);
v_res_1054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(v_waiter_1046_, v_as_1047_, v_sz_boxed_1052_, v_i_boxed_1053_, v_b_1050_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__5(lean_object* v_fst_1057_, lean_object* v_waiter_1058_, lean_object* v_x_1059_){
_start:
{
if (lean_obj_tag(v_x_1059_) == 0)
{
lean_object* v___x_1061_; 
lean_dec_ref(v_waiter_1058_);
lean_dec_ref(v_fst_1057_);
v___x_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1061_, 0, v_x_1059_);
return v___x_1061_;
}
else
{
lean_object* v___f_1062_; lean_object* v___x_1063_; size_t v_sz_1064_; size_t v___x_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
lean_dec_ref_known(v_x_1059_, 1);
v___f_1062_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___lam__5___closed__0));
v___x_1063_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg___closed__3));
v_sz_1064_ = lean_array_size(v_fst_1057_);
v___x_1065_ = ((size_t)0ULL);
v___x_1066_ = lean_unsigned_to_nat(0u);
v___x_1067_ = 0;
v___x_1068_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(v_waiter_1058_, v_fst_1057_, v_sz_1064_, v___x_1065_, v___x_1063_);
v___x_1069_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1066_, v___x_1067_, v___x_1068_, v___f_1062_);
return v___x_1069_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__5___boxed(lean_object* v_fst_1070_, lean_object* v_waiter_1071_, lean_object* v_x_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Std_Async_Selectable_combine___redArg___lam__5(v_fst_1070_, v_waiter_1071_, v_x_1072_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__6(lean_object* v_selectables_1075_, lean_object* v_waiter_1076_, lean_object* v___x_1077_, lean_object* v_x_1078_){
_start:
{
if (lean_obj_tag(v_x_1078_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1088_; 
lean_dec_ref(v_waiter_1076_);
lean_dec_ref(v_selectables_1075_);
v_a_1080_ = lean_ctor_get(v_x_1078_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_x_1078_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1082_ = v_x_1078_;
v_isShared_1083_ = v_isSharedCheck_1088_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v_x_1078_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1088_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
return v___x_1086_;
}
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1090_; lean_object* v_fst_1091_; lean_object* v_snd_1092_; lean_object* v___f_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v_a_1089_ = lean_ctor_get(v_x_1078_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v_x_1078_, 1);
v___x_1090_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(v_selectables_1075_, v_a_1089_);
v_fst_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_fst_1091_);
v_snd_1092_ = lean_ctor_get(v___x_1090_, 1);
lean_inc(v_snd_1092_);
lean_dec_ref(v___x_1090_);
v___f_1093_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_1093_, 0, v_fst_1091_);
lean_closure_set(v___f_1093_, 1, v_waiter_1076_);
v___x_1094_ = lean_unsigned_to_nat(0u);
v___x_1095_ = 0;
v___x_1096_ = lean_st_ref_swap(v___x_1077_, v_snd_1092_);
lean_dec(v___x_1096_);
v___x_1097_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___lam__2___closed__1));
v___x_1098_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1094_, v___x_1095_, v___x_1097_, v___f_1093_);
return v___x_1098_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__6___boxed(lean_object* v_selectables_1099_, lean_object* v_waiter_1100_, lean_object* v___x_1101_, lean_object* v_x_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Std_Async_Selectable_combine___redArg___lam__6(v_selectables_1099_, v_waiter_1100_, v___x_1101_, v_x_1102_);
lean_dec(v___x_1101_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__7(lean_object* v_selectables_1105_, lean_object* v___x_1106_, lean_object* v_waiter_1107_){
_start:
{
lean_object* v___f_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_inc(v___x_1106_);
v___f_1109_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__6___boxed), 5, 3);
lean_closure_set(v___f_1109_, 0, v_selectables_1105_);
lean_closure_set(v___f_1109_, 1, v_waiter_1107_);
lean_closure_set(v___f_1109_, 2, v___x_1106_);
v___x_1110_ = lean_unsigned_to_nat(0u);
v___x_1111_ = 0;
v___x_1112_ = lean_st_ref_get(v___x_1106_);
lean_dec(v___x_1106_);
v___x_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
v___x_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
v___x_1115_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1110_, v___x_1111_, v___x_1114_, v___f_1109_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__7___boxed(lean_object* v_selectables_1116_, lean_object* v___x_1117_, lean_object* v_waiter_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Std_Async_Selectable_combine___redArg___lam__7(v_selectables_1116_, v___x_1117_, v_waiter_1118_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__8(lean_object* v___x_1121_, lean_object* v_x_1122_){
_start:
{
if (lean_obj_tag(v_x_1122_) == 0)
{
lean_object* v___x_1124_; 
v___x_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1124_, 0, v_x_1122_);
return v___x_1124_;
}
else
{
lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1132_; 
v_isSharedCheck_1132_ = !lean_is_exclusive(v_x_1122_);
if (v_isSharedCheck_1132_ == 0)
{
lean_object* v_unused_1133_; 
v_unused_1133_ = lean_ctor_get(v_x_1122_, 0);
lean_dec(v_unused_1133_);
v___x_1126_ = v_x_1122_;
v_isShared_1127_ = v_isSharedCheck_1132_;
goto v_resetjp_1125_;
}
else
{
lean_dec(v_x_1122_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1132_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v___x_1121_);
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1121_);
v___x_1129_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
return v___x_1130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__8___boxed(lean_object* v___x_1134_, lean_object* v_x_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Std_Async_Selectable_combine___redArg___lam__8(v___x_1134_, v_x_1135_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__1(lean_object* v_x_1138_){
_start:
{
if (lean_obj_tag(v_x_1138_) == 0)
{
lean_object* v___x_1140_; 
lean_dec_ref_known(v_x_1138_, 1);
v___x_1140_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___lam__2___closed__1));
return v___x_1140_;
}
else
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1141_, 0, v_x_1138_);
return v___x_1141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__1___boxed(lean_object* v_x_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__1(v_x_1142_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__2(lean_object* v___x_1145_, lean_object* v_x_1146_){
_start:
{
if (lean_obj_tag(v_x_1146_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1156_; 
v_a_1148_ = lean_ctor_get(v_x_1146_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_x_1146_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1150_ = v_x_1146_;
v_isShared_1151_ = v_isSharedCheck_1156_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v_x_1146_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1156_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
return v___x_1154_;
}
}
}
else
{
lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1165_; 
v_isSharedCheck_1165_ = !lean_is_exclusive(v_x_1146_);
if (v_isSharedCheck_1165_ == 0)
{
lean_object* v_unused_1166_; 
v_unused_1166_ = lean_ctor_get(v_x_1146_, 0);
lean_dec(v_unused_1166_);
v___x_1158_ = v_x_1146_;
v_isShared_1159_ = v_isSharedCheck_1165_;
goto v_resetjp_1157_;
}
else
{
lean_dec(v_x_1146_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1165_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1160_; lean_object* v___x_1162_; 
v___x_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1145_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 0, v___x_1160_);
v___x_1162_ = v___x_1158_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1160_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__2___boxed(lean_object* v___x_1167_, lean_object* v_x_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__2(v___x_1167_, v_x_1168_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__0___boxed(lean_object* v_i_1171_, lean_object* v_as_1172_, lean_object* v_sz_1173_, lean_object* v_x_1174_, lean_object* v___y_1175_){
_start:
{
size_t v_i_boxed_1176_; size_t v_sz_boxed_1177_; lean_object* v_res_1178_; 
v_i_boxed_1176_ = lean_unbox_usize(v_i_1171_);
lean_dec(v_i_1171_);
v_sz_boxed_1177_ = lean_unbox_usize(v_sz_1173_);
lean_dec(v_sz_1173_);
v_res_1178_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__0(v_i_boxed_1176_, v_as_1172_, v_sz_boxed_1177_, v_x_1174_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg(lean_object* v_as_1182_, size_t v_sz_1183_, size_t v_i_1184_, lean_object* v_b_1185_){
_start:
{
uint8_t v___x_1187_; 
v___x_1187_ = lean_usize_dec_lt(v_i_1184_, v_sz_1183_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_dec_ref(v_as_1182_);
v___x_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1188_, 0, v_b_1185_);
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
return v___x_1189_;
}
else
{
lean_object* v_a_1190_; lean_object* v_selector_1191_; lean_object* v_unregisterFn_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___f_1195_; lean_object* v___f_1196_; lean_object* v___f_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v_a_1190_ = lean_array_uget_borrowed(v_as_1182_, v_i_1184_);
v_selector_1191_ = lean_ctor_get(v_a_1190_, 0);
v_unregisterFn_1192_ = lean_ctor_get(v_selector_1191_, 2);
lean_inc_ref(v_unregisterFn_1192_);
v___x_1193_ = lean_box_usize(v_i_1184_);
v___x_1194_ = lean_box_usize(v_sz_1183_);
v___f_1195_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1195_, 0, v___x_1193_);
lean_closure_set(v___f_1195_, 1, v_as_1182_);
lean_closure_set(v___f_1195_, 2, v___x_1194_);
v___f_1196_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___closed__0));
v___f_1197_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___closed__1));
v___x_1198_ = lean_unsigned_to_nat(0u);
v___x_1199_ = 0;
v___x_1200_ = lean_apply_1(v_unregisterFn_1192_, lean_box(0));
v___x_1201_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1198_, v___x_1199_, v___x_1200_, v___f_1196_);
v___x_1202_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1198_, v___x_1199_, v___x_1201_, v___f_1197_);
v___x_1203_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1198_, v___x_1199_, v___x_1202_, v___f_1195_);
return v___x_1203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___lam__0(size_t v_i_1204_, lean_object* v_as_1205_, size_t v_sz_1206_, lean_object* v_x_1207_){
_start:
{
if (lean_obj_tag(v_x_1207_) == 0)
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1217_; 
lean_dec_ref(v_as_1205_);
v_a_1209_ = lean_ctor_get(v_x_1207_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_x_1207_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1211_ = v_x_1207_;
v_isShared_1212_ = v_isSharedCheck_1217_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v_x_1207_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1217_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
return v___x_1215_;
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1237_; 
v_a_1218_ = lean_ctor_get(v_x_1207_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_x_1207_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1220_ = v_x_1207_;
v_isShared_1221_ = v_isSharedCheck_1237_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v_x_1207_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1237_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
if (lean_obj_tag(v_a_1218_) == 0)
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1232_; 
lean_dec_ref(v_as_1205_);
v_a_1222_ = lean_ctor_get(v_a_1218_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_a_1218_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1224_ = v_a_1218_;
v_isShared_1225_ = v_isSharedCheck_1232_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v_a_1218_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1232_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v_a_1222_);
v___x_1227_ = v___x_1220_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
lean_object* v___x_1229_; 
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v___x_1227_);
v___x_1229_ = v___x_1224_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1227_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
else
{
lean_object* v_a_1233_; size_t v___x_1234_; size_t v___x_1235_; lean_object* v___x_1236_; 
lean_del_object(v___x_1220_);
v_a_1233_ = lean_ctor_get(v_a_1218_, 0);
lean_inc(v_a_1233_);
lean_dec_ref_known(v_a_1218_, 1);
v___x_1234_ = ((size_t)1ULL);
v___x_1235_ = lean_usize_add(v_i_1204_, v___x_1234_);
v___x_1236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg(v_as_1205_, v_sz_1206_, v___x_1235_, v_a_1233_);
return v___x_1236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg___boxed(lean_object* v_as_1238_, lean_object* v_sz_1239_, lean_object* v_i_1240_, lean_object* v_b_1241_, lean_object* v___y_1242_){
_start:
{
size_t v_sz_boxed_1243_; size_t v_i_boxed_1244_; lean_object* v_res_1245_; 
v_sz_boxed_1243_ = lean_unbox_usize(v_sz_1239_);
lean_dec(v_sz_1239_);
v_i_boxed_1244_ = lean_unbox_usize(v_i_1240_);
lean_dec(v_i_1240_);
v_res_1245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg(v_as_1238_, v_sz_boxed_1243_, v_i_boxed_1244_, v_b_1241_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__9(lean_object* v_selectables_1246_, size_t v_sz_1247_, size_t v___x_1248_, lean_object* v___x_1249_, lean_object* v___f_1250_){
_start:
{
lean_object* v___x_1252_; uint8_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1252_ = lean_unsigned_to_nat(0u);
v___x_1253_ = 0;
v___x_1254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg(v_selectables_1246_, v_sz_1247_, v___x_1248_, v___x_1249_);
v___x_1255_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1252_, v___x_1253_, v___x_1254_, v___f_1250_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___lam__9___boxed(lean_object* v_selectables_1256_, lean_object* v_sz_1257_, lean_object* v___x_1258_, lean_object* v___x_1259_, lean_object* v___f_1260_, lean_object* v___y_1261_){
_start:
{
size_t v_sz_boxed_1262_; size_t v___x_11930__boxed_1263_; lean_object* v_res_1264_; 
v_sz_boxed_1262_ = lean_unbox_usize(v_sz_1257_);
lean_dec(v_sz_1257_);
v___x_11930__boxed_1263_ = lean_unbox_usize(v___x_1258_);
lean_dec(v___x_1258_);
v_res_1264_ = l_Std_Async_Selectable_combine___redArg___lam__9(v_selectables_1256_, v_sz_boxed_1262_, v___x_11930__boxed_1263_, v___x_1259_, v___f_1260_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg(lean_object* v_selectables_1270_){
_start:
{
lean_object* v___f_1272_; lean_object* v___x_1273_; lean_object* v___f_1274_; lean_object* v___f_1275_; lean_object* v___f_1276_; lean_object* v___x_1277_; lean_object* v___f_1278_; size_t v_sz_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___f_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___f_1272_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___closed__0));
v___x_1273_ = l_IO_stdGenRef;
lean_inc_ref_n(v_selectables_1270_, 2);
v___f_1274_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_1274_, 0, v_selectables_1270_);
lean_closure_set(v___f_1274_, 1, v___f_1272_);
lean_closure_set(v___f_1274_, 2, v___x_1273_);
v___f_1275_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_1275_, 0, v___x_1273_);
lean_closure_set(v___f_1275_, 1, v___f_1274_);
v___f_1276_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_1276_, 0, v_selectables_1270_);
lean_closure_set(v___f_1276_, 1, v___x_1273_);
v___x_1277_ = lean_box(0);
v___f_1278_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___closed__1));
v_sz_1279_ = lean_array_size(v_selectables_1270_);
v___x_1280_ = lean_box_usize(v_sz_1279_);
v___x_1281_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___boxed__const__1));
v___f_1282_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__9___boxed), 6, 5);
lean_closure_set(v___f_1282_, 0, v_selectables_1270_);
lean_closure_set(v___f_1282_, 1, v___x_1280_);
lean_closure_set(v___f_1282_, 2, v___x_1281_);
lean_closure_set(v___f_1282_, 3, v___x_1277_);
lean_closure_set(v___f_1282_, 4, v___f_1278_);
v___x_1283_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1283_, 0, v___f_1275_);
lean_ctor_set(v___x_1283_, 1, v___f_1276_);
lean_ctor_set(v___x_1283_, 2, v___f_1282_);
v___x_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___redArg___boxed(lean_object* v_selectables_1285_, lean_object* v_a_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Std_Async_Selectable_combine___redArg(v_selectables_1285_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine(lean_object* v_00_u03b1_1288_, lean_object* v_selectables_1289_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = l_Std_Async_Selectable_combine___redArg(v_selectables_1289_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_combine___boxed(lean_object* v_00_u03b1_1292_, lean_object* v_selectables_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Std_Async_Selectable_combine(v_00_u03b1_1292_, v_selectables_1293_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2(lean_object* v_00_u03b1_1296_, lean_object* v_waiter_1297_, lean_object* v_as_1298_, size_t v_sz_1299_, size_t v_i_1300_, lean_object* v_b_1301_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___redArg(v_waiter_1297_, v_as_1298_, v_sz_1299_, v_i_1300_, v_b_1301_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2___boxed(lean_object* v_00_u03b1_1304_, lean_object* v_waiter_1305_, lean_object* v_as_1306_, lean_object* v_sz_1307_, lean_object* v_i_1308_, lean_object* v_b_1309_, lean_object* v___y_1310_){
_start:
{
size_t v_sz_boxed_1311_; size_t v_i_boxed_1312_; lean_object* v_res_1313_; 
v_sz_boxed_1311_ = lean_unbox_usize(v_sz_1307_);
lean_dec(v_sz_1307_);
v_i_boxed_1312_ = lean_unbox_usize(v_i_1308_);
lean_dec(v_i_1308_);
v_res_1313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__2(v_00_u03b1_1304_, v_waiter_1305_, v_as_1306_, v_sz_boxed_1311_, v_i_boxed_1312_, v_b_1309_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3(lean_object* v_00_u03b1_1314_, lean_object* v_as_1315_, size_t v_sz_1316_, size_t v_i_1317_, lean_object* v_b_1318_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___redArg(v_as_1315_, v_sz_1316_, v_i_1317_, v_b_1318_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3___boxed(lean_object* v_00_u03b1_1321_, lean_object* v_as_1322_, lean_object* v_sz_1323_, lean_object* v_i_1324_, lean_object* v_b_1325_, lean_object* v___y_1326_){
_start:
{
size_t v_sz_boxed_1327_; size_t v_i_boxed_1328_; lean_object* v_res_1329_; 
v_sz_boxed_1327_ = lean_unbox_usize(v_sz_1323_);
lean_dec(v_sz_1323_);
v_i_boxed_1328_ = lean_unbox_usize(v_i_1324_);
lean_dec(v_i_1324_);
v_res_1329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__3(v_00_u03b1_1321_, v_as_1322_, v_sz_boxed_1327_, v_i_boxed_1328_, v_b_1325_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4(lean_object* v_00_u03b1_1330_, lean_object* v_as_1331_, size_t v_sz_1332_, size_t v_i_1333_, lean_object* v_b_1334_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___redArg(v_as_1331_, v_sz_1332_, v_i_1333_, v_b_1334_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4___boxed(lean_object* v_00_u03b1_1337_, lean_object* v_as_1338_, lean_object* v_sz_1339_, lean_object* v_i_1340_, lean_object* v_b_1341_, lean_object* v___y_1342_){
_start:
{
size_t v_sz_boxed_1343_; size_t v_i_boxed_1344_; lean_object* v_res_1345_; 
v_sz_boxed_1343_ = lean_unbox_usize(v_sz_1339_);
lean_dec(v_sz_1339_);
v_i_boxed_1344_ = lean_unbox_usize(v_i_1340_);
lean_dec(v_i_1340_);
v_res_1345_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__4(v_00_u03b1_1337_, v_as_1338_, v_sz_boxed_1343_, v_i_boxed_1344_, v_b_1341_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__0(lean_object* v___y_1346_){
_start:
{
if (lean_obj_tag(v___y_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1354_; 
v_a_1347_ = lean_ctor_get(v___y_1346_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___y_1346_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1349_ = v___y_1346_;
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___y_1346_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1363_; 
v_a_1355_ = lean_ctor_get(v___y_1346_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___y_1346_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1357_ = v___y_1346_;
v_isShared_1358_ = v_isSharedCheck_1363_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___y_1346_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1363_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v_fst_1359_; lean_object* v___x_1361_; 
v_fst_1359_ = lean_ctor_get(v_a_1355_, 0);
lean_inc(v_fst_1359_);
lean_dec(v_a_1355_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v_fst_1359_);
v___x_1361_ = v___x_1357_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_fst_1359_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__1(lean_object* v___x_1364_, lean_object* v_x_1365_){
_start:
{
if (lean_obj_tag(v_x_1365_) == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = lean_mk_io_user_error(v___x_1364_);
v___x_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
return v___x_1367_;
}
else
{
lean_object* v_val_1368_; 
lean_dec_ref(v___x_1364_);
v_val_1368_ = lean_ctor_get(v_x_1365_, 0);
lean_inc(v_val_1368_);
return v_val_1368_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__1___boxed(lean_object* v___x_1369_, lean_object* v_x_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Std_Async_Selectable_one___redArg___lam__1(v___x_1369_, v_x_1370_);
lean_dec(v_x_1370_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__2(lean_object* v___f_1372_, lean_object* v_x_1373_){
_start:
{
if (lean_obj_tag(v_x_1373_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1383_; 
lean_dec_ref(v___f_1372_);
v_a_1375_ = lean_ctor_get(v_x_1373_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_x_1373_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1377_ = v_x_1373_;
v_isShared_1378_ = v_isSharedCheck_1383_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v_x_1373_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1383_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1375_);
v___x_1380_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
lean_object* v___x_1381_; 
v___x_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1380_);
return v___x_1381_;
}
}
}
else
{
lean_object* v_a_1384_; 
v_a_1384_ = lean_ctor_get(v_x_1373_, 0);
lean_inc(v_a_1384_);
lean_dec_ref_known(v_x_1373_, 1);
if (lean_obj_tag(v_a_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1393_; 
lean_dec_ref(v___f_1372_);
v_a_1385_ = lean_ctor_get(v_a_1384_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v_a_1384_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1387_ = v_a_1384_;
v_isShared_1388_ = v_isSharedCheck_1393_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v_a_1384_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1393_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1391_; 
v___x_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
return v___x_1391_;
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v_a_1394_ = lean_ctor_get(v_a_1384_, 0);
lean_inc(v_a_1394_);
lean_dec_ref_known(v_a_1384_, 1);
v___x_1395_ = lean_io_promise_result_opt(v_a_1394_);
lean_dec(v_a_1394_);
v___x_1396_ = lean_unsigned_to_nat(0u);
v___x_1397_ = 0;
v___x_1398_ = lean_task_map(v___f_1372_, v___x_1395_, v___x_1396_, v___x_1397_);
v___x_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
return v___x_1399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__2___boxed(lean_object* v___f_1400_, lean_object* v_x_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Std_Async_Selectable_one___redArg___lam__2(v___f_1400_, v_x_1401_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__3(lean_object* v_x_1409_, lean_object* v_x_1410_){
_start:
{
if (lean_obj_tag(v_x_1410_) == 0)
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1420_; 
lean_dec_ref(v_x_1409_);
v_a_1412_ = lean_ctor_get(v_x_1410_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v_x_1410_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1414_ = v_x_1410_;
v_isShared_1415_ = v_isSharedCheck_1420_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v_x_1410_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1420_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1418_; 
v___x_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
return v___x_1418_;
}
}
}
else
{
lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1432_; 
v_isSharedCheck_1432_ = !lean_is_exclusive(v_x_1410_);
if (v_isSharedCheck_1432_ == 0)
{
lean_object* v_unused_1433_; 
v_unused_1433_ = lean_ctor_get(v_x_1410_, 0);
lean_dec(v_unused_1433_);
v___x_1422_ = v_x_1410_;
v_isShared_1423_ = v_isSharedCheck_1432_;
goto v_resetjp_1421_;
}
else
{
lean_dec(v_x_1410_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1432_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___f_1424_; lean_object* v___x_1425_; uint8_t v___x_1426_; lean_object* v___x_1428_; 
v___f_1424_ = ((lean_object*)(l_Std_Async_Selectable_one___redArg___lam__3___closed__2));
v___x_1425_ = lean_unsigned_to_nat(0u);
v___x_1426_ = 0;
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 0, v_x_1409_);
v___x_1428_ = v___x_1422_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_x_1409_);
v___x_1428_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
v___x_1430_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1425_, v___x_1426_, v___x_1429_, v___f_1424_);
return v___x_1430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__3___boxed(lean_object* v_x_1434_, lean_object* v_x_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Std_Async_Selectable_one___redArg___lam__3(v_x_1434_, v_x_1435_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__4(lean_object* v_a_1438_, lean_object* v_registerFn_1439_, uint8_t v___x_1440_, lean_object* v___f_1441_, lean_object* v_x_1442_){
_start:
{
if (lean_obj_tag(v_x_1442_) == 0)
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1452_; 
lean_dec_ref(v___f_1441_);
lean_dec_ref(v_registerFn_1439_);
lean_dec(v_a_1438_);
v_a_1444_ = lean_ctor_get(v_x_1442_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_x_1442_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1446_ = v_x_1442_;
v_isShared_1447_ = v_isSharedCheck_1452_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v_x_1442_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1452_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
lean_object* v___x_1450_; 
v___x_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
return v___x_1450_;
}
}
}
else
{
lean_object* v_a_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v_a_1453_ = lean_ctor_get(v_x_1442_, 0);
lean_inc(v_a_1453_);
lean_dec_ref_known(v_x_1442_, 1);
v___x_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1454_, 0, v_a_1453_);
lean_ctor_set(v___x_1454_, 1, v_a_1438_);
v___x_1455_ = lean_unsigned_to_nat(0u);
v___x_1456_ = lean_apply_2(v_registerFn_1439_, v___x_1454_, lean_box(0));
v___x_1457_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1455_, v___x_1440_, v___x_1456_, v___f_1441_);
return v___x_1457_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__4___boxed(lean_object* v_a_1458_, lean_object* v_registerFn_1459_, lean_object* v___x_1460_, lean_object* v___f_1461_, lean_object* v_x_1462_, lean_object* v___y_1463_){
_start:
{
uint8_t v___x_1847__boxed_1464_; lean_object* v_res_1465_; 
v___x_1847__boxed_1464_ = lean_unbox(v___x_1460_);
v_res_1465_ = l_Std_Async_Selectable_one___redArg___lam__4(v_a_1458_, v_registerFn_1459_, v___x_1847__boxed_1464_, v___f_1461_, v_x_1462_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__5(uint8_t v___x_1466_, lean_object* v___f_1467_){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1469_ = lean_unsigned_to_nat(0u);
v___x_1470_ = lean_box(v___x_1466_);
v___x_1471_ = lean_st_mk_ref(v___x_1470_);
v___x_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
v___x_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
v___x_1474_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1469_, v___x_1466_, v___x_1473_, v___f_1467_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__5___boxed(lean_object* v___x_1475_, lean_object* v___f_1476_, lean_object* v___y_1477_){
_start:
{
uint8_t v___x_1889__boxed_1478_; lean_object* v_res_1479_; 
v___x_1889__boxed_1478_ = lean_unbox(v___x_1475_);
v_res_1479_ = l_Std_Async_Selectable_one___redArg___lam__5(v___x_1889__boxed_1478_, v___f_1476_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__6(lean_object* v_unregisterFn_1480_, lean_object* v_x_1481_){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = lean_apply_1(v_unregisterFn_1480_, lean_box(0));
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__6___boxed(lean_object* v_unregisterFn_1484_, lean_object* v_x_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Std_Async_Selectable_one___redArg___lam__6(v_unregisterFn_1484_, v_x_1485_);
lean_dec(v_x_1485_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__7(lean_object* v_registerFn_1488_, lean_object* v_unregisterFn_1489_, lean_object* v___f_1490_, lean_object* v_x_1491_){
_start:
{
if (lean_obj_tag(v_x_1491_) == 0)
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1501_; 
lean_dec_ref(v___f_1490_);
lean_dec_ref(v_unregisterFn_1489_);
lean_dec_ref(v_registerFn_1488_);
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
lean_object* v_a_1502_; lean_object* v___f_1503_; uint8_t v___x_1504_; lean_object* v___x_1505_; lean_object* v___f_1506_; lean_object* v___x_1507_; lean_object* v___f_1508_; lean_object* v___f_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___y_1513_; 
v_a_1502_ = lean_ctor_get(v_x_1491_, 0);
lean_inc(v_a_1502_);
v___f_1503_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1503_, 0, v_x_1491_);
v___x_1504_ = 0;
v___x_1505_ = lean_box(v___x_1504_);
v___f_1506_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_1506_, 0, v_a_1502_);
lean_closure_set(v___f_1506_, 1, v_registerFn_1488_);
lean_closure_set(v___f_1506_, 2, v___x_1505_);
lean_closure_set(v___f_1506_, 3, v___f_1503_);
v___x_1507_ = lean_box(v___x_1504_);
v___f_1508_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__5___boxed), 3, 2);
lean_closure_set(v___f_1508_, 0, v___x_1507_);
lean_closure_set(v___f_1508_, 1, v___f_1506_);
v___f_1509_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__6___boxed), 3, 1);
lean_closure_set(v___f_1509_, 0, v_unregisterFn_1489_);
v___x_1510_ = lean_unsigned_to_nat(0u);
v___x_1511_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_1508_, v___f_1509_, v___x_1510_, v___x_1504_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1515_; 
lean_dec_ref(v___f_1490_);
v_a_1515_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1515_);
lean_dec_ref_known(v___x_1511_, 1);
if (lean_obj_tag(v_a_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
v_a_1516_ = lean_ctor_get(v_a_1515_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v_a_1515_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v_a_1515_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v_a_1515_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1516_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
v___y_1513_ = v___x_1521_;
goto v___jp_1512_;
}
}
}
else
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1532_; 
v_a_1524_ = lean_ctor_get(v_a_1515_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v_a_1515_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1526_ = v_a_1515_;
v_isShared_1527_ = v_isSharedCheck_1532_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v_a_1515_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1532_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v_fst_1528_; lean_object* v___x_1530_; 
v_fst_1528_ = lean_ctor_get(v_a_1524_, 0);
lean_inc(v_fst_1528_);
lean_dec(v_a_1524_);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v_fst_1528_);
v___x_1530_ = v___x_1526_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_fst_1528_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
v___y_1513_ = v___x_1530_;
goto v___jp_1512_;
}
}
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1541_; 
v_a_1533_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1535_ = v___x_1511_;
v_isShared_1536_ = v_isSharedCheck_1541_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1511_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1541_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1537_; lean_object* v___x_1539_; 
v___x_1537_ = lean_task_map(v___f_1490_, v_a_1533_, v___x_1510_, v___x_1504_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 0, v___x_1537_);
v___x_1539_ = v___x_1535_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1537_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
v___jp_1512_:
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1514_, 0, v___y_1513_);
return v___x_1514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__7___boxed(lean_object* v_registerFn_1542_, lean_object* v_unregisterFn_1543_, lean_object* v___f_1544_, lean_object* v_x_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Std_Async_Selectable_one___redArg___lam__7(v_registerFn_1542_, v_unregisterFn_1543_, v___f_1544_, v_x_1545_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__8(lean_object* v___f_1548_, lean_object* v_x_1549_){
_start:
{
if (lean_obj_tag(v_x_1549_) == 0)
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1559_; 
lean_dec_ref(v___f_1548_);
v_a_1551_ = lean_ctor_get(v_x_1549_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v_x_1549_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1553_ = v_x_1549_;
v_isShared_1554_ = v_isSharedCheck_1559_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v_x_1549_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1559_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1551_);
v___x_1556_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
lean_object* v___x_1557_; 
v___x_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
return v___x_1557_;
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1583_; 
v_a_1560_ = lean_ctor_get(v_x_1549_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v_x_1549_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1562_ = v_x_1549_;
v_isShared_1563_ = v_isSharedCheck_1583_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v_x_1549_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1583_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
if (lean_obj_tag(v_a_1560_) == 1)
{
lean_object* v_val_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1574_; 
lean_dec_ref(v___f_1548_);
v_val_1564_ = lean_ctor_get(v_a_1560_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v_a_1560_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1566_ = v_a_1560_;
v_isShared_1567_ = v_isSharedCheck_1574_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_val_1564_);
lean_dec(v_a_1560_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1574_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v_val_1564_);
v___x_1569_ = v___x_1562_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_val_1564_);
v___x_1569_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
lean_object* v___x_1571_; 
if (v_isShared_1567_ == 0)
{
lean_ctor_set_tag(v___x_1566_, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1569_);
v___x_1571_ = v___x_1566_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1569_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
else
{
lean_object* v___x_1575_; uint8_t v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1579_; 
lean_dec(v_a_1560_);
v___x_1575_ = lean_unsigned_to_nat(0u);
v___x_1576_ = 0;
v___x_1577_ = lean_io_promise_new();
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1577_);
v___x_1579_ = v___x_1562_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1577_);
v___x_1579_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
v___x_1581_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1575_, v___x_1576_, v___x_1580_, v___f_1548_);
return v___x_1581_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__8___boxed(lean_object* v___f_1584_, lean_object* v_x_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Std_Async_Selectable_one___redArg___lam__8(v___f_1584_, v_x_1585_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__9(lean_object* v___f_1588_, lean_object* v_x_1589_){
_start:
{
if (lean_obj_tag(v_x_1589_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1599_; 
lean_dec_ref(v___f_1588_);
v_a_1591_ = lean_ctor_get(v_x_1589_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v_x_1589_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1593_ = v_x_1589_;
v_isShared_1594_ = v_isSharedCheck_1599_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v_x_1589_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1599_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1597_; 
v___x_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1596_);
return v___x_1597_;
}
}
}
else
{
lean_object* v_a_1600_; lean_object* v_tryFn_1601_; lean_object* v_registerFn_1602_; lean_object* v_unregisterFn_1603_; lean_object* v___f_1604_; lean_object* v___f_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v_a_1600_ = lean_ctor_get(v_x_1589_, 0);
lean_inc(v_a_1600_);
lean_dec_ref_known(v_x_1589_, 1);
v_tryFn_1601_ = lean_ctor_get(v_a_1600_, 0);
lean_inc_ref(v_tryFn_1601_);
v_registerFn_1602_ = lean_ctor_get(v_a_1600_, 1);
lean_inc_ref(v_registerFn_1602_);
v_unregisterFn_1603_ = lean_ctor_get(v_a_1600_, 2);
lean_inc_ref(v_unregisterFn_1603_);
lean_dec(v_a_1600_);
v___f_1604_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__7___boxed), 5, 3);
lean_closure_set(v___f_1604_, 0, v_registerFn_1602_);
lean_closure_set(v___f_1604_, 1, v_unregisterFn_1603_);
lean_closure_set(v___f_1604_, 2, v___f_1588_);
v___f_1605_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__8___boxed), 3, 1);
lean_closure_set(v___f_1605_, 0, v___f_1604_);
v___x_1606_ = lean_unsigned_to_nat(0u);
v___x_1607_ = 0;
v___x_1608_ = lean_apply_1(v_tryFn_1601_, lean_box(0));
v___x_1609_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1606_, v___x_1607_, v___x_1608_, v___f_1605_);
return v___x_1609_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__9___boxed(lean_object* v___f_1610_, lean_object* v_x_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Std_Async_Selectable_one___redArg___lam__9(v___f_1610_, v_x_1611_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__10(lean_object* v___f_1614_, lean_object* v_selectables_1615_, lean_object* v_____r_1616_){
_start:
{
lean_object* v___x_1618_; uint8_t v___x_1619_; lean_object* v_val_1621_; lean_object* v___x_1624_; lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
v___x_1618_ = lean_unsigned_to_nat(0u);
v___x_1619_ = 0;
v___x_1624_ = l_Std_Async_Selectable_combine___redArg(v_selectables_1615_);
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1624_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1624_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v___jp_1620_:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1622_, 0, v_val_1621_);
v___x_1623_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1618_, v___x_1619_, v___x_1622_, v___f_1614_);
return v___x_1623_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
lean_ctor_set_tag(v___x_1627_, 1);
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
v_val_1621_ = v___x_1630_;
goto v___jp_1620_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__10___boxed(lean_object* v___f_1633_, lean_object* v_selectables_1634_, lean_object* v_____r_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Std_Async_Selectable_one___redArg___lam__10(v___f_1633_, v_selectables_1634_, v_____r_1635_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__11(lean_object* v___f_1638_, lean_object* v_x_1639_){
_start:
{
if (lean_obj_tag(v_x_1639_) == 0)
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1649_; 
lean_dec_ref(v___f_1638_);
v_a_1641_ = lean_ctor_get(v_x_1639_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v_x_1639_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1643_ = v_x_1639_;
v_isShared_1644_ = v_isSharedCheck_1649_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v_x_1639_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1649_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
lean_object* v___x_1647_; 
v___x_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
return v___x_1647_;
}
}
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1651_; 
v_a_1650_ = lean_ctor_get(v_x_1639_, 0);
lean_inc(v_a_1650_);
lean_dec_ref_known(v_x_1639_, 1);
v___x_1651_ = lean_apply_2(v___f_1638_, v_a_1650_, lean_box(0));
return v___x_1651_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___lam__11___boxed(lean_object* v___f_1652_, lean_object* v_x_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Std_Async_Selectable_one___redArg___lam__11(v___f_1652_, v_x_1653_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg(lean_object* v_selectables_1666_){
_start:
{
lean_object* v___f_1668_; lean_object* v___f_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; uint8_t v___x_1672_; 
v___f_1668_ = ((lean_object*)(l_Std_Async_Selectable_one___redArg___closed__1));
lean_inc_ref(v_selectables_1666_);
v___f_1669_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__10___boxed), 4, 2);
lean_closure_set(v___f_1669_, 0, v___f_1668_);
lean_closure_set(v___f_1669_, 1, v_selectables_1666_);
v___x_1670_ = lean_array_get_size(v_selectables_1666_);
v___x_1671_ = lean_unsigned_to_nat(0u);
v___x_1672_ = lean_nat_dec_eq(v___x_1670_, v___x_1671_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
lean_dec_ref(v___f_1669_);
v___x_1673_ = lean_box(0);
v___x_1674_ = l_Std_Async_Selectable_one___redArg___lam__10(v___f_1668_, v_selectables_1666_, v___x_1673_);
return v___x_1674_;
}
else
{
lean_object* v___f_1675_; uint8_t v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec_ref(v_selectables_1666_);
v___f_1675_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_one___redArg___lam__11___boxed), 3, 1);
lean_closure_set(v___f_1675_, 0, v___f_1669_);
v___x_1676_ = 0;
v___x_1677_ = ((lean_object*)(l_Std_Async_Selectable_one___redArg___closed__5));
v___x_1678_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1671_, v___x_1676_, v___x_1677_, v___f_1675_);
return v___x_1678_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___redArg___boxed(lean_object* v_selectables_1679_, lean_object* v_a_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Std_Async_Selectable_one___redArg(v_selectables_1679_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one(lean_object* v_00_u03b1_1682_, lean_object* v_selectables_1683_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Std_Async_Selectable_one___redArg(v_selectables_1683_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_one___boxed(lean_object* v_00_u03b1_1686_, lean_object* v_selectables_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Std_Async_Selectable_one(v_00_u03b1_1686_, v_selectables_1687_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__3(lean_object* v_selectables_1690_, lean_object* v___f_1691_, lean_object* v_____r_1692_){
_start:
{
lean_object* v___x_1694_; lean_object* v___f_1695_; lean_object* v___x_1696_; uint8_t v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1694_ = l_IO_stdGenRef;
v___f_1695_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_combine___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_1695_, 0, v_selectables_1690_);
lean_closure_set(v___f_1695_, 1, v___f_1691_);
lean_closure_set(v___f_1695_, 2, v___x_1694_);
v___x_1696_ = lean_unsigned_to_nat(0u);
v___x_1697_ = 0;
v___x_1698_ = lean_st_ref_get(v___x_1694_);
v___x_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
v___x_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1699_);
v___x_1701_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1696_, v___x_1697_, v___x_1700_, v___f_1695_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__3___boxed(lean_object* v_selectables_1702_, lean_object* v___f_1703_, lean_object* v_____r_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Std_Async_Selectable_tryOne___redArg___lam__3(v_selectables_1702_, v___f_1703_, v_____r_1704_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__0(lean_object* v___f_1707_, lean_object* v_x_1708_){
_start:
{
if (lean_obj_tag(v_x_1708_) == 0)
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1718_; 
lean_dec_ref(v___f_1707_);
v_a_1710_ = lean_ctor_get(v_x_1708_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v_x_1708_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1712_ = v_x_1708_;
v_isShared_1713_ = v_isSharedCheck_1718_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v_x_1708_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1718_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
lean_object* v___x_1716_; 
v___x_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
return v___x_1716_;
}
}
}
else
{
lean_object* v_a_1719_; lean_object* v___x_1720_; 
v_a_1719_ = lean_ctor_get(v_x_1708_, 0);
lean_inc(v_a_1719_);
lean_dec_ref_known(v_x_1708_, 1);
v___x_1720_ = lean_apply_2(v___f_1707_, v_a_1719_, lean_box(0));
return v___x_1720_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___lam__0___boxed(lean_object* v___f_1721_, lean_object* v_x_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Std_Async_Selectable_tryOne___redArg___lam__0(v___f_1721_, v_x_1722_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg(lean_object* v_selectables_1732_){
_start:
{
lean_object* v___f_1734_; lean_object* v___f_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___f_1734_ = ((lean_object*)(l_Std_Async_Selectable_combine___redArg___closed__0));
lean_inc_ref(v_selectables_1732_);
v___f_1735_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_tryOne___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1735_, 0, v_selectables_1732_);
lean_closure_set(v___f_1735_, 1, v___f_1734_);
v___x_1736_ = lean_array_get_size(v_selectables_1732_);
v___x_1737_ = lean_unsigned_to_nat(0u);
v___x_1738_ = lean_nat_dec_eq(v___x_1736_, v___x_1737_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
lean_dec_ref(v___f_1735_);
v___x_1739_ = lean_box(0);
v___x_1740_ = l_Std_Async_Selectable_tryOne___redArg___lam__3(v_selectables_1732_, v___f_1734_, v___x_1739_);
return v___x_1740_;
}
else
{
lean_object* v___f_1741_; uint8_t v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
lean_dec_ref(v_selectables_1732_);
v___f_1741_ = lean_alloc_closure((void*)(l_Std_Async_Selectable_tryOne___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1741_, 0, v___f_1735_);
v___x_1742_ = 0;
v___x_1743_ = ((lean_object*)(l_Std_Async_Selectable_tryOne___redArg___closed__3));
v___x_1744_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1737_, v___x_1742_, v___x_1743_, v___f_1741_);
return v___x_1744_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___redArg___boxed(lean_object* v_selectables_1745_, lean_object* v_a_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Std_Async_Selectable_tryOne___redArg(v_selectables_1745_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne(lean_object* v_00_u03b1_1748_, lean_object* v_selectables_1749_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Std_Async_Selectable_tryOne___redArg(v_selectables_1749_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selectable_tryOne___boxed(lean_object* v_00_u03b1_1752_, lean_object* v_selectables_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Std_Async_Selectable_tryOne(v_00_u03b1_1752_, v_selectables_1753_);
return v_res_1755_;
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
