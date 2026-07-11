// Lean compiler output
// Module: Std.Sync.StreamMap
// Imports: public import Std.Data public import Init.Data.Queue public import Std.Async.IO
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Std_Async_Selectable_combine___redArg(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_Async_Selectable_tryOne___redArg(lean_object*);
lean_object* l_Std_Async_Selectable_one___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_AnyAsyncStream_getSelector___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_AnyAsyncStream_getSelector(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instCoeDepAnyAsyncStreamOfAsyncStream___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instCoeDepAnyAsyncStreamOfAsyncStream(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_StreamMap_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_StreamMap_empty___closed__0 = (const lean_object*)&l_Std_StreamMap_empty___closed__0_value;
LEAN_EXPORT lean_object* l_Std_StreamMap_empty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_register___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_StreamMap_register___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_StreamMap_register___redArg___closed__0 = (const lean_object*)&l_Std_StreamMap_register___redArg___closed__0_value;
static const lean_closure_object l_Std_StreamMap_register___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_StreamMap_register___redArg___closed__1 = (const lean_object*)&l_Std_StreamMap_register___redArg___closed__1_value;
static const lean_closure_object l_Std_StreamMap_register___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_StreamMap_register___redArg___closed__2 = (const lean_object*)&l_Std_StreamMap_register___redArg___closed__2_value;
static const lean_closure_object l_Std_StreamMap_register___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_StreamMap_register___redArg___closed__3 = (const lean_object*)&l_Std_StreamMap_register___redArg___closed__3_value;
static const lean_closure_object l_Std_StreamMap_register___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_StreamMap_register___redArg___closed__4 = (const lean_object*)&l_Std_StreamMap_register___redArg___closed__4_value;
static const lean_closure_object l_Std_StreamMap_register___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_StreamMap_register___redArg___closed__5 = (const lean_object*)&l_Std_StreamMap_register___redArg___closed__5_value;
static const lean_closure_object l_Std_StreamMap_register___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_StreamMap_register___redArg___closed__6 = (const lean_object*)&l_Std_StreamMap_register___redArg___closed__6_value;
static const lean_ctor_object l_Std_StreamMap_register___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_StreamMap_register___redArg___closed__0_value),((lean_object*)&l_Std_StreamMap_register___redArg___closed__1_value)}};
static const lean_object* l_Std_StreamMap_register___redArg___closed__7 = (const lean_object*)&l_Std_StreamMap_register___redArg___closed__7_value;
static const lean_ctor_object l_Std_StreamMap_register___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_StreamMap_register___redArg___closed__7_value),((lean_object*)&l_Std_StreamMap_register___redArg___closed__2_value),((lean_object*)&l_Std_StreamMap_register___redArg___closed__3_value),((lean_object*)&l_Std_StreamMap_register___redArg___closed__4_value),((lean_object*)&l_Std_StreamMap_register___redArg___closed__5_value)}};
static const lean_object* l_Std_StreamMap_register___redArg___closed__8 = (const lean_object*)&l_Std_StreamMap_register___redArg___closed__8_value;
static const lean_ctor_object l_Std_StreamMap_register___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_StreamMap_register___redArg___closed__8_value),((lean_object*)&l_Std_StreamMap_register___redArg___closed__6_value)}};
static const lean_object* l_Std_StreamMap_register___redArg___closed__9 = (const lean_object*)&l_Std_StreamMap_register___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Std_StreamMap_register___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_register(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_ofArray___redArg___lam__0(lean_object*);
static const lean_closure_object l_Std_StreamMap_ofArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_StreamMap_ofArray___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_StreamMap_ofArray___redArg___closed__0 = (const lean_object*)&l_Std_StreamMap_ofArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_StreamMap_ofArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_ofArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_ofArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_selector___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_selector___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_selector(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_selector___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_recv___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_recv___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_recv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_recv___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_tryRecv___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_tryRecv___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_tryRecv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_tryRecv___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_unregister___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_unregister(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_StreamMap_contains___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_contains___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_StreamMap_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_StreamMap_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_size(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_size___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_StreamMap_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_StreamMap_isEmpty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_isEmpty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_keys___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_keys(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_get_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_get_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_StreamMap_get_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_StreamMap_get_x3f___redArg___closed__0 = (const lean_object*)&l_Std_StreamMap_get_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_StreamMap_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_filterByName___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_filterByName___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_filterByName(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_filterByName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_toArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_close___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_close___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_close(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_StreamMap_close___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AnyAsyncStream_getSelector___redArg(lean_object* v_x_1_){
_start:
{
lean_object* v_inst_2_; lean_object* v_a_3_; lean_object* v_next_4_; lean_object* v_stop_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_14_; 
v_inst_2_ = lean_ctor_get(v_x_1_, 0);
lean_inc_ref(v_inst_2_);
v_a_3_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_a_3_);
lean_dec_ref(v_x_1_);
v_next_4_ = lean_ctor_get(v_inst_2_, 0);
v_stop_5_ = lean_ctor_get(v_inst_2_, 1);
v_isSharedCheck_14_ = !lean_is_exclusive(v_inst_2_);
if (v_isSharedCheck_14_ == 0)
{
v___x_7_ = v_inst_2_;
v_isShared_8_ = v_isSharedCheck_14_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_stop_5_);
lean_inc(v_next_4_);
lean_dec(v_inst_2_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_14_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_12_; 
lean_inc(v_a_3_);
v___x_9_ = lean_apply_1(v_next_4_, v_a_3_);
v___x_10_ = lean_apply_1(v_stop_5_, v_a_3_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v___x_10_);
lean_ctor_set(v___x_7_, 0, v___x_9_);
v___x_12_ = v___x_7_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v___x_9_);
lean_ctor_set(v_reuseFailAlloc_13_, 1, v___x_10_);
v___x_12_ = v_reuseFailAlloc_13_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
return v___x_12_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AnyAsyncStream_getSelector(lean_object* v_00_u03b1_15_, lean_object* v_x_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Std_AnyAsyncStream_getSelector___redArg(v_x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeDepAnyAsyncStreamOfAsyncStream___redArg(lean_object* v_x_18_, lean_object* v_inst_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_20_, 0, v_inst_19_);
lean_ctor_set(v___x_20_, 1, v_x_18_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeDepAnyAsyncStreamOfAsyncStream(lean_object* v_t_21_, lean_object* v_00_u03b1_22_, lean_object* v_x_23_, lean_object* v_inst_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_25_, 0, v_inst_24_);
lean_ctor_set(v___x_25_, 1, v_x_23_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_empty(lean_object* v_00_u03b2_28_, lean_object* v_00_u03b1_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = ((lean_object*)(l_Std_StreamMap_empty___closed__0));
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_register___redArg___lam__0(lean_object* v_inst_31_, lean_object* v_name_32_, lean_object* v_x1_33_, lean_object* v_x2_34_){
_start:
{
lean_object* v_fst_35_; lean_object* v___x_36_; uint8_t v___x_37_; uint8_t v___x_38_; 
v_fst_35_ = lean_ctor_get(v_x2_34_, 0);
lean_inc(v_fst_35_);
v___x_36_ = lean_apply_2(v_inst_31_, v_fst_35_, v_name_32_);
v___x_37_ = lean_unbox(v___x_36_);
v___x_38_ = lean_bool_not(v___x_37_);
if (v___x_38_ == 0)
{
lean_dec_ref(v_x2_34_);
return v_x1_33_;
}
else
{
lean_object* v___x_39_; 
v___x_39_ = lean_array_push(v_x1_33_, v_x2_34_);
return v___x_39_;
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_register___redArg(lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_sm_61_, lean_object* v_name_62_, lean_object* v_reader_63_){
_start:
{
lean_object* v_next_64_; lean_object* v_stop_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_91_; 
v_next_64_ = lean_ctor_get(v_inst_60_, 0);
v_stop_65_ = lean_ctor_get(v_inst_60_, 1);
v_isSharedCheck_91_ = !lean_is_exclusive(v_inst_60_);
if (v_isSharedCheck_91_ == 0)
{
v___x_67_ = v_inst_60_;
v_isShared_68_ = v_isSharedCheck_91_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_stop_65_);
lean_inc(v_next_64_);
lean_dec(v_inst_60_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_91_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v_newSelector_69_; lean_object* v___y_71_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
lean_inc(v_reader_63_);
v_newSelector_69_ = lean_apply_1(v_next_64_, v_reader_63_);
v___x_78_ = lean_unsigned_to_nat(0u);
v___x_79_ = lean_array_get_size(v_sm_61_);
v___x_80_ = ((lean_object*)(l_Std_StreamMap_empty___closed__0));
v___x_81_ = ((lean_object*)(l_Std_StreamMap_register___redArg___closed__9));
v___x_82_ = lean_nat_dec_lt(v___x_78_, v___x_79_);
if (v___x_82_ == 0)
{
lean_dec_ref(v_sm_61_);
lean_dec_ref(v_inst_59_);
v___y_71_ = v___x_80_;
goto v___jp_70_;
}
else
{
lean_object* v___f_83_; uint8_t v___x_84_; 
lean_inc(v_name_62_);
v___f_83_ = lean_alloc_closure((void*)(l_Std_StreamMap_register___redArg___lam__0), 4, 2);
lean_closure_set(v___f_83_, 0, v_inst_59_);
lean_closure_set(v___f_83_, 1, v_name_62_);
v___x_84_ = lean_nat_dec_le(v___x_79_, v___x_79_);
if (v___x_84_ == 0)
{
if (v___x_82_ == 0)
{
lean_dec_ref(v___f_83_);
lean_dec_ref(v_sm_61_);
v___y_71_ = v___x_80_;
goto v___jp_70_;
}
else
{
size_t v___x_85_; size_t v___x_86_; lean_object* v___x_87_; 
v___x_85_ = ((size_t)0ULL);
v___x_86_ = lean_usize_of_nat(v___x_79_);
v___x_87_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_81_, v___f_83_, v_sm_61_, v___x_85_, v___x_86_, v___x_80_);
v___y_71_ = v___x_87_;
goto v___jp_70_;
}
}
else
{
size_t v___x_88_; size_t v___x_89_; lean_object* v___x_90_; 
v___x_88_ = ((size_t)0ULL);
v___x_89_ = lean_usize_of_nat(v___x_79_);
v___x_90_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_81_, v___f_83_, v_sm_61_, v___x_88_, v___x_89_, v___x_80_);
v___y_71_ = v___x_90_;
goto v___jp_70_;
}
}
v___jp_70_:
{
lean_object* v___x_72_; lean_object* v___x_74_; 
v___x_72_ = lean_apply_1(v_stop_65_, v_reader_63_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 1, v___x_72_);
lean_ctor_set(v___x_67_, 0, v_newSelector_69_);
v___x_74_ = v___x_67_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_newSelector_69_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v___x_72_);
v___x_74_ = v_reuseFailAlloc_77_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_75_, 0, v_name_62_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = lean_array_push(v___y_71_, v___x_75_);
return v___x_76_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_register(lean_object* v_00_u03b1_92_, lean_object* v_t_93_, lean_object* v_00_u03b2_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_sm_97_, lean_object* v_name_98_, lean_object* v_reader_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Std_StreamMap_register___redArg(v_inst_95_, v_inst_96_, v_sm_97_, v_name_98_, v_reader_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_ofArray___redArg___lam__0(lean_object* v_x_101_){
_start:
{
lean_object* v_fst_102_; lean_object* v_snd_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_111_; 
v_fst_102_ = lean_ctor_get(v_x_101_, 0);
v_snd_103_ = lean_ctor_get(v_x_101_, 1);
v_isSharedCheck_111_ = !lean_is_exclusive(v_x_101_);
if (v_isSharedCheck_111_ == 0)
{
v___x_105_ = v_x_101_;
v_isShared_106_ = v_isSharedCheck_111_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_snd_103_);
lean_inc(v_fst_102_);
lean_dec(v_x_101_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_111_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_107_ = l_Std_AnyAsyncStream_getSelector___redArg(v_snd_103_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 1, v___x_107_);
v___x_109_ = v___x_105_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_fst_102_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v___x_107_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_ofArray___redArg(lean_object* v_streams_113_){
_start:
{
lean_object* v___f_114_; lean_object* v___x_115_; size_t v_sz_116_; size_t v___x_117_; lean_object* v_arrayOfSelectors_118_; 
v___f_114_ = ((lean_object*)(l_Std_StreamMap_ofArray___redArg___closed__0));
v___x_115_ = ((lean_object*)(l_Std_StreamMap_register___redArg___closed__9));
v_sz_116_ = lean_array_size(v_streams_113_);
v___x_117_ = ((size_t)0ULL);
v_arrayOfSelectors_118_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_115_, v___f_114_, v_sz_116_, v___x_117_, v_streams_113_);
return v_arrayOfSelectors_118_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_ofArray(lean_object* v_00_u03b1_119_, lean_object* v_00_u03b2_120_, lean_object* v_inst_121_, lean_object* v_streams_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Std_StreamMap_ofArray___redArg(v_streams_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_ofArray___boxed(lean_object* v_00_u03b1_124_, lean_object* v_00_u03b2_125_, lean_object* v_inst_126_, lean_object* v_streams_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Std_StreamMap_ofArray(v_00_u03b1_124_, v_00_u03b2_125_, v_inst_126_, v_streams_127_);
lean_dec_ref(v_inst_126_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___lam__0(lean_object* v_fst_129_, lean_object* v_x_130_){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v_fst_129_);
lean_ctor_set(v___x_132_, 1, v_x_130_);
v___x_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
v___x_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___lam__0___boxed(lean_object* v_fst_135_, lean_object* v_x_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___lam__0(v_fst_135_, v_x_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(size_t v_sz_139_, size_t v_i_140_, lean_object* v_bs_141_){
_start:
{
uint8_t v___x_142_; 
v___x_142_ = lean_usize_dec_lt(v_i_140_, v_sz_139_);
if (v___x_142_ == 0)
{
return v_bs_141_;
}
else
{
lean_object* v_v_143_; lean_object* v_snd_144_; lean_object* v_fst_145_; lean_object* v_fst_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_160_; 
v_v_143_ = lean_array_uget_borrowed(v_bs_141_, v_i_140_);
v_snd_144_ = lean_ctor_get(v_v_143_, 1);
lean_inc(v_snd_144_);
v_fst_145_ = lean_ctor_get(v_v_143_, 0);
lean_inc(v_fst_145_);
v_fst_146_ = lean_ctor_get(v_snd_144_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v_snd_144_);
if (v_isSharedCheck_160_ == 0)
{
lean_object* v_unused_161_; 
v_unused_161_ = lean_ctor_get(v_snd_144_, 1);
lean_dec(v_unused_161_);
v___x_148_ = v_snd_144_;
v_isShared_149_ = v_isSharedCheck_160_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_fst_146_);
lean_dec(v_snd_144_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_160_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_150_; lean_object* v_bs_x27_151_; lean_object* v___f_152_; lean_object* v___x_154_; 
v___x_150_ = lean_unsigned_to_nat(0u);
v_bs_x27_151_ = lean_array_uset(v_bs_141_, v_i_140_, v___x_150_);
v___f_152_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_152_, 0, v_fst_145_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 1, v___f_152_);
v___x_154_ = v___x_148_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_fst_146_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v___f_152_);
v___x_154_ = v_reuseFailAlloc_159_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
size_t v___x_155_; size_t v___x_156_; lean_object* v___x_157_; 
v___x_155_ = ((size_t)1ULL);
v___x_156_ = lean_usize_add(v_i_140_, v___x_155_);
v___x_157_ = lean_array_uset(v_bs_x27_151_, v_i_140_, v___x_154_);
v_i_140_ = v___x_156_;
v_bs_141_ = v___x_157_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___boxed(lean_object* v_sz_162_, lean_object* v_i_163_, lean_object* v_bs_164_){
_start:
{
size_t v_sz_boxed_165_; size_t v_i_boxed_166_; lean_object* v_res_167_; 
v_sz_boxed_165_ = lean_unbox_usize(v_sz_162_);
lean_dec(v_sz_162_);
v_i_boxed_166_ = lean_unbox_usize(v_i_163_);
lean_dec(v_i_163_);
v_res_167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(v_sz_boxed_165_, v_i_boxed_166_, v_bs_164_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_selector___redArg(lean_object* v_stream_168_){
_start:
{
lean_object* v_val_171_; size_t v_sz_173_; size_t v___x_174_; lean_object* v_selectables_175_; lean_object* v___x_176_; 
v_sz_173_ = lean_array_size(v_stream_168_);
v___x_174_ = ((size_t)0ULL);
v_selectables_175_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(v_sz_173_, v___x_174_, v_stream_168_);
v___x_176_ = l_Std_Async_Selectable_combine___redArg(v_selectables_175_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_184_ == 0)
{
v___x_179_ = v___x_176_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_176_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
lean_ctor_set_tag(v___x_179_, 1);
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_a_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
v_val_171_ = v___x_182_;
goto v___jp_170_;
}
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
v_a_185_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_176_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_176_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
lean_ctor_set_tag(v___x_187_, 0);
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
v_val_171_ = v___x_190_;
goto v___jp_170_;
}
}
}
v___jp_170_:
{
lean_object* v___x_172_; 
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v_val_171_);
return v___x_172_;
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_selector___redArg___boxed(lean_object* v_stream_193_, lean_object* v_a_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Std_StreamMap_selector___redArg(v_stream_193_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_selector(lean_object* v_00_u03b1_196_, lean_object* v_00_u03b2_197_, lean_object* v_stream_198_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Std_StreamMap_selector___redArg(v_stream_198_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_selector___boxed(lean_object* v_00_u03b1_201_, lean_object* v_00_u03b2_202_, lean_object* v_stream_203_, lean_object* v_a_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Std_StreamMap_selector(v_00_u03b1_201_, v_00_u03b2_202_, v_stream_203_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0(lean_object* v_00_u03b1_206_, lean_object* v_00_u03b2_207_, size_t v_sz_208_, size_t v_i_209_, lean_object* v_bs_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(v_sz_208_, v_i_209_, v_bs_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___boxed(lean_object* v_00_u03b1_212_, lean_object* v_00_u03b2_213_, lean_object* v_sz_214_, lean_object* v_i_215_, lean_object* v_bs_216_){
_start:
{
size_t v_sz_boxed_217_; size_t v_i_boxed_218_; lean_object* v_res_219_; 
v_sz_boxed_217_ = lean_unbox_usize(v_sz_214_);
lean_dec(v_sz_214_);
v_i_boxed_218_ = lean_unbox_usize(v_i_215_);
lean_dec(v_i_215_);
v_res_219_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0(v_00_u03b1_212_, v_00_u03b2_213_, v_sz_boxed_217_, v_i_boxed_218_, v_bs_216_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_recv___redArg(lean_object* v_stream_220_){
_start:
{
size_t v_sz_222_; size_t v___x_223_; lean_object* v_selectables_224_; lean_object* v___x_225_; 
v_sz_222_ = lean_array_size(v_stream_220_);
v___x_223_ = ((size_t)0ULL);
v_selectables_224_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(v_sz_222_, v___x_223_, v_stream_220_);
v___x_225_ = l_Std_Async_Selectable_one___redArg(v_selectables_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_recv___redArg___boxed(lean_object* v_stream_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Std_StreamMap_recv___redArg(v_stream_226_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_recv(lean_object* v_00_u03b1_229_, lean_object* v_00_u03b2_230_, lean_object* v_stream_231_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Std_StreamMap_recv___redArg(v_stream_231_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_recv___boxed(lean_object* v_00_u03b1_234_, lean_object* v_00_u03b2_235_, lean_object* v_stream_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Std_StreamMap_recv(v_00_u03b1_234_, v_00_u03b2_235_, v_stream_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_tryRecv___redArg(lean_object* v_stream_239_){
_start:
{
size_t v_sz_241_; size_t v___x_242_; lean_object* v_selectables_243_; lean_object* v___x_244_; 
v_sz_241_ = lean_array_size(v_stream_239_);
v___x_242_ = ((size_t)0ULL);
v_selectables_243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(v_sz_241_, v___x_242_, v_stream_239_);
v___x_244_ = l_Std_Async_Selectable_tryOne___redArg(v_selectables_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_tryRecv___redArg___boxed(lean_object* v_stream_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Std_StreamMap_tryRecv___redArg(v_stream_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_tryRecv(lean_object* v_00_u03b1_248_, lean_object* v_00_u03b2_249_, lean_object* v_stream_250_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Std_StreamMap_tryRecv___redArg(v_stream_250_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_tryRecv___boxed(lean_object* v_00_u03b1_253_, lean_object* v_00_u03b2_254_, lean_object* v_stream_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Std_StreamMap_tryRecv(v_00_u03b1_253_, v_00_u03b2_254_, v_stream_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_unregister___redArg(lean_object* v_inst_258_, lean_object* v_sm_259_, lean_object* v_name_260_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_261_ = lean_unsigned_to_nat(0u);
v___x_262_ = lean_array_get_size(v_sm_259_);
v___x_263_ = ((lean_object*)(l_Std_StreamMap_empty___closed__0));
v___x_264_ = ((lean_object*)(l_Std_StreamMap_register___redArg___closed__9));
v___x_265_ = lean_nat_dec_lt(v___x_261_, v___x_262_);
if (v___x_265_ == 0)
{
lean_dec(v_name_260_);
lean_dec_ref(v_sm_259_);
lean_dec_ref(v_inst_258_);
return v___x_263_;
}
else
{
lean_object* v___f_266_; uint8_t v___x_267_; 
v___f_266_ = lean_alloc_closure((void*)(l_Std_StreamMap_register___redArg___lam__0), 4, 2);
lean_closure_set(v___f_266_, 0, v_inst_258_);
lean_closure_set(v___f_266_, 1, v_name_260_);
v___x_267_ = lean_nat_dec_le(v___x_262_, v___x_262_);
if (v___x_267_ == 0)
{
if (v___x_265_ == 0)
{
lean_dec_ref(v___f_266_);
lean_dec_ref(v_sm_259_);
return v___x_263_;
}
else
{
size_t v___x_268_; size_t v___x_269_; lean_object* v___x_270_; 
v___x_268_ = ((size_t)0ULL);
v___x_269_ = lean_usize_of_nat(v___x_262_);
v___x_270_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_264_, v___f_266_, v_sm_259_, v___x_268_, v___x_269_, v___x_263_);
return v___x_270_;
}
}
else
{
size_t v___x_271_; size_t v___x_272_; lean_object* v___x_273_; 
v___x_271_ = ((size_t)0ULL);
v___x_272_ = lean_usize_of_nat(v___x_262_);
v___x_273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_264_, v___f_266_, v_sm_259_, v___x_271_, v___x_272_, v___x_263_);
return v___x_273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_unregister(lean_object* v_00_u03b1_274_, lean_object* v_00_u03b2_275_, lean_object* v_inst_276_, lean_object* v_sm_277_, lean_object* v_name_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Std_StreamMap_unregister___redArg(v_inst_276_, v_sm_277_, v_name_278_);
return v___x_279_;
}
}
LEAN_EXPORT uint8_t l_Std_StreamMap_contains___redArg___lam__0(lean_object* v_inst_280_, lean_object* v_name_281_, lean_object* v_x_282_){
_start:
{
lean_object* v_fst_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v_fst_283_ = lean_ctor_get(v_x_282_, 0);
lean_inc(v_fst_283_);
lean_dec_ref(v_x_282_);
v___x_284_ = lean_apply_2(v_inst_280_, v_fst_283_, v_name_281_);
v___x_285_ = lean_unbox(v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_contains___redArg___lam__0___boxed(lean_object* v_inst_286_, lean_object* v_name_287_, lean_object* v_x_288_){
_start:
{
uint8_t v_res_289_; lean_object* v_r_290_; 
v_res_289_ = l_Std_StreamMap_contains___redArg___lam__0(v_inst_286_, v_name_287_, v_x_288_);
v_r_290_ = lean_box(v_res_289_);
return v_r_290_;
}
}
LEAN_EXPORT uint8_t l_Std_StreamMap_contains___redArg(lean_object* v_inst_291_, lean_object* v_sm_292_, lean_object* v_name_293_){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = lean_array_get_size(v_sm_292_);
v___x_296_ = ((lean_object*)(l_Std_StreamMap_register___redArg___closed__9));
v___x_297_ = lean_nat_dec_lt(v___x_294_, v___x_295_);
if (v___x_297_ == 0)
{
lean_dec(v_name_293_);
lean_dec_ref(v_sm_292_);
lean_dec_ref(v_inst_291_);
return v___x_297_;
}
else
{
if (v___x_297_ == 0)
{
lean_dec(v_name_293_);
lean_dec_ref(v_sm_292_);
lean_dec_ref(v_inst_291_);
return v___x_297_;
}
else
{
lean_object* v___f_298_; size_t v___x_299_; size_t v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v___f_298_ = lean_alloc_closure((void*)(l_Std_StreamMap_contains___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_298_, 0, v_inst_291_);
lean_closure_set(v___f_298_, 1, v_name_293_);
v___x_299_ = ((size_t)0ULL);
v___x_300_ = lean_usize_of_nat(v___x_295_);
v___x_301_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_296_, v___f_298_, v_sm_292_, v___x_299_, v___x_300_);
v___x_302_ = lean_unbox(v___x_301_);
lean_dec(v___x_301_);
return v___x_302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_contains___redArg___boxed(lean_object* v_inst_303_, lean_object* v_sm_304_, lean_object* v_name_305_){
_start:
{
uint8_t v_res_306_; lean_object* v_r_307_; 
v_res_306_ = l_Std_StreamMap_contains___redArg(v_inst_303_, v_sm_304_, v_name_305_);
v_r_307_ = lean_box(v_res_306_);
return v_r_307_;
}
}
LEAN_EXPORT uint8_t l_Std_StreamMap_contains(lean_object* v_00_u03b1_308_, lean_object* v_00_u03b2_309_, lean_object* v_inst_310_, lean_object* v_sm_311_, lean_object* v_name_312_){
_start:
{
uint8_t v___x_313_; 
v___x_313_ = l_Std_StreamMap_contains___redArg(v_inst_310_, v_sm_311_, v_name_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_contains___boxed(lean_object* v_00_u03b1_314_, lean_object* v_00_u03b2_315_, lean_object* v_inst_316_, lean_object* v_sm_317_, lean_object* v_name_318_){
_start:
{
uint8_t v_res_319_; lean_object* v_r_320_; 
v_res_319_ = l_Std_StreamMap_contains(v_00_u03b1_314_, v_00_u03b2_315_, v_inst_316_, v_sm_317_, v_name_318_);
v_r_320_ = lean_box(v_res_319_);
return v_r_320_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_size___redArg(lean_object* v_sm_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = lean_array_get_size(v_sm_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_size___redArg___boxed(lean_object* v_sm_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Std_StreamMap_size___redArg(v_sm_323_);
lean_dec_ref(v_sm_323_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_size(lean_object* v_00_u03b1_325_, lean_object* v_00_u03b2_326_, lean_object* v_sm_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = lean_array_get_size(v_sm_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_size___boxed(lean_object* v_00_u03b1_329_, lean_object* v_00_u03b2_330_, lean_object* v_sm_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Std_StreamMap_size(v_00_u03b1_329_, v_00_u03b2_330_, v_sm_331_);
lean_dec_ref(v_sm_331_);
return v_res_332_;
}
}
LEAN_EXPORT uint8_t l_Std_StreamMap_isEmpty___redArg(lean_object* v_sm_333_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_334_ = lean_array_get_size(v_sm_333_);
v___x_335_ = lean_unsigned_to_nat(0u);
v___x_336_ = lean_nat_dec_eq(v___x_334_, v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_isEmpty___redArg___boxed(lean_object* v_sm_337_){
_start:
{
uint8_t v_res_338_; lean_object* v_r_339_; 
v_res_338_ = l_Std_StreamMap_isEmpty___redArg(v_sm_337_);
lean_dec_ref(v_sm_337_);
v_r_339_ = lean_box(v_res_338_);
return v_r_339_;
}
}
LEAN_EXPORT uint8_t l_Std_StreamMap_isEmpty(lean_object* v_00_u03b1_340_, lean_object* v_00_u03b2_341_, lean_object* v_sm_342_){
_start:
{
uint8_t v___x_343_; 
v___x_343_ = l_Std_StreamMap_isEmpty___redArg(v_sm_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_isEmpty___boxed(lean_object* v_00_u03b1_344_, lean_object* v_00_u03b2_345_, lean_object* v_sm_346_){
_start:
{
uint8_t v_res_347_; lean_object* v_r_348_; 
v_res_347_ = l_Std_StreamMap_isEmpty(v_00_u03b1_344_, v_00_u03b2_345_, v_sm_346_);
lean_dec_ref(v_sm_346_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg(size_t v_sz_349_, size_t v_i_350_, lean_object* v_bs_351_){
_start:
{
uint8_t v___x_352_; 
v___x_352_ = lean_usize_dec_lt(v_i_350_, v_sz_349_);
if (v___x_352_ == 0)
{
return v_bs_351_;
}
else
{
lean_object* v_v_353_; lean_object* v_fst_354_; lean_object* v___x_355_; lean_object* v_bs_x27_356_; size_t v___x_357_; size_t v___x_358_; lean_object* v___x_359_; 
v_v_353_ = lean_array_uget_borrowed(v_bs_351_, v_i_350_);
v_fst_354_ = lean_ctor_get(v_v_353_, 0);
lean_inc(v_fst_354_);
v___x_355_ = lean_unsigned_to_nat(0u);
v_bs_x27_356_ = lean_array_uset(v_bs_351_, v_i_350_, v___x_355_);
v___x_357_ = ((size_t)1ULL);
v___x_358_ = lean_usize_add(v_i_350_, v___x_357_);
v___x_359_ = lean_array_uset(v_bs_x27_356_, v_i_350_, v_fst_354_);
v_i_350_ = v___x_358_;
v_bs_351_ = v___x_359_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg___boxed(lean_object* v_sz_361_, lean_object* v_i_362_, lean_object* v_bs_363_){
_start:
{
size_t v_sz_boxed_364_; size_t v_i_boxed_365_; lean_object* v_res_366_; 
v_sz_boxed_364_ = lean_unbox_usize(v_sz_361_);
lean_dec(v_sz_361_);
v_i_boxed_365_ = lean_unbox_usize(v_i_362_);
lean_dec(v_i_362_);
v_res_366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg(v_sz_boxed_364_, v_i_boxed_365_, v_bs_363_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_keys___redArg(lean_object* v_sm_367_){
_start:
{
size_t v_sz_368_; size_t v___x_369_; lean_object* v___x_370_; 
v_sz_368_ = lean_array_size(v_sm_367_);
v___x_369_ = ((size_t)0ULL);
v___x_370_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg(v_sz_368_, v___x_369_, v_sm_367_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_keys(lean_object* v_00_u03b1_371_, lean_object* v_00_u03b2_372_, lean_object* v_sm_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Std_StreamMap_keys___redArg(v_sm_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0(lean_object* v_00_u03b1_375_, lean_object* v_00_u03b2_376_, size_t v_sz_377_, size_t v_i_378_, lean_object* v_bs_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg(v_sz_377_, v_i_378_, v_bs_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___boxed(lean_object* v_00_u03b1_381_, lean_object* v_00_u03b2_382_, lean_object* v_sz_383_, lean_object* v_i_384_, lean_object* v_bs_385_){
_start:
{
size_t v_sz_boxed_386_; size_t v_i_boxed_387_; lean_object* v_res_388_; 
v_sz_boxed_386_ = lean_unbox_usize(v_sz_383_);
lean_dec(v_sz_383_);
v_i_boxed_387_ = lean_unbox_usize(v_i_384_);
lean_dec(v_i_384_);
v_res_388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0(v_00_u03b1_381_, v_00_u03b2_382_, v_sz_boxed_386_, v_i_boxed_387_, v_bs_385_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_get_x3f___redArg___lam__0(lean_object* v_inst_389_, lean_object* v_name_390_, lean_object* v___x_391_, lean_object* v___x_392_, lean_object* v_a_393_, lean_object* v_x_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_fst_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v_fst_396_ = lean_ctor_get(v_a_393_, 0);
lean_inc(v_fst_396_);
v___x_397_ = lean_apply_2(v_inst_389_, v_fst_396_, v_name_390_);
v___x_398_ = lean_unbox(v___x_397_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; 
lean_dec_ref(v_a_393_);
v___x_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_391_);
return v___x_399_;
}
else
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
lean_dec_ref(v___x_391_);
v___x_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_400_, 0, v_a_393_);
v___x_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set(v___x_402_, 1, v___x_392_);
v___x_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
return v___x_403_;
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_get_x3f___redArg___lam__0___boxed(lean_object* v_inst_404_, lean_object* v_name_405_, lean_object* v___x_406_, lean_object* v___x_407_, lean_object* v_a_408_, lean_object* v_x_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Std_StreamMap_get_x3f___redArg___lam__0(v_inst_404_, v_name_405_, v___x_406_, v___x_407_, v_a_408_, v_x_409_, v___y_410_);
lean_dec_ref(v___y_410_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_get_x3f___redArg(lean_object* v_inst_415_, lean_object* v_sm_416_, lean_object* v_name_417_){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___f_422_; size_t v_sz_423_; size_t v___x_424_; lean_object* v___x_425_; lean_object* v_fst_426_; 
v___x_418_ = ((lean_object*)(l_Std_StreamMap_register___redArg___closed__9));
v___x_419_ = lean_box(0);
v___x_420_ = lean_box(0);
v___x_421_ = ((lean_object*)(l_Std_StreamMap_get_x3f___redArg___closed__0));
v___f_422_ = lean_alloc_closure((void*)(l_Std_StreamMap_get_x3f___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_422_, 0, v_inst_415_);
lean_closure_set(v___f_422_, 1, v_name_417_);
lean_closure_set(v___f_422_, 2, v___x_421_);
lean_closure_set(v___f_422_, 3, v___x_420_);
v_sz_423_ = lean_array_size(v_sm_416_);
v___x_424_ = ((size_t)0ULL);
v___x_425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_418_, v_sm_416_, v___f_422_, v_sz_423_, v___x_424_, v___x_421_);
v_fst_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_fst_426_);
lean_dec(v___x_425_);
if (lean_obj_tag(v_fst_426_) == 0)
{
return v___x_419_;
}
else
{
lean_object* v_val_427_; 
v_val_427_ = lean_ctor_get(v_fst_426_, 0);
lean_inc(v_val_427_);
lean_dec_ref_known(v_fst_426_, 1);
if (lean_obj_tag(v_val_427_) == 0)
{
return v___x_419_;
}
else
{
lean_object* v_val_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_437_; 
v_val_428_ = lean_ctor_get(v_val_427_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v_val_427_);
if (v_isSharedCheck_437_ == 0)
{
v___x_430_ = v_val_427_;
v_isShared_431_ = v_isSharedCheck_437_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_val_428_);
lean_dec(v_val_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_437_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v_snd_432_; lean_object* v_fst_433_; lean_object* v___x_435_; 
v_snd_432_ = lean_ctor_get(v_val_428_, 1);
lean_inc(v_snd_432_);
lean_dec(v_val_428_);
v_fst_433_ = lean_ctor_get(v_snd_432_, 0);
lean_inc(v_fst_433_);
lean_dec(v_snd_432_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v_fst_433_);
v___x_435_ = v___x_430_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_fst_433_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_get_x3f(lean_object* v_00_u03b1_438_, lean_object* v_00_u03b2_439_, lean_object* v_inst_440_, lean_object* v_sm_441_, lean_object* v_name_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Std_StreamMap_get_x3f___redArg(v_inst_440_, v_sm_441_, v_name_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(lean_object* v_pred_444_, lean_object* v_as_445_, size_t v_i_446_, size_t v_stop_447_, lean_object* v_b_448_){
_start:
{
lean_object* v___y_450_; uint8_t v___x_454_; 
v___x_454_ = lean_usize_dec_eq(v_i_446_, v_stop_447_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v_fst_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_455_ = lean_array_uget_borrowed(v_as_445_, v_i_446_);
v_fst_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc_ref(v_pred_444_);
lean_inc(v_fst_456_);
v___x_457_ = lean_apply_1(v_pred_444_, v_fst_456_);
v___x_458_ = lean_unbox(v___x_457_);
if (v___x_458_ == 0)
{
v___y_450_ = v_b_448_;
goto v___jp_449_;
}
else
{
lean_object* v___x_459_; 
lean_inc(v___x_455_);
v___x_459_ = lean_array_push(v_b_448_, v___x_455_);
v___y_450_ = v___x_459_;
goto v___jp_449_;
}
}
else
{
lean_dec_ref(v_pred_444_);
return v_b_448_;
}
v___jp_449_:
{
size_t v___x_451_; size_t v___x_452_; 
v___x_451_ = ((size_t)1ULL);
v___x_452_ = lean_usize_add(v_i_446_, v___x_451_);
v_i_446_ = v___x_452_;
v_b_448_ = v___y_450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg___boxed(lean_object* v_pred_460_, lean_object* v_as_461_, lean_object* v_i_462_, lean_object* v_stop_463_, lean_object* v_b_464_){
_start:
{
size_t v_i_boxed_465_; size_t v_stop_boxed_466_; lean_object* v_res_467_; 
v_i_boxed_465_ = lean_unbox_usize(v_i_462_);
lean_dec(v_i_462_);
v_stop_boxed_466_ = lean_unbox_usize(v_stop_463_);
lean_dec(v_stop_463_);
v_res_467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(v_pred_460_, v_as_461_, v_i_boxed_465_, v_stop_boxed_466_, v_b_464_);
lean_dec_ref(v_as_461_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_filterByName___redArg(lean_object* v_sm_468_, lean_object* v_pred_469_){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_470_ = lean_unsigned_to_nat(0u);
v___x_471_ = lean_array_get_size(v_sm_468_);
v___x_472_ = ((lean_object*)(l_Std_StreamMap_empty___closed__0));
v___x_473_ = lean_nat_dec_lt(v___x_470_, v___x_471_);
if (v___x_473_ == 0)
{
lean_dec_ref(v_pred_469_);
return v___x_472_;
}
else
{
uint8_t v___x_474_; 
v___x_474_ = lean_nat_dec_le(v___x_471_, v___x_471_);
if (v___x_474_ == 0)
{
if (v___x_473_ == 0)
{
lean_dec_ref(v_pred_469_);
return v___x_472_;
}
else
{
size_t v___x_475_; size_t v___x_476_; lean_object* v___x_477_; 
v___x_475_ = ((size_t)0ULL);
v___x_476_ = lean_usize_of_nat(v___x_471_);
v___x_477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(v_pred_469_, v_sm_468_, v___x_475_, v___x_476_, v___x_472_);
return v___x_477_;
}
}
else
{
size_t v___x_478_; size_t v___x_479_; lean_object* v___x_480_; 
v___x_478_ = ((size_t)0ULL);
v___x_479_ = lean_usize_of_nat(v___x_471_);
v___x_480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(v_pred_469_, v_sm_468_, v___x_478_, v___x_479_, v___x_472_);
return v___x_480_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_filterByName___redArg___boxed(lean_object* v_sm_481_, lean_object* v_pred_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Std_StreamMap_filterByName___redArg(v_sm_481_, v_pred_482_);
lean_dec_ref(v_sm_481_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_filterByName(lean_object* v_00_u03b1_484_, lean_object* v_00_u03b2_485_, lean_object* v_sm_486_, lean_object* v_pred_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Std_StreamMap_filterByName___redArg(v_sm_486_, v_pred_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_filterByName___boxed(lean_object* v_00_u03b1_489_, lean_object* v_00_u03b2_490_, lean_object* v_sm_491_, lean_object* v_pred_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Std_StreamMap_filterByName(v_00_u03b1_489_, v_00_u03b2_490_, v_sm_491_, v_pred_492_);
lean_dec_ref(v_sm_491_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0(lean_object* v_00_u03b1_494_, lean_object* v_00_u03b2_495_, lean_object* v_pred_496_, lean_object* v_as_497_, size_t v_i_498_, size_t v_stop_499_, lean_object* v_b_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(v_pred_496_, v_as_497_, v_i_498_, v_stop_499_, v_b_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___boxed(lean_object* v_00_u03b1_502_, lean_object* v_00_u03b2_503_, lean_object* v_pred_504_, lean_object* v_as_505_, lean_object* v_i_506_, lean_object* v_stop_507_, lean_object* v_b_508_){
_start:
{
size_t v_i_boxed_509_; size_t v_stop_boxed_510_; lean_object* v_res_511_; 
v_i_boxed_509_ = lean_unbox_usize(v_i_506_);
lean_dec(v_i_506_);
v_stop_boxed_510_ = lean_unbox_usize(v_stop_507_);
lean_dec(v_stop_507_);
v_res_511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0(v_00_u03b1_502_, v_00_u03b2_503_, v_pred_504_, v_as_505_, v_i_boxed_509_, v_stop_boxed_510_, v_b_508_);
lean_dec_ref(v_as_505_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg(size_t v_sz_512_, size_t v_i_513_, lean_object* v_bs_514_){
_start:
{
uint8_t v___x_515_; 
v___x_515_ = lean_usize_dec_lt(v_i_513_, v_sz_512_);
if (v___x_515_ == 0)
{
return v_bs_514_;
}
else
{
lean_object* v_v_516_; lean_object* v_snd_517_; lean_object* v_fst_518_; lean_object* v_fst_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_532_; 
v_v_516_ = lean_array_uget_borrowed(v_bs_514_, v_i_513_);
v_snd_517_ = lean_ctor_get(v_v_516_, 1);
lean_inc(v_snd_517_);
v_fst_518_ = lean_ctor_get(v_v_516_, 0);
lean_inc(v_fst_518_);
v_fst_519_ = lean_ctor_get(v_snd_517_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v_snd_517_);
if (v_isSharedCheck_532_ == 0)
{
lean_object* v_unused_533_; 
v_unused_533_ = lean_ctor_get(v_snd_517_, 1);
lean_dec(v_unused_533_);
v___x_521_ = v_snd_517_;
v_isShared_522_ = v_isSharedCheck_532_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_fst_519_);
lean_dec(v_snd_517_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_532_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; lean_object* v_bs_x27_524_; lean_object* v___x_526_; 
v___x_523_ = lean_unsigned_to_nat(0u);
v_bs_x27_524_ = lean_array_uset(v_bs_514_, v_i_513_, v___x_523_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v_fst_519_);
lean_ctor_set(v___x_521_, 0, v_fst_518_);
v___x_526_ = v___x_521_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_fst_518_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_fst_519_);
v___x_526_ = v_reuseFailAlloc_531_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
size_t v___x_527_; size_t v___x_528_; lean_object* v___x_529_; 
v___x_527_ = ((size_t)1ULL);
v___x_528_ = lean_usize_add(v_i_513_, v___x_527_);
v___x_529_ = lean_array_uset(v_bs_x27_524_, v_i_513_, v___x_526_);
v_i_513_ = v___x_528_;
v_bs_514_ = v___x_529_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg___boxed(lean_object* v_sz_534_, lean_object* v_i_535_, lean_object* v_bs_536_){
_start:
{
size_t v_sz_boxed_537_; size_t v_i_boxed_538_; lean_object* v_res_539_; 
v_sz_boxed_537_ = lean_unbox_usize(v_sz_534_);
lean_dec(v_sz_534_);
v_i_boxed_538_ = lean_unbox_usize(v_i_535_);
lean_dec(v_i_535_);
v_res_539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg(v_sz_boxed_537_, v_i_boxed_538_, v_bs_536_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_toArray___redArg(lean_object* v_sm_540_){
_start:
{
size_t v_sz_541_; size_t v___x_542_; lean_object* v___x_543_; 
v_sz_541_ = lean_array_size(v_sm_540_);
v___x_542_ = ((size_t)0ULL);
v___x_543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg(v_sz_541_, v___x_542_, v_sm_540_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_toArray(lean_object* v_00_u03b1_544_, lean_object* v_00_u03b2_545_, lean_object* v_sm_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Std_StreamMap_toArray___redArg(v_sm_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0(lean_object* v_00_u03b1_548_, lean_object* v_00_u03b2_549_, size_t v_sz_550_, size_t v_i_551_, lean_object* v_bs_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg(v_sz_550_, v_i_551_, v_bs_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___boxed(lean_object* v_00_u03b1_554_, lean_object* v_00_u03b2_555_, lean_object* v_sz_556_, lean_object* v_i_557_, lean_object* v_bs_558_){
_start:
{
size_t v_sz_boxed_559_; size_t v_i_boxed_560_; lean_object* v_res_561_; 
v_sz_boxed_559_ = lean_unbox_usize(v_sz_556_);
lean_dec(v_sz_556_);
v_i_boxed_560_ = lean_unbox_usize(v_i_557_);
lean_dec(v_i_557_);
v_res_561_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0(v_00_u03b1_554_, v_00_u03b2_555_, v_sz_boxed_559_, v_i_boxed_560_, v_bs_558_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(lean_object* v_as_562_, size_t v_i_563_, size_t v_stop_564_, lean_object* v_b_565_){
_start:
{
uint8_t v___x_567_; 
v___x_567_ = lean_usize_dec_eq(v_i_563_, v_stop_564_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v_snd_569_; lean_object* v_snd_570_; lean_object* v___x_571_; 
v___x_568_ = lean_array_uget_borrowed(v_as_562_, v_i_563_);
v_snd_569_ = lean_ctor_get(v___x_568_, 1);
v_snd_570_ = lean_ctor_get(v_snd_569_, 1);
lean_inc(v_snd_570_);
v___x_571_ = lean_apply_1(v_snd_570_, lean_box(0));
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; size_t v___x_573_; size_t v___x_574_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_572_);
lean_dec_ref_known(v___x_571_, 1);
v___x_573_ = ((size_t)1ULL);
v___x_574_ = lean_usize_add(v_i_563_, v___x_573_);
v_i_563_ = v___x_574_;
v_b_565_ = v_a_572_;
goto _start;
}
else
{
return v___x_571_;
}
}
else
{
lean_object* v___x_576_; 
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v_b_565_);
return v___x_576_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg___boxed(lean_object* v_as_577_, lean_object* v_i_578_, lean_object* v_stop_579_, lean_object* v_b_580_, lean_object* v___y_581_){
_start:
{
size_t v_i_boxed_582_; size_t v_stop_boxed_583_; lean_object* v_res_584_; 
v_i_boxed_582_ = lean_unbox_usize(v_i_578_);
lean_dec(v_i_578_);
v_stop_boxed_583_ = lean_unbox_usize(v_stop_579_);
lean_dec(v_stop_579_);
v_res_584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(v_as_577_, v_i_boxed_582_, v_stop_boxed_583_, v_b_580_);
lean_dec_ref(v_as_577_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_close___redArg(lean_object* v_sm_585_){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_587_ = lean_unsigned_to_nat(0u);
v___x_588_ = lean_array_get_size(v_sm_585_);
v___x_589_ = lean_box(0);
v___x_590_ = lean_nat_dec_lt(v___x_587_, v___x_588_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; 
v___x_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_591_, 0, v___x_589_);
return v___x_591_;
}
else
{
uint8_t v___x_592_; 
v___x_592_ = lean_nat_dec_le(v___x_588_, v___x_588_);
if (v___x_592_ == 0)
{
if (v___x_590_ == 0)
{
lean_object* v___x_593_; 
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_589_);
return v___x_593_;
}
else
{
size_t v___x_594_; size_t v___x_595_; lean_object* v___x_596_; 
v___x_594_ = ((size_t)0ULL);
v___x_595_ = lean_usize_of_nat(v___x_588_);
v___x_596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(v_sm_585_, v___x_594_, v___x_595_, v___x_589_);
return v___x_596_;
}
}
else
{
size_t v___x_597_; size_t v___x_598_; lean_object* v___x_599_; 
v___x_597_ = ((size_t)0ULL);
v___x_598_ = lean_usize_of_nat(v___x_588_);
v___x_599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(v_sm_585_, v___x_597_, v___x_598_, v___x_589_);
return v___x_599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_close___redArg___boxed(lean_object* v_sm_600_, lean_object* v_a_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Std_StreamMap_close___redArg(v_sm_600_);
lean_dec_ref(v_sm_600_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_close(lean_object* v_00_u03b1_603_, lean_object* v_00_u03b2_604_, lean_object* v_sm_605_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Std_StreamMap_close___redArg(v_sm_605_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_close___boxed(lean_object* v_00_u03b1_608_, lean_object* v_00_u03b2_609_, lean_object* v_sm_610_, lean_object* v_a_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Std_StreamMap_close(v_00_u03b1_608_, v_00_u03b2_609_, v_sm_610_);
lean_dec_ref(v_sm_610_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0(lean_object* v_00_u03b1_613_, lean_object* v_00_u03b2_614_, lean_object* v_as_615_, size_t v_i_616_, size_t v_stop_617_, lean_object* v_b_618_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(v_as_615_, v_i_616_, v_stop_617_, v_b_618_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___boxed(lean_object* v_00_u03b1_621_, lean_object* v_00_u03b2_622_, lean_object* v_as_623_, lean_object* v_i_624_, lean_object* v_stop_625_, lean_object* v_b_626_, lean_object* v___y_627_){
_start:
{
size_t v_i_boxed_628_; size_t v_stop_boxed_629_; lean_object* v_res_630_; 
v_i_boxed_628_ = lean_unbox_usize(v_i_624_);
lean_dec(v_i_624_);
v_stop_boxed_629_ = lean_unbox_usize(v_stop_625_);
lean_dec(v_stop_625_);
v_res_630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0(v_00_u03b1_621_, v_00_u03b2_622_, v_as_623_, v_i_boxed_628_, v_stop_boxed_629_, v_b_626_);
lean_dec_ref(v_as_623_);
return v_res_630_;
}
}
lean_object* runtime_initialize_Std_Data(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Queue(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_IO(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sync_StreamMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Queue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sync_StreamMap(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data(uint8_t builtin);
lean_object* initialize_Init_Data_Queue(uint8_t builtin);
lean_object* initialize_Std_Async_IO(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sync_StreamMap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Queue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Async_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_StreamMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sync_StreamMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sync_StreamMap(builtin);
}
#ifdef __cplusplus
}
#endif
