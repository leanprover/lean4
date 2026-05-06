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
lean_object* v_fst_35_; lean_object* v___x_36_; uint8_t v___x_37_; 
v_fst_35_ = lean_ctor_get(v_x2_34_, 0);
lean_inc(v_fst_35_);
v___x_36_ = lean_apply_2(v_inst_31_, v_fst_35_, v_name_32_);
v___x_37_ = lean_unbox(v___x_36_);
if (v___x_37_ == 0)
{
lean_object* v___x_38_; 
v___x_38_ = lean_array_push(v_x1_33_, v_x2_34_);
return v___x_38_;
}
else
{
lean_dec_ref(v_x2_34_);
return v_x1_33_;
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_register___redArg(lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_sm_60_, lean_object* v_name_61_, lean_object* v_reader_62_){
_start:
{
lean_object* v_next_63_; lean_object* v_stop_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_90_; 
v_next_63_ = lean_ctor_get(v_inst_59_, 0);
v_stop_64_ = lean_ctor_get(v_inst_59_, 1);
v_isSharedCheck_90_ = !lean_is_exclusive(v_inst_59_);
if (v_isSharedCheck_90_ == 0)
{
v___x_66_ = v_inst_59_;
v_isShared_67_ = v_isSharedCheck_90_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_stop_64_);
lean_inc(v_next_63_);
lean_dec(v_inst_59_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_90_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v_newSelector_68_; lean_object* v___y_70_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
lean_inc(v_reader_62_);
v_newSelector_68_ = lean_apply_1(v_next_63_, v_reader_62_);
v___x_77_ = lean_unsigned_to_nat(0u);
v___x_78_ = lean_array_get_size(v_sm_60_);
v___x_79_ = ((lean_object*)(l_Std_StreamMap_empty___closed__0));
v___x_80_ = ((lean_object*)(l_Std_StreamMap_register___redArg___closed__9));
v___x_81_ = lean_nat_dec_lt(v___x_77_, v___x_78_);
if (v___x_81_ == 0)
{
lean_dec_ref(v_sm_60_);
lean_dec_ref(v_inst_58_);
v___y_70_ = v___x_79_;
goto v___jp_69_;
}
else
{
lean_object* v___f_82_; uint8_t v___x_83_; 
lean_inc(v_name_61_);
v___f_82_ = lean_alloc_closure((void*)(l_Std_StreamMap_register___redArg___lam__0), 4, 2);
lean_closure_set(v___f_82_, 0, v_inst_58_);
lean_closure_set(v___f_82_, 1, v_name_61_);
v___x_83_ = lean_nat_dec_le(v___x_78_, v___x_78_);
if (v___x_83_ == 0)
{
if (v___x_81_ == 0)
{
lean_dec_ref(v___f_82_);
lean_dec_ref(v_sm_60_);
v___y_70_ = v___x_79_;
goto v___jp_69_;
}
else
{
size_t v___x_84_; size_t v___x_85_; lean_object* v___x_86_; 
v___x_84_ = ((size_t)0ULL);
v___x_85_ = lean_usize_of_nat(v___x_78_);
v___x_86_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_80_, v___f_82_, v_sm_60_, v___x_84_, v___x_85_, v___x_79_);
v___y_70_ = v___x_86_;
goto v___jp_69_;
}
}
else
{
size_t v___x_87_; size_t v___x_88_; lean_object* v___x_89_; 
v___x_87_ = ((size_t)0ULL);
v___x_88_ = lean_usize_of_nat(v___x_78_);
v___x_89_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_80_, v___f_82_, v_sm_60_, v___x_87_, v___x_88_, v___x_79_);
v___y_70_ = v___x_89_;
goto v___jp_69_;
}
}
v___jp_69_:
{
lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_71_ = lean_apply_1(v_stop_64_, v_reader_62_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 1, v___x_71_);
lean_ctor_set(v___x_66_, 0, v_newSelector_68_);
v___x_73_ = v___x_66_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_newSelector_68_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v___x_71_);
v___x_73_ = v_reuseFailAlloc_76_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_74_, 0, v_name_61_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
v___x_75_ = lean_array_push(v___y_70_, v___x_74_);
return v___x_75_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_register(lean_object* v_00_u03b1_91_, lean_object* v_t_92_, lean_object* v_00_u03b2_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_sm_96_, lean_object* v_name_97_, lean_object* v_reader_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Std_StreamMap_register___redArg(v_inst_94_, v_inst_95_, v_sm_96_, v_name_97_, v_reader_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_ofArray___redArg___lam__0(lean_object* v_x_100_){
_start:
{
lean_object* v_fst_101_; lean_object* v_snd_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_110_; 
v_fst_101_ = lean_ctor_get(v_x_100_, 0);
v_snd_102_ = lean_ctor_get(v_x_100_, 1);
v_isSharedCheck_110_ = !lean_is_exclusive(v_x_100_);
if (v_isSharedCheck_110_ == 0)
{
v___x_104_ = v_x_100_;
v_isShared_105_ = v_isSharedCheck_110_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_snd_102_);
lean_inc(v_fst_101_);
lean_dec(v_x_100_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_110_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_106_; lean_object* v___x_108_; 
v___x_106_ = l_Std_AnyAsyncStream_getSelector___redArg(v_snd_102_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 1, v___x_106_);
v___x_108_ = v___x_104_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_fst_101_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v___x_106_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_ofArray___redArg(lean_object* v_streams_112_){
_start:
{
lean_object* v___f_113_; lean_object* v___x_114_; size_t v_sz_115_; size_t v___x_116_; lean_object* v_arrayOfSelectors_117_; 
v___f_113_ = ((lean_object*)(l_Std_StreamMap_ofArray___redArg___closed__0));
v___x_114_ = ((lean_object*)(l_Std_StreamMap_register___redArg___closed__9));
v_sz_115_ = lean_array_size(v_streams_112_);
v___x_116_ = ((size_t)0ULL);
v_arrayOfSelectors_117_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_114_, v___f_113_, v_sz_115_, v___x_116_, v_streams_112_);
return v_arrayOfSelectors_117_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_ofArray(lean_object* v_00_u03b1_118_, lean_object* v_00_u03b2_119_, lean_object* v_inst_120_, lean_object* v_streams_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Std_StreamMap_ofArray___redArg(v_streams_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_ofArray___boxed(lean_object* v_00_u03b1_123_, lean_object* v_00_u03b2_124_, lean_object* v_inst_125_, lean_object* v_streams_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Std_StreamMap_ofArray(v_00_u03b1_123_, v_00_u03b2_124_, v_inst_125_, v_streams_126_);
lean_dec_ref(v_inst_125_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___lam__0(lean_object* v_fst_128_, lean_object* v_x_129_){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v_fst_128_);
lean_ctor_set(v___x_131_, 1, v_x_129_);
v___x_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
v___x_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___lam__0___boxed(lean_object* v_fst_134_, lean_object* v_x_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___lam__0(v_fst_134_, v_x_135_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(size_t v_sz_138_, size_t v_i_139_, lean_object* v_bs_140_){
_start:
{
uint8_t v___x_141_; 
v___x_141_ = lean_usize_dec_lt(v_i_139_, v_sz_138_);
if (v___x_141_ == 0)
{
return v_bs_140_;
}
else
{
lean_object* v_v_142_; lean_object* v_snd_143_; lean_object* v_fst_144_; lean_object* v_fst_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_159_; 
v_v_142_ = lean_array_uget_borrowed(v_bs_140_, v_i_139_);
v_snd_143_ = lean_ctor_get(v_v_142_, 1);
lean_inc(v_snd_143_);
v_fst_144_ = lean_ctor_get(v_v_142_, 0);
lean_inc(v_fst_144_);
v_fst_145_ = lean_ctor_get(v_snd_143_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v_snd_143_);
if (v_isSharedCheck_159_ == 0)
{
lean_object* v_unused_160_; 
v_unused_160_ = lean_ctor_get(v_snd_143_, 1);
lean_dec(v_unused_160_);
v___x_147_ = v_snd_143_;
v_isShared_148_ = v_isSharedCheck_159_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_fst_145_);
lean_dec(v_snd_143_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_159_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_149_; lean_object* v_bs_x27_150_; lean_object* v___f_151_; lean_object* v___x_153_; 
v___x_149_ = lean_unsigned_to_nat(0u);
v_bs_x27_150_ = lean_array_uset(v_bs_140_, v_i_139_, v___x_149_);
v___f_151_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_151_, 0, v_fst_144_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 1, v___f_151_);
v___x_153_ = v___x_147_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_fst_145_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v___f_151_);
v___x_153_ = v_reuseFailAlloc_158_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
size_t v___x_154_; size_t v___x_155_; lean_object* v___x_156_; 
v___x_154_ = ((size_t)1ULL);
v___x_155_ = lean_usize_add(v_i_139_, v___x_154_);
v___x_156_ = lean_array_uset(v_bs_x27_150_, v_i_139_, v___x_153_);
v_i_139_ = v___x_155_;
v_bs_140_ = v___x_156_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___boxed(lean_object* v_sz_161_, lean_object* v_i_162_, lean_object* v_bs_163_){
_start:
{
size_t v_sz_boxed_164_; size_t v_i_boxed_165_; lean_object* v_res_166_; 
v_sz_boxed_164_ = lean_unbox_usize(v_sz_161_);
lean_dec(v_sz_161_);
v_i_boxed_165_ = lean_unbox_usize(v_i_162_);
lean_dec(v_i_162_);
v_res_166_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(v_sz_boxed_164_, v_i_boxed_165_, v_bs_163_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_selector___redArg(lean_object* v_stream_167_){
_start:
{
lean_object* v_val_170_; size_t v_sz_172_; size_t v___x_173_; lean_object* v_selectables_174_; lean_object* v___x_175_; 
v_sz_172_ = lean_array_size(v_stream_167_);
v___x_173_ = ((size_t)0ULL);
v_selectables_174_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(v_sz_172_, v___x_173_, v_stream_167_);
v___x_175_ = l_Std_Async_Selectable_combine___redArg(v_selectables_174_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_183_ == 0)
{
v___x_178_ = v___x_175_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_175_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set_tag(v___x_178_, 1);
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_a_176_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
v_val_170_ = v___x_181_;
goto v___jp_169_;
}
}
}
else
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
v_a_184_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_191_ == 0)
{
v___x_186_ = v___x_175_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_175_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
lean_ctor_set_tag(v___x_186_, 0);
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_a_184_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
v_val_170_ = v___x_189_;
goto v___jp_169_;
}
}
}
v___jp_169_:
{
lean_object* v___x_171_; 
v___x_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_171_, 0, v_val_170_);
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_selector___redArg___boxed(lean_object* v_stream_192_, lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Std_StreamMap_selector___redArg(v_stream_192_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_selector(lean_object* v_00_u03b1_195_, lean_object* v_00_u03b2_196_, lean_object* v_stream_197_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Std_StreamMap_selector___redArg(v_stream_197_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_selector___boxed(lean_object* v_00_u03b1_200_, lean_object* v_00_u03b2_201_, lean_object* v_stream_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Std_StreamMap_selector(v_00_u03b1_200_, v_00_u03b2_201_, v_stream_202_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0(lean_object* v_00_u03b1_205_, lean_object* v_00_u03b2_206_, size_t v_sz_207_, size_t v_i_208_, lean_object* v_bs_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(v_sz_207_, v_i_208_, v_bs_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___boxed(lean_object* v_00_u03b1_211_, lean_object* v_00_u03b2_212_, lean_object* v_sz_213_, lean_object* v_i_214_, lean_object* v_bs_215_){
_start:
{
size_t v_sz_boxed_216_; size_t v_i_boxed_217_; lean_object* v_res_218_; 
v_sz_boxed_216_ = lean_unbox_usize(v_sz_213_);
lean_dec(v_sz_213_);
v_i_boxed_217_ = lean_unbox_usize(v_i_214_);
lean_dec(v_i_214_);
v_res_218_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0(v_00_u03b1_211_, v_00_u03b2_212_, v_sz_boxed_216_, v_i_boxed_217_, v_bs_215_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_recv___redArg(lean_object* v_stream_219_){
_start:
{
size_t v_sz_221_; size_t v___x_222_; lean_object* v_selectables_223_; lean_object* v___x_224_; 
v_sz_221_ = lean_array_size(v_stream_219_);
v___x_222_ = ((size_t)0ULL);
v_selectables_223_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(v_sz_221_, v___x_222_, v_stream_219_);
v___x_224_ = l_Std_Async_Selectable_one___redArg(v_selectables_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_recv___redArg___boxed(lean_object* v_stream_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Std_StreamMap_recv___redArg(v_stream_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_recv(lean_object* v_00_u03b1_228_, lean_object* v_00_u03b2_229_, lean_object* v_stream_230_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Std_StreamMap_recv___redArg(v_stream_230_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_recv___boxed(lean_object* v_00_u03b1_233_, lean_object* v_00_u03b2_234_, lean_object* v_stream_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Std_StreamMap_recv(v_00_u03b1_233_, v_00_u03b2_234_, v_stream_235_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_tryRecv___redArg(lean_object* v_stream_238_){
_start:
{
size_t v_sz_240_; size_t v___x_241_; lean_object* v_selectables_242_; lean_object* v___x_243_; 
v_sz_240_ = lean_array_size(v_stream_238_);
v___x_241_ = ((size_t)0ULL);
v_selectables_242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(v_sz_240_, v___x_241_, v_stream_238_);
v___x_243_ = l_Std_Async_Selectable_tryOne___redArg(v_selectables_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_tryRecv___redArg___boxed(lean_object* v_stream_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Std_StreamMap_tryRecv___redArg(v_stream_244_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_tryRecv(lean_object* v_00_u03b1_247_, lean_object* v_00_u03b2_248_, lean_object* v_stream_249_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Std_StreamMap_tryRecv___redArg(v_stream_249_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_tryRecv___boxed(lean_object* v_00_u03b1_252_, lean_object* v_00_u03b2_253_, lean_object* v_stream_254_, lean_object* v_a_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Std_StreamMap_tryRecv(v_00_u03b1_252_, v_00_u03b2_253_, v_stream_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_unregister___redArg(lean_object* v_inst_257_, lean_object* v_sm_258_, lean_object* v_name_259_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_260_ = lean_unsigned_to_nat(0u);
v___x_261_ = lean_array_get_size(v_sm_258_);
v___x_262_ = ((lean_object*)(l_Std_StreamMap_empty___closed__0));
v___x_263_ = ((lean_object*)(l_Std_StreamMap_register___redArg___closed__9));
v___x_264_ = lean_nat_dec_lt(v___x_260_, v___x_261_);
if (v___x_264_ == 0)
{
lean_dec(v_name_259_);
lean_dec_ref(v_sm_258_);
lean_dec_ref(v_inst_257_);
return v___x_262_;
}
else
{
lean_object* v___f_265_; uint8_t v___x_266_; 
v___f_265_ = lean_alloc_closure((void*)(l_Std_StreamMap_register___redArg___lam__0), 4, 2);
lean_closure_set(v___f_265_, 0, v_inst_257_);
lean_closure_set(v___f_265_, 1, v_name_259_);
v___x_266_ = lean_nat_dec_le(v___x_261_, v___x_261_);
if (v___x_266_ == 0)
{
if (v___x_264_ == 0)
{
lean_dec_ref(v___f_265_);
lean_dec_ref(v_sm_258_);
return v___x_262_;
}
else
{
size_t v___x_267_; size_t v___x_268_; lean_object* v___x_269_; 
v___x_267_ = ((size_t)0ULL);
v___x_268_ = lean_usize_of_nat(v___x_261_);
v___x_269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_263_, v___f_265_, v_sm_258_, v___x_267_, v___x_268_, v___x_262_);
return v___x_269_;
}
}
else
{
size_t v___x_270_; size_t v___x_271_; lean_object* v___x_272_; 
v___x_270_ = ((size_t)0ULL);
v___x_271_ = lean_usize_of_nat(v___x_261_);
v___x_272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_263_, v___f_265_, v_sm_258_, v___x_270_, v___x_271_, v___x_262_);
return v___x_272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_unregister(lean_object* v_00_u03b1_273_, lean_object* v_00_u03b2_274_, lean_object* v_inst_275_, lean_object* v_sm_276_, lean_object* v_name_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Std_StreamMap_unregister___redArg(v_inst_275_, v_sm_276_, v_name_277_);
return v___x_278_;
}
}
LEAN_EXPORT uint8_t l_Std_StreamMap_contains___redArg___lam__0(lean_object* v_inst_279_, lean_object* v_name_280_, lean_object* v_x_281_){
_start:
{
lean_object* v_fst_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v_fst_282_ = lean_ctor_get(v_x_281_, 0);
lean_inc(v_fst_282_);
lean_dec_ref(v_x_281_);
v___x_283_ = lean_apply_2(v_inst_279_, v_fst_282_, v_name_280_);
v___x_284_ = lean_unbox(v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_contains___redArg___lam__0___boxed(lean_object* v_inst_285_, lean_object* v_name_286_, lean_object* v_x_287_){
_start:
{
uint8_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = l_Std_StreamMap_contains___redArg___lam__0(v_inst_285_, v_name_286_, v_x_287_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT uint8_t l_Std_StreamMap_contains___redArg(lean_object* v_inst_290_, lean_object* v_sm_291_, lean_object* v_name_292_){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = lean_array_get_size(v_sm_291_);
v___x_295_ = ((lean_object*)(l_Std_StreamMap_register___redArg___closed__9));
v___x_296_ = lean_nat_dec_lt(v___x_293_, v___x_294_);
if (v___x_296_ == 0)
{
lean_dec(v_name_292_);
lean_dec_ref(v_sm_291_);
lean_dec_ref(v_inst_290_);
return v___x_296_;
}
else
{
if (v___x_296_ == 0)
{
lean_dec(v_name_292_);
lean_dec_ref(v_sm_291_);
lean_dec_ref(v_inst_290_);
return v___x_296_;
}
else
{
lean_object* v___f_297_; size_t v___x_298_; size_t v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___f_297_ = lean_alloc_closure((void*)(l_Std_StreamMap_contains___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_297_, 0, v_inst_290_);
lean_closure_set(v___f_297_, 1, v_name_292_);
v___x_298_ = ((size_t)0ULL);
v___x_299_ = lean_usize_of_nat(v___x_294_);
v___x_300_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_295_, v___f_297_, v_sm_291_, v___x_298_, v___x_299_);
v___x_301_ = lean_unbox(v___x_300_);
lean_dec(v___x_300_);
return v___x_301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_contains___redArg___boxed(lean_object* v_inst_302_, lean_object* v_sm_303_, lean_object* v_name_304_){
_start:
{
uint8_t v_res_305_; lean_object* v_r_306_; 
v_res_305_ = l_Std_StreamMap_contains___redArg(v_inst_302_, v_sm_303_, v_name_304_);
v_r_306_ = lean_box(v_res_305_);
return v_r_306_;
}
}
LEAN_EXPORT uint8_t l_Std_StreamMap_contains(lean_object* v_00_u03b1_307_, lean_object* v_00_u03b2_308_, lean_object* v_inst_309_, lean_object* v_sm_310_, lean_object* v_name_311_){
_start:
{
uint8_t v___x_312_; 
v___x_312_ = l_Std_StreamMap_contains___redArg(v_inst_309_, v_sm_310_, v_name_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_contains___boxed(lean_object* v_00_u03b1_313_, lean_object* v_00_u03b2_314_, lean_object* v_inst_315_, lean_object* v_sm_316_, lean_object* v_name_317_){
_start:
{
uint8_t v_res_318_; lean_object* v_r_319_; 
v_res_318_ = l_Std_StreamMap_contains(v_00_u03b1_313_, v_00_u03b2_314_, v_inst_315_, v_sm_316_, v_name_317_);
v_r_319_ = lean_box(v_res_318_);
return v_r_319_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_size___redArg(lean_object* v_sm_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = lean_array_get_size(v_sm_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_size___redArg___boxed(lean_object* v_sm_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Std_StreamMap_size___redArg(v_sm_322_);
lean_dec_ref(v_sm_322_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_size(lean_object* v_00_u03b1_324_, lean_object* v_00_u03b2_325_, lean_object* v_sm_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = lean_array_get_size(v_sm_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_size___boxed(lean_object* v_00_u03b1_328_, lean_object* v_00_u03b2_329_, lean_object* v_sm_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_StreamMap_size(v_00_u03b1_328_, v_00_u03b2_329_, v_sm_330_);
lean_dec_ref(v_sm_330_);
return v_res_331_;
}
}
LEAN_EXPORT uint8_t l_Std_StreamMap_isEmpty___redArg(lean_object* v_sm_332_){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_333_ = lean_array_get_size(v_sm_332_);
v___x_334_ = lean_unsigned_to_nat(0u);
v___x_335_ = lean_nat_dec_eq(v___x_333_, v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_isEmpty___redArg___boxed(lean_object* v_sm_336_){
_start:
{
uint8_t v_res_337_; lean_object* v_r_338_; 
v_res_337_ = l_Std_StreamMap_isEmpty___redArg(v_sm_336_);
lean_dec_ref(v_sm_336_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT uint8_t l_Std_StreamMap_isEmpty(lean_object* v_00_u03b1_339_, lean_object* v_00_u03b2_340_, lean_object* v_sm_341_){
_start:
{
uint8_t v___x_342_; 
v___x_342_ = l_Std_StreamMap_isEmpty___redArg(v_sm_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_isEmpty___boxed(lean_object* v_00_u03b1_343_, lean_object* v_00_u03b2_344_, lean_object* v_sm_345_){
_start:
{
uint8_t v_res_346_; lean_object* v_r_347_; 
v_res_346_ = l_Std_StreamMap_isEmpty(v_00_u03b1_343_, v_00_u03b2_344_, v_sm_345_);
lean_dec_ref(v_sm_345_);
v_r_347_ = lean_box(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg(size_t v_sz_348_, size_t v_i_349_, lean_object* v_bs_350_){
_start:
{
uint8_t v___x_351_; 
v___x_351_ = lean_usize_dec_lt(v_i_349_, v_sz_348_);
if (v___x_351_ == 0)
{
return v_bs_350_;
}
else
{
lean_object* v_v_352_; lean_object* v_fst_353_; lean_object* v___x_354_; lean_object* v_bs_x27_355_; size_t v___x_356_; size_t v___x_357_; lean_object* v___x_358_; 
v_v_352_ = lean_array_uget_borrowed(v_bs_350_, v_i_349_);
v_fst_353_ = lean_ctor_get(v_v_352_, 0);
lean_inc(v_fst_353_);
v___x_354_ = lean_unsigned_to_nat(0u);
v_bs_x27_355_ = lean_array_uset(v_bs_350_, v_i_349_, v___x_354_);
v___x_356_ = ((size_t)1ULL);
v___x_357_ = lean_usize_add(v_i_349_, v___x_356_);
v___x_358_ = lean_array_uset(v_bs_x27_355_, v_i_349_, v_fst_353_);
v_i_349_ = v___x_357_;
v_bs_350_ = v___x_358_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg___boxed(lean_object* v_sz_360_, lean_object* v_i_361_, lean_object* v_bs_362_){
_start:
{
size_t v_sz_boxed_363_; size_t v_i_boxed_364_; lean_object* v_res_365_; 
v_sz_boxed_363_ = lean_unbox_usize(v_sz_360_);
lean_dec(v_sz_360_);
v_i_boxed_364_ = lean_unbox_usize(v_i_361_);
lean_dec(v_i_361_);
v_res_365_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg(v_sz_boxed_363_, v_i_boxed_364_, v_bs_362_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_keys___redArg(lean_object* v_sm_366_){
_start:
{
size_t v_sz_367_; size_t v___x_368_; lean_object* v___x_369_; 
v_sz_367_ = lean_array_size(v_sm_366_);
v___x_368_ = ((size_t)0ULL);
v___x_369_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg(v_sz_367_, v___x_368_, v_sm_366_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_keys(lean_object* v_00_u03b1_370_, lean_object* v_00_u03b2_371_, lean_object* v_sm_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Std_StreamMap_keys___redArg(v_sm_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0(lean_object* v_00_u03b1_374_, lean_object* v_00_u03b2_375_, size_t v_sz_376_, size_t v_i_377_, lean_object* v_bs_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg(v_sz_376_, v_i_377_, v_bs_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___boxed(lean_object* v_00_u03b1_380_, lean_object* v_00_u03b2_381_, lean_object* v_sz_382_, lean_object* v_i_383_, lean_object* v_bs_384_){
_start:
{
size_t v_sz_boxed_385_; size_t v_i_boxed_386_; lean_object* v_res_387_; 
v_sz_boxed_385_ = lean_unbox_usize(v_sz_382_);
lean_dec(v_sz_382_);
v_i_boxed_386_ = lean_unbox_usize(v_i_383_);
lean_dec(v_i_383_);
v_res_387_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0(v_00_u03b1_380_, v_00_u03b2_381_, v_sz_boxed_385_, v_i_boxed_386_, v_bs_384_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_get_x3f___redArg___lam__0(lean_object* v_inst_388_, lean_object* v_name_389_, lean_object* v___x_390_, lean_object* v___x_391_, lean_object* v_a_392_, lean_object* v_x_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_fst_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v_fst_395_ = lean_ctor_get(v_a_392_, 0);
lean_inc(v_fst_395_);
v___x_396_ = lean_apply_2(v_inst_388_, v_fst_395_, v_name_389_);
v___x_397_ = lean_unbox(v___x_396_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; 
lean_dec_ref(v_a_392_);
v___x_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_390_);
return v___x_398_;
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
lean_dec_ref(v___x_390_);
v___x_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_399_, 0, v_a_392_);
v___x_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
v___x_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
lean_ctor_set(v___x_401_, 1, v___x_391_);
v___x_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
return v___x_402_;
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_get_x3f___redArg___lam__0___boxed(lean_object* v_inst_403_, lean_object* v_name_404_, lean_object* v___x_405_, lean_object* v___x_406_, lean_object* v_a_407_, lean_object* v_x_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Std_StreamMap_get_x3f___redArg___lam__0(v_inst_403_, v_name_404_, v___x_405_, v___x_406_, v_a_407_, v_x_408_, v___y_409_);
lean_dec_ref(v___y_409_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_get_x3f___redArg(lean_object* v_inst_414_, lean_object* v_sm_415_, lean_object* v_name_416_){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___f_421_; size_t v_sz_422_; size_t v___x_423_; lean_object* v___x_424_; lean_object* v_fst_425_; 
v___x_417_ = ((lean_object*)(l_Std_StreamMap_register___redArg___closed__9));
v___x_418_ = lean_box(0);
v___x_419_ = lean_box(0);
v___x_420_ = ((lean_object*)(l_Std_StreamMap_get_x3f___redArg___closed__0));
v___f_421_ = lean_alloc_closure((void*)(l_Std_StreamMap_get_x3f___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_421_, 0, v_inst_414_);
lean_closure_set(v___f_421_, 1, v_name_416_);
lean_closure_set(v___f_421_, 2, v___x_420_);
lean_closure_set(v___f_421_, 3, v___x_419_);
v_sz_422_ = lean_array_size(v_sm_415_);
v___x_423_ = ((size_t)0ULL);
v___x_424_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_417_, v_sm_415_, v___f_421_, v_sz_422_, v___x_423_, v___x_420_);
v_fst_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_fst_425_);
lean_dec(v___x_424_);
if (lean_obj_tag(v_fst_425_) == 0)
{
return v___x_418_;
}
else
{
lean_object* v_val_426_; 
v_val_426_ = lean_ctor_get(v_fst_425_, 0);
lean_inc(v_val_426_);
lean_dec_ref(v_fst_425_);
if (lean_obj_tag(v_val_426_) == 0)
{
return v___x_418_;
}
else
{
lean_object* v_val_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_436_; 
v_val_427_ = lean_ctor_get(v_val_426_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v_val_426_);
if (v_isSharedCheck_436_ == 0)
{
v___x_429_ = v_val_426_;
v_isShared_430_ = v_isSharedCheck_436_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_val_427_);
lean_dec(v_val_426_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_436_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v_snd_431_; lean_object* v_fst_432_; lean_object* v___x_434_; 
v_snd_431_ = lean_ctor_get(v_val_427_, 1);
lean_inc(v_snd_431_);
lean_dec(v_val_427_);
v_fst_432_ = lean_ctor_get(v_snd_431_, 0);
lean_inc(v_fst_432_);
lean_dec(v_snd_431_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v_fst_432_);
v___x_434_ = v___x_429_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_fst_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_get_x3f(lean_object* v_00_u03b1_437_, lean_object* v_00_u03b2_438_, lean_object* v_inst_439_, lean_object* v_sm_440_, lean_object* v_name_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Std_StreamMap_get_x3f___redArg(v_inst_439_, v_sm_440_, v_name_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(lean_object* v_pred_443_, lean_object* v_as_444_, size_t v_i_445_, size_t v_stop_446_, lean_object* v_b_447_){
_start:
{
lean_object* v___y_449_; uint8_t v___x_453_; 
v___x_453_ = lean_usize_dec_eq(v_i_445_, v_stop_446_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v_fst_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_454_ = lean_array_uget_borrowed(v_as_444_, v_i_445_);
v_fst_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc_ref(v_pred_443_);
lean_inc(v_fst_455_);
v___x_456_ = lean_apply_1(v_pred_443_, v_fst_455_);
v___x_457_ = lean_unbox(v___x_456_);
if (v___x_457_ == 0)
{
v___y_449_ = v_b_447_;
goto v___jp_448_;
}
else
{
lean_object* v___x_458_; 
lean_inc(v___x_454_);
v___x_458_ = lean_array_push(v_b_447_, v___x_454_);
v___y_449_ = v___x_458_;
goto v___jp_448_;
}
}
else
{
lean_dec_ref(v_pred_443_);
return v_b_447_;
}
v___jp_448_:
{
size_t v___x_450_; size_t v___x_451_; 
v___x_450_ = ((size_t)1ULL);
v___x_451_ = lean_usize_add(v_i_445_, v___x_450_);
v_i_445_ = v___x_451_;
v_b_447_ = v___y_449_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg___boxed(lean_object* v_pred_459_, lean_object* v_as_460_, lean_object* v_i_461_, lean_object* v_stop_462_, lean_object* v_b_463_){
_start:
{
size_t v_i_boxed_464_; size_t v_stop_boxed_465_; lean_object* v_res_466_; 
v_i_boxed_464_ = lean_unbox_usize(v_i_461_);
lean_dec(v_i_461_);
v_stop_boxed_465_ = lean_unbox_usize(v_stop_462_);
lean_dec(v_stop_462_);
v_res_466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(v_pred_459_, v_as_460_, v_i_boxed_464_, v_stop_boxed_465_, v_b_463_);
lean_dec_ref(v_as_460_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_filterByName___redArg(lean_object* v_sm_467_, lean_object* v_pred_468_){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_469_ = lean_unsigned_to_nat(0u);
v___x_470_ = lean_array_get_size(v_sm_467_);
v___x_471_ = ((lean_object*)(l_Std_StreamMap_empty___closed__0));
v___x_472_ = lean_nat_dec_lt(v___x_469_, v___x_470_);
if (v___x_472_ == 0)
{
lean_dec_ref(v_pred_468_);
return v___x_471_;
}
else
{
uint8_t v___x_473_; 
v___x_473_ = lean_nat_dec_le(v___x_470_, v___x_470_);
if (v___x_473_ == 0)
{
if (v___x_472_ == 0)
{
lean_dec_ref(v_pred_468_);
return v___x_471_;
}
else
{
size_t v___x_474_; size_t v___x_475_; lean_object* v___x_476_; 
v___x_474_ = ((size_t)0ULL);
v___x_475_ = lean_usize_of_nat(v___x_470_);
v___x_476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(v_pred_468_, v_sm_467_, v___x_474_, v___x_475_, v___x_471_);
return v___x_476_;
}
}
else
{
size_t v___x_477_; size_t v___x_478_; lean_object* v___x_479_; 
v___x_477_ = ((size_t)0ULL);
v___x_478_ = lean_usize_of_nat(v___x_470_);
v___x_479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(v_pred_468_, v_sm_467_, v___x_477_, v___x_478_, v___x_471_);
return v___x_479_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_filterByName___redArg___boxed(lean_object* v_sm_480_, lean_object* v_pred_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_StreamMap_filterByName___redArg(v_sm_480_, v_pred_481_);
lean_dec_ref(v_sm_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_filterByName(lean_object* v_00_u03b1_483_, lean_object* v_00_u03b2_484_, lean_object* v_sm_485_, lean_object* v_pred_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Std_StreamMap_filterByName___redArg(v_sm_485_, v_pred_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_filterByName___boxed(lean_object* v_00_u03b1_488_, lean_object* v_00_u03b2_489_, lean_object* v_sm_490_, lean_object* v_pred_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Std_StreamMap_filterByName(v_00_u03b1_488_, v_00_u03b2_489_, v_sm_490_, v_pred_491_);
lean_dec_ref(v_sm_490_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0(lean_object* v_00_u03b1_493_, lean_object* v_00_u03b2_494_, lean_object* v_pred_495_, lean_object* v_as_496_, size_t v_i_497_, size_t v_stop_498_, lean_object* v_b_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(v_pred_495_, v_as_496_, v_i_497_, v_stop_498_, v_b_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___boxed(lean_object* v_00_u03b1_501_, lean_object* v_00_u03b2_502_, lean_object* v_pred_503_, lean_object* v_as_504_, lean_object* v_i_505_, lean_object* v_stop_506_, lean_object* v_b_507_){
_start:
{
size_t v_i_boxed_508_; size_t v_stop_boxed_509_; lean_object* v_res_510_; 
v_i_boxed_508_ = lean_unbox_usize(v_i_505_);
lean_dec(v_i_505_);
v_stop_boxed_509_ = lean_unbox_usize(v_stop_506_);
lean_dec(v_stop_506_);
v_res_510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0(v_00_u03b1_501_, v_00_u03b2_502_, v_pred_503_, v_as_504_, v_i_boxed_508_, v_stop_boxed_509_, v_b_507_);
lean_dec_ref(v_as_504_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg(size_t v_sz_511_, size_t v_i_512_, lean_object* v_bs_513_){
_start:
{
uint8_t v___x_514_; 
v___x_514_ = lean_usize_dec_lt(v_i_512_, v_sz_511_);
if (v___x_514_ == 0)
{
return v_bs_513_;
}
else
{
lean_object* v_v_515_; lean_object* v_snd_516_; lean_object* v_fst_517_; lean_object* v_fst_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_531_; 
v_v_515_ = lean_array_uget_borrowed(v_bs_513_, v_i_512_);
v_snd_516_ = lean_ctor_get(v_v_515_, 1);
lean_inc(v_snd_516_);
v_fst_517_ = lean_ctor_get(v_v_515_, 0);
lean_inc(v_fst_517_);
v_fst_518_ = lean_ctor_get(v_snd_516_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v_snd_516_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; 
v_unused_532_ = lean_ctor_get(v_snd_516_, 1);
lean_dec(v_unused_532_);
v___x_520_ = v_snd_516_;
v_isShared_521_ = v_isSharedCheck_531_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_fst_518_);
lean_dec(v_snd_516_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_531_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; lean_object* v_bs_x27_523_; lean_object* v___x_525_; 
v___x_522_ = lean_unsigned_to_nat(0u);
v_bs_x27_523_ = lean_array_uset(v_bs_513_, v_i_512_, v___x_522_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 1, v_fst_518_);
lean_ctor_set(v___x_520_, 0, v_fst_517_);
v___x_525_ = v___x_520_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_fst_517_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_fst_518_);
v___x_525_ = v_reuseFailAlloc_530_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
size_t v___x_526_; size_t v___x_527_; lean_object* v___x_528_; 
v___x_526_ = ((size_t)1ULL);
v___x_527_ = lean_usize_add(v_i_512_, v___x_526_);
v___x_528_ = lean_array_uset(v_bs_x27_523_, v_i_512_, v___x_525_);
v_i_512_ = v___x_527_;
v_bs_513_ = v___x_528_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg___boxed(lean_object* v_sz_533_, lean_object* v_i_534_, lean_object* v_bs_535_){
_start:
{
size_t v_sz_boxed_536_; size_t v_i_boxed_537_; lean_object* v_res_538_; 
v_sz_boxed_536_ = lean_unbox_usize(v_sz_533_);
lean_dec(v_sz_533_);
v_i_boxed_537_ = lean_unbox_usize(v_i_534_);
lean_dec(v_i_534_);
v_res_538_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg(v_sz_boxed_536_, v_i_boxed_537_, v_bs_535_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_toArray___redArg(lean_object* v_sm_539_){
_start:
{
size_t v_sz_540_; size_t v___x_541_; lean_object* v___x_542_; 
v_sz_540_ = lean_array_size(v_sm_539_);
v___x_541_ = ((size_t)0ULL);
v___x_542_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg(v_sz_540_, v___x_541_, v_sm_539_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_toArray(lean_object* v_00_u03b1_543_, lean_object* v_00_u03b2_544_, lean_object* v_sm_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Std_StreamMap_toArray___redArg(v_sm_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0(lean_object* v_00_u03b1_547_, lean_object* v_00_u03b2_548_, size_t v_sz_549_, size_t v_i_550_, lean_object* v_bs_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg(v_sz_549_, v_i_550_, v_bs_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___boxed(lean_object* v_00_u03b1_553_, lean_object* v_00_u03b2_554_, lean_object* v_sz_555_, lean_object* v_i_556_, lean_object* v_bs_557_){
_start:
{
size_t v_sz_boxed_558_; size_t v_i_boxed_559_; lean_object* v_res_560_; 
v_sz_boxed_558_ = lean_unbox_usize(v_sz_555_);
lean_dec(v_sz_555_);
v_i_boxed_559_ = lean_unbox_usize(v_i_556_);
lean_dec(v_i_556_);
v_res_560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0(v_00_u03b1_553_, v_00_u03b2_554_, v_sz_boxed_558_, v_i_boxed_559_, v_bs_557_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(lean_object* v_as_561_, size_t v_i_562_, size_t v_stop_563_, lean_object* v_b_564_){
_start:
{
uint8_t v___x_566_; 
v___x_566_ = lean_usize_dec_eq(v_i_562_, v_stop_563_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v_snd_568_; lean_object* v_snd_569_; lean_object* v___x_570_; 
v___x_567_ = lean_array_uget_borrowed(v_as_561_, v_i_562_);
v_snd_568_ = lean_ctor_get(v___x_567_, 1);
v_snd_569_ = lean_ctor_get(v_snd_568_, 1);
lean_inc(v_snd_569_);
v___x_570_ = lean_apply_1(v_snd_569_, lean_box(0));
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; size_t v___x_572_; size_t v___x_573_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
lean_dec_ref(v___x_570_);
v___x_572_ = ((size_t)1ULL);
v___x_573_ = lean_usize_add(v_i_562_, v___x_572_);
v_i_562_ = v___x_573_;
v_b_564_ = v_a_571_;
goto _start;
}
else
{
return v___x_570_;
}
}
else
{
lean_object* v___x_575_; 
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v_b_564_);
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg___boxed(lean_object* v_as_576_, lean_object* v_i_577_, lean_object* v_stop_578_, lean_object* v_b_579_, lean_object* v___y_580_){
_start:
{
size_t v_i_boxed_581_; size_t v_stop_boxed_582_; lean_object* v_res_583_; 
v_i_boxed_581_ = lean_unbox_usize(v_i_577_);
lean_dec(v_i_577_);
v_stop_boxed_582_ = lean_unbox_usize(v_stop_578_);
lean_dec(v_stop_578_);
v_res_583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(v_as_576_, v_i_boxed_581_, v_stop_boxed_582_, v_b_579_);
lean_dec_ref(v_as_576_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_close___redArg(lean_object* v_sm_584_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_array_get_size(v_sm_584_);
v___x_588_ = lean_box(0);
v___x_589_ = lean_nat_dec_lt(v___x_586_, v___x_587_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_588_);
return v___x_590_;
}
else
{
uint8_t v___x_591_; 
v___x_591_ = lean_nat_dec_le(v___x_587_, v___x_587_);
if (v___x_591_ == 0)
{
if (v___x_589_ == 0)
{
lean_object* v___x_592_; 
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_588_);
return v___x_592_;
}
else
{
size_t v___x_593_; size_t v___x_594_; lean_object* v___x_595_; 
v___x_593_ = ((size_t)0ULL);
v___x_594_ = lean_usize_of_nat(v___x_587_);
v___x_595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(v_sm_584_, v___x_593_, v___x_594_, v___x_588_);
return v___x_595_;
}
}
else
{
size_t v___x_596_; size_t v___x_597_; lean_object* v___x_598_; 
v___x_596_ = ((size_t)0ULL);
v___x_597_ = lean_usize_of_nat(v___x_587_);
v___x_598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(v_sm_584_, v___x_596_, v___x_597_, v___x_588_);
return v___x_598_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_close___redArg___boxed(lean_object* v_sm_599_, lean_object* v_a_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Std_StreamMap_close___redArg(v_sm_599_);
lean_dec_ref(v_sm_599_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_close(lean_object* v_00_u03b1_602_, lean_object* v_00_u03b2_603_, lean_object* v_sm_604_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Std_StreamMap_close___redArg(v_sm_604_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_close___boxed(lean_object* v_00_u03b1_607_, lean_object* v_00_u03b2_608_, lean_object* v_sm_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Std_StreamMap_close(v_00_u03b1_607_, v_00_u03b2_608_, v_sm_609_);
lean_dec_ref(v_sm_609_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0(lean_object* v_00_u03b1_612_, lean_object* v_00_u03b2_613_, lean_object* v_as_614_, size_t v_i_615_, size_t v_stop_616_, lean_object* v_b_617_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(v_as_614_, v_i_615_, v_stop_616_, v_b_617_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___boxed(lean_object* v_00_u03b1_620_, lean_object* v_00_u03b2_621_, lean_object* v_as_622_, lean_object* v_i_623_, lean_object* v_stop_624_, lean_object* v_b_625_, lean_object* v___y_626_){
_start:
{
size_t v_i_boxed_627_; size_t v_stop_boxed_628_; lean_object* v_res_629_; 
v_i_boxed_627_ = lean_unbox_usize(v_i_623_);
lean_dec(v_i_623_);
v_stop_boxed_628_ = lean_unbox_usize(v_stop_624_);
lean_dec(v_stop_624_);
v_res_629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0(v_00_u03b1_620_, v_00_u03b2_621_, v_as_622_, v_i_boxed_627_, v_stop_boxed_628_, v_b_625_);
lean_dec_ref(v_as_622_);
return v_res_629_;
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
