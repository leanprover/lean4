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
static const lean_array_object l_Std_StreamMap_empty___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_StreamMap_empty___redArg___closed__0 = (const lean_object*)&l_Std_StreamMap_empty___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_StreamMap_empty___redArg();
LEAN_EXPORT lean_object* l_Std_StreamMap_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_StreamMap_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_StreamMap_empty___closed__0;
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
LEAN_EXPORT lean_object* l_Std_StreamMap_empty___redArg(){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = ((lean_object*)(l_Std_StreamMap_empty___redArg___closed__0));
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_empty___redArg___boxed(lean_object* v___dummy_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Std_StreamMap_empty___redArg();
return v_res_31_;
}
}
static lean_object* _init_l_Std_StreamMap_empty___closed__0(void){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Std_StreamMap_empty___redArg();
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_empty(lean_object* v_00_u03b2_33_, lean_object* v_00_u03b1_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lean_obj_once(&l_Std_StreamMap_empty___closed__0, &l_Std_StreamMap_empty___closed__0_once, _init_l_Std_StreamMap_empty___closed__0);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_register___redArg___lam__0(lean_object* v_inst_36_, lean_object* v_name_37_, lean_object* v_x1_38_, lean_object* v_x2_39_){
_start:
{
lean_object* v_fst_40_; lean_object* v___x_41_; uint8_t v___x_42_; 
v_fst_40_ = lean_ctor_get(v_x2_39_, 0);
lean_inc(v_fst_40_);
v___x_41_ = lean_apply_2(v_inst_36_, v_fst_40_, v_name_37_);
v___x_42_ = lean_unbox(v___x_41_);
if (v___x_42_ == 0)
{
lean_object* v___x_43_; 
v___x_43_ = lean_array_push(v_x1_38_, v_x2_39_);
return v___x_43_;
}
else
{
lean_dec_ref(v_x2_39_);
return v_x1_38_;
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_register___redArg(lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_sm_65_, lean_object* v_name_66_, lean_object* v_reader_67_){
_start:
{
lean_object* v_next_68_; lean_object* v_stop_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_91_; 
v_next_68_ = lean_ctor_get(v_inst_64_, 0);
v_stop_69_ = lean_ctor_get(v_inst_64_, 1);
v_isSharedCheck_91_ = !lean_is_exclusive(v_inst_64_);
if (v_isSharedCheck_91_ == 0)
{
v___x_71_ = v_inst_64_;
v_isShared_72_ = v_isSharedCheck_91_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_stop_69_);
lean_inc(v_next_68_);
lean_dec(v_inst_64_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_91_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v_newSelector_73_; lean_object* v___y_75_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
lean_inc(v_reader_67_);
v_newSelector_73_ = lean_apply_1(v_next_68_, v_reader_67_);
v___x_82_ = lean_unsigned_to_nat(0u);
v___x_83_ = lean_array_get_size(v_sm_65_);
v___x_84_ = ((lean_object*)(l_Std_StreamMap_empty___redArg___closed__0));
v___x_85_ = ((lean_object*)(l_Std_StreamMap_register___redArg___closed__9));
v___x_86_ = lean_nat_dec_lt(v___x_82_, v___x_83_);
if (v___x_86_ == 0)
{
lean_dec_ref(v_sm_65_);
lean_dec_ref(v_inst_63_);
v___y_75_ = v___x_84_;
goto v___jp_74_;
}
else
{
lean_object* v___f_87_; size_t v___x_88_; size_t v___x_89_; lean_object* v___x_90_; 
lean_inc(v_name_66_);
v___f_87_ = lean_alloc_closure((void*)(l_Std_StreamMap_register___redArg___lam__0), 4, 2);
lean_closure_set(v___f_87_, 0, v_inst_63_);
lean_closure_set(v___f_87_, 1, v_name_66_);
v___x_88_ = ((size_t)0ULL);
v___x_89_ = lean_usize_of_nat(v___x_83_);
v___x_90_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_85_, v___f_87_, v_sm_65_, v___x_88_, v___x_89_, v___x_84_);
v___y_75_ = v___x_90_;
goto v___jp_74_;
}
v___jp_74_:
{
lean_object* v___x_76_; lean_object* v___x_78_; 
v___x_76_ = lean_apply_1(v_stop_69_, v_reader_67_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 1, v___x_76_);
lean_ctor_set(v___x_71_, 0, v_newSelector_73_);
v___x_78_ = v___x_71_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_newSelector_73_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v___x_76_);
v___x_78_ = v_reuseFailAlloc_81_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_79_, 0, v_name_66_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v___x_80_ = lean_array_push(v___y_75_, v___x_79_);
return v___x_80_;
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
v___x_263_ = ((lean_object*)(l_Std_StreamMap_empty___redArg___closed__0));
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
lean_object* v___f_266_; size_t v___x_267_; size_t v___x_268_; lean_object* v___x_269_; 
v___f_266_ = lean_alloc_closure((void*)(l_Std_StreamMap_register___redArg___lam__0), 4, 2);
lean_closure_set(v___f_266_, 0, v_inst_258_);
lean_closure_set(v___f_266_, 1, v_name_260_);
v___x_267_ = ((size_t)0ULL);
v___x_268_ = lean_usize_of_nat(v___x_262_);
v___x_269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_264_, v___f_266_, v_sm_259_, v___x_267_, v___x_268_, v___x_263_);
return v___x_269_;
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_unregister(lean_object* v_00_u03b1_270_, lean_object* v_00_u03b2_271_, lean_object* v_inst_272_, lean_object* v_sm_273_, lean_object* v_name_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Std_StreamMap_unregister___redArg(v_inst_272_, v_sm_273_, v_name_274_);
return v___x_275_;
}
}
LEAN_EXPORT uint8_t l_Std_StreamMap_contains___redArg___lam__0(lean_object* v_inst_276_, lean_object* v_name_277_, lean_object* v_x_278_){
_start:
{
lean_object* v_fst_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v_fst_279_ = lean_ctor_get(v_x_278_, 0);
lean_inc(v_fst_279_);
lean_dec_ref(v_x_278_);
v___x_280_ = lean_apply_2(v_inst_276_, v_fst_279_, v_name_277_);
v___x_281_ = lean_unbox(v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_contains___redArg___lam__0___boxed(lean_object* v_inst_282_, lean_object* v_name_283_, lean_object* v_x_284_){
_start:
{
uint8_t v_res_285_; lean_object* v_r_286_; 
v_res_285_ = l_Std_StreamMap_contains___redArg___lam__0(v_inst_282_, v_name_283_, v_x_284_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
LEAN_EXPORT uint8_t l_Std_StreamMap_contains___redArg(lean_object* v_inst_287_, lean_object* v_sm_288_, lean_object* v_name_289_){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = lean_array_get_size(v_sm_288_);
v___x_292_ = ((lean_object*)(l_Std_StreamMap_register___redArg___closed__9));
v___x_293_ = lean_nat_dec_lt(v___x_290_, v___x_291_);
if (v___x_293_ == 0)
{
lean_dec(v_name_289_);
lean_dec_ref(v_sm_288_);
lean_dec_ref(v_inst_287_);
return v___x_293_;
}
else
{
if (v___x_293_ == 0)
{
lean_dec(v_name_289_);
lean_dec_ref(v_sm_288_);
lean_dec_ref(v_inst_287_);
return v___x_293_;
}
else
{
lean_object* v___f_294_; size_t v___x_295_; size_t v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v___f_294_ = lean_alloc_closure((void*)(l_Std_StreamMap_contains___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_294_, 0, v_inst_287_);
lean_closure_set(v___f_294_, 1, v_name_289_);
v___x_295_ = ((size_t)0ULL);
v___x_296_ = lean_usize_of_nat(v___x_291_);
v___x_297_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_292_, v___f_294_, v_sm_288_, v___x_295_, v___x_296_);
v___x_298_ = lean_unbox(v___x_297_);
lean_dec(v___x_297_);
return v___x_298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_contains___redArg___boxed(lean_object* v_inst_299_, lean_object* v_sm_300_, lean_object* v_name_301_){
_start:
{
uint8_t v_res_302_; lean_object* v_r_303_; 
v_res_302_ = l_Std_StreamMap_contains___redArg(v_inst_299_, v_sm_300_, v_name_301_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
LEAN_EXPORT uint8_t l_Std_StreamMap_contains(lean_object* v_00_u03b1_304_, lean_object* v_00_u03b2_305_, lean_object* v_inst_306_, lean_object* v_sm_307_, lean_object* v_name_308_){
_start:
{
uint8_t v___x_309_; 
v___x_309_ = l_Std_StreamMap_contains___redArg(v_inst_306_, v_sm_307_, v_name_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_contains___boxed(lean_object* v_00_u03b1_310_, lean_object* v_00_u03b2_311_, lean_object* v_inst_312_, lean_object* v_sm_313_, lean_object* v_name_314_){
_start:
{
uint8_t v_res_315_; lean_object* v_r_316_; 
v_res_315_ = l_Std_StreamMap_contains(v_00_u03b1_310_, v_00_u03b2_311_, v_inst_312_, v_sm_313_, v_name_314_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_size___redArg(lean_object* v_sm_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = lean_array_get_size(v_sm_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_size___redArg___boxed(lean_object* v_sm_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Std_StreamMap_size___redArg(v_sm_319_);
lean_dec_ref(v_sm_319_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_size(lean_object* v_00_u03b1_321_, lean_object* v_00_u03b2_322_, lean_object* v_sm_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = lean_array_get_size(v_sm_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_size___boxed(lean_object* v_00_u03b1_325_, lean_object* v_00_u03b2_326_, lean_object* v_sm_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Std_StreamMap_size(v_00_u03b1_325_, v_00_u03b2_326_, v_sm_327_);
lean_dec_ref(v_sm_327_);
return v_res_328_;
}
}
LEAN_EXPORT uint8_t l_Std_StreamMap_isEmpty___redArg(lean_object* v_sm_329_){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_330_ = lean_array_get_size(v_sm_329_);
v___x_331_ = lean_unsigned_to_nat(0u);
v___x_332_ = lean_nat_dec_eq(v___x_330_, v___x_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_isEmpty___redArg___boxed(lean_object* v_sm_333_){
_start:
{
uint8_t v_res_334_; lean_object* v_r_335_; 
v_res_334_ = l_Std_StreamMap_isEmpty___redArg(v_sm_333_);
lean_dec_ref(v_sm_333_);
v_r_335_ = lean_box(v_res_334_);
return v_r_335_;
}
}
LEAN_EXPORT uint8_t l_Std_StreamMap_isEmpty(lean_object* v_00_u03b1_336_, lean_object* v_00_u03b2_337_, lean_object* v_sm_338_){
_start:
{
uint8_t v___x_339_; 
v___x_339_ = l_Std_StreamMap_isEmpty___redArg(v_sm_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_isEmpty___boxed(lean_object* v_00_u03b1_340_, lean_object* v_00_u03b2_341_, lean_object* v_sm_342_){
_start:
{
uint8_t v_res_343_; lean_object* v_r_344_; 
v_res_343_ = l_Std_StreamMap_isEmpty(v_00_u03b1_340_, v_00_u03b2_341_, v_sm_342_);
lean_dec_ref(v_sm_342_);
v_r_344_ = lean_box(v_res_343_);
return v_r_344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg(size_t v_sz_345_, size_t v_i_346_, lean_object* v_bs_347_){
_start:
{
uint8_t v___x_348_; 
v___x_348_ = lean_usize_dec_lt(v_i_346_, v_sz_345_);
if (v___x_348_ == 0)
{
return v_bs_347_;
}
else
{
lean_object* v_v_349_; lean_object* v_fst_350_; lean_object* v___x_351_; lean_object* v_bs_x27_352_; size_t v___x_353_; size_t v___x_354_; lean_object* v___x_355_; 
v_v_349_ = lean_array_uget_borrowed(v_bs_347_, v_i_346_);
v_fst_350_ = lean_ctor_get(v_v_349_, 0);
lean_inc(v_fst_350_);
v___x_351_ = lean_unsigned_to_nat(0u);
v_bs_x27_352_ = lean_array_uset(v_bs_347_, v_i_346_, v___x_351_);
v___x_353_ = ((size_t)1ULL);
v___x_354_ = lean_usize_add(v_i_346_, v___x_353_);
v___x_355_ = lean_array_uset(v_bs_x27_352_, v_i_346_, v_fst_350_);
v_i_346_ = v___x_354_;
v_bs_347_ = v___x_355_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg___boxed(lean_object* v_sz_357_, lean_object* v_i_358_, lean_object* v_bs_359_){
_start:
{
size_t v_sz_boxed_360_; size_t v_i_boxed_361_; lean_object* v_res_362_; 
v_sz_boxed_360_ = lean_unbox_usize(v_sz_357_);
lean_dec(v_sz_357_);
v_i_boxed_361_ = lean_unbox_usize(v_i_358_);
lean_dec(v_i_358_);
v_res_362_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg(v_sz_boxed_360_, v_i_boxed_361_, v_bs_359_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_keys___redArg(lean_object* v_sm_363_){
_start:
{
size_t v_sz_364_; size_t v___x_365_; lean_object* v___x_366_; 
v_sz_364_ = lean_array_size(v_sm_363_);
v___x_365_ = ((size_t)0ULL);
v___x_366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg(v_sz_364_, v___x_365_, v_sm_363_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_keys(lean_object* v_00_u03b1_367_, lean_object* v_00_u03b2_368_, lean_object* v_sm_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Std_StreamMap_keys___redArg(v_sm_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0(lean_object* v_00_u03b1_371_, lean_object* v_00_u03b2_372_, size_t v_sz_373_, size_t v_i_374_, lean_object* v_bs_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg(v_sz_373_, v_i_374_, v_bs_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___boxed(lean_object* v_00_u03b1_377_, lean_object* v_00_u03b2_378_, lean_object* v_sz_379_, lean_object* v_i_380_, lean_object* v_bs_381_){
_start:
{
size_t v_sz_boxed_382_; size_t v_i_boxed_383_; lean_object* v_res_384_; 
v_sz_boxed_382_ = lean_unbox_usize(v_sz_379_);
lean_dec(v_sz_379_);
v_i_boxed_383_ = lean_unbox_usize(v_i_380_);
lean_dec(v_i_380_);
v_res_384_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0(v_00_u03b1_377_, v_00_u03b2_378_, v_sz_boxed_382_, v_i_boxed_383_, v_bs_381_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_get_x3f___redArg___lam__0(lean_object* v_inst_385_, lean_object* v_name_386_, lean_object* v___x_387_, lean_object* v___x_388_, lean_object* v_a_389_, lean_object* v_x_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_fst_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v_fst_392_ = lean_ctor_get(v_a_389_, 0);
lean_inc(v_fst_392_);
v___x_393_ = lean_apply_2(v_inst_385_, v_fst_392_, v_name_386_);
v___x_394_ = lean_unbox(v___x_393_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; 
lean_dec_ref(v_a_389_);
v___x_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_387_);
return v___x_395_;
}
else
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
lean_dec_ref(v___x_387_);
v___x_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_396_, 0, v_a_389_);
v___x_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v___x_388_);
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
return v___x_399_;
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_get_x3f___redArg___lam__0___boxed(lean_object* v_inst_400_, lean_object* v_name_401_, lean_object* v___x_402_, lean_object* v___x_403_, lean_object* v_a_404_, lean_object* v_x_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Std_StreamMap_get_x3f___redArg___lam__0(v_inst_400_, v_name_401_, v___x_402_, v___x_403_, v_a_404_, v_x_405_, v___y_406_);
lean_dec_ref(v___y_406_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_get_x3f___redArg(lean_object* v_inst_411_, lean_object* v_sm_412_, lean_object* v_name_413_){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___f_418_; size_t v_sz_419_; size_t v___x_420_; lean_object* v___x_421_; lean_object* v_fst_422_; 
v___x_414_ = ((lean_object*)(l_Std_StreamMap_register___redArg___closed__9));
v___x_415_ = lean_box(0);
v___x_416_ = lean_box(0);
v___x_417_ = ((lean_object*)(l_Std_StreamMap_get_x3f___redArg___closed__0));
v___f_418_ = lean_alloc_closure((void*)(l_Std_StreamMap_get_x3f___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_418_, 0, v_inst_411_);
lean_closure_set(v___f_418_, 1, v_name_413_);
lean_closure_set(v___f_418_, 2, v___x_417_);
lean_closure_set(v___f_418_, 3, v___x_416_);
v_sz_419_ = lean_array_size(v_sm_412_);
v___x_420_ = ((size_t)0ULL);
v___x_421_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_414_, v_sm_412_, v___f_418_, v_sz_419_, v___x_420_, v___x_417_);
v_fst_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_fst_422_);
lean_dec(v___x_421_);
if (lean_obj_tag(v_fst_422_) == 0)
{
return v___x_415_;
}
else
{
lean_object* v_val_423_; 
v_val_423_ = lean_ctor_get(v_fst_422_, 0);
lean_inc(v_val_423_);
lean_dec_ref_known(v_fst_422_, 1);
if (lean_obj_tag(v_val_423_) == 0)
{
return v___x_415_;
}
else
{
lean_object* v_val_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_433_; 
v_val_424_ = lean_ctor_get(v_val_423_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v_val_423_);
if (v_isSharedCheck_433_ == 0)
{
v___x_426_ = v_val_423_;
v_isShared_427_ = v_isSharedCheck_433_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_val_424_);
lean_dec(v_val_423_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_433_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v_snd_428_; lean_object* v_fst_429_; lean_object* v___x_431_; 
v_snd_428_ = lean_ctor_get(v_val_424_, 1);
lean_inc(v_snd_428_);
lean_dec(v_val_424_);
v_fst_429_ = lean_ctor_get(v_snd_428_, 0);
lean_inc(v_fst_429_);
lean_dec(v_snd_428_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v_fst_429_);
v___x_431_ = v___x_426_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_fst_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_get_x3f(lean_object* v_00_u03b1_434_, lean_object* v_00_u03b2_435_, lean_object* v_inst_436_, lean_object* v_sm_437_, lean_object* v_name_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Std_StreamMap_get_x3f___redArg(v_inst_436_, v_sm_437_, v_name_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(lean_object* v_pred_440_, lean_object* v_as_441_, size_t v_i_442_, size_t v_stop_443_, lean_object* v_b_444_){
_start:
{
lean_object* v___y_446_; uint8_t v___x_450_; 
v___x_450_ = lean_usize_dec_eq(v_i_442_, v_stop_443_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; lean_object* v_fst_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_451_ = lean_array_uget_borrowed(v_as_441_, v_i_442_);
v_fst_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc_ref(v_pred_440_);
lean_inc(v_fst_452_);
v___x_453_ = lean_apply_1(v_pred_440_, v_fst_452_);
v___x_454_ = lean_unbox(v___x_453_);
if (v___x_454_ == 0)
{
v___y_446_ = v_b_444_;
goto v___jp_445_;
}
else
{
lean_object* v___x_455_; 
lean_inc(v___x_451_);
v___x_455_ = lean_array_push(v_b_444_, v___x_451_);
v___y_446_ = v___x_455_;
goto v___jp_445_;
}
}
else
{
lean_dec_ref(v_pred_440_);
return v_b_444_;
}
v___jp_445_:
{
size_t v___x_447_; size_t v___x_448_; 
v___x_447_ = ((size_t)1ULL);
v___x_448_ = lean_usize_add(v_i_442_, v___x_447_);
v_i_442_ = v___x_448_;
v_b_444_ = v___y_446_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg___boxed(lean_object* v_pred_456_, lean_object* v_as_457_, lean_object* v_i_458_, lean_object* v_stop_459_, lean_object* v_b_460_){
_start:
{
size_t v_i_boxed_461_; size_t v_stop_boxed_462_; lean_object* v_res_463_; 
v_i_boxed_461_ = lean_unbox_usize(v_i_458_);
lean_dec(v_i_458_);
v_stop_boxed_462_ = lean_unbox_usize(v_stop_459_);
lean_dec(v_stop_459_);
v_res_463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(v_pred_456_, v_as_457_, v_i_boxed_461_, v_stop_boxed_462_, v_b_460_);
lean_dec_ref(v_as_457_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_filterByName___redArg(lean_object* v_sm_464_, lean_object* v_pred_465_){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_466_ = lean_unsigned_to_nat(0u);
v___x_467_ = lean_array_get_size(v_sm_464_);
v___x_468_ = ((lean_object*)(l_Std_StreamMap_empty___redArg___closed__0));
v___x_469_ = lean_nat_dec_lt(v___x_466_, v___x_467_);
if (v___x_469_ == 0)
{
lean_dec_ref(v_pred_465_);
return v___x_468_;
}
else
{
size_t v___x_470_; size_t v___x_471_; lean_object* v___x_472_; 
v___x_470_ = ((size_t)0ULL);
v___x_471_ = lean_usize_of_nat(v___x_467_);
v___x_472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(v_pred_465_, v_sm_464_, v___x_470_, v___x_471_, v___x_468_);
return v___x_472_;
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_filterByName___redArg___boxed(lean_object* v_sm_473_, lean_object* v_pred_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Std_StreamMap_filterByName___redArg(v_sm_473_, v_pred_474_);
lean_dec_ref(v_sm_473_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_filterByName(lean_object* v_00_u03b1_476_, lean_object* v_00_u03b2_477_, lean_object* v_sm_478_, lean_object* v_pred_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Std_StreamMap_filterByName___redArg(v_sm_478_, v_pred_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_filterByName___boxed(lean_object* v_00_u03b1_481_, lean_object* v_00_u03b2_482_, lean_object* v_sm_483_, lean_object* v_pred_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Std_StreamMap_filterByName(v_00_u03b1_481_, v_00_u03b2_482_, v_sm_483_, v_pred_484_);
lean_dec_ref(v_sm_483_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0(lean_object* v_00_u03b1_486_, lean_object* v_00_u03b2_487_, lean_object* v_pred_488_, lean_object* v_as_489_, size_t v_i_490_, size_t v_stop_491_, lean_object* v_b_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(v_pred_488_, v_as_489_, v_i_490_, v_stop_491_, v_b_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___boxed(lean_object* v_00_u03b1_494_, lean_object* v_00_u03b2_495_, lean_object* v_pred_496_, lean_object* v_as_497_, lean_object* v_i_498_, lean_object* v_stop_499_, lean_object* v_b_500_){
_start:
{
size_t v_i_boxed_501_; size_t v_stop_boxed_502_; lean_object* v_res_503_; 
v_i_boxed_501_ = lean_unbox_usize(v_i_498_);
lean_dec(v_i_498_);
v_stop_boxed_502_ = lean_unbox_usize(v_stop_499_);
lean_dec(v_stop_499_);
v_res_503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0(v_00_u03b1_494_, v_00_u03b2_495_, v_pred_496_, v_as_497_, v_i_boxed_501_, v_stop_boxed_502_, v_b_500_);
lean_dec_ref(v_as_497_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg(size_t v_sz_504_, size_t v_i_505_, lean_object* v_bs_506_){
_start:
{
uint8_t v___x_507_; 
v___x_507_ = lean_usize_dec_lt(v_i_505_, v_sz_504_);
if (v___x_507_ == 0)
{
return v_bs_506_;
}
else
{
lean_object* v_v_508_; lean_object* v_snd_509_; lean_object* v_fst_510_; lean_object* v_fst_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_524_; 
v_v_508_ = lean_array_uget_borrowed(v_bs_506_, v_i_505_);
v_snd_509_ = lean_ctor_get(v_v_508_, 1);
lean_inc(v_snd_509_);
v_fst_510_ = lean_ctor_get(v_v_508_, 0);
lean_inc(v_fst_510_);
v_fst_511_ = lean_ctor_get(v_snd_509_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v_snd_509_);
if (v_isSharedCheck_524_ == 0)
{
lean_object* v_unused_525_; 
v_unused_525_ = lean_ctor_get(v_snd_509_, 1);
lean_dec(v_unused_525_);
v___x_513_ = v_snd_509_;
v_isShared_514_ = v_isSharedCheck_524_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_fst_511_);
lean_dec(v_snd_509_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_524_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; lean_object* v_bs_x27_516_; lean_object* v___x_518_; 
v___x_515_ = lean_unsigned_to_nat(0u);
v_bs_x27_516_ = lean_array_uset(v_bs_506_, v_i_505_, v___x_515_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 1, v_fst_511_);
lean_ctor_set(v___x_513_, 0, v_fst_510_);
v___x_518_ = v___x_513_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_fst_510_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_fst_511_);
v___x_518_ = v_reuseFailAlloc_523_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
size_t v___x_519_; size_t v___x_520_; lean_object* v___x_521_; 
v___x_519_ = ((size_t)1ULL);
v___x_520_ = lean_usize_add(v_i_505_, v___x_519_);
v___x_521_ = lean_array_uset(v_bs_x27_516_, v_i_505_, v___x_518_);
v_i_505_ = v___x_520_;
v_bs_506_ = v___x_521_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg___boxed(lean_object* v_sz_526_, lean_object* v_i_527_, lean_object* v_bs_528_){
_start:
{
size_t v_sz_boxed_529_; size_t v_i_boxed_530_; lean_object* v_res_531_; 
v_sz_boxed_529_ = lean_unbox_usize(v_sz_526_);
lean_dec(v_sz_526_);
v_i_boxed_530_ = lean_unbox_usize(v_i_527_);
lean_dec(v_i_527_);
v_res_531_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg(v_sz_boxed_529_, v_i_boxed_530_, v_bs_528_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_toArray___redArg(lean_object* v_sm_532_){
_start:
{
size_t v_sz_533_; size_t v___x_534_; lean_object* v___x_535_; 
v_sz_533_ = lean_array_size(v_sm_532_);
v___x_534_ = ((size_t)0ULL);
v___x_535_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg(v_sz_533_, v___x_534_, v_sm_532_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_toArray(lean_object* v_00_u03b1_536_, lean_object* v_00_u03b2_537_, lean_object* v_sm_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Std_StreamMap_toArray___redArg(v_sm_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0(lean_object* v_00_u03b1_540_, lean_object* v_00_u03b2_541_, size_t v_sz_542_, size_t v_i_543_, lean_object* v_bs_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg(v_sz_542_, v_i_543_, v_bs_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___boxed(lean_object* v_00_u03b1_546_, lean_object* v_00_u03b2_547_, lean_object* v_sz_548_, lean_object* v_i_549_, lean_object* v_bs_550_){
_start:
{
size_t v_sz_boxed_551_; size_t v_i_boxed_552_; lean_object* v_res_553_; 
v_sz_boxed_551_ = lean_unbox_usize(v_sz_548_);
lean_dec(v_sz_548_);
v_i_boxed_552_ = lean_unbox_usize(v_i_549_);
lean_dec(v_i_549_);
v_res_553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0(v_00_u03b1_546_, v_00_u03b2_547_, v_sz_boxed_551_, v_i_boxed_552_, v_bs_550_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(lean_object* v_as_554_, size_t v_i_555_, size_t v_stop_556_, lean_object* v_b_557_){
_start:
{
uint8_t v___x_559_; 
v___x_559_ = lean_usize_dec_eq(v_i_555_, v_stop_556_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; lean_object* v_snd_561_; lean_object* v_snd_562_; lean_object* v___x_563_; 
v___x_560_ = lean_array_uget_borrowed(v_as_554_, v_i_555_);
v_snd_561_ = lean_ctor_get(v___x_560_, 1);
v_snd_562_ = lean_ctor_get(v_snd_561_, 1);
lean_inc(v_snd_562_);
v___x_563_ = lean_apply_1(v_snd_562_, lean_box(0));
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; size_t v___x_565_; size_t v___x_566_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_564_);
lean_dec_ref_known(v___x_563_, 1);
v___x_565_ = ((size_t)1ULL);
v___x_566_ = lean_usize_add(v_i_555_, v___x_565_);
v_i_555_ = v___x_566_;
v_b_557_ = v_a_564_;
goto _start;
}
else
{
return v___x_563_;
}
}
else
{
lean_object* v___x_568_; 
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v_b_557_);
return v___x_568_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg___boxed(lean_object* v_as_569_, lean_object* v_i_570_, lean_object* v_stop_571_, lean_object* v_b_572_, lean_object* v___y_573_){
_start:
{
size_t v_i_boxed_574_; size_t v_stop_boxed_575_; lean_object* v_res_576_; 
v_i_boxed_574_ = lean_unbox_usize(v_i_570_);
lean_dec(v_i_570_);
v_stop_boxed_575_ = lean_unbox_usize(v_stop_571_);
lean_dec(v_stop_571_);
v_res_576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(v_as_569_, v_i_boxed_574_, v_stop_boxed_575_, v_b_572_);
lean_dec_ref(v_as_569_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_close___redArg(lean_object* v_sm_577_){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_579_ = lean_unsigned_to_nat(0u);
v___x_580_ = lean_array_get_size(v_sm_577_);
v___x_581_ = lean_box(0);
v___x_582_ = lean_nat_dec_lt(v___x_579_, v___x_580_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; 
v___x_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_581_);
return v___x_583_;
}
else
{
size_t v___x_584_; size_t v___x_585_; lean_object* v___x_586_; 
v___x_584_ = ((size_t)0ULL);
v___x_585_ = lean_usize_of_nat(v___x_580_);
v___x_586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(v_sm_577_, v___x_584_, v___x_585_, v___x_581_);
return v___x_586_;
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_close___redArg___boxed(lean_object* v_sm_587_, lean_object* v_a_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Std_StreamMap_close___redArg(v_sm_587_);
lean_dec_ref(v_sm_587_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_close(lean_object* v_00_u03b1_590_, lean_object* v_00_u03b2_591_, lean_object* v_sm_592_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Std_StreamMap_close___redArg(v_sm_592_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_close___boxed(lean_object* v_00_u03b1_595_, lean_object* v_00_u03b2_596_, lean_object* v_sm_597_, lean_object* v_a_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Std_StreamMap_close(v_00_u03b1_595_, v_00_u03b2_596_, v_sm_597_);
lean_dec_ref(v_sm_597_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0(lean_object* v_00_u03b1_600_, lean_object* v_00_u03b2_601_, lean_object* v_as_602_, size_t v_i_603_, size_t v_stop_604_, lean_object* v_b_605_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(v_as_602_, v_i_603_, v_stop_604_, v_b_605_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___boxed(lean_object* v_00_u03b1_608_, lean_object* v_00_u03b2_609_, lean_object* v_as_610_, lean_object* v_i_611_, lean_object* v_stop_612_, lean_object* v_b_613_, lean_object* v___y_614_){
_start:
{
size_t v_i_boxed_615_; size_t v_stop_boxed_616_; lean_object* v_res_617_; 
v_i_boxed_615_ = lean_unbox_usize(v_i_611_);
lean_dec(v_i_611_);
v_stop_boxed_616_ = lean_unbox_usize(v_stop_612_);
lean_dec(v_stop_612_);
v_res_617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0(v_00_u03b1_608_, v_00_u03b2_609_, v_as_610_, v_i_boxed_615_, v_stop_boxed_616_, v_b_613_);
lean_dec_ref(v_as_610_);
return v_res_617_;
}
}
lean_object* runtime_initialize_Std_Data(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Queue(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_IO(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sync_StreamMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
