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
lean_object* l_Std_StreamMap_empty___redArg(){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = ((lean_object*)(l_Std_StreamMap_empty___redArg___closed__0));
return v___x_29_;
}
}
LEAN_EXPORT void l_Std_StreamMap_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_30_;
v_res_30_ = l_Std_StreamMap_empty___redArg();
stack->m_obj
 = v_res_30_;
}
LEAN_EXPORT lean_object* l_Std_StreamMap_empty___redArg___boxed(lean_object* v___dummy_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Std_StreamMap_empty___redArg();
return v_res_32_;
}
}
static lean_object* _init_l_Std_StreamMap_empty___closed__0(void){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Std_StreamMap_empty___redArg();
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_empty(lean_object* v_00_u03b2_34_, lean_object* v_00_u03b1_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lean_obj_once(&l_Std_StreamMap_empty___closed__0, &l_Std_StreamMap_empty___closed__0_once, _init_l_Std_StreamMap_empty___closed__0);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_register___redArg___lam__0(lean_object* v_inst_37_, lean_object* v_name_38_, lean_object* v_x1_39_, lean_object* v_x2_40_){
_start:
{
lean_object* v_fst_41_; lean_object* v___x_42_; uint8_t v___x_43_; 
v_fst_41_ = lean_ctor_get(v_x2_40_, 0);
lean_inc(v_fst_41_);
v___x_42_ = lean_apply_2(v_inst_37_, v_fst_41_, v_name_38_);
v___x_43_ = lean_unbox(v___x_42_);
if (v___x_43_ == 0)
{
lean_object* v___x_44_; 
v___x_44_ = lean_array_push(v_x1_39_, v_x2_40_);
return v___x_44_;
}
else
{
lean_dec_ref(v_x2_40_);
return v_x1_39_;
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_register___redArg(lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_sm_66_, lean_object* v_name_67_, lean_object* v_reader_68_){
_start:
{
lean_object* v_next_69_; lean_object* v_stop_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_96_; 
v_next_69_ = lean_ctor_get(v_inst_65_, 0);
v_stop_70_ = lean_ctor_get(v_inst_65_, 1);
v_isSharedCheck_96_ = !lean_is_exclusive(v_inst_65_);
if (v_isSharedCheck_96_ == 0)
{
v___x_72_ = v_inst_65_;
v_isShared_73_ = v_isSharedCheck_96_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_stop_70_);
lean_inc(v_next_69_);
lean_dec(v_inst_65_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_96_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v_newSelector_74_; lean_object* v___y_76_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
lean_inc(v_reader_68_);
v_newSelector_74_ = lean_apply_1(v_next_69_, v_reader_68_);
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = lean_array_get_size(v_sm_66_);
v___x_85_ = ((lean_object*)(l_Std_StreamMap_empty___redArg___closed__0));
v___x_86_ = ((lean_object*)(l_Std_StreamMap_register___redArg___closed__9));
v___x_87_ = lean_nat_dec_lt(v___x_83_, v___x_84_);
if (v___x_87_ == 0)
{
lean_dec_ref(v_sm_66_);
lean_dec_ref(v_inst_64_);
v___y_76_ = v___x_85_;
goto v___jp_75_;
}
else
{
lean_object* v___f_88_; uint8_t v___x_89_; 
lean_inc(v_name_67_);
v___f_88_ = lean_alloc_closure((void*)(l_Std_StreamMap_register___redArg___lam__0), 4, 2);
lean_closure_set(v___f_88_, 0, v_inst_64_);
lean_closure_set(v___f_88_, 1, v_name_67_);
v___x_89_ = lean_nat_dec_le(v___x_84_, v___x_84_);
if (v___x_89_ == 0)
{
if (v___x_87_ == 0)
{
lean_dec_ref(v___f_88_);
lean_dec_ref(v_sm_66_);
v___y_76_ = v___x_85_;
goto v___jp_75_;
}
else
{
size_t v___x_90_; size_t v___x_91_; lean_object* v___x_92_; 
v___x_90_ = ((size_t)0ULL);
v___x_91_ = lean_usize_of_nat(v___x_84_);
v___x_92_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_86_, v___f_88_, v_sm_66_, v___x_90_, v___x_91_, v___x_85_);
v___y_76_ = v___x_92_;
goto v___jp_75_;
}
}
else
{
size_t v___x_93_; size_t v___x_94_; lean_object* v___x_95_; 
v___x_93_ = ((size_t)0ULL);
v___x_94_ = lean_usize_of_nat(v___x_84_);
v___x_95_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_86_, v___f_88_, v_sm_66_, v___x_93_, v___x_94_, v___x_85_);
v___y_76_ = v___x_95_;
goto v___jp_75_;
}
}
v___jp_75_:
{
lean_object* v___x_77_; lean_object* v___x_79_; 
v___x_77_ = lean_apply_1(v_stop_70_, v_reader_68_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 1, v___x_77_);
lean_ctor_set(v___x_72_, 0, v_newSelector_74_);
v___x_79_ = v___x_72_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_newSelector_74_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v___x_77_);
v___x_79_ = v_reuseFailAlloc_82_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_80_, 0, v_name_67_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = lean_array_push(v___y_76_, v___x_80_);
return v___x_81_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_register(lean_object* v_00_u03b1_97_, lean_object* v_t_98_, lean_object* v_00_u03b2_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_sm_102_, lean_object* v_name_103_, lean_object* v_reader_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Std_StreamMap_register___redArg(v_inst_100_, v_inst_101_, v_sm_102_, v_name_103_, v_reader_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_ofArray___redArg___lam__0(lean_object* v_x_106_){
_start:
{
lean_object* v_fst_107_; lean_object* v_snd_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_116_; 
v_fst_107_ = lean_ctor_get(v_x_106_, 0);
v_snd_108_ = lean_ctor_get(v_x_106_, 1);
v_isSharedCheck_116_ = !lean_is_exclusive(v_x_106_);
if (v_isSharedCheck_116_ == 0)
{
v___x_110_ = v_x_106_;
v_isShared_111_ = v_isSharedCheck_116_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_snd_108_);
lean_inc(v_fst_107_);
lean_dec(v_x_106_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_116_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_112_ = l_Std_AnyAsyncStream_getSelector___redArg(v_snd_108_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 1, v___x_112_);
v___x_114_ = v___x_110_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_fst_107_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v___x_112_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_ofArray___redArg(lean_object* v_streams_118_){
_start:
{
lean_object* v___f_119_; lean_object* v___x_120_; size_t v_sz_121_; size_t v___x_122_; lean_object* v_arrayOfSelectors_123_; 
v___f_119_ = ((lean_object*)(l_Std_StreamMap_ofArray___redArg___closed__0));
v___x_120_ = ((lean_object*)(l_Std_StreamMap_register___redArg___closed__9));
v_sz_121_ = lean_array_size(v_streams_118_);
v___x_122_ = ((size_t)0ULL);
v_arrayOfSelectors_123_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_120_, v___f_119_, v_sz_121_, v___x_122_, v_streams_118_);
return v_arrayOfSelectors_123_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_ofArray(lean_object* v_00_u03b1_124_, lean_object* v_00_u03b2_125_, lean_object* v_inst_126_, lean_object* v_streams_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Std_StreamMap_ofArray___redArg(v_streams_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_ofArray___boxed(lean_object* v_00_u03b1_129_, lean_object* v_00_u03b2_130_, lean_object* v_inst_131_, lean_object* v_streams_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Std_StreamMap_ofArray(v_00_u03b1_129_, v_00_u03b2_130_, v_inst_131_, v_streams_132_);
lean_dec_ref(v_inst_131_);
return v_res_133_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___lam__0(lean_object* v_fst_134_, lean_object* v_x_135_){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v_fst_134_);
lean_ctor_set(v___x_137_, 1, v_x_135_);
v___x_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
v___x_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_134_ = stack[0].m_obj;
lean_object* v_x_135_ = stack[1].m_obj;
lean_object* v_res_140_;
v_res_140_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___lam__0(v_fst_134_, v_x_135_);
stack->m_obj
 = v_res_140_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___lam__0___boxed(lean_object* v_fst_141_, lean_object* v_x_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___lam__0(v_fst_141_, v_x_142_);
return v_res_144_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(size_t v_sz_145_, size_t v_i_146_, lean_object* v_bs_147_){
_start:
{
uint8_t v___x_148_; 
v___x_148_ = lean_usize_dec_lt(v_i_146_, v_sz_145_);
if (v___x_148_ == 0)
{
return v_bs_147_;
}
else
{
lean_object* v_v_149_; lean_object* v_snd_150_; lean_object* v_fst_151_; lean_object* v_fst_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_166_; 
v_v_149_ = lean_array_uget_borrowed(v_bs_147_, v_i_146_);
v_snd_150_ = lean_ctor_get(v_v_149_, 1);
lean_inc(v_snd_150_);
v_fst_151_ = lean_ctor_get(v_v_149_, 0);
lean_inc(v_fst_151_);
v_fst_152_ = lean_ctor_get(v_snd_150_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v_snd_150_);
if (v_isSharedCheck_166_ == 0)
{
lean_object* v_unused_167_; 
v_unused_167_ = lean_ctor_get(v_snd_150_, 1);
lean_dec(v_unused_167_);
v___x_154_ = v_snd_150_;
v_isShared_155_ = v_isSharedCheck_166_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_fst_152_);
lean_dec(v_snd_150_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_166_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_156_; lean_object* v_bs_x27_157_; lean_object* v___f_158_; lean_object* v___x_160_; 
v___x_156_ = lean_unsigned_to_nat(0u);
v_bs_x27_157_ = lean_array_uset(v_bs_147_, v_i_146_, v___x_156_);
v___f_158_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_158_, 0, v_fst_151_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 1, v___f_158_);
v___x_160_ = v___x_154_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_fst_152_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v___f_158_);
v___x_160_ = v_reuseFailAlloc_165_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
size_t v___x_161_; size_t v___x_162_; lean_object* v___x_163_; 
v___x_161_ = ((size_t)1ULL);
v___x_162_ = lean_usize_add(v_i_146_, v___x_161_);
v___x_163_ = lean_array_uset(v_bs_x27_157_, v_i_146_, v___x_160_);
v_i_146_ = v___x_162_;
v_bs_147_ = v___x_163_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_145_ = stack[0].m_num;
size_t v_i_146_ = stack[1].m_num;
lean_object* v_bs_147_ = stack[2].m_obj;
lean_object* v_res_168_;
v_res_168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(v_sz_145_, v_i_146_, v_bs_147_);
stack->m_obj
 = v_res_168_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___boxed(lean_object* v_sz_169_, lean_object* v_i_170_, lean_object* v_bs_171_){
_start:
{
size_t v_sz_boxed_172_; size_t v_i_boxed_173_; lean_object* v_res_174_; 
v_sz_boxed_172_ = lean_unbox_usize(v_sz_169_);
lean_dec(v_sz_169_);
v_i_boxed_173_ = lean_unbox_usize(v_i_170_);
lean_dec(v_i_170_);
v_res_174_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(v_sz_boxed_172_, v_i_boxed_173_, v_bs_171_);
return v_res_174_;
}
}
lean_object* l_Std_StreamMap_selector___redArg(lean_object* v_stream_175_){
_start:
{
lean_object* v_val_178_; size_t v_sz_180_; size_t v___x_181_; lean_object* v_selectables_182_; lean_object* v___x_183_; 
v_sz_180_ = lean_array_size(v_stream_175_);
v___x_181_ = ((size_t)0ULL);
v_selectables_182_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(v_sz_180_, v___x_181_, v_stream_175_);
v___x_183_ = l_Std_Async_Selectable_combine___redArg(v_selectables_182_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_191_ == 0)
{
v___x_186_ = v___x_183_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_183_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
lean_ctor_set_tag(v___x_186_, 1);
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_a_184_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
v_val_178_ = v___x_189_;
goto v___jp_177_;
}
}
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
v_a_192_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_183_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_183_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
lean_ctor_set_tag(v___x_194_, 0);
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
v_val_178_ = v___x_197_;
goto v___jp_177_;
}
}
}
v___jp_177_:
{
lean_object* v___x_179_; 
v___x_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_179_, 0, v_val_178_);
return v___x_179_;
}
}
}
LEAN_EXPORT void l_Std_StreamMap_selector___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_175_ = stack[0].m_obj;
lean_object* v_res_200_;
v_res_200_ = l_Std_StreamMap_selector___redArg(v_stream_175_);
stack->m_obj
 = v_res_200_;
}
LEAN_EXPORT lean_object* l_Std_StreamMap_selector___redArg___boxed(lean_object* v_stream_201_, lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Std_StreamMap_selector___redArg(v_stream_201_);
return v_res_203_;
}
}
lean_object* l_Std_StreamMap_selector(lean_object* v_00_u03b1_204_, lean_object* v_00_u03b2_205_, lean_object* v_stream_206_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Std_StreamMap_selector___redArg(v_stream_206_);
return v___x_208_;
}
}
LEAN_EXPORT void l_Std_StreamMap_selector_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_206_ = stack[2].m_obj;
lean_object* v_res_209_;
v_res_209_ = l_Std_StreamMap_selector(lean_box(0), lean_box(0), v_stream_206_);
stack->m_obj
 = v_res_209_;
}
LEAN_EXPORT lean_object* l_Std_StreamMap_selector___boxed(lean_object* v_00_u03b1_210_, lean_object* v_00_u03b2_211_, lean_object* v_stream_212_, lean_object* v_a_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Std_StreamMap_selector(v_00_u03b1_210_, v_00_u03b2_211_, v_stream_212_);
return v_res_214_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0(lean_object* v_00_u03b1_215_, lean_object* v_00_u03b2_216_, size_t v_sz_217_, size_t v_i_218_, lean_object* v_bs_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(v_sz_217_, v_i_218_, v_bs_219_);
return v___x_220_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_217_ = stack[2].m_num;
size_t v_i_218_ = stack[3].m_num;
lean_object* v_bs_219_ = stack[4].m_obj;
lean_object* v_res_221_;
v_res_221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0(lean_box(0), lean_box(0), v_sz_217_, v_i_218_, v_bs_219_);
stack->m_obj
 = v_res_221_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___boxed(lean_object* v_00_u03b1_222_, lean_object* v_00_u03b2_223_, lean_object* v_sz_224_, lean_object* v_i_225_, lean_object* v_bs_226_){
_start:
{
size_t v_sz_boxed_227_; size_t v_i_boxed_228_; lean_object* v_res_229_; 
v_sz_boxed_227_ = lean_unbox_usize(v_sz_224_);
lean_dec(v_sz_224_);
v_i_boxed_228_ = lean_unbox_usize(v_i_225_);
lean_dec(v_i_225_);
v_res_229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0(v_00_u03b1_222_, v_00_u03b2_223_, v_sz_boxed_227_, v_i_boxed_228_, v_bs_226_);
return v_res_229_;
}
}
lean_object* l_Std_StreamMap_recv___redArg(lean_object* v_stream_230_){
_start:
{
size_t v_sz_232_; size_t v___x_233_; lean_object* v_selectables_234_; lean_object* v___x_235_; 
v_sz_232_ = lean_array_size(v_stream_230_);
v___x_233_ = ((size_t)0ULL);
v_selectables_234_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(v_sz_232_, v___x_233_, v_stream_230_);
v___x_235_ = l_Std_Async_Selectable_one___redArg(v_selectables_234_);
return v___x_235_;
}
}
LEAN_EXPORT void l_Std_StreamMap_recv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_230_ = stack[0].m_obj;
lean_object* v_res_236_;
v_res_236_ = l_Std_StreamMap_recv___redArg(v_stream_230_);
stack->m_obj
 = v_res_236_;
}
LEAN_EXPORT lean_object* l_Std_StreamMap_recv___redArg___boxed(lean_object* v_stream_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Std_StreamMap_recv___redArg(v_stream_237_);
return v_res_239_;
}
}
lean_object* l_Std_StreamMap_recv(lean_object* v_00_u03b1_240_, lean_object* v_00_u03b2_241_, lean_object* v_stream_242_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Std_StreamMap_recv___redArg(v_stream_242_);
return v___x_244_;
}
}
LEAN_EXPORT void l_Std_StreamMap_recv_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_242_ = stack[2].m_obj;
lean_object* v_res_245_;
v_res_245_ = l_Std_StreamMap_recv(lean_box(0), lean_box(0), v_stream_242_);
stack->m_obj
 = v_res_245_;
}
LEAN_EXPORT lean_object* l_Std_StreamMap_recv___boxed(lean_object* v_00_u03b1_246_, lean_object* v_00_u03b2_247_, lean_object* v_stream_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Std_StreamMap_recv(v_00_u03b1_246_, v_00_u03b2_247_, v_stream_248_);
return v_res_250_;
}
}
lean_object* l_Std_StreamMap_tryRecv___redArg(lean_object* v_stream_251_){
_start:
{
size_t v_sz_253_; size_t v___x_254_; lean_object* v_selectables_255_; lean_object* v___x_256_; 
v_sz_253_ = lean_array_size(v_stream_251_);
v___x_254_ = ((size_t)0ULL);
v_selectables_255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(v_sz_253_, v___x_254_, v_stream_251_);
v___x_256_ = l_Std_Async_Selectable_tryOne___redArg(v_selectables_255_);
return v___x_256_;
}
}
LEAN_EXPORT void l_Std_StreamMap_tryRecv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_251_ = stack[0].m_obj;
lean_object* v_res_257_;
v_res_257_ = l_Std_StreamMap_tryRecv___redArg(v_stream_251_);
stack->m_obj
 = v_res_257_;
}
LEAN_EXPORT lean_object* l_Std_StreamMap_tryRecv___redArg___boxed(lean_object* v_stream_258_, lean_object* v_a_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Std_StreamMap_tryRecv___redArg(v_stream_258_);
return v_res_260_;
}
}
lean_object* l_Std_StreamMap_tryRecv(lean_object* v_00_u03b1_261_, lean_object* v_00_u03b2_262_, lean_object* v_stream_263_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_Std_StreamMap_tryRecv___redArg(v_stream_263_);
return v___x_265_;
}
}
LEAN_EXPORT void l_Std_StreamMap_tryRecv_0interp(lean_interpreter_value* stack)
{
lean_object* v_stream_263_ = stack[2].m_obj;
lean_object* v_res_266_;
v_res_266_ = l_Std_StreamMap_tryRecv(lean_box(0), lean_box(0), v_stream_263_);
stack->m_obj
 = v_res_266_;
}
LEAN_EXPORT lean_object* l_Std_StreamMap_tryRecv___boxed(lean_object* v_00_u03b1_267_, lean_object* v_00_u03b2_268_, lean_object* v_stream_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Std_StreamMap_tryRecv(v_00_u03b1_267_, v_00_u03b2_268_, v_stream_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_unregister___redArg(lean_object* v_inst_272_, lean_object* v_sm_273_, lean_object* v_name_274_){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_275_ = lean_unsigned_to_nat(0u);
v___x_276_ = lean_array_get_size(v_sm_273_);
v___x_277_ = ((lean_object*)(l_Std_StreamMap_empty___redArg___closed__0));
v___x_278_ = ((lean_object*)(l_Std_StreamMap_register___redArg___closed__9));
v___x_279_ = lean_nat_dec_lt(v___x_275_, v___x_276_);
if (v___x_279_ == 0)
{
lean_dec(v_name_274_);
lean_dec_ref(v_sm_273_);
lean_dec_ref(v_inst_272_);
return v___x_277_;
}
else
{
lean_object* v___f_280_; uint8_t v___x_281_; 
v___f_280_ = lean_alloc_closure((void*)(l_Std_StreamMap_register___redArg___lam__0), 4, 2);
lean_closure_set(v___f_280_, 0, v_inst_272_);
lean_closure_set(v___f_280_, 1, v_name_274_);
v___x_281_ = lean_nat_dec_le(v___x_276_, v___x_276_);
if (v___x_281_ == 0)
{
if (v___x_279_ == 0)
{
lean_dec_ref(v___f_280_);
lean_dec_ref(v_sm_273_);
return v___x_277_;
}
else
{
size_t v___x_282_; size_t v___x_283_; lean_object* v___x_284_; 
v___x_282_ = ((size_t)0ULL);
v___x_283_ = lean_usize_of_nat(v___x_276_);
v___x_284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_278_, v___f_280_, v_sm_273_, v___x_282_, v___x_283_, v___x_277_);
return v___x_284_;
}
}
else
{
size_t v___x_285_; size_t v___x_286_; lean_object* v___x_287_; 
v___x_285_ = ((size_t)0ULL);
v___x_286_ = lean_usize_of_nat(v___x_276_);
v___x_287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_278_, v___f_280_, v_sm_273_, v___x_285_, v___x_286_, v___x_277_);
return v___x_287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_unregister(lean_object* v_00_u03b1_288_, lean_object* v_00_u03b2_289_, lean_object* v_inst_290_, lean_object* v_sm_291_, lean_object* v_name_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Std_StreamMap_unregister___redArg(v_inst_290_, v_sm_291_, v_name_292_);
return v___x_293_;
}
}
uint8_t l_Std_StreamMap_contains___redArg___lam__0(lean_object* v_inst_294_, lean_object* v_name_295_, lean_object* v_x_296_){
_start:
{
lean_object* v_fst_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v_fst_297_ = lean_ctor_get(v_x_296_, 0);
lean_inc(v_fst_297_);
lean_dec_ref(v_x_296_);
v___x_298_ = lean_apply_2(v_inst_294_, v_fst_297_, v_name_295_);
v___x_299_ = lean_unbox(v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT void l_Std_StreamMap_contains___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_294_ = stack[0].m_obj;
lean_object* v_name_295_ = stack[1].m_obj;
lean_object* v_x_296_ = stack[2].m_obj;
uint8_t v_res_300_;
v_res_300_ = l_Std_StreamMap_contains___redArg___lam__0(v_inst_294_, v_name_295_, v_x_296_);
stack->m_num = v_res_300_;
}
LEAN_EXPORT lean_object* l_Std_StreamMap_contains___redArg___lam__0___boxed(lean_object* v_inst_301_, lean_object* v_name_302_, lean_object* v_x_303_){
_start:
{
uint8_t v_res_304_; lean_object* v_r_305_; 
v_res_304_ = l_Std_StreamMap_contains___redArg___lam__0(v_inst_301_, v_name_302_, v_x_303_);
v_r_305_ = lean_box(v_res_304_);
return v_r_305_;
}
}
uint8_t l_Std_StreamMap_contains___redArg(lean_object* v_inst_306_, lean_object* v_sm_307_, lean_object* v_name_308_){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = lean_array_get_size(v_sm_307_);
v___x_311_ = ((lean_object*)(l_Std_StreamMap_register___redArg___closed__9));
v___x_312_ = lean_nat_dec_lt(v___x_309_, v___x_310_);
if (v___x_312_ == 0)
{
lean_dec(v_name_308_);
lean_dec_ref(v_sm_307_);
lean_dec_ref(v_inst_306_);
return v___x_312_;
}
else
{
if (v___x_312_ == 0)
{
lean_dec(v_name_308_);
lean_dec_ref(v_sm_307_);
lean_dec_ref(v_inst_306_);
return v___x_312_;
}
else
{
lean_object* v___f_313_; size_t v___x_314_; size_t v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v___f_313_ = lean_alloc_closure((void*)(l_Std_StreamMap_contains___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_313_, 0, v_inst_306_);
lean_closure_set(v___f_313_, 1, v_name_308_);
v___x_314_ = ((size_t)0ULL);
v___x_315_ = lean_usize_of_nat(v___x_310_);
v___x_316_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_311_, v___f_313_, v_sm_307_, v___x_314_, v___x_315_);
v___x_317_ = lean_unbox(v___x_316_);
lean_dec(v___x_316_);
return v___x_317_;
}
}
}
}
LEAN_EXPORT void l_Std_StreamMap_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_306_ = stack[0].m_obj;
lean_object* v_sm_307_ = stack[1].m_obj;
lean_object* v_name_308_ = stack[2].m_obj;
uint8_t v_res_318_;
v_res_318_ = l_Std_StreamMap_contains___redArg(v_inst_306_, v_sm_307_, v_name_308_);
stack->m_num = v_res_318_;
}
LEAN_EXPORT lean_object* l_Std_StreamMap_contains___redArg___boxed(lean_object* v_inst_319_, lean_object* v_sm_320_, lean_object* v_name_321_){
_start:
{
uint8_t v_res_322_; lean_object* v_r_323_; 
v_res_322_ = l_Std_StreamMap_contains___redArg(v_inst_319_, v_sm_320_, v_name_321_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
uint8_t l_Std_StreamMap_contains(lean_object* v_00_u03b1_324_, lean_object* v_00_u03b2_325_, lean_object* v_inst_326_, lean_object* v_sm_327_, lean_object* v_name_328_){
_start:
{
uint8_t v___x_329_; 
v___x_329_ = l_Std_StreamMap_contains___redArg(v_inst_326_, v_sm_327_, v_name_328_);
return v___x_329_;
}
}
LEAN_EXPORT void l_Std_StreamMap_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_326_ = stack[2].m_obj;
lean_object* v_sm_327_ = stack[3].m_obj;
lean_object* v_name_328_ = stack[4].m_obj;
uint8_t v_res_330_;
v_res_330_ = l_Std_StreamMap_contains(lean_box(0), lean_box(0), v_inst_326_, v_sm_327_, v_name_328_);
stack->m_num = v_res_330_;
}
LEAN_EXPORT lean_object* l_Std_StreamMap_contains___boxed(lean_object* v_00_u03b1_331_, lean_object* v_00_u03b2_332_, lean_object* v_inst_333_, lean_object* v_sm_334_, lean_object* v_name_335_){
_start:
{
uint8_t v_res_336_; lean_object* v_r_337_; 
v_res_336_ = l_Std_StreamMap_contains(v_00_u03b1_331_, v_00_u03b2_332_, v_inst_333_, v_sm_334_, v_name_335_);
v_r_337_ = lean_box(v_res_336_);
return v_r_337_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_size___redArg(lean_object* v_sm_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = lean_array_get_size(v_sm_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_size___redArg___boxed(lean_object* v_sm_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Std_StreamMap_size___redArg(v_sm_340_);
lean_dec_ref(v_sm_340_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_size(lean_object* v_00_u03b1_342_, lean_object* v_00_u03b2_343_, lean_object* v_sm_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = lean_array_get_size(v_sm_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_size___boxed(lean_object* v_00_u03b1_346_, lean_object* v_00_u03b2_347_, lean_object* v_sm_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Std_StreamMap_size(v_00_u03b1_346_, v_00_u03b2_347_, v_sm_348_);
lean_dec_ref(v_sm_348_);
return v_res_349_;
}
}
uint8_t l_Std_StreamMap_isEmpty___redArg(lean_object* v_sm_350_){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_351_ = lean_array_get_size(v_sm_350_);
v___x_352_ = lean_unsigned_to_nat(0u);
v___x_353_ = lean_nat_dec_eq(v___x_351_, v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT void l_Std_StreamMap_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_sm_350_ = stack[0].m_obj;
uint8_t v_res_354_;
v_res_354_ = l_Std_StreamMap_isEmpty___redArg(v_sm_350_);
stack->m_num = v_res_354_;
}
LEAN_EXPORT lean_object* l_Std_StreamMap_isEmpty___redArg___boxed(lean_object* v_sm_355_){
_start:
{
uint8_t v_res_356_; lean_object* v_r_357_; 
v_res_356_ = l_Std_StreamMap_isEmpty___redArg(v_sm_355_);
lean_dec_ref(v_sm_355_);
v_r_357_ = lean_box(v_res_356_);
return v_r_357_;
}
}
uint8_t l_Std_StreamMap_isEmpty(lean_object* v_00_u03b1_358_, lean_object* v_00_u03b2_359_, lean_object* v_sm_360_){
_start:
{
uint8_t v___x_361_; 
v___x_361_ = l_Std_StreamMap_isEmpty___redArg(v_sm_360_);
return v___x_361_;
}
}
LEAN_EXPORT void l_Std_StreamMap_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_sm_360_ = stack[2].m_obj;
uint8_t v_res_362_;
v_res_362_ = l_Std_StreamMap_isEmpty(lean_box(0), lean_box(0), v_sm_360_);
stack->m_num = v_res_362_;
}
LEAN_EXPORT lean_object* l_Std_StreamMap_isEmpty___boxed(lean_object* v_00_u03b1_363_, lean_object* v_00_u03b2_364_, lean_object* v_sm_365_){
_start:
{
uint8_t v_res_366_; lean_object* v_r_367_; 
v_res_366_ = l_Std_StreamMap_isEmpty(v_00_u03b1_363_, v_00_u03b2_364_, v_sm_365_);
lean_dec_ref(v_sm_365_);
v_r_367_ = lean_box(v_res_366_);
return v_r_367_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg(size_t v_sz_368_, size_t v_i_369_, lean_object* v_bs_370_){
_start:
{
uint8_t v___x_371_; 
v___x_371_ = lean_usize_dec_lt(v_i_369_, v_sz_368_);
if (v___x_371_ == 0)
{
return v_bs_370_;
}
else
{
lean_object* v_v_372_; lean_object* v_fst_373_; lean_object* v___x_374_; lean_object* v_bs_x27_375_; size_t v___x_376_; size_t v___x_377_; lean_object* v___x_378_; 
v_v_372_ = lean_array_uget_borrowed(v_bs_370_, v_i_369_);
v_fst_373_ = lean_ctor_get(v_v_372_, 0);
lean_inc(v_fst_373_);
v___x_374_ = lean_unsigned_to_nat(0u);
v_bs_x27_375_ = lean_array_uset(v_bs_370_, v_i_369_, v___x_374_);
v___x_376_ = ((size_t)1ULL);
v___x_377_ = lean_usize_add(v_i_369_, v___x_376_);
v___x_378_ = lean_array_uset(v_bs_x27_375_, v_i_369_, v_fst_373_);
v_i_369_ = v___x_377_;
v_bs_370_ = v___x_378_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_368_ = stack[0].m_num;
size_t v_i_369_ = stack[1].m_num;
lean_object* v_bs_370_ = stack[2].m_obj;
lean_object* v_res_380_;
v_res_380_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg(v_sz_368_, v_i_369_, v_bs_370_);
stack->m_obj
 = v_res_380_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg___boxed(lean_object* v_sz_381_, lean_object* v_i_382_, lean_object* v_bs_383_){
_start:
{
size_t v_sz_boxed_384_; size_t v_i_boxed_385_; lean_object* v_res_386_; 
v_sz_boxed_384_ = lean_unbox_usize(v_sz_381_);
lean_dec(v_sz_381_);
v_i_boxed_385_ = lean_unbox_usize(v_i_382_);
lean_dec(v_i_382_);
v_res_386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg(v_sz_boxed_384_, v_i_boxed_385_, v_bs_383_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_keys___redArg(lean_object* v_sm_387_){
_start:
{
size_t v_sz_388_; size_t v___x_389_; lean_object* v___x_390_; 
v_sz_388_ = lean_array_size(v_sm_387_);
v___x_389_ = ((size_t)0ULL);
v___x_390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg(v_sz_388_, v___x_389_, v_sm_387_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_keys(lean_object* v_00_u03b1_391_, lean_object* v_00_u03b2_392_, lean_object* v_sm_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Std_StreamMap_keys___redArg(v_sm_393_);
return v___x_394_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0(lean_object* v_00_u03b1_395_, lean_object* v_00_u03b2_396_, size_t v_sz_397_, size_t v_i_398_, lean_object* v_bs_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg(v_sz_397_, v_i_398_, v_bs_399_);
return v___x_400_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_397_ = stack[2].m_num;
size_t v_i_398_ = stack[3].m_num;
lean_object* v_bs_399_ = stack[4].m_obj;
lean_object* v_res_401_;
v_res_401_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0(lean_box(0), lean_box(0), v_sz_397_, v_i_398_, v_bs_399_);
stack->m_obj
 = v_res_401_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___boxed(lean_object* v_00_u03b1_402_, lean_object* v_00_u03b2_403_, lean_object* v_sz_404_, lean_object* v_i_405_, lean_object* v_bs_406_){
_start:
{
size_t v_sz_boxed_407_; size_t v_i_boxed_408_; lean_object* v_res_409_; 
v_sz_boxed_407_ = lean_unbox_usize(v_sz_404_);
lean_dec(v_sz_404_);
v_i_boxed_408_ = lean_unbox_usize(v_i_405_);
lean_dec(v_i_405_);
v_res_409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0(v_00_u03b1_402_, v_00_u03b2_403_, v_sz_boxed_407_, v_i_boxed_408_, v_bs_406_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_get_x3f___redArg___lam__0(lean_object* v_inst_410_, lean_object* v_name_411_, lean_object* v___x_412_, lean_object* v___x_413_, lean_object* v_a_414_, lean_object* v_x_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_fst_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v_fst_417_ = lean_ctor_get(v_a_414_, 0);
lean_inc(v_fst_417_);
v___x_418_ = lean_apply_2(v_inst_410_, v_fst_417_, v_name_411_);
v___x_419_ = lean_unbox(v___x_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; 
lean_dec_ref(v_a_414_);
v___x_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_412_);
return v___x_420_;
}
else
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
lean_dec_ref(v___x_412_);
v___x_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_421_, 0, v_a_414_);
v___x_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v___x_413_);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_get_x3f___redArg___lam__0___boxed(lean_object* v_inst_425_, lean_object* v_name_426_, lean_object* v___x_427_, lean_object* v___x_428_, lean_object* v_a_429_, lean_object* v_x_430_, lean_object* v___y_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Std_StreamMap_get_x3f___redArg___lam__0(v_inst_425_, v_name_426_, v___x_427_, v___x_428_, v_a_429_, v_x_430_, v___y_431_);
lean_dec_ref(v___y_431_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_get_x3f___redArg(lean_object* v_inst_436_, lean_object* v_sm_437_, lean_object* v_name_438_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___f_443_; size_t v_sz_444_; size_t v___x_445_; lean_object* v___x_446_; lean_object* v_fst_447_; 
v___x_439_ = ((lean_object*)(l_Std_StreamMap_register___redArg___closed__9));
v___x_440_ = lean_box(0);
v___x_441_ = lean_box(0);
v___x_442_ = ((lean_object*)(l_Std_StreamMap_get_x3f___redArg___closed__0));
v___f_443_ = lean_alloc_closure((void*)(l_Std_StreamMap_get_x3f___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_443_, 0, v_inst_436_);
lean_closure_set(v___f_443_, 1, v_name_438_);
lean_closure_set(v___f_443_, 2, v___x_442_);
lean_closure_set(v___f_443_, 3, v___x_441_);
v_sz_444_ = lean_array_size(v_sm_437_);
v___x_445_ = ((size_t)0ULL);
v___x_446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_439_, v_sm_437_, v___f_443_, v_sz_444_, v___x_445_, v___x_442_);
v_fst_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_fst_447_);
lean_dec(v___x_446_);
if (lean_obj_tag(v_fst_447_) == 0)
{
return v___x_440_;
}
else
{
lean_object* v_val_448_; 
v_val_448_ = lean_ctor_get(v_fst_447_, 0);
lean_inc(v_val_448_);
lean_dec_ref_known(v_fst_447_, 1);
if (lean_obj_tag(v_val_448_) == 0)
{
return v___x_440_;
}
else
{
lean_object* v_val_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_458_; 
v_val_449_ = lean_ctor_get(v_val_448_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v_val_448_);
if (v_isSharedCheck_458_ == 0)
{
v___x_451_ = v_val_448_;
v_isShared_452_ = v_isSharedCheck_458_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_val_449_);
lean_dec(v_val_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_458_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v_snd_453_; lean_object* v_fst_454_; lean_object* v___x_456_; 
v_snd_453_ = lean_ctor_get(v_val_449_, 1);
lean_inc(v_snd_453_);
lean_dec(v_val_449_);
v_fst_454_ = lean_ctor_get(v_snd_453_, 0);
lean_inc(v_fst_454_);
lean_dec(v_snd_453_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v_fst_454_);
v___x_456_ = v___x_451_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_fst_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_get_x3f(lean_object* v_00_u03b1_459_, lean_object* v_00_u03b2_460_, lean_object* v_inst_461_, lean_object* v_sm_462_, lean_object* v_name_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Std_StreamMap_get_x3f___redArg(v_inst_461_, v_sm_462_, v_name_463_);
return v___x_464_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(lean_object* v_pred_465_, lean_object* v_as_466_, size_t v_i_467_, size_t v_stop_468_, lean_object* v_b_469_){
_start:
{
lean_object* v___y_471_; uint8_t v___x_475_; 
v___x_475_ = lean_usize_dec_eq(v_i_467_, v_stop_468_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; lean_object* v_fst_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_476_ = lean_array_uget_borrowed(v_as_466_, v_i_467_);
v_fst_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc_ref(v_pred_465_);
lean_inc(v_fst_477_);
v___x_478_ = lean_apply_1(v_pred_465_, v_fst_477_);
v___x_479_ = lean_unbox(v___x_478_);
if (v___x_479_ == 0)
{
v___y_471_ = v_b_469_;
goto v___jp_470_;
}
else
{
lean_object* v___x_480_; 
lean_inc(v___x_476_);
v___x_480_ = lean_array_push(v_b_469_, v___x_476_);
v___y_471_ = v___x_480_;
goto v___jp_470_;
}
}
else
{
lean_dec_ref(v_pred_465_);
return v_b_469_;
}
v___jp_470_:
{
size_t v___x_472_; size_t v___x_473_; 
v___x_472_ = ((size_t)1ULL);
v___x_473_ = lean_usize_add(v_i_467_, v___x_472_);
v_i_467_ = v___x_473_;
v_b_469_ = v___y_471_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_pred_465_ = stack[0].m_obj;
lean_object* v_as_466_ = stack[1].m_obj;
size_t v_i_467_ = stack[2].m_num;
size_t v_stop_468_ = stack[3].m_num;
lean_object* v_b_469_ = stack[4].m_obj;
lean_object* v_res_481_;
v_res_481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(v_pred_465_, v_as_466_, v_i_467_, v_stop_468_, v_b_469_);
stack->m_obj
 = v_res_481_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg___boxed(lean_object* v_pred_482_, lean_object* v_as_483_, lean_object* v_i_484_, lean_object* v_stop_485_, lean_object* v_b_486_){
_start:
{
size_t v_i_boxed_487_; size_t v_stop_boxed_488_; lean_object* v_res_489_; 
v_i_boxed_487_ = lean_unbox_usize(v_i_484_);
lean_dec(v_i_484_);
v_stop_boxed_488_ = lean_unbox_usize(v_stop_485_);
lean_dec(v_stop_485_);
v_res_489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(v_pred_482_, v_as_483_, v_i_boxed_487_, v_stop_boxed_488_, v_b_486_);
lean_dec_ref(v_as_483_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_filterByName___redArg(lean_object* v_sm_490_, lean_object* v_pred_491_){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_492_ = lean_unsigned_to_nat(0u);
v___x_493_ = lean_array_get_size(v_sm_490_);
v___x_494_ = ((lean_object*)(l_Std_StreamMap_empty___redArg___closed__0));
v___x_495_ = lean_nat_dec_lt(v___x_492_, v___x_493_);
if (v___x_495_ == 0)
{
lean_dec_ref(v_pred_491_);
return v___x_494_;
}
else
{
uint8_t v___x_496_; 
v___x_496_ = lean_nat_dec_le(v___x_493_, v___x_493_);
if (v___x_496_ == 0)
{
if (v___x_495_ == 0)
{
lean_dec_ref(v_pred_491_);
return v___x_494_;
}
else
{
size_t v___x_497_; size_t v___x_498_; lean_object* v___x_499_; 
v___x_497_ = ((size_t)0ULL);
v___x_498_ = lean_usize_of_nat(v___x_493_);
v___x_499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(v_pred_491_, v_sm_490_, v___x_497_, v___x_498_, v___x_494_);
return v___x_499_;
}
}
else
{
size_t v___x_500_; size_t v___x_501_; lean_object* v___x_502_; 
v___x_500_ = ((size_t)0ULL);
v___x_501_ = lean_usize_of_nat(v___x_493_);
v___x_502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(v_pred_491_, v_sm_490_, v___x_500_, v___x_501_, v___x_494_);
return v___x_502_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_filterByName___redArg___boxed(lean_object* v_sm_503_, lean_object* v_pred_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Std_StreamMap_filterByName___redArg(v_sm_503_, v_pred_504_);
lean_dec_ref(v_sm_503_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_filterByName(lean_object* v_00_u03b1_506_, lean_object* v_00_u03b2_507_, lean_object* v_sm_508_, lean_object* v_pred_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Std_StreamMap_filterByName___redArg(v_sm_508_, v_pred_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_filterByName___boxed(lean_object* v_00_u03b1_511_, lean_object* v_00_u03b2_512_, lean_object* v_sm_513_, lean_object* v_pred_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Std_StreamMap_filterByName(v_00_u03b1_511_, v_00_u03b2_512_, v_sm_513_, v_pred_514_);
lean_dec_ref(v_sm_513_);
return v_res_515_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0(lean_object* v_00_u03b1_516_, lean_object* v_00_u03b2_517_, lean_object* v_pred_518_, lean_object* v_as_519_, size_t v_i_520_, size_t v_stop_521_, lean_object* v_b_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(v_pred_518_, v_as_519_, v_i_520_, v_stop_521_, v_b_522_);
return v___x_523_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pred_518_ = stack[2].m_obj;
lean_object* v_as_519_ = stack[3].m_obj;
size_t v_i_520_ = stack[4].m_num;
size_t v_stop_521_ = stack[5].m_num;
lean_object* v_b_522_ = stack[6].m_obj;
lean_object* v_res_524_;
v_res_524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0(lean_box(0), lean_box(0), v_pred_518_, v_as_519_, v_i_520_, v_stop_521_, v_b_522_);
stack->m_obj
 = v_res_524_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___boxed(lean_object* v_00_u03b1_525_, lean_object* v_00_u03b2_526_, lean_object* v_pred_527_, lean_object* v_as_528_, lean_object* v_i_529_, lean_object* v_stop_530_, lean_object* v_b_531_){
_start:
{
size_t v_i_boxed_532_; size_t v_stop_boxed_533_; lean_object* v_res_534_; 
v_i_boxed_532_ = lean_unbox_usize(v_i_529_);
lean_dec(v_i_529_);
v_stop_boxed_533_ = lean_unbox_usize(v_stop_530_);
lean_dec(v_stop_530_);
v_res_534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0(v_00_u03b1_525_, v_00_u03b2_526_, v_pred_527_, v_as_528_, v_i_boxed_532_, v_stop_boxed_533_, v_b_531_);
lean_dec_ref(v_as_528_);
return v_res_534_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg(size_t v_sz_535_, size_t v_i_536_, lean_object* v_bs_537_){
_start:
{
uint8_t v___x_538_; 
v___x_538_ = lean_usize_dec_lt(v_i_536_, v_sz_535_);
if (v___x_538_ == 0)
{
return v_bs_537_;
}
else
{
lean_object* v_v_539_; lean_object* v_snd_540_; lean_object* v_fst_541_; lean_object* v_fst_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_555_; 
v_v_539_ = lean_array_uget_borrowed(v_bs_537_, v_i_536_);
v_snd_540_ = lean_ctor_get(v_v_539_, 1);
lean_inc(v_snd_540_);
v_fst_541_ = lean_ctor_get(v_v_539_, 0);
lean_inc(v_fst_541_);
v_fst_542_ = lean_ctor_get(v_snd_540_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v_snd_540_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; 
v_unused_556_ = lean_ctor_get(v_snd_540_, 1);
lean_dec(v_unused_556_);
v___x_544_ = v_snd_540_;
v_isShared_545_ = v_isSharedCheck_555_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_fst_542_);
lean_dec(v_snd_540_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_555_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v_bs_x27_547_; lean_object* v___x_549_; 
v___x_546_ = lean_unsigned_to_nat(0u);
v_bs_x27_547_ = lean_array_uset(v_bs_537_, v_i_536_, v___x_546_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 1, v_fst_542_);
lean_ctor_set(v___x_544_, 0, v_fst_541_);
v___x_549_ = v___x_544_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_fst_541_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_fst_542_);
v___x_549_ = v_reuseFailAlloc_554_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
size_t v___x_550_; size_t v___x_551_; lean_object* v___x_552_; 
v___x_550_ = ((size_t)1ULL);
v___x_551_ = lean_usize_add(v_i_536_, v___x_550_);
v___x_552_ = lean_array_uset(v_bs_x27_547_, v_i_536_, v___x_549_);
v_i_536_ = v___x_551_;
v_bs_537_ = v___x_552_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_535_ = stack[0].m_num;
size_t v_i_536_ = stack[1].m_num;
lean_object* v_bs_537_ = stack[2].m_obj;
lean_object* v_res_557_;
v_res_557_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg(v_sz_535_, v_i_536_, v_bs_537_);
stack->m_obj
 = v_res_557_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg___boxed(lean_object* v_sz_558_, lean_object* v_i_559_, lean_object* v_bs_560_){
_start:
{
size_t v_sz_boxed_561_; size_t v_i_boxed_562_; lean_object* v_res_563_; 
v_sz_boxed_561_ = lean_unbox_usize(v_sz_558_);
lean_dec(v_sz_558_);
v_i_boxed_562_ = lean_unbox_usize(v_i_559_);
lean_dec(v_i_559_);
v_res_563_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg(v_sz_boxed_561_, v_i_boxed_562_, v_bs_560_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_toArray___redArg(lean_object* v_sm_564_){
_start:
{
size_t v_sz_565_; size_t v___x_566_; lean_object* v___x_567_; 
v_sz_565_ = lean_array_size(v_sm_564_);
v___x_566_ = ((size_t)0ULL);
v___x_567_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg(v_sz_565_, v___x_566_, v_sm_564_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_toArray(lean_object* v_00_u03b1_568_, lean_object* v_00_u03b2_569_, lean_object* v_sm_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Std_StreamMap_toArray___redArg(v_sm_570_);
return v___x_571_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0(lean_object* v_00_u03b1_572_, lean_object* v_00_u03b2_573_, size_t v_sz_574_, size_t v_i_575_, lean_object* v_bs_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg(v_sz_574_, v_i_575_, v_bs_576_);
return v___x_577_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_574_ = stack[2].m_num;
size_t v_i_575_ = stack[3].m_num;
lean_object* v_bs_576_ = stack[4].m_obj;
lean_object* v_res_578_;
v_res_578_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0(lean_box(0), lean_box(0), v_sz_574_, v_i_575_, v_bs_576_);
stack->m_obj
 = v_res_578_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___boxed(lean_object* v_00_u03b1_579_, lean_object* v_00_u03b2_580_, lean_object* v_sz_581_, lean_object* v_i_582_, lean_object* v_bs_583_){
_start:
{
size_t v_sz_boxed_584_; size_t v_i_boxed_585_; lean_object* v_res_586_; 
v_sz_boxed_584_ = lean_unbox_usize(v_sz_581_);
lean_dec(v_sz_581_);
v_i_boxed_585_ = lean_unbox_usize(v_i_582_);
lean_dec(v_i_582_);
v_res_586_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0(v_00_u03b1_579_, v_00_u03b2_580_, v_sz_boxed_584_, v_i_boxed_585_, v_bs_583_);
return v_res_586_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(lean_object* v_as_587_, size_t v_i_588_, size_t v_stop_589_, lean_object* v_b_590_){
_start:
{
uint8_t v___x_592_; 
v___x_592_ = lean_usize_dec_eq(v_i_588_, v_stop_589_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; lean_object* v_snd_594_; lean_object* v_snd_595_; lean_object* v___x_596_; 
v___x_593_ = lean_array_uget_borrowed(v_as_587_, v_i_588_);
v_snd_594_ = lean_ctor_get(v___x_593_, 1);
v_snd_595_ = lean_ctor_get(v_snd_594_, 1);
lean_inc(v_snd_595_);
v___x_596_ = lean_apply_1(v_snd_595_, lean_box(0));
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; size_t v___x_598_; size_t v___x_599_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_a_597_);
lean_dec_ref_known(v___x_596_, 1);
v___x_598_ = ((size_t)1ULL);
v___x_599_ = lean_usize_add(v_i_588_, v___x_598_);
v_i_588_ = v___x_599_;
v_b_590_ = v_a_597_;
goto _start;
}
else
{
return v___x_596_;
}
}
else
{
lean_object* v___x_601_; 
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v_b_590_);
return v___x_601_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_587_ = stack[0].m_obj;
size_t v_i_588_ = stack[1].m_num;
size_t v_stop_589_ = stack[2].m_num;
lean_object* v_b_590_ = stack[3].m_obj;
lean_object* v_res_602_;
v_res_602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(v_as_587_, v_i_588_, v_stop_589_, v_b_590_);
stack->m_obj
 = v_res_602_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg___boxed(lean_object* v_as_603_, lean_object* v_i_604_, lean_object* v_stop_605_, lean_object* v_b_606_, lean_object* v___y_607_){
_start:
{
size_t v_i_boxed_608_; size_t v_stop_boxed_609_; lean_object* v_res_610_; 
v_i_boxed_608_ = lean_unbox_usize(v_i_604_);
lean_dec(v_i_604_);
v_stop_boxed_609_ = lean_unbox_usize(v_stop_605_);
lean_dec(v_stop_605_);
v_res_610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(v_as_603_, v_i_boxed_608_, v_stop_boxed_609_, v_b_606_);
lean_dec_ref(v_as_603_);
return v_res_610_;
}
}
lean_object* l_Std_StreamMap_close___redArg(lean_object* v_sm_611_){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_613_ = lean_unsigned_to_nat(0u);
v___x_614_ = lean_array_get_size(v_sm_611_);
v___x_615_ = lean_box(0);
v___x_616_ = lean_nat_dec_lt(v___x_613_, v___x_614_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; 
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_615_);
return v___x_617_;
}
else
{
uint8_t v___x_618_; 
v___x_618_ = lean_nat_dec_le(v___x_614_, v___x_614_);
if (v___x_618_ == 0)
{
if (v___x_616_ == 0)
{
lean_object* v___x_619_; 
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_615_);
return v___x_619_;
}
else
{
size_t v___x_620_; size_t v___x_621_; lean_object* v___x_622_; 
v___x_620_ = ((size_t)0ULL);
v___x_621_ = lean_usize_of_nat(v___x_614_);
v___x_622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(v_sm_611_, v___x_620_, v___x_621_, v___x_615_);
return v___x_622_;
}
}
else
{
size_t v___x_623_; size_t v___x_624_; lean_object* v___x_625_; 
v___x_623_ = ((size_t)0ULL);
v___x_624_ = lean_usize_of_nat(v___x_614_);
v___x_625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(v_sm_611_, v___x_623_, v___x_624_, v___x_615_);
return v___x_625_;
}
}
}
}
LEAN_EXPORT void l_Std_StreamMap_close___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_sm_611_ = stack[0].m_obj;
lean_object* v_res_626_;
v_res_626_ = l_Std_StreamMap_close___redArg(v_sm_611_);
stack->m_obj
 = v_res_626_;
}
LEAN_EXPORT lean_object* l_Std_StreamMap_close___redArg___boxed(lean_object* v_sm_627_, lean_object* v_a_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Std_StreamMap_close___redArg(v_sm_627_);
lean_dec_ref(v_sm_627_);
return v_res_629_;
}
}
lean_object* l_Std_StreamMap_close(lean_object* v_00_u03b1_630_, lean_object* v_00_u03b2_631_, lean_object* v_sm_632_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Std_StreamMap_close___redArg(v_sm_632_);
return v___x_634_;
}
}
LEAN_EXPORT void l_Std_StreamMap_close_0interp(lean_interpreter_value* stack)
{
lean_object* v_sm_632_ = stack[2].m_obj;
lean_object* v_res_635_;
v_res_635_ = l_Std_StreamMap_close(lean_box(0), lean_box(0), v_sm_632_);
stack->m_obj
 = v_res_635_;
}
LEAN_EXPORT lean_object* l_Std_StreamMap_close___boxed(lean_object* v_00_u03b1_636_, lean_object* v_00_u03b2_637_, lean_object* v_sm_638_, lean_object* v_a_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Std_StreamMap_close(v_00_u03b1_636_, v_00_u03b2_637_, v_sm_638_);
lean_dec_ref(v_sm_638_);
return v_res_640_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0(lean_object* v_00_u03b1_641_, lean_object* v_00_u03b2_642_, lean_object* v_as_643_, size_t v_i_644_, size_t v_stop_645_, lean_object* v_b_646_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(v_as_643_, v_i_644_, v_stop_645_, v_b_646_);
return v___x_648_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_643_ = stack[2].m_obj;
size_t v_i_644_ = stack[3].m_num;
size_t v_stop_645_ = stack[4].m_num;
lean_object* v_b_646_ = stack[5].m_obj;
lean_object* v_res_649_;
v_res_649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0(lean_box(0), lean_box(0), v_as_643_, v_i_644_, v_stop_645_, v_b_646_);
stack->m_obj
 = v_res_649_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___boxed(lean_object* v_00_u03b1_650_, lean_object* v_00_u03b2_651_, lean_object* v_as_652_, lean_object* v_i_653_, lean_object* v_stop_654_, lean_object* v_b_655_, lean_object* v___y_656_){
_start:
{
size_t v_i_boxed_657_; size_t v_stop_boxed_658_; lean_object* v_res_659_; 
v_i_boxed_657_ = lean_unbox_usize(v_i_653_);
lean_dec(v_i_653_);
v_stop_boxed_658_ = lean_unbox_usize(v_stop_654_);
lean_dec(v_stop_654_);
v_res_659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0(v_00_u03b1_650_, v_00_u03b2_651_, v_as_652_, v_i_boxed_657_, v_stop_boxed_658_, v_b_655_);
lean_dec_ref(v_as_652_);
return v_res_659_;
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
