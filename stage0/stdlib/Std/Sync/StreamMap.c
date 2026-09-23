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
lean_object* v_next_68_; lean_object* v_stop_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_95_; 
v_next_68_ = lean_ctor_get(v_inst_64_, 0);
v_stop_69_ = lean_ctor_get(v_inst_64_, 1);
v_isSharedCheck_95_ = !lean_is_exclusive(v_inst_64_);
if (v_isSharedCheck_95_ == 0)
{
v___x_71_ = v_inst_64_;
v_isShared_72_ = v_isSharedCheck_95_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_stop_69_);
lean_inc(v_next_68_);
lean_dec(v_inst_64_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_95_;
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
lean_object* v___f_87_; uint8_t v___x_88_; 
lean_inc(v_name_66_);
v___f_87_ = lean_alloc_closure((void*)(l_Std_StreamMap_register___redArg___lam__0), 4, 2);
lean_closure_set(v___f_87_, 0, v_inst_63_);
lean_closure_set(v___f_87_, 1, v_name_66_);
v___x_88_ = lean_nat_dec_le(v___x_83_, v___x_83_);
if (v___x_88_ == 0)
{
if (v___x_86_ == 0)
{
lean_dec_ref(v___f_87_);
lean_dec_ref(v_sm_65_);
v___y_75_ = v___x_84_;
goto v___jp_74_;
}
else
{
size_t v___x_89_; size_t v___x_90_; lean_object* v___x_91_; 
v___x_89_ = ((size_t)0ULL);
v___x_90_ = lean_usize_of_nat(v___x_83_);
v___x_91_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_85_, v___f_87_, v_sm_65_, v___x_89_, v___x_90_, v___x_84_);
v___y_75_ = v___x_91_;
goto v___jp_74_;
}
}
else
{
size_t v___x_92_; size_t v___x_93_; lean_object* v___x_94_; 
v___x_92_ = ((size_t)0ULL);
v___x_93_ = lean_usize_of_nat(v___x_83_);
v___x_94_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_85_, v___f_87_, v_sm_65_, v___x_92_, v___x_93_, v___x_84_);
v___y_75_ = v___x_94_;
goto v___jp_74_;
}
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
LEAN_EXPORT lean_object* l_Std_StreamMap_register(lean_object* v_00_u03b1_96_, lean_object* v_t_97_, lean_object* v_00_u03b2_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_sm_101_, lean_object* v_name_102_, lean_object* v_reader_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Std_StreamMap_register___redArg(v_inst_99_, v_inst_100_, v_sm_101_, v_name_102_, v_reader_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_ofArray___redArg___lam__0(lean_object* v_x_105_){
_start:
{
lean_object* v_fst_106_; lean_object* v_snd_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_115_; 
v_fst_106_ = lean_ctor_get(v_x_105_, 0);
v_snd_107_ = lean_ctor_get(v_x_105_, 1);
v_isSharedCheck_115_ = !lean_is_exclusive(v_x_105_);
if (v_isSharedCheck_115_ == 0)
{
v___x_109_ = v_x_105_;
v_isShared_110_ = v_isSharedCheck_115_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_snd_107_);
lean_inc(v_fst_106_);
lean_dec(v_x_105_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_115_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_113_; 
v___x_111_ = l_Std_AnyAsyncStream_getSelector___redArg(v_snd_107_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v___x_111_);
v___x_113_ = v___x_109_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_fst_106_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v___x_111_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_ofArray___redArg(lean_object* v_streams_117_){
_start:
{
lean_object* v___f_118_; lean_object* v___x_119_; size_t v_sz_120_; size_t v___x_121_; lean_object* v_arrayOfSelectors_122_; 
v___f_118_ = ((lean_object*)(l_Std_StreamMap_ofArray___redArg___closed__0));
v___x_119_ = ((lean_object*)(l_Std_StreamMap_register___redArg___closed__9));
v_sz_120_ = lean_array_size(v_streams_117_);
v___x_121_ = ((size_t)0ULL);
v_arrayOfSelectors_122_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_119_, v___f_118_, v_sz_120_, v___x_121_, v_streams_117_);
return v_arrayOfSelectors_122_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_ofArray(lean_object* v_00_u03b1_123_, lean_object* v_00_u03b2_124_, lean_object* v_inst_125_, lean_object* v_streams_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Std_StreamMap_ofArray___redArg(v_streams_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_ofArray___boxed(lean_object* v_00_u03b1_128_, lean_object* v_00_u03b2_129_, lean_object* v_inst_130_, lean_object* v_streams_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Std_StreamMap_ofArray(v_00_u03b1_128_, v_00_u03b2_129_, v_inst_130_, v_streams_131_);
lean_dec_ref(v_inst_130_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___lam__0(lean_object* v_fst_133_, lean_object* v_x_134_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_136_, 0, v_fst_133_);
lean_ctor_set(v___x_136_, 1, v_x_134_);
v___x_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___lam__0___boxed(lean_object* v_fst_139_, lean_object* v_x_140_, lean_object* v___y_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___lam__0(v_fst_139_, v_x_140_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(size_t v_sz_143_, size_t v_i_144_, lean_object* v_bs_145_){
_start:
{
uint8_t v___x_146_; 
v___x_146_ = lean_usize_dec_lt(v_i_144_, v_sz_143_);
if (v___x_146_ == 0)
{
return v_bs_145_;
}
else
{
lean_object* v_v_147_; lean_object* v_snd_148_; lean_object* v_fst_149_; lean_object* v_fst_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_164_; 
v_v_147_ = lean_array_uget_borrowed(v_bs_145_, v_i_144_);
v_snd_148_ = lean_ctor_get(v_v_147_, 1);
lean_inc(v_snd_148_);
v_fst_149_ = lean_ctor_get(v_v_147_, 0);
lean_inc(v_fst_149_);
v_fst_150_ = lean_ctor_get(v_snd_148_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v_snd_148_);
if (v_isSharedCheck_164_ == 0)
{
lean_object* v_unused_165_; 
v_unused_165_ = lean_ctor_get(v_snd_148_, 1);
lean_dec(v_unused_165_);
v___x_152_ = v_snd_148_;
v_isShared_153_ = v_isSharedCheck_164_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_fst_150_);
lean_dec(v_snd_148_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_164_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; lean_object* v_bs_x27_155_; lean_object* v___f_156_; lean_object* v___x_158_; 
v___x_154_ = lean_unsigned_to_nat(0u);
v_bs_x27_155_ = lean_array_uset(v_bs_145_, v_i_144_, v___x_154_);
v___f_156_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_156_, 0, v_fst_149_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 1, v___f_156_);
v___x_158_ = v___x_152_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_fst_150_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v___f_156_);
v___x_158_ = v_reuseFailAlloc_163_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
size_t v___x_159_; size_t v___x_160_; lean_object* v___x_161_; 
v___x_159_ = ((size_t)1ULL);
v___x_160_ = lean_usize_add(v_i_144_, v___x_159_);
v___x_161_ = lean_array_uset(v_bs_x27_155_, v_i_144_, v___x_158_);
v_i_144_ = v___x_160_;
v_bs_145_ = v___x_161_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___boxed(lean_object* v_sz_166_, lean_object* v_i_167_, lean_object* v_bs_168_){
_start:
{
size_t v_sz_boxed_169_; size_t v_i_boxed_170_; lean_object* v_res_171_; 
v_sz_boxed_169_ = lean_unbox_usize(v_sz_166_);
lean_dec(v_sz_166_);
v_i_boxed_170_ = lean_unbox_usize(v_i_167_);
lean_dec(v_i_167_);
v_res_171_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(v_sz_boxed_169_, v_i_boxed_170_, v_bs_168_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_selector___redArg(lean_object* v_stream_172_){
_start:
{
lean_object* v_val_175_; size_t v_sz_177_; size_t v___x_178_; lean_object* v_selectables_179_; lean_object* v___x_180_; 
v_sz_177_ = lean_array_size(v_stream_172_);
v___x_178_ = ((size_t)0ULL);
v_selectables_179_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(v_sz_177_, v___x_178_, v_stream_172_);
v___x_180_ = l_Std_Async_Selectable_combine___redArg(v_selectables_179_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v___x_180_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_180_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set_tag(v___x_183_, 1);
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_181_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
v_val_175_ = v___x_186_;
goto v___jp_174_;
}
}
}
else
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_196_; 
v_a_189_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_196_ == 0)
{
v___x_191_ = v___x_180_;
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_180_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
if (v_isShared_192_ == 0)
{
lean_ctor_set_tag(v___x_191_, 0);
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_189_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
v_val_175_ = v___x_194_;
goto v___jp_174_;
}
}
}
v___jp_174_:
{
lean_object* v___x_176_; 
v___x_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_176_, 0, v_val_175_);
return v___x_176_;
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_selector___redArg___boxed(lean_object* v_stream_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Std_StreamMap_selector___redArg(v_stream_197_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_selector(lean_object* v_00_u03b1_200_, lean_object* v_00_u03b2_201_, lean_object* v_stream_202_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Std_StreamMap_selector___redArg(v_stream_202_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_selector___boxed(lean_object* v_00_u03b1_205_, lean_object* v_00_u03b2_206_, lean_object* v_stream_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Std_StreamMap_selector(v_00_u03b1_205_, v_00_u03b2_206_, v_stream_207_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0(lean_object* v_00_u03b1_210_, lean_object* v_00_u03b2_211_, size_t v_sz_212_, size_t v_i_213_, lean_object* v_bs_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(v_sz_212_, v_i_213_, v_bs_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___boxed(lean_object* v_00_u03b1_216_, lean_object* v_00_u03b2_217_, lean_object* v_sz_218_, lean_object* v_i_219_, lean_object* v_bs_220_){
_start:
{
size_t v_sz_boxed_221_; size_t v_i_boxed_222_; lean_object* v_res_223_; 
v_sz_boxed_221_ = lean_unbox_usize(v_sz_218_);
lean_dec(v_sz_218_);
v_i_boxed_222_ = lean_unbox_usize(v_i_219_);
lean_dec(v_i_219_);
v_res_223_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0(v_00_u03b1_216_, v_00_u03b2_217_, v_sz_boxed_221_, v_i_boxed_222_, v_bs_220_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_recv___redArg(lean_object* v_stream_224_){
_start:
{
size_t v_sz_226_; size_t v___x_227_; lean_object* v_selectables_228_; lean_object* v___x_229_; 
v_sz_226_ = lean_array_size(v_stream_224_);
v___x_227_ = ((size_t)0ULL);
v_selectables_228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(v_sz_226_, v___x_227_, v_stream_224_);
v___x_229_ = l_Std_Async_Selectable_one___redArg(v_selectables_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_recv___redArg___boxed(lean_object* v_stream_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Std_StreamMap_recv___redArg(v_stream_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_recv(lean_object* v_00_u03b1_233_, lean_object* v_00_u03b2_234_, lean_object* v_stream_235_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Std_StreamMap_recv___redArg(v_stream_235_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_recv___boxed(lean_object* v_00_u03b1_238_, lean_object* v_00_u03b2_239_, lean_object* v_stream_240_, lean_object* v_a_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Std_StreamMap_recv(v_00_u03b1_238_, v_00_u03b2_239_, v_stream_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_tryRecv___redArg(lean_object* v_stream_243_){
_start:
{
size_t v_sz_245_; size_t v___x_246_; lean_object* v_selectables_247_; lean_object* v___x_248_; 
v_sz_245_ = lean_array_size(v_stream_243_);
v___x_246_ = ((size_t)0ULL);
v_selectables_247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(v_sz_245_, v___x_246_, v_stream_243_);
v___x_248_ = l_Std_Async_Selectable_tryOne___redArg(v_selectables_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_tryRecv___redArg___boxed(lean_object* v_stream_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Std_StreamMap_tryRecv___redArg(v_stream_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_tryRecv(lean_object* v_00_u03b1_252_, lean_object* v_00_u03b2_253_, lean_object* v_stream_254_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Std_StreamMap_tryRecv___redArg(v_stream_254_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_tryRecv___boxed(lean_object* v_00_u03b1_257_, lean_object* v_00_u03b2_258_, lean_object* v_stream_259_, lean_object* v_a_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Std_StreamMap_tryRecv(v_00_u03b1_257_, v_00_u03b2_258_, v_stream_259_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_unregister___redArg(lean_object* v_inst_262_, lean_object* v_sm_263_, lean_object* v_name_264_){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = lean_array_get_size(v_sm_263_);
v___x_267_ = ((lean_object*)(l_Std_StreamMap_empty___redArg___closed__0));
v___x_268_ = ((lean_object*)(l_Std_StreamMap_register___redArg___closed__9));
v___x_269_ = lean_nat_dec_lt(v___x_265_, v___x_266_);
if (v___x_269_ == 0)
{
lean_dec(v_name_264_);
lean_dec_ref(v_sm_263_);
lean_dec_ref(v_inst_262_);
return v___x_267_;
}
else
{
lean_object* v___f_270_; uint8_t v___x_271_; 
v___f_270_ = lean_alloc_closure((void*)(l_Std_StreamMap_register___redArg___lam__0), 4, 2);
lean_closure_set(v___f_270_, 0, v_inst_262_);
lean_closure_set(v___f_270_, 1, v_name_264_);
v___x_271_ = lean_nat_dec_le(v___x_266_, v___x_266_);
if (v___x_271_ == 0)
{
if (v___x_269_ == 0)
{
lean_dec_ref(v___f_270_);
lean_dec_ref(v_sm_263_);
return v___x_267_;
}
else
{
size_t v___x_272_; size_t v___x_273_; lean_object* v___x_274_; 
v___x_272_ = ((size_t)0ULL);
v___x_273_ = lean_usize_of_nat(v___x_266_);
v___x_274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_268_, v___f_270_, v_sm_263_, v___x_272_, v___x_273_, v___x_267_);
return v___x_274_;
}
}
else
{
size_t v___x_275_; size_t v___x_276_; lean_object* v___x_277_; 
v___x_275_ = ((size_t)0ULL);
v___x_276_ = lean_usize_of_nat(v___x_266_);
v___x_277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_268_, v___f_270_, v_sm_263_, v___x_275_, v___x_276_, v___x_267_);
return v___x_277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_unregister(lean_object* v_00_u03b1_278_, lean_object* v_00_u03b2_279_, lean_object* v_inst_280_, lean_object* v_sm_281_, lean_object* v_name_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Std_StreamMap_unregister___redArg(v_inst_280_, v_sm_281_, v_name_282_);
return v___x_283_;
}
}
LEAN_EXPORT uint8_t l_Std_StreamMap_contains___redArg___lam__0(lean_object* v_inst_284_, lean_object* v_name_285_, lean_object* v_x_286_){
_start:
{
lean_object* v_fst_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v_fst_287_ = lean_ctor_get(v_x_286_, 0);
lean_inc(v_fst_287_);
lean_dec_ref(v_x_286_);
v___x_288_ = lean_apply_2(v_inst_284_, v_fst_287_, v_name_285_);
v___x_289_ = lean_unbox(v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_contains___redArg___lam__0___boxed(lean_object* v_inst_290_, lean_object* v_name_291_, lean_object* v_x_292_){
_start:
{
uint8_t v_res_293_; lean_object* v_r_294_; 
v_res_293_ = l_Std_StreamMap_contains___redArg___lam__0(v_inst_290_, v_name_291_, v_x_292_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
LEAN_EXPORT uint8_t l_Std_StreamMap_contains___redArg(lean_object* v_inst_295_, lean_object* v_sm_296_, lean_object* v_name_297_){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = lean_array_get_size(v_sm_296_);
v___x_300_ = ((lean_object*)(l_Std_StreamMap_register___redArg___closed__9));
v___x_301_ = lean_nat_dec_lt(v___x_298_, v___x_299_);
if (v___x_301_ == 0)
{
lean_dec(v_name_297_);
lean_dec_ref(v_sm_296_);
lean_dec_ref(v_inst_295_);
return v___x_301_;
}
else
{
if (v___x_301_ == 0)
{
lean_dec(v_name_297_);
lean_dec_ref(v_sm_296_);
lean_dec_ref(v_inst_295_);
return v___x_301_;
}
else
{
lean_object* v___f_302_; size_t v___x_303_; size_t v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___f_302_ = lean_alloc_closure((void*)(l_Std_StreamMap_contains___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_302_, 0, v_inst_295_);
lean_closure_set(v___f_302_, 1, v_name_297_);
v___x_303_ = ((size_t)0ULL);
v___x_304_ = lean_usize_of_nat(v___x_299_);
v___x_305_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_300_, v___f_302_, v_sm_296_, v___x_303_, v___x_304_);
v___x_306_ = lean_unbox(v___x_305_);
lean_dec(v___x_305_);
return v___x_306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_contains___redArg___boxed(lean_object* v_inst_307_, lean_object* v_sm_308_, lean_object* v_name_309_){
_start:
{
uint8_t v_res_310_; lean_object* v_r_311_; 
v_res_310_ = l_Std_StreamMap_contains___redArg(v_inst_307_, v_sm_308_, v_name_309_);
v_r_311_ = lean_box(v_res_310_);
return v_r_311_;
}
}
LEAN_EXPORT uint8_t l_Std_StreamMap_contains(lean_object* v_00_u03b1_312_, lean_object* v_00_u03b2_313_, lean_object* v_inst_314_, lean_object* v_sm_315_, lean_object* v_name_316_){
_start:
{
uint8_t v___x_317_; 
v___x_317_ = l_Std_StreamMap_contains___redArg(v_inst_314_, v_sm_315_, v_name_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_contains___boxed(lean_object* v_00_u03b1_318_, lean_object* v_00_u03b2_319_, lean_object* v_inst_320_, lean_object* v_sm_321_, lean_object* v_name_322_){
_start:
{
uint8_t v_res_323_; lean_object* v_r_324_; 
v_res_323_ = l_Std_StreamMap_contains(v_00_u03b1_318_, v_00_u03b2_319_, v_inst_320_, v_sm_321_, v_name_322_);
v_r_324_ = lean_box(v_res_323_);
return v_r_324_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_size___redArg(lean_object* v_sm_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = lean_array_get_size(v_sm_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_size___redArg___boxed(lean_object* v_sm_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Std_StreamMap_size___redArg(v_sm_327_);
lean_dec_ref(v_sm_327_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_size(lean_object* v_00_u03b1_329_, lean_object* v_00_u03b2_330_, lean_object* v_sm_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = lean_array_get_size(v_sm_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_size___boxed(lean_object* v_00_u03b1_333_, lean_object* v_00_u03b2_334_, lean_object* v_sm_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Std_StreamMap_size(v_00_u03b1_333_, v_00_u03b2_334_, v_sm_335_);
lean_dec_ref(v_sm_335_);
return v_res_336_;
}
}
LEAN_EXPORT uint8_t l_Std_StreamMap_isEmpty___redArg(lean_object* v_sm_337_){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_338_ = lean_array_get_size(v_sm_337_);
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_nat_dec_eq(v___x_338_, v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_isEmpty___redArg___boxed(lean_object* v_sm_341_){
_start:
{
uint8_t v_res_342_; lean_object* v_r_343_; 
v_res_342_ = l_Std_StreamMap_isEmpty___redArg(v_sm_341_);
lean_dec_ref(v_sm_341_);
v_r_343_ = lean_box(v_res_342_);
return v_r_343_;
}
}
LEAN_EXPORT uint8_t l_Std_StreamMap_isEmpty(lean_object* v_00_u03b1_344_, lean_object* v_00_u03b2_345_, lean_object* v_sm_346_){
_start:
{
uint8_t v___x_347_; 
v___x_347_ = l_Std_StreamMap_isEmpty___redArg(v_sm_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_isEmpty___boxed(lean_object* v_00_u03b1_348_, lean_object* v_00_u03b2_349_, lean_object* v_sm_350_){
_start:
{
uint8_t v_res_351_; lean_object* v_r_352_; 
v_res_351_ = l_Std_StreamMap_isEmpty(v_00_u03b1_348_, v_00_u03b2_349_, v_sm_350_);
lean_dec_ref(v_sm_350_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg(size_t v_sz_353_, size_t v_i_354_, lean_object* v_bs_355_){
_start:
{
uint8_t v___x_356_; 
v___x_356_ = lean_usize_dec_lt(v_i_354_, v_sz_353_);
if (v___x_356_ == 0)
{
return v_bs_355_;
}
else
{
lean_object* v_v_357_; lean_object* v_fst_358_; lean_object* v___x_359_; lean_object* v_bs_x27_360_; size_t v___x_361_; size_t v___x_362_; lean_object* v___x_363_; 
v_v_357_ = lean_array_uget_borrowed(v_bs_355_, v_i_354_);
v_fst_358_ = lean_ctor_get(v_v_357_, 0);
lean_inc(v_fst_358_);
v___x_359_ = lean_unsigned_to_nat(0u);
v_bs_x27_360_ = lean_array_uset(v_bs_355_, v_i_354_, v___x_359_);
v___x_361_ = ((size_t)1ULL);
v___x_362_ = lean_usize_add(v_i_354_, v___x_361_);
v___x_363_ = lean_array_uset(v_bs_x27_360_, v_i_354_, v_fst_358_);
v_i_354_ = v___x_362_;
v_bs_355_ = v___x_363_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg___boxed(lean_object* v_sz_365_, lean_object* v_i_366_, lean_object* v_bs_367_){
_start:
{
size_t v_sz_boxed_368_; size_t v_i_boxed_369_; lean_object* v_res_370_; 
v_sz_boxed_368_ = lean_unbox_usize(v_sz_365_);
lean_dec(v_sz_365_);
v_i_boxed_369_ = lean_unbox_usize(v_i_366_);
lean_dec(v_i_366_);
v_res_370_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg(v_sz_boxed_368_, v_i_boxed_369_, v_bs_367_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_keys___redArg(lean_object* v_sm_371_){
_start:
{
size_t v_sz_372_; size_t v___x_373_; lean_object* v___x_374_; 
v_sz_372_ = lean_array_size(v_sm_371_);
v___x_373_ = ((size_t)0ULL);
v___x_374_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg(v_sz_372_, v___x_373_, v_sm_371_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_keys(lean_object* v_00_u03b1_375_, lean_object* v_00_u03b2_376_, lean_object* v_sm_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Std_StreamMap_keys___redArg(v_sm_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0(lean_object* v_00_u03b1_379_, lean_object* v_00_u03b2_380_, size_t v_sz_381_, size_t v_i_382_, lean_object* v_bs_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg(v_sz_381_, v_i_382_, v_bs_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___boxed(lean_object* v_00_u03b1_385_, lean_object* v_00_u03b2_386_, lean_object* v_sz_387_, lean_object* v_i_388_, lean_object* v_bs_389_){
_start:
{
size_t v_sz_boxed_390_; size_t v_i_boxed_391_; lean_object* v_res_392_; 
v_sz_boxed_390_ = lean_unbox_usize(v_sz_387_);
lean_dec(v_sz_387_);
v_i_boxed_391_ = lean_unbox_usize(v_i_388_);
lean_dec(v_i_388_);
v_res_392_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0(v_00_u03b1_385_, v_00_u03b2_386_, v_sz_boxed_390_, v_i_boxed_391_, v_bs_389_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_get_x3f___redArg___lam__0(lean_object* v_inst_393_, lean_object* v_name_394_, lean_object* v___x_395_, lean_object* v___x_396_, lean_object* v_a_397_, lean_object* v_x_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_fst_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v_fst_400_ = lean_ctor_get(v_a_397_, 0);
lean_inc(v_fst_400_);
v___x_401_ = lean_apply_2(v_inst_393_, v_fst_400_, v_name_394_);
v___x_402_ = lean_unbox(v___x_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; 
lean_dec_ref(v_a_397_);
v___x_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_403_, 0, v___x_395_);
return v___x_403_;
}
else
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
lean_dec_ref(v___x_395_);
v___x_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_404_, 0, v_a_397_);
v___x_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v___x_396_);
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
return v___x_407_;
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_get_x3f___redArg___lam__0___boxed(lean_object* v_inst_408_, lean_object* v_name_409_, lean_object* v___x_410_, lean_object* v___x_411_, lean_object* v_a_412_, lean_object* v_x_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Std_StreamMap_get_x3f___redArg___lam__0(v_inst_408_, v_name_409_, v___x_410_, v___x_411_, v_a_412_, v_x_413_, v___y_414_);
lean_dec_ref(v___y_414_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_get_x3f___redArg(lean_object* v_inst_419_, lean_object* v_sm_420_, lean_object* v_name_421_){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___f_426_; size_t v_sz_427_; size_t v___x_428_; lean_object* v___x_429_; lean_object* v_fst_430_; 
v___x_422_ = ((lean_object*)(l_Std_StreamMap_register___redArg___closed__9));
v___x_423_ = lean_box(0);
v___x_424_ = lean_box(0);
v___x_425_ = ((lean_object*)(l_Std_StreamMap_get_x3f___redArg___closed__0));
v___f_426_ = lean_alloc_closure((void*)(l_Std_StreamMap_get_x3f___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_426_, 0, v_inst_419_);
lean_closure_set(v___f_426_, 1, v_name_421_);
lean_closure_set(v___f_426_, 2, v___x_425_);
lean_closure_set(v___f_426_, 3, v___x_424_);
v_sz_427_ = lean_array_size(v_sm_420_);
v___x_428_ = ((size_t)0ULL);
v___x_429_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_422_, v_sm_420_, v___f_426_, v_sz_427_, v___x_428_, v___x_425_);
v_fst_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_fst_430_);
lean_dec(v___x_429_);
if (lean_obj_tag(v_fst_430_) == 0)
{
return v___x_423_;
}
else
{
lean_object* v_val_431_; 
v_val_431_ = lean_ctor_get(v_fst_430_, 0);
lean_inc(v_val_431_);
lean_dec_ref_known(v_fst_430_, 1);
if (lean_obj_tag(v_val_431_) == 0)
{
return v___x_423_;
}
else
{
lean_object* v_val_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_441_; 
v_val_432_ = lean_ctor_get(v_val_431_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v_val_431_);
if (v_isSharedCheck_441_ == 0)
{
v___x_434_ = v_val_431_;
v_isShared_435_ = v_isSharedCheck_441_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_val_432_);
lean_dec(v_val_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_441_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v_snd_436_; lean_object* v_fst_437_; lean_object* v___x_439_; 
v_snd_436_ = lean_ctor_get(v_val_432_, 1);
lean_inc(v_snd_436_);
lean_dec(v_val_432_);
v_fst_437_ = lean_ctor_get(v_snd_436_, 0);
lean_inc(v_fst_437_);
lean_dec(v_snd_436_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v_fst_437_);
v___x_439_ = v___x_434_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_fst_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_get_x3f(lean_object* v_00_u03b1_442_, lean_object* v_00_u03b2_443_, lean_object* v_inst_444_, lean_object* v_sm_445_, lean_object* v_name_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Std_StreamMap_get_x3f___redArg(v_inst_444_, v_sm_445_, v_name_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(lean_object* v_pred_448_, lean_object* v_as_449_, size_t v_i_450_, size_t v_stop_451_, lean_object* v_b_452_){
_start:
{
lean_object* v___y_454_; uint8_t v___x_458_; 
v___x_458_ = lean_usize_dec_eq(v_i_450_, v_stop_451_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; lean_object* v_fst_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_459_ = lean_array_uget_borrowed(v_as_449_, v_i_450_);
v_fst_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc_ref(v_pred_448_);
lean_inc(v_fst_460_);
v___x_461_ = lean_apply_1(v_pred_448_, v_fst_460_);
v___x_462_ = lean_unbox(v___x_461_);
if (v___x_462_ == 0)
{
v___y_454_ = v_b_452_;
goto v___jp_453_;
}
else
{
lean_object* v___x_463_; 
lean_inc(v___x_459_);
v___x_463_ = lean_array_push(v_b_452_, v___x_459_);
v___y_454_ = v___x_463_;
goto v___jp_453_;
}
}
else
{
lean_dec_ref(v_pred_448_);
return v_b_452_;
}
v___jp_453_:
{
size_t v___x_455_; size_t v___x_456_; 
v___x_455_ = ((size_t)1ULL);
v___x_456_ = lean_usize_add(v_i_450_, v___x_455_);
v_i_450_ = v___x_456_;
v_b_452_ = v___y_454_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg___boxed(lean_object* v_pred_464_, lean_object* v_as_465_, lean_object* v_i_466_, lean_object* v_stop_467_, lean_object* v_b_468_){
_start:
{
size_t v_i_boxed_469_; size_t v_stop_boxed_470_; lean_object* v_res_471_; 
v_i_boxed_469_ = lean_unbox_usize(v_i_466_);
lean_dec(v_i_466_);
v_stop_boxed_470_ = lean_unbox_usize(v_stop_467_);
lean_dec(v_stop_467_);
v_res_471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(v_pred_464_, v_as_465_, v_i_boxed_469_, v_stop_boxed_470_, v_b_468_);
lean_dec_ref(v_as_465_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_filterByName___redArg(lean_object* v_sm_472_, lean_object* v_pred_473_){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_array_get_size(v_sm_472_);
v___x_476_ = ((lean_object*)(l_Std_StreamMap_empty___redArg___closed__0));
v___x_477_ = lean_nat_dec_lt(v___x_474_, v___x_475_);
if (v___x_477_ == 0)
{
lean_dec_ref(v_pred_473_);
return v___x_476_;
}
else
{
uint8_t v___x_478_; 
v___x_478_ = lean_nat_dec_le(v___x_475_, v___x_475_);
if (v___x_478_ == 0)
{
if (v___x_477_ == 0)
{
lean_dec_ref(v_pred_473_);
return v___x_476_;
}
else
{
size_t v___x_479_; size_t v___x_480_; lean_object* v___x_481_; 
v___x_479_ = ((size_t)0ULL);
v___x_480_ = lean_usize_of_nat(v___x_475_);
v___x_481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(v_pred_473_, v_sm_472_, v___x_479_, v___x_480_, v___x_476_);
return v___x_481_;
}
}
else
{
size_t v___x_482_; size_t v___x_483_; lean_object* v___x_484_; 
v___x_482_ = ((size_t)0ULL);
v___x_483_ = lean_usize_of_nat(v___x_475_);
v___x_484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(v_pred_473_, v_sm_472_, v___x_482_, v___x_483_, v___x_476_);
return v___x_484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_filterByName___redArg___boxed(lean_object* v_sm_485_, lean_object* v_pred_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Std_StreamMap_filterByName___redArg(v_sm_485_, v_pred_486_);
lean_dec_ref(v_sm_485_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_filterByName(lean_object* v_00_u03b1_488_, lean_object* v_00_u03b2_489_, lean_object* v_sm_490_, lean_object* v_pred_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Std_StreamMap_filterByName___redArg(v_sm_490_, v_pred_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_filterByName___boxed(lean_object* v_00_u03b1_493_, lean_object* v_00_u03b2_494_, lean_object* v_sm_495_, lean_object* v_pred_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Std_StreamMap_filterByName(v_00_u03b1_493_, v_00_u03b2_494_, v_sm_495_, v_pred_496_);
lean_dec_ref(v_sm_495_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0(lean_object* v_00_u03b1_498_, lean_object* v_00_u03b2_499_, lean_object* v_pred_500_, lean_object* v_as_501_, size_t v_i_502_, size_t v_stop_503_, lean_object* v_b_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(v_pred_500_, v_as_501_, v_i_502_, v_stop_503_, v_b_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___boxed(lean_object* v_00_u03b1_506_, lean_object* v_00_u03b2_507_, lean_object* v_pred_508_, lean_object* v_as_509_, lean_object* v_i_510_, lean_object* v_stop_511_, lean_object* v_b_512_){
_start:
{
size_t v_i_boxed_513_; size_t v_stop_boxed_514_; lean_object* v_res_515_; 
v_i_boxed_513_ = lean_unbox_usize(v_i_510_);
lean_dec(v_i_510_);
v_stop_boxed_514_ = lean_unbox_usize(v_stop_511_);
lean_dec(v_stop_511_);
v_res_515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0(v_00_u03b1_506_, v_00_u03b2_507_, v_pred_508_, v_as_509_, v_i_boxed_513_, v_stop_boxed_514_, v_b_512_);
lean_dec_ref(v_as_509_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg(size_t v_sz_516_, size_t v_i_517_, lean_object* v_bs_518_){
_start:
{
uint8_t v___x_519_; 
v___x_519_ = lean_usize_dec_lt(v_i_517_, v_sz_516_);
if (v___x_519_ == 0)
{
return v_bs_518_;
}
else
{
lean_object* v_v_520_; lean_object* v_snd_521_; lean_object* v_fst_522_; lean_object* v_fst_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_536_; 
v_v_520_ = lean_array_uget_borrowed(v_bs_518_, v_i_517_);
v_snd_521_ = lean_ctor_get(v_v_520_, 1);
lean_inc(v_snd_521_);
v_fst_522_ = lean_ctor_get(v_v_520_, 0);
lean_inc(v_fst_522_);
v_fst_523_ = lean_ctor_get(v_snd_521_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v_snd_521_);
if (v_isSharedCheck_536_ == 0)
{
lean_object* v_unused_537_; 
v_unused_537_ = lean_ctor_get(v_snd_521_, 1);
lean_dec(v_unused_537_);
v___x_525_ = v_snd_521_;
v_isShared_526_ = v_isSharedCheck_536_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_fst_523_);
lean_dec(v_snd_521_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_536_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v_bs_x27_528_; lean_object* v___x_530_; 
v___x_527_ = lean_unsigned_to_nat(0u);
v_bs_x27_528_ = lean_array_uset(v_bs_518_, v_i_517_, v___x_527_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 1, v_fst_523_);
lean_ctor_set(v___x_525_, 0, v_fst_522_);
v___x_530_ = v___x_525_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_fst_522_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_fst_523_);
v___x_530_ = v_reuseFailAlloc_535_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
size_t v___x_531_; size_t v___x_532_; lean_object* v___x_533_; 
v___x_531_ = ((size_t)1ULL);
v___x_532_ = lean_usize_add(v_i_517_, v___x_531_);
v___x_533_ = lean_array_uset(v_bs_x27_528_, v_i_517_, v___x_530_);
v_i_517_ = v___x_532_;
v_bs_518_ = v___x_533_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg___boxed(lean_object* v_sz_538_, lean_object* v_i_539_, lean_object* v_bs_540_){
_start:
{
size_t v_sz_boxed_541_; size_t v_i_boxed_542_; lean_object* v_res_543_; 
v_sz_boxed_541_ = lean_unbox_usize(v_sz_538_);
lean_dec(v_sz_538_);
v_i_boxed_542_ = lean_unbox_usize(v_i_539_);
lean_dec(v_i_539_);
v_res_543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg(v_sz_boxed_541_, v_i_boxed_542_, v_bs_540_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_toArray___redArg(lean_object* v_sm_544_){
_start:
{
size_t v_sz_545_; size_t v___x_546_; lean_object* v___x_547_; 
v_sz_545_ = lean_array_size(v_sm_544_);
v___x_546_ = ((size_t)0ULL);
v___x_547_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg(v_sz_545_, v___x_546_, v_sm_544_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_toArray(lean_object* v_00_u03b1_548_, lean_object* v_00_u03b2_549_, lean_object* v_sm_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Std_StreamMap_toArray___redArg(v_sm_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0(lean_object* v_00_u03b1_552_, lean_object* v_00_u03b2_553_, size_t v_sz_554_, size_t v_i_555_, lean_object* v_bs_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg(v_sz_554_, v_i_555_, v_bs_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___boxed(lean_object* v_00_u03b1_558_, lean_object* v_00_u03b2_559_, lean_object* v_sz_560_, lean_object* v_i_561_, lean_object* v_bs_562_){
_start:
{
size_t v_sz_boxed_563_; size_t v_i_boxed_564_; lean_object* v_res_565_; 
v_sz_boxed_563_ = lean_unbox_usize(v_sz_560_);
lean_dec(v_sz_560_);
v_i_boxed_564_ = lean_unbox_usize(v_i_561_);
lean_dec(v_i_561_);
v_res_565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0(v_00_u03b1_558_, v_00_u03b2_559_, v_sz_boxed_563_, v_i_boxed_564_, v_bs_562_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(lean_object* v_as_566_, size_t v_i_567_, size_t v_stop_568_, lean_object* v_b_569_){
_start:
{
uint8_t v___x_571_; 
v___x_571_ = lean_usize_dec_eq(v_i_567_, v_stop_568_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; lean_object* v_snd_573_; lean_object* v_snd_574_; lean_object* v___x_575_; 
v___x_572_ = lean_array_uget_borrowed(v_as_566_, v_i_567_);
v_snd_573_ = lean_ctor_get(v___x_572_, 1);
v_snd_574_ = lean_ctor_get(v_snd_573_, 1);
lean_inc(v_snd_574_);
v___x_575_ = lean_apply_1(v_snd_574_, lean_box(0));
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; size_t v___x_577_; size_t v___x_578_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_a_576_);
lean_dec_ref_known(v___x_575_, 1);
v___x_577_ = ((size_t)1ULL);
v___x_578_ = lean_usize_add(v_i_567_, v___x_577_);
v_i_567_ = v___x_578_;
v_b_569_ = v_a_576_;
goto _start;
}
else
{
return v___x_575_;
}
}
else
{
lean_object* v___x_580_; 
v___x_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_580_, 0, v_b_569_);
return v___x_580_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg___boxed(lean_object* v_as_581_, lean_object* v_i_582_, lean_object* v_stop_583_, lean_object* v_b_584_, lean_object* v___y_585_){
_start:
{
size_t v_i_boxed_586_; size_t v_stop_boxed_587_; lean_object* v_res_588_; 
v_i_boxed_586_ = lean_unbox_usize(v_i_582_);
lean_dec(v_i_582_);
v_stop_boxed_587_ = lean_unbox_usize(v_stop_583_);
lean_dec(v_stop_583_);
v_res_588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(v_as_581_, v_i_boxed_586_, v_stop_boxed_587_, v_b_584_);
lean_dec_ref(v_as_581_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_close___redArg(lean_object* v_sm_589_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_591_ = lean_unsigned_to_nat(0u);
v___x_592_ = lean_array_get_size(v_sm_589_);
v___x_593_ = lean_box(0);
v___x_594_ = lean_nat_dec_lt(v___x_591_, v___x_592_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; 
v___x_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_593_);
return v___x_595_;
}
else
{
uint8_t v___x_596_; 
v___x_596_ = lean_nat_dec_le(v___x_592_, v___x_592_);
if (v___x_596_ == 0)
{
if (v___x_594_ == 0)
{
lean_object* v___x_597_; 
v___x_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_593_);
return v___x_597_;
}
else
{
size_t v___x_598_; size_t v___x_599_; lean_object* v___x_600_; 
v___x_598_ = ((size_t)0ULL);
v___x_599_ = lean_usize_of_nat(v___x_592_);
v___x_600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(v_sm_589_, v___x_598_, v___x_599_, v___x_593_);
return v___x_600_;
}
}
else
{
size_t v___x_601_; size_t v___x_602_; lean_object* v___x_603_; 
v___x_601_ = ((size_t)0ULL);
v___x_602_ = lean_usize_of_nat(v___x_592_);
v___x_603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(v_sm_589_, v___x_601_, v___x_602_, v___x_593_);
return v___x_603_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_close___redArg___boxed(lean_object* v_sm_604_, lean_object* v_a_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Std_StreamMap_close___redArg(v_sm_604_);
lean_dec_ref(v_sm_604_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_close(lean_object* v_00_u03b1_607_, lean_object* v_00_u03b2_608_, lean_object* v_sm_609_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Std_StreamMap_close___redArg(v_sm_609_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Std_StreamMap_close___boxed(lean_object* v_00_u03b1_612_, lean_object* v_00_u03b2_613_, lean_object* v_sm_614_, lean_object* v_a_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Std_StreamMap_close(v_00_u03b1_612_, v_00_u03b2_613_, v_sm_614_);
lean_dec_ref(v_sm_614_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0(lean_object* v_00_u03b1_617_, lean_object* v_00_u03b2_618_, lean_object* v_as_619_, size_t v_i_620_, size_t v_stop_621_, lean_object* v_b_622_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(v_as_619_, v_i_620_, v_stop_621_, v_b_622_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___boxed(lean_object* v_00_u03b1_625_, lean_object* v_00_u03b2_626_, lean_object* v_as_627_, lean_object* v_i_628_, lean_object* v_stop_629_, lean_object* v_b_630_, lean_object* v___y_631_){
_start:
{
size_t v_i_boxed_632_; size_t v_stop_boxed_633_; lean_object* v_res_634_; 
v_i_boxed_632_ = lean_unbox_usize(v_i_628_);
lean_dec(v_i_628_);
v_stop_boxed_633_ = lean_unbox_usize(v_stop_629_);
lean_dec(v_stop_629_);
v_res_634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0(v_00_u03b1_625_, v_00_u03b2_626_, v_as_627_, v_i_boxed_632_, v_stop_boxed_633_, v_b_630_);
lean_dec_ref(v_as_627_);
return v_res_634_;
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
