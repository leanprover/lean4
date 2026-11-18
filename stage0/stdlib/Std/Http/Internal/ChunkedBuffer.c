// Lean compiler output
// Module: Std.Http.Internal.ChunkedBuffer
// Imports: import Init.Data.ToString import Init.Data.Array.Lemmas public import Init.Data.String.Basic public import Init.Data.ByteArray.Basic
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_byte_array(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_ByteArray_isEmpty(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static const lean_array_object l_Std_Http_Internal_ChunkedBuffer_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_empty___closed__0 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_empty___closed__0_value;
static const lean_ctor_object l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Internal_ChunkedBuffer_empty___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_empty___closed__1 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_Internal_ChunkedBuffer_empty = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__0 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__0_value;
static const lean_closure_object l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__1 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__1_value;
static const lean_closure_object l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__2 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__2_value;
static const lean_closure_object l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__3 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__3_value;
static const lean_closure_object l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__4 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__4_value;
static const lean_closure_object l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__5 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__5_value;
static const lean_closure_object l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__6 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__6_value;
static const lean_ctor_object l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__0_value),((lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__1_value)}};
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__7 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__7_value;
static const lean_ctor_object l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__7_value),((lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__2_value),((lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__3_value),((lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__4_value),((lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__5_value)}};
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__8 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__8_value;
static const lean_ctor_object l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__8_value),((lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__6_value)}};
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_ChunkedBuffer_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_isEmpty___boxed(lean_object*);
LEAN_EXPORT const lean_object* l_Std_Http_Internal_ChunkedBuffer_instInhabited = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_Internal_ChunkedBuffer_instEmptyCollection = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_push(lean_object* v_c_7_, lean_object* v_b_8_){
_start:
{
uint8_t v___x_9_; 
v___x_9_ = l_ByteArray_isEmpty(v_b_8_);
if (v___x_9_ == 0)
{
lean_object* v_data_10_; lean_object* v_size_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_21_; 
v_data_10_ = lean_ctor_get(v_c_7_, 0);
v_size_11_ = lean_ctor_get(v_c_7_, 1);
v_isSharedCheck_21_ = !lean_is_exclusive(v_c_7_);
if (v_isSharedCheck_21_ == 0)
{
v___x_13_ = v_c_7_;
v_isShared_14_ = v_isSharedCheck_21_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_size_11_);
lean_inc(v_data_10_);
lean_dec(v_c_7_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_21_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_19_; 
lean_inc_ref(v_b_8_);
v___x_15_ = lean_array_push(v_data_10_, v_b_8_);
v___x_16_ = lean_byte_array_size(v_b_8_);
lean_dec_ref(v_b_8_);
v___x_17_ = lean_nat_add(v_size_11_, v___x_16_);
lean_dec(v_size_11_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 1, v___x_17_);
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_19_ = v___x_13_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v___x_15_);
lean_ctor_set(v_reuseFailAlloc_20_, 1, v___x_17_);
v___x_19_ = v_reuseFailAlloc_20_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
return v___x_19_;
}
}
}
else
{
lean_dec_ref(v_b_8_);
return v_c_7_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0(uint8_t v___x_22_, lean_object* v_x1_23_, lean_object* v_x2_24_){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_25_ = lean_unsigned_to_nat(0u);
v___x_26_ = lean_byte_array_size(v_x1_23_);
v___x_27_ = lean_byte_array_size(v_x2_24_);
v___x_28_ = lean_byte_array_copy_slice(v_x2_24_, v___x_25_, v_x1_23_, v___x_26_, v___x_27_, v___x_22_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0___boxed(lean_object* v___x_29_, lean_object* v_x1_30_, lean_object* v_x2_31_){
_start:
{
uint8_t v___x_94__boxed_32_; lean_object* v_res_33_; 
v___x_94__boxed_32_ = lean_unbox(v___x_29_);
v_res_33_ = l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0(v___x_94__boxed_32_, v_x1_30_, v_x2_31_);
lean_dec_ref(v_x2_31_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray(lean_object* v_cb_53_){
_start:
{
lean_object* v_data_54_; lean_object* v_size_55_; lean_object* v___x_56_; lean_object* v___x_57_; uint8_t v___x_58_; 
v_data_54_ = lean_ctor_get(v_cb_53_, 0);
lean_inc_ref(v_data_54_);
v_size_55_ = lean_ctor_get(v_cb_53_, 1);
lean_inc(v_size_55_);
lean_dec_ref(v_cb_53_);
v___x_56_ = lean_unsigned_to_nat(1u);
v___x_57_ = lean_array_get_size(v_data_54_);
v___x_58_ = lean_nat_dec_eq(v___x_56_, v___x_57_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_59_ = lean_mk_empty_byte_array(v_size_55_);
lean_dec(v_size_55_);
v___x_60_ = lean_unsigned_to_nat(0u);
v___x_61_ = ((lean_object*)(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9));
v___x_62_ = lean_nat_dec_lt(v___x_60_, v___x_57_);
if (v___x_62_ == 0)
{
lean_dec_ref(v_data_54_);
return v___x_59_;
}
else
{
lean_object* v___x_63_; lean_object* v___f_64_; size_t v___x_65_; size_t v___x_66_; lean_object* v___x_67_; 
v___x_63_ = lean_box(v___x_58_);
v___f_64_ = lean_alloc_closure((void*)(l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0___boxed), 3, 1);
lean_closure_set(v___f_64_, 0, v___x_63_);
v___x_65_ = ((size_t)0ULL);
v___x_66_ = lean_usize_of_nat(v___x_57_);
v___x_67_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_61_, v___f_64_, v_data_54_, v___x_65_, v___x_66_, v___x_59_);
return v___x_67_;
}
}
else
{
lean_object* v___x_68_; lean_object* v___x_69_; 
lean_dec(v_size_55_);
v___x_68_ = lean_unsigned_to_nat(0u);
v___x_69_ = lean_array_fget(v_data_54_, v___x_68_);
lean_dec_ref(v_data_54_);
return v___x_69_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_ChunkedBuffer_isEmpty(lean_object* v_bb_70_){
_start:
{
lean_object* v_size_71_; lean_object* v___x_72_; uint8_t v___x_73_; 
v_size_71_ = lean_ctor_get(v_bb_70_, 1);
v___x_72_ = lean_unsigned_to_nat(0u);
v___x_73_ = lean_nat_dec_eq(v_size_71_, v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_isEmpty___boxed(lean_object* v_bb_74_){
_start:
{
uint8_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l_Std_Http_Internal_ChunkedBuffer_isEmpty(v_bb_74_);
lean_dec_ref(v_bb_74_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Internal_ChunkedBuffer(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ByteArray_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Internal_ChunkedBuffer(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Internal_ChunkedBuffer(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Internal_ChunkedBuffer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Internal_ChunkedBuffer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Internal_ChunkedBuffer(builtin);
}
#ifdef __cplusplus
}
#endif
