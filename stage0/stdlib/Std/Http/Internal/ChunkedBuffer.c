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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
lean_object* lean_byte_array_mk(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static const lean_array_object l_Std_Http_Internal_ChunkedBuffer_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_empty___closed__0 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_empty___closed__0_value;
static const lean_ctor_object l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Internal_ChunkedBuffer_empty___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_empty___closed__1 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_Internal_ChunkedBuffer_empty = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_write(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_writeChar(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_writeChar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_writeString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_writeString___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_ofByteArray(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Internal_ChunkedBuffer_ofArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_ofArray___closed__0 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_ofArray___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_ofArray(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_ChunkedBuffer_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_isEmpty___boxed(lean_object*);
LEAN_EXPORT const lean_object* l_Std_Http_Internal_ChunkedBuffer_instInhabited = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_Internal_ChunkedBuffer_instEmptyCollection = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value;
static const lean_closure_object l_Std_Http_Internal_ChunkedBuffer_instCoeByteArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_ChunkedBuffer_ofByteArray, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_instCoeByteArray___closed__0 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_instCoeByteArray___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Internal_ChunkedBuffer_instCoeByteArray = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_instCoeByteArray___closed__0_value;
static const lean_closure_object l_Std_Http_Internal_ChunkedBuffer_instCoeArrayByteArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_ChunkedBuffer_ofArray, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_instCoeArrayByteArray___closed__0 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_instCoeArrayByteArray___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Internal_ChunkedBuffer_instCoeArrayByteArray = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_instCoeArrayByteArray___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_push(lean_object* v_c_7_, lean_object* v_b_8_){
_start:
{
lean_object* v_data_9_; lean_object* v_size_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_20_; 
v_data_9_ = lean_ctor_get(v_c_7_, 0);
v_size_10_ = lean_ctor_get(v_c_7_, 1);
v_isSharedCheck_20_ = !lean_is_exclusive(v_c_7_);
if (v_isSharedCheck_20_ == 0)
{
v___x_12_ = v_c_7_;
v_isShared_13_ = v_isSharedCheck_20_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_size_10_);
lean_inc(v_data_9_);
lean_dec(v_c_7_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_20_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_18_; 
lean_inc_ref(v_b_8_);
v___x_14_ = lean_array_push(v_data_9_, v_b_8_);
v___x_15_ = lean_byte_array_size(v_b_8_);
lean_dec_ref(v_b_8_);
v___x_16_ = lean_nat_add(v_size_10_, v___x_15_);
lean_dec(v_size_10_);
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 1, v___x_16_);
lean_ctor_set(v___x_12_, 0, v___x_14_);
v___x_18_ = v___x_12_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_19_; 
v_reuseFailAlloc_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_19_, 0, v___x_14_);
lean_ctor_set(v_reuseFailAlloc_19_, 1, v___x_16_);
v___x_18_ = v_reuseFailAlloc_19_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
return v___x_18_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_write(lean_object* v_buffer_21_, lean_object* v_data_22_){
_start:
{
lean_object* v_data_23_; lean_object* v_size_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_34_; 
v_data_23_ = lean_ctor_get(v_buffer_21_, 0);
v_size_24_ = lean_ctor_get(v_buffer_21_, 1);
v_isSharedCheck_34_ = !lean_is_exclusive(v_buffer_21_);
if (v_isSharedCheck_34_ == 0)
{
v___x_26_ = v_buffer_21_;
v_isShared_27_ = v_isSharedCheck_34_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_size_24_);
lean_inc(v_data_23_);
lean_dec(v_buffer_21_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_34_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_32_; 
lean_inc_ref(v_data_22_);
v___x_28_ = lean_array_push(v_data_23_, v_data_22_);
v___x_29_ = lean_byte_array_size(v_data_22_);
lean_dec_ref(v_data_22_);
v___x_30_ = lean_nat_add(v_size_24_, v___x_29_);
lean_dec(v_size_24_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 1, v___x_30_);
lean_ctor_set(v___x_26_, 0, v___x_28_);
v___x_32_ = v___x_26_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v___x_28_);
lean_ctor_set(v_reuseFailAlloc_33_, 1, v___x_30_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_append(lean_object* v_buffer_35_, lean_object* v_data_36_){
_start:
{
lean_object* v_data_37_; lean_object* v_size_38_; lean_object* v_data_39_; lean_object* v_size_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_49_; 
v_data_37_ = lean_ctor_get(v_buffer_35_, 0);
lean_inc_ref(v_data_37_);
v_size_38_ = lean_ctor_get(v_buffer_35_, 1);
lean_inc(v_size_38_);
lean_dec_ref(v_buffer_35_);
v_data_39_ = lean_ctor_get(v_data_36_, 0);
v_size_40_ = lean_ctor_get(v_data_36_, 1);
v_isSharedCheck_49_ = !lean_is_exclusive(v_data_36_);
if (v_isSharedCheck_49_ == 0)
{
v___x_42_ = v_data_36_;
v_isShared_43_ = v_isSharedCheck_49_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_size_40_);
lean_inc(v_data_39_);
lean_dec(v_data_36_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_49_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_47_; 
v___x_44_ = l_Array_append___redArg(v_data_37_, v_data_39_);
lean_dec_ref(v_data_39_);
v___x_45_ = lean_nat_add(v_size_38_, v_size_40_);
lean_dec(v_size_40_);
lean_dec(v_size_38_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 1, v___x_45_);
lean_ctor_set(v___x_42_, 0, v___x_44_);
v___x_47_ = v___x_42_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v___x_44_);
lean_ctor_set(v_reuseFailAlloc_48_, 1, v___x_45_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
return v___x_47_;
}
}
}
}
lean_object* l_Std_Http_Internal_ChunkedBuffer_writeChar(lean_object* v_buffer_50_, uint32_t v_data_51_){
_start:
{
lean_object* v_data_52_; lean_object* v_size_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_69_; 
v_data_52_ = lean_ctor_get(v_buffer_50_, 0);
v_size_53_ = lean_ctor_get(v_buffer_50_, 1);
v_isSharedCheck_69_ = !lean_is_exclusive(v_buffer_50_);
if (v_isSharedCheck_69_ == 0)
{
v___x_55_ = v_buffer_50_;
v_isShared_56_ = v_isSharedCheck_69_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_size_53_);
lean_inc(v_data_52_);
lean_dec(v_buffer_50_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_69_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
uint8_t v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_67_; 
v___x_57_ = lean_uint32_to_uint8(v_data_51_);
v___x_58_ = lean_unsigned_to_nat(1u);
v___x_59_ = lean_mk_empty_array_with_capacity(v___x_58_);
v___x_60_ = lean_box(v___x_57_);
v___x_61_ = lean_array_push(v___x_59_, v___x_60_);
v___x_62_ = lean_byte_array_mk(v___x_61_);
lean_inc_ref(v___x_62_);
v___x_63_ = lean_array_push(v_data_52_, v___x_62_);
v___x_64_ = lean_byte_array_size(v___x_62_);
lean_dec_ref(v___x_62_);
v___x_65_ = lean_nat_add(v_size_53_, v___x_64_);
lean_dec(v_size_53_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 1, v___x_65_);
lean_ctor_set(v___x_55_, 0, v___x_63_);
v___x_67_ = v___x_55_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v___x_63_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v___x_65_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_ChunkedBuffer_writeChar_0interp(lean_interpreter_value* stack)
{
lean_object* v_buffer_50_ = stack[0].m_obj;
uint32_t v_data_51_ = stack[1].m_num;
lean_object* v_res_70_;
v_res_70_ = l_Std_Http_Internal_ChunkedBuffer_writeChar(v_buffer_50_, v_data_51_);
stack->m_obj
 = v_res_70_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_writeChar___boxed(lean_object* v_buffer_71_, lean_object* v_data_72_){
_start:
{
uint32_t v_data_boxed_73_; lean_object* v_res_74_; 
v_data_boxed_73_ = lean_unbox_uint32(v_data_72_);
lean_dec(v_data_72_);
v_res_74_ = l_Std_Http_Internal_ChunkedBuffer_writeChar(v_buffer_71_, v_data_boxed_73_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_writeString(lean_object* v_buffer_75_, lean_object* v_data_76_){
_start:
{
lean_object* v_data_77_; lean_object* v_size_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_89_; 
v_data_77_ = lean_ctor_get(v_buffer_75_, 0);
v_size_78_ = lean_ctor_get(v_buffer_75_, 1);
v_isSharedCheck_89_ = !lean_is_exclusive(v_buffer_75_);
if (v_isSharedCheck_89_ == 0)
{
v___x_80_ = v_buffer_75_;
v_isShared_81_ = v_isSharedCheck_89_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_size_78_);
lean_inc(v_data_77_);
lean_dec(v_buffer_75_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_89_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_82_ = lean_string_to_utf8(v_data_76_);
lean_inc_ref(v___x_82_);
v___x_83_ = lean_array_push(v_data_77_, v___x_82_);
v___x_84_ = lean_byte_array_size(v___x_82_);
lean_dec_ref(v___x_82_);
v___x_85_ = lean_nat_add(v_size_78_, v___x_84_);
lean_dec(v_size_78_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 1, v___x_85_);
lean_ctor_set(v___x_80_, 0, v___x_83_);
v___x_87_ = v___x_80_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_83_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_writeString___boxed(lean_object* v_buffer_90_, lean_object* v_data_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Std_Http_Internal_ChunkedBuffer_writeString(v_buffer_90_, v_data_91_);
lean_dec_ref(v_data_91_);
return v_res_92_;
}
}
lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0(uint8_t v___x_93_, lean_object* v_x1_94_, lean_object* v_x2_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_96_ = lean_unsigned_to_nat(0u);
v___x_97_ = lean_byte_array_size(v_x1_94_);
v___x_98_ = lean_byte_array_size(v_x2_95_);
v___x_99_ = lean_byte_array_copy_slice(v_x2_95_, v___x_96_, v_x1_94_, v___x_97_, v___x_98_, v___x_93_);
return v___x_99_;
}
}
LEAN_EXPORT void l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_93_ = stack[0].m_num;
lean_object* v_x1_94_ = stack[1].m_obj;
lean_object* v_x2_95_ = stack[2].m_obj;
lean_object* v_res_100_;
v_res_100_ = l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0(v___x_93_, v_x1_94_, v_x2_95_);
stack->m_obj
 = v_res_100_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0___boxed(lean_object* v___x_101_, lean_object* v_x1_102_, lean_object* v_x2_103_){
_start:
{
uint8_t v___x_94__boxed_104_; lean_object* v_res_105_; 
v___x_94__boxed_104_ = lean_unbox(v___x_101_);
v_res_105_ = l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0(v___x_94__boxed_104_, v_x1_102_, v_x2_103_);
lean_dec_ref(v_x2_103_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray(lean_object* v_cb_125_){
_start:
{
lean_object* v_data_126_; lean_object* v_size_127_; lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v_data_126_ = lean_ctor_get(v_cb_125_, 0);
lean_inc_ref(v_data_126_);
v_size_127_ = lean_ctor_get(v_cb_125_, 1);
lean_inc(v_size_127_);
lean_dec_ref(v_cb_125_);
v___x_128_ = lean_unsigned_to_nat(1u);
v___x_129_ = lean_array_get_size(v_data_126_);
v___x_130_ = lean_nat_dec_eq(v___x_128_, v___x_129_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_131_ = lean_mk_empty_byte_array(v_size_127_);
lean_dec(v_size_127_);
v___x_132_ = lean_unsigned_to_nat(0u);
v___x_133_ = ((lean_object*)(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9));
v___x_134_ = lean_nat_dec_lt(v___x_132_, v___x_129_);
if (v___x_134_ == 0)
{
lean_dec_ref(v_data_126_);
return v___x_131_;
}
else
{
lean_object* v___x_135_; lean_object* v___f_136_; uint8_t v___x_137_; 
v___x_135_ = lean_box(v___x_130_);
v___f_136_ = lean_alloc_closure((void*)(l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0___boxed), 3, 1);
lean_closure_set(v___f_136_, 0, v___x_135_);
v___x_137_ = lean_nat_dec_le(v___x_129_, v___x_129_);
if (v___x_137_ == 0)
{
if (v___x_134_ == 0)
{
lean_dec_ref(v___f_136_);
lean_dec_ref(v_data_126_);
return v___x_131_;
}
else
{
size_t v___x_138_; size_t v___x_139_; lean_object* v___x_140_; 
v___x_138_ = ((size_t)0ULL);
v___x_139_ = lean_usize_of_nat(v___x_129_);
v___x_140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_133_, v___f_136_, v_data_126_, v___x_138_, v___x_139_, v___x_131_);
return v___x_140_;
}
}
else
{
size_t v___x_141_; size_t v___x_142_; lean_object* v___x_143_; 
v___x_141_ = ((size_t)0ULL);
v___x_142_ = lean_usize_of_nat(v___x_129_);
v___x_143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_133_, v___f_136_, v_data_126_, v___x_141_, v___x_142_, v___x_131_);
return v___x_143_;
}
}
}
else
{
lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec(v_size_127_);
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = lean_array_fget(v_data_126_, v___x_144_);
lean_dec_ref(v_data_126_);
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_ofByteArray(lean_object* v_bs_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_147_ = lean_unsigned_to_nat(1u);
v___x_148_ = lean_mk_empty_array_with_capacity(v___x_147_);
lean_inc_ref(v_bs_146_);
v___x_149_ = lean_array_push(v___x_148_, v_bs_146_);
v___x_150_ = lean_byte_array_size(v_bs_146_);
lean_dec_ref(v_bs_146_);
v___x_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_149_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0(lean_object* v_x1_152_, lean_object* v_x2_153_){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_byte_array_size(v_x2_153_);
v___x_155_ = lean_nat_add(v_x1_152_, v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0___boxed(lean_object* v_x1_156_, lean_object* v_x2_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0(v_x1_156_, v_x2_157_);
lean_dec_ref(v_x2_157_);
lean_dec(v_x1_156_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_ofArray(lean_object* v_bs_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_161_ = lean_unsigned_to_nat(0u);
v___x_162_ = lean_array_get_size(v_bs_160_);
v___x_163_ = ((lean_object*)(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9));
v___x_164_ = lean_nat_dec_lt(v___x_161_, v___x_162_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; 
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v_bs_160_);
lean_ctor_set(v___x_165_, 1, v___x_161_);
return v___x_165_;
}
else
{
lean_object* v___f_166_; uint8_t v___x_167_; 
v___f_166_ = ((lean_object*)(l_Std_Http_Internal_ChunkedBuffer_ofArray___closed__0));
v___x_167_ = lean_nat_dec_le(v___x_162_, v___x_162_);
if (v___x_167_ == 0)
{
if (v___x_164_ == 0)
{
lean_object* v___x_168_; 
v___x_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_168_, 0, v_bs_160_);
lean_ctor_set(v___x_168_, 1, v___x_161_);
return v___x_168_;
}
else
{
size_t v___x_169_; size_t v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_169_ = ((size_t)0ULL);
v___x_170_ = lean_usize_of_nat(v___x_162_);
lean_inc_ref(v_bs_160_);
v___x_171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_163_, v___f_166_, v_bs_160_, v___x_169_, v___x_170_, v___x_161_);
v___x_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_172_, 0, v_bs_160_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
return v___x_172_;
}
}
else
{
size_t v___x_173_; size_t v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_173_ = ((size_t)0ULL);
v___x_174_ = lean_usize_of_nat(v___x_162_);
lean_inc_ref(v_bs_160_);
v___x_175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_163_, v___f_166_, v_bs_160_, v___x_173_, v___x_174_, v___x_161_);
v___x_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_176_, 0, v_bs_160_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
return v___x_176_;
}
}
}
}
uint8_t l_Std_Http_Internal_ChunkedBuffer_isEmpty(lean_object* v_bb_177_){
_start:
{
lean_object* v_size_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v_size_178_ = lean_ctor_get(v_bb_177_, 1);
v___x_179_ = lean_unsigned_to_nat(0u);
v___x_180_ = lean_nat_dec_eq(v_size_178_, v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT void l_Std_Http_Internal_ChunkedBuffer_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_bb_177_ = stack[0].m_obj;
uint8_t v_res_181_;
v_res_181_ = l_Std_Http_Internal_ChunkedBuffer_isEmpty(v_bb_177_);
stack->m_num = v_res_181_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_isEmpty___boxed(lean_object* v_bb_182_){
_start:
{
uint8_t v_res_183_; lean_object* v_r_184_; 
v_res_183_ = l_Std_Http_Internal_ChunkedBuffer_isEmpty(v_bb_182_);
lean_dec_ref(v_bb_182_);
v_r_184_ = lean_box(v_res_183_);
return v_r_184_;
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
