// Lean compiler output
// Module: Std.Http.Internal.ChunkedBuffer
// Imports: import Init.Data.ToString import Init.Data.Array.Lemmas public import Init.Data.String.Basic public import Init.Data.ByteArray
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
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_writeChar(lean_object* v_buffer_50_, uint32_t v_data_51_){
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
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_writeChar___boxed(lean_object* v_buffer_70_, lean_object* v_data_71_){
_start:
{
uint32_t v_data_boxed_72_; lean_object* v_res_73_; 
v_data_boxed_72_ = lean_unbox_uint32(v_data_71_);
lean_dec(v_data_71_);
v_res_73_ = l_Std_Http_Internal_ChunkedBuffer_writeChar(v_buffer_70_, v_data_boxed_72_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_writeString(lean_object* v_buffer_74_, lean_object* v_data_75_){
_start:
{
lean_object* v_data_76_; lean_object* v_size_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_88_; 
v_data_76_ = lean_ctor_get(v_buffer_74_, 0);
v_size_77_ = lean_ctor_get(v_buffer_74_, 1);
v_isSharedCheck_88_ = !lean_is_exclusive(v_buffer_74_);
if (v_isSharedCheck_88_ == 0)
{
v___x_79_ = v_buffer_74_;
v_isShared_80_ = v_isSharedCheck_88_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_size_77_);
lean_inc(v_data_76_);
lean_dec(v_buffer_74_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_88_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
v___x_81_ = lean_string_to_utf8(v_data_75_);
lean_inc_ref(v___x_81_);
v___x_82_ = lean_array_push(v_data_76_, v___x_81_);
v___x_83_ = lean_byte_array_size(v___x_81_);
lean_dec_ref(v___x_81_);
v___x_84_ = lean_nat_add(v_size_77_, v___x_83_);
lean_dec(v_size_77_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 1, v___x_84_);
lean_ctor_set(v___x_79_, 0, v___x_82_);
v___x_86_ = v___x_79_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_82_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v___x_84_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_writeString___boxed(lean_object* v_buffer_89_, lean_object* v_data_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Std_Http_Internal_ChunkedBuffer_writeString(v_buffer_89_, v_data_90_);
lean_dec_ref(v_data_90_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0(uint8_t v___x_92_, lean_object* v_x1_93_, lean_object* v_x2_94_){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_95_ = lean_unsigned_to_nat(0u);
v___x_96_ = lean_byte_array_size(v_x1_93_);
v___x_97_ = lean_byte_array_size(v_x2_94_);
v___x_98_ = lean_byte_array_copy_slice(v_x2_94_, v___x_95_, v_x1_93_, v___x_96_, v___x_97_, v___x_92_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0___boxed(lean_object* v___x_99_, lean_object* v_x1_100_, lean_object* v_x2_101_){
_start:
{
uint8_t v___x_92__boxed_102_; lean_object* v_res_103_; 
v___x_92__boxed_102_ = lean_unbox(v___x_99_);
v_res_103_ = l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0(v___x_92__boxed_102_, v_x1_100_, v_x2_101_);
lean_dec_ref(v_x2_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray(lean_object* v_cb_123_){
_start:
{
lean_object* v_data_124_; lean_object* v_size_125_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v_data_124_ = lean_ctor_get(v_cb_123_, 0);
lean_inc_ref(v_data_124_);
v_size_125_ = lean_ctor_get(v_cb_123_, 1);
lean_inc(v_size_125_);
lean_dec_ref(v_cb_123_);
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = lean_array_get_size(v_data_124_);
v___x_128_ = lean_nat_dec_eq(v___x_126_, v___x_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_129_ = lean_mk_empty_byte_array(v_size_125_);
lean_dec(v_size_125_);
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = ((lean_object*)(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9));
v___x_132_ = lean_nat_dec_lt(v___x_130_, v___x_127_);
if (v___x_132_ == 0)
{
lean_dec_ref(v_data_124_);
return v___x_129_;
}
else
{
lean_object* v___x_133_; lean_object* v___f_134_; uint8_t v___x_135_; 
v___x_133_ = lean_box(v___x_128_);
v___f_134_ = lean_alloc_closure((void*)(l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0___boxed), 3, 1);
lean_closure_set(v___f_134_, 0, v___x_133_);
v___x_135_ = lean_nat_dec_le(v___x_127_, v___x_127_);
if (v___x_135_ == 0)
{
if (v___x_132_ == 0)
{
lean_dec_ref(v___f_134_);
lean_dec_ref(v_data_124_);
return v___x_129_;
}
else
{
size_t v___x_136_; size_t v___x_137_; lean_object* v___x_138_; 
v___x_136_ = ((size_t)0ULL);
v___x_137_ = lean_usize_of_nat(v___x_127_);
v___x_138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_131_, v___f_134_, v_data_124_, v___x_136_, v___x_137_, v___x_129_);
return v___x_138_;
}
}
else
{
size_t v___x_139_; size_t v___x_140_; lean_object* v___x_141_; 
v___x_139_ = ((size_t)0ULL);
v___x_140_ = lean_usize_of_nat(v___x_127_);
v___x_141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_131_, v___f_134_, v_data_124_, v___x_139_, v___x_140_, v___x_129_);
return v___x_141_;
}
}
}
else
{
lean_object* v___x_142_; lean_object* v___x_143_; 
lean_dec(v_size_125_);
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = lean_array_fget(v_data_124_, v___x_142_);
lean_dec_ref(v_data_124_);
return v___x_143_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_ofByteArray(lean_object* v_bs_144_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_145_ = lean_unsigned_to_nat(1u);
v___x_146_ = lean_mk_empty_array_with_capacity(v___x_145_);
lean_inc_ref(v_bs_144_);
v___x_147_ = lean_array_push(v___x_146_, v_bs_144_);
v___x_148_ = lean_byte_array_size(v_bs_144_);
lean_dec_ref(v_bs_144_);
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_147_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0(lean_object* v_x1_150_, lean_object* v_x2_151_){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_byte_array_size(v_x2_151_);
v___x_153_ = lean_nat_add(v_x1_150_, v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0___boxed(lean_object* v_x1_154_, lean_object* v_x2_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0(v_x1_154_, v_x2_155_);
lean_dec_ref(v_x2_155_);
lean_dec(v_x1_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_ofArray(lean_object* v_bs_158_){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_159_ = lean_unsigned_to_nat(0u);
v___x_160_ = lean_array_get_size(v_bs_158_);
v___x_161_ = ((lean_object*)(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9));
v___x_162_ = lean_nat_dec_lt(v___x_159_, v___x_160_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; 
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v_bs_158_);
lean_ctor_set(v___x_163_, 1, v___x_159_);
return v___x_163_;
}
else
{
lean_object* v___f_164_; uint8_t v___x_165_; 
v___f_164_ = ((lean_object*)(l_Std_Http_Internal_ChunkedBuffer_ofArray___closed__0));
v___x_165_ = lean_nat_dec_le(v___x_160_, v___x_160_);
if (v___x_165_ == 0)
{
if (v___x_162_ == 0)
{
lean_object* v___x_166_; 
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v_bs_158_);
lean_ctor_set(v___x_166_, 1, v___x_159_);
return v___x_166_;
}
else
{
size_t v___x_167_; size_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_167_ = ((size_t)0ULL);
v___x_168_ = lean_usize_of_nat(v___x_160_);
lean_inc_ref(v_bs_158_);
v___x_169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_161_, v___f_164_, v_bs_158_, v___x_167_, v___x_168_, v___x_159_);
v___x_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_170_, 0, v_bs_158_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
return v___x_170_;
}
}
else
{
size_t v___x_171_; size_t v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_171_ = ((size_t)0ULL);
v___x_172_ = lean_usize_of_nat(v___x_160_);
lean_inc_ref(v_bs_158_);
v___x_173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_161_, v___f_164_, v_bs_158_, v___x_171_, v___x_172_, v___x_159_);
v___x_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_174_, 0, v_bs_158_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
return v___x_174_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_ChunkedBuffer_isEmpty(lean_object* v_bb_175_){
_start:
{
lean_object* v_size_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v_size_176_ = lean_ctor_get(v_bb_175_, 1);
v___x_177_ = lean_unsigned_to_nat(0u);
v___x_178_ = lean_nat_dec_eq(v_size_176_, v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_isEmpty___boxed(lean_object* v_bb_179_){
_start:
{
uint8_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = l_Std_Http_Internal_ChunkedBuffer_isEmpty(v_bb_179_);
lean_dec_ref(v_bb_179_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Internal_ChunkedBuffer(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ByteArray(builtin);
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
lean_object* initialize_Init_Data_ByteArray(uint8_t builtin);
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
res = initialize_Init_Data_ByteArray(builtin);
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
