// Lean compiler output
// Module: Std.Http.Protocol.H1.Message
// Imports: import Init.Data.Array public import Std.Http.Data
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
lean_object* l_Std_Http_Response_instReprHead_repr___redArg(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Http_Request_instReprHead_repr___redArg(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Std_Http_Headers_empty;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_byte_array_mk(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___redArg___lam__0___boxed(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_splitToSubslice___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint16_t l_Std_Http_Status_toCode(lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Std_Http_Status_reasonPhrase(lean_object*);
lean_object* l_Std_Http_Headers_fold___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_uv_ntop_v4(lean_object*);
lean_object* lean_uv_ntop_v6(lean_object*);
lean_object* l_Std_Http_URI_Query_formatOption(lean_object*);
lean_object* l_Std_Http_URI_EncodedFragment_encode(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
uint8_t l_Std_Http_instBEqVersion_beq(uint8_t, uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_connection;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_Http_Header_Connection_parse(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_transferEncoding;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Std_Http_Header_ContentLength_parse(lean_object*);
lean_object* l_Std_Http_Header_TransferEncoding_parse(lean_object*);
uint8_t l_Std_Http_Header_TransferEncoding_isChunked(lean_object*);
extern lean_object* l_Std_Http_Header_Name_contentLength;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_receiving_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_receiving_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_receiving_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_receiving_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_sending_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_sending_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_sending_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_sending_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_instBEqDirection_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instBEqDirection_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Protocol_H1_instBEqDirection___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_instBEqDirection_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instBEqDirection___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_instBEqDirection___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Protocol_H1_instBEqDirection = (const lean_object*)&l_Std_Http_Protocol_H1_instBEqDirection___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Direction_swap(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_swap___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_headers(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_headers___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_setHeaders(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_setHeaders___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Message_Head_version(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_version___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Message_Head_getSize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize___closed__2 = (const lean_object*)&l_Std_Http_Protocol_H1_Message_Head_getSize___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize(uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "close"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___closed__0_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "keep-alive"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___closed__0_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__1_value;
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Protocol_H1_instReprHead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_instReprHead___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instReprHead___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprHead___closed__0_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instReprHead___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_instReprHead___aux__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instReprHead___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprHead___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__0_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__1_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__2 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__2_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__3 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__3_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed__const__1;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__0_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2;
static lean_once_cell_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.0"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.1"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/2.0"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/3.0"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__13 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__13_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__17 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__17_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__18 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__18_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__19 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__19_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__13_value),((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__20 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__20_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__20_value),((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15_value),((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16_value),((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__17_value),((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__18_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__21 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__21_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__21_value),((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__19_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22_value;
static const lean_sarray_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_sarray_object) + 1, .m_other = 1, .m_tag = 248}, .m_size = 1, .m_capacity = 1, .m_data = {32}};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "//"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ACL"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "BASELINE-CONTROL"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "BIND"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CHECKIN"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CHECKOUT"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CONNECT"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "COPY"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "DELETE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "GET"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "LABEL"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LINK"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LOCK"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MERGE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKACTIVITY"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKCALENDAR"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MKCOL"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "MKREDIRECTREF"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MKWORKSPACE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "MOVE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "OPTIONS"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ORDERPATCH"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PATCH"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "POST"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PRI"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "PROPFIND"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PROPPATCH"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PUT"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "QUERY"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REBIND"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REPORT"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "SEARCH"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "TRACE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNBIND"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "UNCHECKOUT"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLINK"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLOCK"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UPDATE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "UPDATEREDIRECTREF"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "VERSION-CONTROL"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___closed__0_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___boxed(lean_object*);
static lean_once_cell_t l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0;
static lean_once_cell_t l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead___boxed(lean_object*);
lean_object* l_Std_Http_Protocol_H1_Direction_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Direction_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Std_Http_Protocol_H1_Direction_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Std_Http_Protocol_H1_Direction_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Std_Http_Protocol_H1_Direction_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Std_Http_Protocol_H1_Direction_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Direction_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Std_Http_Protocol_H1_Direction_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Std_Http_Protocol_H1_Direction_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_receiving_elim___redArg(lean_object* v_receiving_24_){
_start:
{
lean_inc(v_receiving_24_);
return v_receiving_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_receiving_elim___redArg___boxed(lean_object* v_receiving_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_Http_Protocol_H1_Direction_receiving_elim___redArg(v_receiving_25_);
lean_dec(v_receiving_25_);
return v_res_26_;
}
}
lean_object* l_Std_Http_Protocol_H1_Direction_receiving_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_receiving_30_){
_start:
{
lean_inc(v_receiving_30_);
return v_receiving_30_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Direction_receiving_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_receiving_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Std_Http_Protocol_H1_Direction_receiving_elim(lean_box(0), v_t_28_, lean_box(0), v_receiving_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_receiving_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_receiving_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Std_Http_Protocol_H1_Direction_receiving_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_receiving_35_);
lean_dec(v_receiving_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_sending_elim___redArg(lean_object* v_sending_38_){
_start:
{
lean_inc(v_sending_38_);
return v_sending_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_sending_elim___redArg___boxed(lean_object* v_sending_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_Http_Protocol_H1_Direction_sending_elim___redArg(v_sending_39_);
lean_dec(v_sending_39_);
return v_res_40_;
}
}
lean_object* l_Std_Http_Protocol_H1_Direction_sending_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_sending_44_){
_start:
{
lean_inc(v_sending_44_);
return v_sending_44_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Direction_sending_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_sending_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Std_Http_Protocol_H1_Direction_sending_elim(lean_box(0), v_t_42_, lean_box(0), v_sending_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_sending_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_sending_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Std_Http_Protocol_H1_Direction_sending_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_sending_49_);
lean_dec(v_sending_49_);
return v_res_51_;
}
}
uint8_t l_Std_Http_Protocol_H1_instBEqDirection_beq(uint8_t v_x_52_, uint8_t v_y_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; uint8_t v___x_58_; 
v___x_54_ = lean_box(v_x_52_);
v___x_55_ = lean_obj_tag_nat(v___x_54_);
lean_dec(v___x_54_);
v___x_56_ = lean_box(v_y_53_);
v___x_57_ = lean_obj_tag_nat(v___x_56_);
lean_dec(v___x_56_);
v___x_58_ = lean_nat_dec_eq(v___x_55_, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_instBEqDirection_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_52_ = stack[0].m_num;
uint8_t v_y_53_ = stack[1].m_num;
uint8_t v_res_59_;
v_res_59_ = l_Std_Http_Protocol_H1_instBEqDirection_beq(v_x_52_, v_y_53_);
stack->m_num = v_res_59_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instBEqDirection_beq___boxed(lean_object* v_x_60_, lean_object* v_y_61_){
_start:
{
uint8_t v_x_24__boxed_62_; uint8_t v_y_25__boxed_63_; uint8_t v_res_64_; lean_object* v_r_65_; 
v_x_24__boxed_62_ = lean_unbox(v_x_60_);
v_y_25__boxed_63_ = lean_unbox(v_y_61_);
v_res_64_ = l_Std_Http_Protocol_H1_instBEqDirection_beq(v_x_24__boxed_62_, v_y_25__boxed_63_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
uint8_t l_Std_Http_Protocol_H1_Direction_swap(uint8_t v_x_68_){
_start:
{
if (v_x_68_ == 0)
{
uint8_t v___x_69_; 
v___x_69_ = 1;
return v___x_69_;
}
else
{
uint8_t v___x_70_; 
v___x_70_ = 0;
return v___x_70_;
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Direction_swap_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_68_ = stack[0].m_num;
uint8_t v_res_71_;
v_res_71_ = l_Std_Http_Protocol_H1_Direction_swap(v_x_68_);
stack->m_num = v_res_71_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_swap___boxed(lean_object* v_x_72_){
_start:
{
uint8_t v_x_18__boxed_73_; uint8_t v_res_74_; lean_object* v_r_75_; 
v_x_18__boxed_73_ = lean_unbox(v_x_72_);
v_res_74_ = l_Std_Http_Protocol_H1_Direction_swap(v_x_18__boxed_73_);
v_r_75_ = lean_box(v_res_74_);
return v_r_75_;
}
}
lean_object* l_Std_Http_Protocol_H1_Message_Head_headers(uint8_t v_dir_76_, lean_object* v_m_77_){
_start:
{
lean_object* v_headers_78_; 
v_headers_78_ = lean_ctor_get(v_m_77_, 1);
lean_inc_ref(v_headers_78_);
return v_headers_78_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Message_Head_headers_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_76_ = stack[0].m_num;
lean_object* v_m_77_ = stack[1].m_obj;
lean_object* v_res_79_;
v_res_79_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_76_, v_m_77_);
stack->m_obj
 = v_res_79_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_headers___boxed(lean_object* v_dir_80_, lean_object* v_m_81_){
_start:
{
uint8_t v_dir_boxed_82_; lean_object* v_res_83_; 
v_dir_boxed_82_ = lean_unbox(v_dir_80_);
v_res_83_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_boxed_82_, v_m_81_);
lean_dec(v_m_81_);
return v_res_83_;
}
}
lean_object* l_Std_Http_Protocol_H1_Message_Head_setHeaders(uint8_t v_dir_84_, lean_object* v_m_85_, lean_object* v_headers_86_){
_start:
{
if (v_dir_84_ == 0)
{
uint8_t v_method_87_; uint8_t v_version_88_; lean_object* v_uri_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_96_; 
v_method_87_ = lean_ctor_get_uint8(v_m_85_, sizeof(void*)*2);
v_version_88_ = lean_ctor_get_uint8(v_m_85_, sizeof(void*)*2 + 1);
v_uri_89_ = lean_ctor_get(v_m_85_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v_m_85_);
if (v_isSharedCheck_96_ == 0)
{
lean_object* v_unused_97_; 
v_unused_97_ = lean_ctor_get(v_m_85_, 1);
lean_dec(v_unused_97_);
v___x_91_ = v_m_85_;
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_uri_89_);
lean_dec(v_m_85_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 1, v_headers_86_);
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_uri_89_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v_headers_86_);
lean_ctor_set_uint8(v_reuseFailAlloc_95_, sizeof(void*)*2, v_method_87_);
lean_ctor_set_uint8(v_reuseFailAlloc_95_, sizeof(void*)*2 + 1, v_version_88_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
else
{
lean_object* v_status_98_; uint8_t v_version_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_106_; 
v_status_98_ = lean_ctor_get(v_m_85_, 0);
v_version_99_ = lean_ctor_get_uint8(v_m_85_, sizeof(void*)*2);
v_isSharedCheck_106_ = !lean_is_exclusive(v_m_85_);
if (v_isSharedCheck_106_ == 0)
{
lean_object* v_unused_107_; 
v_unused_107_ = lean_ctor_get(v_m_85_, 1);
lean_dec(v_unused_107_);
v___x_101_ = v_m_85_;
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_status_98_);
lean_dec(v_m_85_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_104_; 
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v_headers_86_);
v___x_104_ = v___x_101_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_status_98_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v_headers_86_);
lean_ctor_set_uint8(v_reuseFailAlloc_105_, sizeof(void*)*2, v_version_99_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Message_Head_setHeaders_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_84_ = stack[0].m_num;
lean_object* v_m_85_ = stack[1].m_obj;
lean_object* v_headers_86_ = stack[2].m_obj;
lean_object* v_res_108_;
v_res_108_ = l_Std_Http_Protocol_H1_Message_Head_setHeaders(v_dir_84_, v_m_85_, v_headers_86_);
stack->m_obj
 = v_res_108_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_setHeaders___boxed(lean_object* v_dir_109_, lean_object* v_m_110_, lean_object* v_headers_111_){
_start:
{
uint8_t v_dir_boxed_112_; lean_object* v_res_113_; 
v_dir_boxed_112_ = lean_unbox(v_dir_109_);
v_res_113_ = l_Std_Http_Protocol_H1_Message_Head_setHeaders(v_dir_boxed_112_, v_m_110_, v_headers_111_);
return v_res_113_;
}
}
uint8_t l_Std_Http_Protocol_H1_Message_Head_version(uint8_t v_dir_114_, lean_object* v_m_115_){
_start:
{
if (v_dir_114_ == 0)
{
uint8_t v_version_116_; 
v_version_116_ = lean_ctor_get_uint8(v_m_115_, sizeof(void*)*2 + 1);
return v_version_116_;
}
else
{
uint8_t v_version_117_; 
v_version_117_ = lean_ctor_get_uint8(v_m_115_, sizeof(void*)*2);
return v_version_117_;
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Message_Head_version_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_114_ = stack[0].m_num;
lean_object* v_m_115_ = stack[1].m_obj;
uint8_t v_res_118_;
v_res_118_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_114_, v_m_115_);
stack->m_num = v_res_118_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_version___boxed(lean_object* v_dir_119_, lean_object* v_m_120_){
_start:
{
uint8_t v_dir_boxed_121_; uint8_t v_res_122_; lean_object* v_r_123_; 
v_dir_boxed_121_ = lean_unbox(v_dir_119_);
v_res_122_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_boxed_121_, v_m_120_);
lean_dec(v_m_120_);
v_r_123_ = lean_box(v_res_122_);
return v_r_123_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg(lean_object* v___x_124_, lean_object* v___x_125_, size_t v_sz_126_, size_t v_i_127_, lean_object* v_bs_128_){
_start:
{
uint8_t v___x_129_; 
v___x_129_ = lean_usize_dec_lt(v_i_127_, v_sz_126_);
if (v___x_129_ == 0)
{
return v_bs_128_;
}
else
{
lean_object* v_entries_130_; lean_object* v___x_131_; lean_object* v_bs_x27_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v_snd_136_; size_t v___x_137_; size_t v___x_138_; lean_object* v___x_139_; 
v_entries_130_ = lean_ctor_get(v___x_124_, 0);
v___x_131_ = lean_unsigned_to_nat(0u);
v_bs_x27_132_ = lean_array_uset(v_bs_128_, v_i_127_, v___x_131_);
v___x_133_ = lean_usize_to_nat(v_i_127_);
v___x_134_ = lean_array_fget_borrowed(v___x_125_, v___x_133_);
lean_dec(v___x_133_);
v___x_135_ = lean_array_fget_borrowed(v_entries_130_, v___x_134_);
v_snd_136_ = lean_ctor_get(v___x_135_, 1);
v___x_137_ = ((size_t)1ULL);
v___x_138_ = lean_usize_add(v_i_127_, v___x_137_);
lean_inc(v_snd_136_);
v___x_139_ = lean_array_uset(v_bs_x27_132_, v_i_127_, v_snd_136_);
v_i_127_ = v___x_138_;
v_bs_128_ = v___x_139_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_124_ = stack[0].m_obj;
lean_object* v___x_125_ = stack[1].m_obj;
size_t v_sz_126_ = stack[2].m_num;
size_t v_i_127_ = stack[3].m_num;
lean_object* v_bs_128_ = stack[4].m_obj;
lean_object* v_res_141_;
v_res_141_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg(v___x_124_, v___x_125_, v_sz_126_, v_i_127_, v_bs_128_);
stack->m_obj
 = v_res_141_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg___boxed(lean_object* v___x_142_, lean_object* v___x_143_, lean_object* v_sz_144_, lean_object* v_i_145_, lean_object* v_bs_146_){
_start:
{
size_t v_sz_boxed_147_; size_t v_i_boxed_148_; lean_object* v_res_149_; 
v_sz_boxed_147_ = lean_unbox_usize(v_sz_144_);
lean_dec(v_sz_144_);
v_i_boxed_148_ = lean_unbox_usize(v_i_145_);
lean_dec(v_i_145_);
v_res_149_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg(v___x_142_, v___x_143_, v_sz_boxed_147_, v_i_boxed_148_, v_bs_146_);
lean_dec_ref(v___x_143_);
lean_dec_ref(v___x_142_);
return v_res_149_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(lean_object* v_a_150_, lean_object* v_x_151_){
_start:
{
if (lean_obj_tag(v_x_151_) == 0)
{
uint8_t v___x_152_; 
v___x_152_ = 0;
return v___x_152_;
}
else
{
lean_object* v_key_153_; lean_object* v_tail_154_; uint8_t v___x_155_; 
v_key_153_ = lean_ctor_get(v_x_151_, 0);
v_tail_154_ = lean_ctor_get(v_x_151_, 2);
v___x_155_ = lean_string_dec_eq(v_key_153_, v_a_150_);
if (v___x_155_ == 0)
{
v_x_151_ = v_tail_154_;
goto _start;
}
else
{
return v___x_155_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_150_ = stack[0].m_obj;
lean_object* v_x_151_ = stack[1].m_obj;
uint8_t v_res_157_;
v_res_157_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_a_150_, v_x_151_);
stack->m_num = v_res_157_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg___boxed(lean_object* v_a_158_, lean_object* v_x_159_){
_start:
{
uint8_t v_res_160_; lean_object* v_r_161_; 
v_res_160_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_a_158_, v_x_159_);
lean_dec(v_x_159_);
lean_dec_ref(v_a_158_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(lean_object* v_m_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_buckets_164_; lean_object* v___x_165_; uint64_t v___x_166_; uint64_t v___x_167_; uint64_t v___x_168_; uint64_t v_fold_169_; uint64_t v___x_170_; uint64_t v___x_171_; uint64_t v___x_172_; size_t v___x_173_; size_t v___x_174_; size_t v___x_175_; size_t v___x_176_; size_t v___x_177_; lean_object* v___x_178_; uint8_t v___x_179_; 
v_buckets_164_ = lean_ctor_get(v_m_162_, 1);
v___x_165_ = lean_array_get_size(v_buckets_164_);
v___x_166_ = lean_string_hash(v_a_163_);
v___x_167_ = 32ULL;
v___x_168_ = lean_uint64_shift_right(v___x_166_, v___x_167_);
v_fold_169_ = lean_uint64_xor(v___x_166_, v___x_168_);
v___x_170_ = 16ULL;
v___x_171_ = lean_uint64_shift_right(v_fold_169_, v___x_170_);
v___x_172_ = lean_uint64_xor(v_fold_169_, v___x_171_);
v___x_173_ = lean_uint64_to_usize(v___x_172_);
v___x_174_ = lean_usize_of_nat(v___x_165_);
v___x_175_ = ((size_t)1ULL);
v___x_176_ = lean_usize_sub(v___x_174_, v___x_175_);
v___x_177_ = lean_usize_land(v___x_173_, v___x_176_);
v___x_178_ = lean_array_uget_borrowed(v_buckets_164_, v___x_177_);
v___x_179_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_a_163_, v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_162_ = stack[0].m_obj;
lean_object* v_a_163_ = stack[1].m_obj;
uint8_t v_res_180_;
v_res_180_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_m_162_, v_a_163_);
stack->m_num = v_res_180_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg___boxed(lean_object* v_m_181_, lean_object* v_a_182_){
_start:
{
uint8_t v_res_183_; lean_object* v_r_184_; 
v_res_183_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_m_181_, v_a_182_);
lean_dec_ref(v_a_182_);
lean_dec_ref(v_m_181_);
v_r_184_ = lean_box(v_res_183_);
return v_r_184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2___redArg(lean_object* v_a_185_, lean_object* v_x_186_){
_start:
{
lean_object* v_key_187_; lean_object* v_value_188_; lean_object* v_tail_189_; uint8_t v___x_190_; 
v_key_187_ = lean_ctor_get(v_x_186_, 0);
v_value_188_ = lean_ctor_get(v_x_186_, 1);
v_tail_189_ = lean_ctor_get(v_x_186_, 2);
v___x_190_ = lean_string_dec_eq(v_key_187_, v_a_185_);
if (v___x_190_ == 0)
{
v_x_186_ = v_tail_189_;
goto _start;
}
else
{
lean_inc(v_value_188_);
return v_value_188_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2___redArg___boxed(lean_object* v_a_192_, lean_object* v_x_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2___redArg(v_a_192_, v_x_193_);
lean_dec(v_x_193_);
lean_dec_ref(v_a_192_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(lean_object* v_m_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_buckets_197_; lean_object* v___x_198_; uint64_t v___x_199_; uint64_t v___x_200_; uint64_t v___x_201_; uint64_t v_fold_202_; uint64_t v___x_203_; uint64_t v___x_204_; uint64_t v___x_205_; size_t v___x_206_; size_t v___x_207_; size_t v___x_208_; size_t v___x_209_; size_t v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v_buckets_197_ = lean_ctor_get(v_m_195_, 1);
v___x_198_ = lean_array_get_size(v_buckets_197_);
v___x_199_ = lean_string_hash(v_a_196_);
v___x_200_ = 32ULL;
v___x_201_ = lean_uint64_shift_right(v___x_199_, v___x_200_);
v_fold_202_ = lean_uint64_xor(v___x_199_, v___x_201_);
v___x_203_ = 16ULL;
v___x_204_ = lean_uint64_shift_right(v_fold_202_, v___x_203_);
v___x_205_ = lean_uint64_xor(v_fold_202_, v___x_204_);
v___x_206_ = lean_uint64_to_usize(v___x_205_);
v___x_207_ = lean_usize_of_nat(v___x_198_);
v___x_208_ = ((size_t)1ULL);
v___x_209_ = lean_usize_sub(v___x_207_, v___x_208_);
v___x_210_ = lean_usize_land(v___x_206_, v___x_209_);
v___x_211_ = lean_array_uget_borrowed(v_buckets_197_, v___x_210_);
v___x_212_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2___redArg(v_a_196_, v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg___boxed(lean_object* v_m_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v_m_213_, v_a_214_);
lean_dec_ref(v_a_214_);
lean_dec_ref(v_m_213_);
return v_res_215_;
}
}
lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize(uint8_t v_dir_222_, lean_object* v_message_223_, uint8_t v_allowEOFBody_224_){
_start:
{
lean_object* v___x_225_; lean_object* v___y_227_; lean_object* v_indexes_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_225_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_222_, v_message_223_);
v_indexes_278_ = lean_ctor_get(v___x_225_, 1);
v___x_279_ = l_Std_Http_Header_Name_contentLength;
v___x_280_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_278_, v___x_279_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; 
v___x_281_ = lean_box(0);
v___y_227_ = v___x_281_;
goto v___jp_226_;
}
else
{
lean_object* v___x_282_; size_t v_sz_283_; size_t v___x_284_; lean_object* v_entries_285_; lean_object* v___x_286_; 
v___x_282_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v_indexes_278_, v___x_279_);
v_sz_283_ = lean_array_size(v___x_282_);
v___x_284_ = ((size_t)0ULL);
lean_inc(v___x_282_);
v_entries_285_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg(v___x_225_, v___x_282_, v_sz_283_, v___x_284_, v___x_282_);
lean_dec(v___x_282_);
v___x_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_286_, 0, v_entries_285_);
v___y_227_ = v___x_286_;
goto v___jp_226_;
}
v___jp_226_:
{
lean_object* v_indexes_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v_indexes_228_ = lean_ctor_get(v___x_225_, 1);
v___x_229_ = l_Std_Http_Header_Name_transferEncoding;
v___x_230_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_228_, v___x_229_);
if (v___x_230_ == 0)
{
lean_dec_ref(v___x_225_);
if (lean_obj_tag(v___y_227_) == 0)
{
if (v_allowEOFBody_224_ == 0)
{
lean_object* v___x_231_; 
v___x_231_ = lean_box(0);
return v___x_231_;
}
else
{
lean_object* v___x_232_; 
v___x_232_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1));
return v___x_232_;
}
}
else
{
lean_object* v_val_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_256_; 
v_val_233_ = lean_ctor_get(v___y_227_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___y_227_);
if (v_isSharedCheck_256_ == 0)
{
v___x_235_ = v___y_227_;
v_isShared_236_ = v_isSharedCheck_256_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_val_233_);
lean_dec(v___y_227_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_256_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_237_ = lean_array_get_size(v_val_233_);
v___x_238_ = lean_unsigned_to_nat(1u);
v___x_239_ = lean_nat_dec_eq(v___x_237_, v___x_238_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; 
lean_del_object(v___x_235_);
lean_dec(v_val_233_);
v___x_240_ = lean_box(0);
return v___x_240_;
}
else
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_241_ = lean_unsigned_to_nat(0u);
v___x_242_ = lean_array_fget(v_val_233_, v___x_241_);
lean_dec(v_val_233_);
v___x_243_ = l_Std_Http_Header_ContentLength_parse(v___x_242_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v___x_244_; 
lean_del_object(v___x_235_);
v___x_244_ = lean_box(0);
return v___x_244_;
}
else
{
lean_object* v_val_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_255_; 
v_val_245_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_255_ == 0)
{
v___x_247_ = v___x_243_;
v_isShared_248_ = v_isSharedCheck_255_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_val_245_);
lean_dec(v___x_243_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_255_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v_val_245_);
v___x_250_ = v___x_235_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_val_245_);
v___x_250_ = v_reuseFailAlloc_254_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_252_; 
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_250_);
v___x_252_ = v___x_247_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_250_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_257_; size_t v_sz_258_; size_t v___x_259_; lean_object* v_entries_260_; lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_257_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v_indexes_228_, v___x_229_);
v_sz_258_ = lean_array_size(v___x_257_);
v___x_259_ = ((size_t)0ULL);
lean_inc(v___x_257_);
v_entries_260_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg(v___x_225_, v___x_257_, v_sz_258_, v___x_259_, v___x_257_);
lean_dec(v___x_257_);
lean_dec_ref(v___x_225_);
v___x_261_ = lean_array_get_size(v_entries_260_);
v___x_262_ = lean_unsigned_to_nat(1u);
v___x_263_ = lean_nat_dec_eq(v___x_261_, v___x_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; 
lean_dec_ref(v_entries_260_);
lean_dec(v___y_227_);
v___x_264_ = lean_box(0);
return v___x_264_;
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v_te_267_; 
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = lean_array_fget(v_entries_260_, v___x_265_);
lean_dec_ref(v_entries_260_);
v_te_267_ = l_Std_Http_Header_TransferEncoding_parse(v___x_266_);
if (lean_obj_tag(v_te_267_) == 0)
{
lean_object* v___x_268_; 
lean_dec(v___y_227_);
v___x_268_ = lean_box(0);
return v___x_268_;
}
else
{
lean_object* v_val_269_; uint8_t v___x_270_; 
v_val_269_ = lean_ctor_get(v_te_267_, 0);
lean_inc(v_val_269_);
lean_dec_ref_known(v_te_267_, 1);
v___x_270_ = l_Std_Http_Header_TransferEncoding_isChunked(v_val_269_);
lean_dec(v_val_269_);
if (v___x_270_ == 1)
{
if (lean_obj_tag(v___y_227_) == 0)
{
uint8_t v___x_271_; uint8_t v___x_272_; uint8_t v___x_273_; 
v___x_271_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_222_, v_message_223_);
v___x_272_ = 0;
v___x_273_ = l_Std_Http_instBEqVersion_beq(v___x_271_, v___x_272_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; 
v___x_274_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__2));
return v___x_274_;
}
else
{
lean_object* v___x_275_; 
v___x_275_ = lean_box(0);
return v___x_275_;
}
}
else
{
lean_object* v___x_276_; 
lean_dec(v___y_227_);
v___x_276_ = lean_box(0);
return v___x_276_;
}
}
else
{
lean_object* v___x_277_; 
lean_dec(v___y_227_);
v___x_277_ = lean_box(0);
return v___x_277_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Message_Head_getSize_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_222_ = stack[0].m_num;
lean_object* v_message_223_ = stack[1].m_obj;
uint8_t v_allowEOFBody_224_ = stack[2].m_num;
lean_object* v_res_287_;
v_res_287_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v_dir_222_, v_message_223_, v_allowEOFBody_224_);
stack->m_obj
 = v_res_287_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize___boxed(lean_object* v_dir_288_, lean_object* v_message_289_, lean_object* v_allowEOFBody_290_){
_start:
{
uint8_t v_dir_boxed_291_; uint8_t v_allowEOFBody_boxed_292_; lean_object* v_res_293_; 
v_dir_boxed_291_ = lean_unbox(v_dir_288_);
v_allowEOFBody_boxed_292_ = lean_unbox(v_allowEOFBody_290_);
v_res_293_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v_dir_boxed_291_, v_message_289_, v_allowEOFBody_boxed_292_);
lean_dec(v_message_289_);
return v_res_293_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(lean_object* v_00_u03b2_294_, lean_object* v_m_295_, lean_object* v_a_296_){
_start:
{
uint8_t v___x_297_; 
v___x_297_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_m_295_, v_a_296_);
return v___x_297_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_295_ = stack[1].m_obj;
lean_object* v_a_296_ = stack[2].m_obj;
uint8_t v_res_298_;
v_res_298_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(lean_box(0), v_m_295_, v_a_296_);
stack->m_num = v_res_298_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___boxed(lean_object* v_00_u03b2_299_, lean_object* v_m_300_, lean_object* v_a_301_){
_start:
{
uint8_t v_res_302_; lean_object* v_r_303_; 
v_res_302_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(v_00_u03b2_299_, v_m_300_, v_a_301_);
lean_dec_ref(v_a_301_);
lean_dec_ref(v_m_300_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(lean_object* v_00_u03b2_304_, lean_object* v_m_305_, lean_object* v_a_306_, lean_object* v_hma_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v_m_305_, v_a_306_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___boxed(lean_object* v_00_u03b2_309_, lean_object* v_m_310_, lean_object* v_a_311_, lean_object* v_hma_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(v_00_u03b2_309_, v_m_310_, v_a_311_, v_hma_312_);
lean_dec_ref(v_a_311_);
lean_dec_ref(v_m_310_);
return v_res_313_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2(lean_object* v___x_314_, lean_object* v___x_315_, lean_object* v_as_316_, size_t v_sz_317_, size_t v_i_318_, lean_object* v_bs_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg(v___x_314_, v___x_315_, v_sz_317_, v_i_318_, v_bs_319_);
return v___x_320_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_314_ = stack[0].m_obj;
lean_object* v___x_315_ = stack[1].m_obj;
lean_object* v_as_316_ = stack[2].m_obj;
size_t v_sz_317_ = stack[3].m_num;
size_t v_i_318_ = stack[4].m_num;
lean_object* v_bs_319_ = stack[5].m_obj;
lean_object* v_res_321_;
v_res_321_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2(v___x_314_, v___x_315_, v_as_316_, v_sz_317_, v_i_318_, v_bs_319_);
stack->m_obj
 = v_res_321_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___boxed(lean_object* v___x_322_, lean_object* v___x_323_, lean_object* v_as_324_, lean_object* v_sz_325_, lean_object* v_i_326_, lean_object* v_bs_327_){
_start:
{
size_t v_sz_boxed_328_; size_t v_i_boxed_329_; lean_object* v_res_330_; 
v_sz_boxed_328_ = lean_unbox_usize(v_sz_325_);
lean_dec(v_sz_325_);
v_i_boxed_329_ = lean_unbox_usize(v_i_326_);
lean_dec(v_i_326_);
v_res_330_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2(v___x_322_, v___x_323_, v_as_324_, v_sz_boxed_328_, v_i_boxed_329_, v_bs_327_);
lean_dec_ref(v_as_324_);
lean_dec_ref(v___x_323_);
lean_dec_ref(v___x_322_);
return v_res_330_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0(lean_object* v_00_u03b2_331_, lean_object* v_a_332_, lean_object* v_x_333_){
_start:
{
uint8_t v___x_334_; 
v___x_334_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_a_332_, v_x_333_);
return v___x_334_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_332_ = stack[1].m_obj;
lean_object* v_x_333_ = stack[2].m_obj;
uint8_t v_res_335_;
v_res_335_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0(lean_box(0), v_a_332_, v_x_333_);
stack->m_num = v_res_335_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_336_, lean_object* v_a_337_, lean_object* v_x_338_){
_start:
{
uint8_t v_res_339_; lean_object* v_r_340_; 
v_res_339_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0(v_00_u03b2_336_, v_a_337_, v_x_338_);
lean_dec(v_x_338_);
lean_dec_ref(v_a_337_);
v_r_340_ = lean_box(v_res_339_);
return v_r_340_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2(lean_object* v_00_u03b2_341_, lean_object* v_a_342_, lean_object* v_x_343_, lean_object* v_x_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2___redArg(v_a_342_, v_x_343_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2___boxed(lean_object* v_00_u03b2_346_, lean_object* v_a_347_, lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2(v_00_u03b2_346_, v_a_347_, v_x_348_, v_x_349_);
lean_dec(v_x_348_);
lean_dec_ref(v_a_347_);
return v_res_350_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(lean_object* v_as_352_, size_t v_i_353_, size_t v_stop_354_){
_start:
{
uint8_t v___x_355_; 
v___x_355_ = lean_usize_dec_eq(v_i_353_, v_stop_354_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_356_ = lean_array_uget_borrowed(v_as_352_, v_i_353_);
v___x_357_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___closed__0));
v___x_358_ = lean_string_dec_eq(v___x_356_, v___x_357_);
if (v___x_358_ == 0)
{
size_t v___x_359_; size_t v___x_360_; 
v___x_359_ = ((size_t)1ULL);
v___x_360_ = lean_usize_add(v_i_353_, v___x_359_);
v_i_353_ = v___x_360_;
goto _start;
}
else
{
return v___x_358_;
}
}
else
{
uint8_t v___x_362_; 
v___x_362_ = 0;
return v___x_362_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_352_ = stack[0].m_obj;
size_t v_i_353_ = stack[1].m_num;
size_t v_stop_354_ = stack[2].m_num;
uint8_t v_res_363_;
v_res_363_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(v_as_352_, v_i_353_, v_stop_354_);
stack->m_num = v_res_363_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___boxed(lean_object* v_as_364_, lean_object* v_i_365_, lean_object* v_stop_366_){
_start:
{
size_t v_i_boxed_367_; size_t v_stop_boxed_368_; uint8_t v_res_369_; lean_object* v_r_370_; 
v_i_boxed_367_ = lean_unbox_usize(v_i_365_);
lean_dec(v_i_365_);
v_stop_boxed_368_ = lean_unbox_usize(v_stop_366_);
lean_dec(v_stop_366_);
v_res_369_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(v_as_364_, v_i_boxed_367_, v_stop_boxed_368_);
lean_dec_ref(v_as_364_);
v_r_370_ = lean_box(v_res_369_);
return v_r_370_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(lean_object* v_as_372_, size_t v_i_373_, size_t v_stop_374_){
_start:
{
uint8_t v___x_375_; 
v___x_375_ = lean_usize_dec_eq(v_i_373_, v_stop_374_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_376_ = lean_array_uget_borrowed(v_as_372_, v_i_373_);
v___x_377_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___closed__0));
v___x_378_ = lean_string_dec_eq(v___x_376_, v___x_377_);
if (v___x_378_ == 0)
{
size_t v___x_379_; size_t v___x_380_; 
v___x_379_ = ((size_t)1ULL);
v___x_380_ = lean_usize_add(v_i_373_, v___x_379_);
v_i_373_ = v___x_380_;
goto _start;
}
else
{
return v___x_378_;
}
}
else
{
uint8_t v___x_382_; 
v___x_382_ = 0;
return v___x_382_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_372_ = stack[0].m_obj;
size_t v_i_373_ = stack[1].m_num;
size_t v_stop_374_ = stack[2].m_num;
uint8_t v_res_383_;
v_res_383_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(v_as_372_, v_i_373_, v_stop_374_);
stack->m_num = v_res_383_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___boxed(lean_object* v_as_384_, lean_object* v_i_385_, lean_object* v_stop_386_){
_start:
{
size_t v_i_boxed_387_; size_t v_stop_boxed_388_; uint8_t v_res_389_; lean_object* v_r_390_; 
v_i_boxed_387_ = lean_unbox_usize(v_i_385_);
lean_dec(v_i_385_);
v_stop_boxed_388_ = lean_unbox_usize(v_stop_386_);
lean_dec(v_stop_386_);
v_res_389_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(v_as_384_, v_i_boxed_387_, v_stop_boxed_388_);
lean_dec_ref(v_as_384_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(lean_object* v_as_391_, size_t v_i_392_, size_t v_stop_393_, lean_object* v_b_394_){
_start:
{
lean_object* v___y_396_; uint8_t v___x_400_; 
v___x_400_ = lean_usize_dec_eq(v_i_392_, v_stop_393_);
if (v___x_400_ == 0)
{
if (lean_obj_tag(v_b_394_) == 0)
{
v___y_396_ = v_b_394_;
goto v___jp_395_;
}
else
{
lean_object* v_val_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v_val_401_ = lean_ctor_get(v_b_394_, 0);
lean_inc(v_val_401_);
lean_dec_ref_known(v_b_394_, 1);
v___x_402_ = lean_array_uget_borrowed(v_as_391_, v_i_392_);
lean_inc(v___x_402_);
v___x_403_ = l_Std_Http_Header_Connection_parse(v___x_402_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v___x_404_; 
lean_dec(v_val_401_);
v___x_404_ = lean_box(0);
v___y_396_ = v___x_404_;
goto v___jp_395_;
}
else
{
lean_object* v_val_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_413_; 
v_val_405_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_413_ == 0)
{
v___x_407_ = v___x_403_;
v_isShared_408_ = v_isSharedCheck_413_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_val_405_);
lean_dec(v___x_403_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_413_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_409_ = l_Array_append___redArg(v_val_401_, v_val_405_);
lean_dec(v_val_405_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v___x_409_);
v___x_411_ = v___x_407_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
v___y_396_ = v___x_411_;
goto v___jp_395_;
}
}
}
}
}
else
{
return v_b_394_;
}
v___jp_395_:
{
size_t v___x_397_; size_t v___x_398_; 
v___x_397_ = ((size_t)1ULL);
v___x_398_ = lean_usize_add(v_i_392_, v___x_397_);
v_i_392_ = v___x_398_;
v_b_394_ = v___y_396_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_391_ = stack[0].m_obj;
size_t v_i_392_ = stack[1].m_num;
size_t v_stop_393_ = stack[2].m_num;
lean_object* v_b_394_ = stack[3].m_obj;
lean_object* v_res_414_;
v_res_414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_as_391_, v_i_392_, v_stop_393_, v_b_394_);
stack->m_obj
 = v_res_414_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2___boxed(lean_object* v_as_415_, lean_object* v_i_416_, lean_object* v_stop_417_, lean_object* v_b_418_){
_start:
{
size_t v_i_boxed_419_; size_t v_stop_boxed_420_; lean_object* v_res_421_; 
v_i_boxed_419_ = lean_unbox_usize(v_i_416_);
lean_dec(v_i_416_);
v_stop_boxed_420_ = lean_unbox_usize(v_stop_417_);
lean_dec(v_stop_417_);
v_res_421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_as_415_, v_i_boxed_419_, v_stop_boxed_420_, v_b_418_);
lean_dec_ref(v_as_415_);
return v_res_421_;
}
}
uint8_t l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(uint8_t v_dir_426_, lean_object* v_message_427_){
_start:
{
lean_object* v_val_429_; lean_object* v___y_447_; lean_object* v___x_450_; lean_object* v_indexes_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_450_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_426_, v_message_427_);
v_indexes_451_ = lean_ctor_get(v___x_450_, 1);
v___x_452_ = l_Std_Http_Header_Name_connection;
v___x_453_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_451_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; 
lean_dec_ref(v___x_450_);
v___x_454_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0));
v_val_429_ = v___x_454_;
goto v___jp_428_;
}
else
{
lean_object* v___x_455_; size_t v_sz_456_; size_t v___x_457_; lean_object* v_entries_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_455_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v_indexes_451_, v___x_452_);
v_sz_456_ = lean_array_size(v___x_455_);
v___x_457_ = ((size_t)0ULL);
lean_inc(v___x_455_);
v_entries_458_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg(v___x_450_, v___x_455_, v_sz_456_, v___x_457_, v___x_455_);
lean_dec(v___x_455_);
lean_dec_ref(v___x_450_);
v___x_459_ = lean_unsigned_to_nat(0u);
v___x_460_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0));
v___x_461_ = lean_array_get_size(v_entries_458_);
v___x_462_ = lean_nat_dec_lt(v___x_459_, v___x_461_);
if (v___x_462_ == 0)
{
lean_dec_ref(v_entries_458_);
v_val_429_ = v___x_460_;
goto v___jp_428_;
}
else
{
lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_463_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__1));
v___x_464_ = lean_nat_dec_le(v___x_461_, v___x_461_);
if (v___x_464_ == 0)
{
if (v___x_462_ == 0)
{
lean_dec_ref(v_entries_458_);
v_val_429_ = v___x_460_;
goto v___jp_428_;
}
else
{
size_t v___x_465_; lean_object* v___x_466_; 
v___x_465_ = lean_usize_of_nat(v___x_461_);
v___x_466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_entries_458_, v___x_457_, v___x_465_, v___x_463_);
lean_dec_ref(v_entries_458_);
v___y_447_ = v___x_466_;
goto v___jp_446_;
}
}
else
{
size_t v___x_467_; lean_object* v___x_468_; 
v___x_467_ = lean_usize_of_nat(v___x_461_);
v___x_468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_entries_458_, v___x_457_, v___x_467_, v___x_463_);
lean_dec_ref(v_entries_458_);
v___y_447_ = v___x_468_;
goto v___jp_446_;
}
}
}
v___jp_428_:
{
uint8_t v___x_430_; uint8_t v___x_431_; uint8_t v___x_432_; 
v___x_430_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_426_, v_message_427_);
v___x_431_ = 1;
v___x_432_ = l_Std_Http_instBEqVersion_beq(v___x_430_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_433_ = lean_unsigned_to_nat(0u);
v___x_434_ = lean_array_get_size(v_val_429_);
v___x_435_ = lean_nat_dec_lt(v___x_433_, v___x_434_);
if (v___x_435_ == 0)
{
lean_dec_ref(v_val_429_);
return v___x_435_;
}
else
{
if (v___x_435_ == 0)
{
lean_dec_ref(v_val_429_);
return v___x_435_;
}
else
{
size_t v___x_436_; size_t v___x_437_; uint8_t v___x_438_; 
v___x_436_ = ((size_t)0ULL);
v___x_437_ = lean_usize_of_nat(v___x_434_);
v___x_438_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(v_val_429_, v___x_436_, v___x_437_);
lean_dec_ref(v_val_429_);
return v___x_438_;
}
}
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = lean_array_get_size(v_val_429_);
v___x_441_ = lean_nat_dec_lt(v___x_439_, v___x_440_);
if (v___x_441_ == 0)
{
lean_dec_ref(v_val_429_);
return v___x_432_;
}
else
{
if (v___x_441_ == 0)
{
lean_dec_ref(v_val_429_);
return v___x_432_;
}
else
{
size_t v___x_442_; size_t v___x_443_; uint8_t v___x_444_; 
v___x_442_ = ((size_t)0ULL);
v___x_443_ = lean_usize_of_nat(v___x_440_);
v___x_444_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(v_val_429_, v___x_442_, v___x_443_);
lean_dec_ref(v_val_429_);
if (v___x_444_ == 0)
{
return v___x_432_;
}
else
{
uint8_t v___x_445_; 
v___x_445_ = 0;
return v___x_445_;
}
}
}
}
}
v___jp_446_:
{
if (lean_obj_tag(v___y_447_) == 0)
{
uint8_t v___x_448_; 
v___x_448_ = 0;
return v___x_448_;
}
else
{
lean_object* v_val_449_; 
v_val_449_ = lean_ctor_get(v___y_447_, 0);
lean_inc(v_val_449_);
lean_dec_ref_known(v___y_447_, 1);
v_val_429_ = v_val_449_;
goto v___jp_428_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_426_ = stack[0].m_num;
lean_object* v_message_427_ = stack[1].m_obj;
uint8_t v_res_469_;
v_res_469_ = l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(v_dir_426_, v_message_427_);
stack->m_num = v_res_469_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___boxed(lean_object* v_dir_470_, lean_object* v_message_471_){
_start:
{
uint8_t v_dir_boxed_472_; uint8_t v_res_473_; lean_object* v_r_474_; 
v_dir_boxed_472_ = lean_unbox(v_dir_470_);
v_res_473_ = l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(v_dir_boxed_472_, v_message_471_);
lean_dec(v_message_471_);
v_r_474_ = lean_box(v_res_473_);
return v_r_474_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1___redArg(lean_object* v_x_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Std_Http_Request_instReprHead_repr___redArg(v_x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1(lean_object* v_x_477_, lean_object* v_prec_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Std_Http_Request_instReprHead_repr___redArg(v_x_477_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1___boxed(lean_object* v_x_480_, lean_object* v_prec_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_Http_Protocol_H1_instReprHead___aux__1(v_x_480_, v_prec_481_);
lean_dec(v_prec_481_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3___redArg(lean_object* v_x_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Std_Http_Response_instReprHead_repr___redArg(v_x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3(lean_object* v_x_485_, lean_object* v_prec_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Std_Http_Response_instReprHead_repr___redArg(v_x_485_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3___boxed(lean_object* v_x_488_, lean_object* v_prec_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Std_Http_Protocol_H1_instReprHead___aux__3(v_x_488_, v_prec_489_);
lean_dec(v_prec_489_);
return v_res_490_;
}
}
lean_object* l_Std_Http_Protocol_H1_instReprHead(uint8_t v_dir_493_){
_start:
{
if (v_dir_493_ == 0)
{
lean_object* v___x_494_; 
v___x_494_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprHead___closed__0));
return v___x_494_;
}
else
{
lean_object* v___x_495_; 
v___x_495_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprHead___closed__1));
return v___x_495_;
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_instReprHead_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_493_ = stack[0].m_num;
lean_object* v_res_496_;
v_res_496_ = l_Std_Http_Protocol_H1_instReprHead(v_dir_493_);
stack->m_obj
 = v_res_496_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___boxed(lean_object* v_dir_497_){
_start:
{
uint8_t v_dir_boxed_498_; lean_object* v_res_499_; 
v_dir_boxed_498_ = lean_unbox(v_dir_497_);
v_res_499_ = l_Std_Http_Protocol_H1_instReprHead(v_dir_boxed_498_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__0(lean_object* v_x_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = lean_string_from_utf8_unchecked(v_x_500_);
return v___x_501_;
}
}
lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1(lean_object* v___x_502_, lean_object* v___x_503_, lean_object* v___x_504_, lean_object* v_name_505_, lean_object* v___x_506_, uint32_t v___x_507_, lean_object* v___x_508_, lean_object* v_it_509_, lean_object* v_acc_510_, lean_object* v_hP_511_, lean_object* v_recur_512_){
_start:
{
lean_object* v_it_514_; lean_object* v_out_515_; lean_object* v_it_531_; lean_object* v_startInclusive_532_; lean_object* v_endExclusive_533_; 
if (lean_obj_tag(v_it_509_) == 0)
{
lean_object* v_currPos_545_; lean_object* v_searcher_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_568_; 
v_currPos_545_ = lean_ctor_get(v_it_509_, 0);
v_searcher_546_ = lean_ctor_get(v_it_509_, 1);
v_isSharedCheck_568_ = !lean_is_exclusive(v_it_509_);
if (v_isSharedCheck_568_ == 0)
{
v___x_548_ = v_it_509_;
v_isShared_549_ = v_isSharedCheck_568_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_searcher_546_);
lean_inc(v_currPos_545_);
lean_dec(v_it_509_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_568_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
uint8_t v_decide_550_; 
v_decide_550_ = lean_nat_dec_eq(v_searcher_546_, v___x_506_);
if (v_decide_550_ == 0)
{
uint32_t v___x_551_; uint8_t v___x_552_; 
lean_dec(v___x_506_);
v___x_551_ = lean_string_utf8_get_fast(v_name_505_, v_searcher_546_);
v___x_552_ = lean_uint32_dec_eq(v___x_551_, v___x_507_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_553_ = lean_string_utf8_next_fast(v_name_505_, v_searcher_546_);
lean_dec(v_searcher_546_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 1, v___x_553_);
v___x_555_ = v___x_548_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_currPos_545_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v___x_553_);
v___x_555_ = v_reuseFailAlloc_557_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_556_; 
v___x_556_ = lean_apply_4(v_recur_512_, v___x_555_, v_acc_510_, lean_box(0), lean_box(0));
return v___x_556_;
}
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v_slice_561_; lean_object* v_nextIt_563_; 
v___x_558_ = lean_string_utf8_next_fast(v_name_505_, v_searcher_546_);
v___x_559_ = lean_nat_sub(v___x_558_, v_searcher_546_);
v___x_560_ = lean_nat_add(v_searcher_546_, v___x_559_);
lean_dec(v___x_559_);
v_slice_561_ = l_String_Slice_subslice_x21(v___x_508_, v_currPos_545_, v_searcher_546_);
lean_inc(v___x_560_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 1, v___x_560_);
lean_ctor_set(v___x_548_, 0, v___x_560_);
v_nextIt_563_ = v___x_548_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v___x_560_);
v_nextIt_563_ = v_reuseFailAlloc_566_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v_startInclusive_564_; lean_object* v_endExclusive_565_; 
v_startInclusive_564_ = lean_ctor_get(v_slice_561_, 0);
lean_inc(v_startInclusive_564_);
v_endExclusive_565_ = lean_ctor_get(v_slice_561_, 1);
lean_inc(v_endExclusive_565_);
lean_dec_ref(v_slice_561_);
v_it_531_ = v_nextIt_563_;
v_startInclusive_532_ = v_startInclusive_564_;
v_endExclusive_533_ = v_endExclusive_565_;
goto v___jp_530_;
}
}
}
else
{
lean_object* v___x_567_; 
lean_del_object(v___x_548_);
lean_dec(v_searcher_546_);
v___x_567_ = lean_box(1);
v_it_531_ = v___x_567_;
v_startInclusive_532_ = v_currPos_545_;
v_endExclusive_533_ = v___x_506_;
goto v___jp_530_;
}
}
}
else
{
lean_dec_ref(v_recur_512_);
lean_dec(v___x_506_);
return v_acc_510_;
}
v___jp_513_:
{
if (lean_obj_tag(v_acc_510_) == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_516_, 0, v_out_515_);
v___x_517_ = lean_apply_4(v_recur_512_, v_it_514_, v___x_516_, lean_box(0), lean_box(0));
return v___x_517_;
}
else
{
lean_object* v_val_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_529_; 
v_val_518_ = lean_ctor_get(v_acc_510_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v_acc_510_);
if (v_isSharedCheck_529_ == 0)
{
v___x_520_ = v_acc_510_;
v_isShared_521_ = v_isSharedCheck_529_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_val_518_);
lean_dec(v_acc_510_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_529_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_522_ = lean_string_utf8_extract_fast(v___x_502_, v___x_503_, v___x_504_);
v___x_523_ = lean_string_append(v_val_518_, v___x_522_);
lean_dec_ref(v___x_522_);
v___x_524_ = lean_string_append(v___x_523_, v_out_515_);
lean_dec_ref(v_out_515_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_524_);
v___x_526_ = v___x_520_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_528_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_527_; 
v___x_527_ = lean_apply_4(v_recur_512_, v_it_514_, v___x_526_, lean_box(0), lean_box(0));
return v___x_527_;
}
}
}
}
v___jp_530_:
{
lean_object* v___x_534_; uint32_t v___x_535_; uint32_t v___x_536_; uint8_t v___x_537_; 
v___x_534_ = lean_string_utf8_extract_fast(v_name_505_, v_startInclusive_532_, v_endExclusive_533_);
lean_dec(v_endExclusive_533_);
lean_dec(v_startInclusive_532_);
v___x_535_ = lean_string_utf8_get(v___x_534_, v___x_503_);
v___x_536_ = 97;
v___x_537_ = lean_uint32_dec_le(v___x_536_, v___x_535_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; 
v___x_538_ = lean_string_utf8_set(v___x_534_, v___x_503_, v___x_535_);
v_it_514_ = v_it_531_;
v_out_515_ = v___x_538_;
goto v___jp_513_;
}
else
{
uint32_t v___x_539_; uint8_t v___x_540_; 
v___x_539_ = 122;
v___x_540_ = lean_uint32_dec_le(v___x_535_, v___x_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; 
v___x_541_ = lean_string_utf8_set(v___x_534_, v___x_503_, v___x_535_);
v_it_514_ = v_it_531_;
v_out_515_ = v___x_541_;
goto v___jp_513_;
}
else
{
uint32_t v___x_542_; uint32_t v___x_543_; lean_object* v___x_544_; 
v___x_542_ = 4294967264;
v___x_543_ = lean_uint32_add(v___x_535_, v___x_542_);
v___x_544_ = lean_string_utf8_set(v___x_534_, v___x_503_, v___x_543_);
v_it_514_ = v_it_531_;
v_out_515_ = v___x_544_;
goto v___jp_513_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_502_ = stack[0].m_obj;
lean_object* v___x_503_ = stack[1].m_obj;
lean_object* v___x_504_ = stack[2].m_obj;
lean_object* v_name_505_ = stack[3].m_obj;
lean_object* v___x_506_ = stack[4].m_obj;
uint32_t v___x_507_ = stack[5].m_num;
lean_object* v___x_508_ = stack[6].m_obj;
lean_object* v_it_509_ = stack[7].m_obj;
lean_object* v_acc_510_ = stack[8].m_obj;
lean_object* v_recur_512_ = stack[10].m_obj;
lean_object* v_res_569_;
v_res_569_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1(v___x_502_, v___x_503_, v___x_504_, v_name_505_, v___x_506_, v___x_507_, v___x_508_, v_it_509_, v_acc_510_, lean_box(0), v_recur_512_);
stack->m_obj
 = v_res_569_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1___boxed(lean_object* v___x_570_, lean_object* v___x_571_, lean_object* v___x_572_, lean_object* v_name_573_, lean_object* v___x_574_, lean_object* v___x_575_, lean_object* v___x_576_, lean_object* v_it_577_, lean_object* v_acc_578_, lean_object* v_hP_579_, lean_object* v_recur_580_){
_start:
{
uint32_t v___x_2760__boxed_581_; lean_object* v_res_582_; 
v___x_2760__boxed_581_ = lean_unbox_uint32(v___x_575_);
lean_dec(v___x_575_);
v_res_582_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1(v___x_570_, v___x_571_, v___x_572_, v_name_573_, v___x_574_, v___x_2760__boxed_581_, v___x_576_, v_it_577_, v_acc_578_, v_hP_579_, v_recur_580_);
lean_dec_ref(v___x_576_);
lean_dec_ref(v_name_573_);
lean_dec(v___x_572_);
lean_dec(v___x_571_);
lean_dec_ref(v___x_570_);
return v_res_582_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed__const__1(void){
_start:
{
uint32_t v___x_588_; lean_object* v___x_589_; 
v___x_588_ = 45;
v___x_589_ = lean_box_uint32(v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2(lean_object* v_buf_590_, lean_object* v_name_591_, lean_object* v_value_592_){
_start:
{
lean_object* v___y_594_; lean_object* v___f_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v_it_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___f_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___f_613_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__2));
v___x_614_ = lean_unsigned_to_nat(0u);
v___x_615_ = lean_string_utf8_byte_size(v_name_591_);
lean_inc_ref(v_name_591_);
v___x_616_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_616_, 0, v_name_591_);
lean_ctor_set(v___x_616_, 1, v___x_614_);
lean_ctor_set(v___x_616_, 2, v___x_615_);
lean_inc_ref(v___x_616_);
v_it_617_ = l_String_Slice_splitToSubslice___redArg(v___x_616_, v___f_613_);
v___x_618_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__3));
v___x_619_ = lean_unsigned_to_nat(1u);
v___x_620_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed__const__1;
v___f_621_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1___boxed), 11, 7);
lean_closure_set(v___f_621_, 0, v___x_618_);
lean_closure_set(v___f_621_, 1, v___x_614_);
lean_closure_set(v___f_621_, 2, v___x_619_);
lean_closure_set(v___f_621_, 3, v_name_591_);
lean_closure_set(v___f_621_, 4, v___x_615_);
lean_closure_set(v___f_621_, 5, v___x_620_);
lean_closure_set(v___f_621_, 6, v___x_616_);
v___x_622_ = lean_box(0);
v___x_623_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_621_, v_it_617_, v___x_622_, lean_box(0));
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v___x_624_; 
v___x_624_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_594_ = v___x_624_;
goto v___jp_593_;
}
else
{
lean_object* v_val_625_; 
v_val_625_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_val_625_);
lean_dec_ref_known(v___x_623_, 1);
v___y_594_ = v_val_625_;
goto v___jp_593_;
}
v___jp_593_:
{
lean_object* v_data_595_; lean_object* v_size_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_612_; 
v_data_595_ = lean_ctor_get(v_buf_590_, 0);
v_size_596_ = lean_ctor_get(v_buf_590_, 1);
v_isSharedCheck_612_ = !lean_is_exclusive(v_buf_590_);
if (v_isSharedCheck_612_ == 0)
{
v___x_598_ = v_buf_590_;
v_isShared_599_ = v_isSharedCheck_612_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_size_596_);
lean_inc(v_data_595_);
lean_dec(v_buf_590_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_612_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_600_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__0));
v___x_601_ = lean_string_append(v___y_594_, v___x_600_);
v___x_602_ = lean_string_append(v___x_601_, v_value_592_);
v___x_603_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__1));
v___x_604_ = lean_string_append(v___x_602_, v___x_603_);
v___x_605_ = lean_string_to_utf8(v___x_604_);
lean_dec_ref(v___x_604_);
lean_inc_ref(v___x_605_);
v___x_606_ = lean_array_push(v_data_595_, v___x_605_);
v___x_607_ = lean_byte_array_size(v___x_605_);
lean_dec_ref(v___x_605_);
v___x_608_ = lean_nat_add(v_size_596_, v___x_607_);
lean_dec(v_size_596_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 1, v___x_608_);
lean_ctor_set(v___x_598_, 0, v___x_606_);
v___x_610_ = v___x_598_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed(lean_object* v_buf_626_, lean_object* v_name_627_, lean_object* v_value_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2(v_buf_626_, v_name_627_, v_value_628_);
lean_dec_ref(v_value_628_);
return v_res_629_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__1));
v___x_633_ = lean_string_to_utf8(v___x_632_);
return v___x_633_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_635_ = lean_byte_array_size(v___x_634_);
return v___x_635_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23));
v___x_671_ = lean_byte_array_size(v___x_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1(lean_object* v_buffer_715_, lean_object* v_req_716_){
_start:
{
uint8_t v_method_717_; uint8_t v_version_718_; lean_object* v_uri_719_; lean_object* v_headers_720_; lean_object* v___f_721_; lean_object* v___f_722_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v_port_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v_host_793_; lean_object* v_port_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v_port_891_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v_host_910_; lean_object* v_port_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_927_; 
v_method_717_ = lean_ctor_get_uint8(v_req_716_, sizeof(void*)*2);
v_version_718_ = lean_ctor_get_uint8(v_req_716_, sizeof(void*)*2 + 1);
v_uri_719_ = lean_ctor_get(v_req_716_, 0);
lean_inc(v_uri_719_);
v_headers_720_ = lean_ctor_get(v_req_716_, 1);
lean_inc_ref(v_headers_720_);
lean_dec_ref(v_req_716_);
v___f_721_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__0));
v___f_722_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1));
switch(v_method_717_)
{
case 0:
{
lean_object* v___x_1007_; 
v___x_1007_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28));
v___y_927_ = v___x_1007_;
goto v___jp_926_;
}
case 1:
{
lean_object* v___x_1008_; 
v___x_1008_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29));
v___y_927_ = v___x_1008_;
goto v___jp_926_;
}
case 2:
{
lean_object* v___x_1009_; 
v___x_1009_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30));
v___y_927_ = v___x_1009_;
goto v___jp_926_;
}
case 3:
{
lean_object* v___x_1010_; 
v___x_1010_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31));
v___y_927_ = v___x_1010_;
goto v___jp_926_;
}
case 4:
{
lean_object* v___x_1011_; 
v___x_1011_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32));
v___y_927_ = v___x_1011_;
goto v___jp_926_;
}
case 5:
{
lean_object* v___x_1012_; 
v___x_1012_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33));
v___y_927_ = v___x_1012_;
goto v___jp_926_;
}
case 6:
{
lean_object* v___x_1013_; 
v___x_1013_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34));
v___y_927_ = v___x_1013_;
goto v___jp_926_;
}
case 7:
{
lean_object* v___x_1014_; 
v___x_1014_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35));
v___y_927_ = v___x_1014_;
goto v___jp_926_;
}
case 8:
{
lean_object* v___x_1015_; 
v___x_1015_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36));
v___y_927_ = v___x_1015_;
goto v___jp_926_;
}
case 9:
{
lean_object* v___x_1016_; 
v___x_1016_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37));
v___y_927_ = v___x_1016_;
goto v___jp_926_;
}
case 10:
{
lean_object* v___x_1017_; 
v___x_1017_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38));
v___y_927_ = v___x_1017_;
goto v___jp_926_;
}
case 11:
{
lean_object* v___x_1018_; 
v___x_1018_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39));
v___y_927_ = v___x_1018_;
goto v___jp_926_;
}
case 12:
{
lean_object* v___x_1019_; 
v___x_1019_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40));
v___y_927_ = v___x_1019_;
goto v___jp_926_;
}
case 13:
{
lean_object* v___x_1020_; 
v___x_1020_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41));
v___y_927_ = v___x_1020_;
goto v___jp_926_;
}
case 14:
{
lean_object* v___x_1021_; 
v___x_1021_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42));
v___y_927_ = v___x_1021_;
goto v___jp_926_;
}
case 15:
{
lean_object* v___x_1022_; 
v___x_1022_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43));
v___y_927_ = v___x_1022_;
goto v___jp_926_;
}
case 16:
{
lean_object* v___x_1023_; 
v___x_1023_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44));
v___y_927_ = v___x_1023_;
goto v___jp_926_;
}
case 17:
{
lean_object* v___x_1024_; 
v___x_1024_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45));
v___y_927_ = v___x_1024_;
goto v___jp_926_;
}
case 18:
{
lean_object* v___x_1025_; 
v___x_1025_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46));
v___y_927_ = v___x_1025_;
goto v___jp_926_;
}
case 19:
{
lean_object* v___x_1026_; 
v___x_1026_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47));
v___y_927_ = v___x_1026_;
goto v___jp_926_;
}
case 20:
{
lean_object* v___x_1027_; 
v___x_1027_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48));
v___y_927_ = v___x_1027_;
goto v___jp_926_;
}
case 21:
{
lean_object* v___x_1028_; 
v___x_1028_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49));
v___y_927_ = v___x_1028_;
goto v___jp_926_;
}
case 22:
{
lean_object* v___x_1029_; 
v___x_1029_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50));
v___y_927_ = v___x_1029_;
goto v___jp_926_;
}
case 23:
{
lean_object* v___x_1030_; 
v___x_1030_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51));
v___y_927_ = v___x_1030_;
goto v___jp_926_;
}
case 24:
{
lean_object* v___x_1031_; 
v___x_1031_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52));
v___y_927_ = v___x_1031_;
goto v___jp_926_;
}
case 25:
{
lean_object* v___x_1032_; 
v___x_1032_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53));
v___y_927_ = v___x_1032_;
goto v___jp_926_;
}
case 26:
{
lean_object* v___x_1033_; 
v___x_1033_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54));
v___y_927_ = v___x_1033_;
goto v___jp_926_;
}
case 27:
{
lean_object* v___x_1034_; 
v___x_1034_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55));
v___y_927_ = v___x_1034_;
goto v___jp_926_;
}
case 28:
{
lean_object* v___x_1035_; 
v___x_1035_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56));
v___y_927_ = v___x_1035_;
goto v___jp_926_;
}
case 29:
{
lean_object* v___x_1036_; 
v___x_1036_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57));
v___y_927_ = v___x_1036_;
goto v___jp_926_;
}
case 30:
{
lean_object* v___x_1037_; 
v___x_1037_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58));
v___y_927_ = v___x_1037_;
goto v___jp_926_;
}
case 31:
{
lean_object* v___x_1038_; 
v___x_1038_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59));
v___y_927_ = v___x_1038_;
goto v___jp_926_;
}
case 32:
{
lean_object* v___x_1039_; 
v___x_1039_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60));
v___y_927_ = v___x_1039_;
goto v___jp_926_;
}
case 33:
{
lean_object* v___x_1040_; 
v___x_1040_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61));
v___y_927_ = v___x_1040_;
goto v___jp_926_;
}
case 34:
{
lean_object* v___x_1041_; 
v___x_1041_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62));
v___y_927_ = v___x_1041_;
goto v___jp_926_;
}
case 35:
{
lean_object* v___x_1042_; 
v___x_1042_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63));
v___y_927_ = v___x_1042_;
goto v___jp_926_;
}
case 36:
{
lean_object* v___x_1043_; 
v___x_1043_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64));
v___y_927_ = v___x_1043_;
goto v___jp_926_;
}
case 37:
{
lean_object* v___x_1044_; 
v___x_1044_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65));
v___y_927_ = v___x_1044_;
goto v___jp_926_;
}
case 38:
{
lean_object* v___x_1045_; 
v___x_1045_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66));
v___y_927_ = v___x_1045_;
goto v___jp_926_;
}
default: 
{
lean_object* v___x_1046_; 
v___x_1046_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67));
v___y_927_ = v___x_1046_;
goto v___jp_926_;
}
}
v___jp_723_:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v_buffer_735_; lean_object* v_buffer_736_; lean_object* v_data_737_; lean_object* v_size_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_747_; 
v___x_727_ = lean_string_to_utf8(v___y_726_);
lean_inc_ref(v___x_727_);
v___x_728_ = lean_array_push(v___y_725_, v___x_727_);
v___x_729_ = lean_byte_array_size(v___x_727_);
lean_dec_ref(v___x_727_);
v___x_730_ = lean_nat_add(v___y_724_, v___x_729_);
lean_dec(v___y_724_);
v___x_731_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_732_ = lean_array_push(v___x_728_, v___x_731_);
v___x_733_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3);
v___x_734_ = lean_nat_add(v___x_730_, v___x_733_);
lean_dec(v___x_730_);
v_buffer_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_buffer_735_, 0, v___x_732_);
lean_ctor_set(v_buffer_735_, 1, v___x_734_);
v_buffer_736_ = l_Std_Http_Headers_fold___redArg(v_headers_720_, v_buffer_735_, v___f_722_);
lean_dec_ref(v_headers_720_);
v_data_737_ = lean_ctor_get(v_buffer_736_, 0);
v_size_738_ = lean_ctor_get(v_buffer_736_, 1);
v_isSharedCheck_747_ = !lean_is_exclusive(v_buffer_736_);
if (v_isSharedCheck_747_ == 0)
{
v___x_740_ = v_buffer_736_;
v_isShared_741_ = v_isSharedCheck_747_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_size_738_);
lean_inc(v_data_737_);
lean_dec(v_buffer_736_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_747_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_742_ = lean_array_push(v_data_737_, v___x_731_);
v___x_743_ = lean_nat_add(v_size_738_, v___x_733_);
lean_dec(v_size_738_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 1, v___x_743_);
lean_ctor_set(v___x_740_, 0, v___x_742_);
v___x_745_ = v___x_740_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
v___jp_748_:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_754_ = lean_string_to_utf8(v___y_753_);
lean_dec_ref(v___y_753_);
lean_inc_ref(v___x_754_);
v___x_755_ = lean_array_push(v___y_751_, v___x_754_);
v___x_756_ = lean_byte_array_size(v___x_754_);
lean_dec_ref(v___x_754_);
v___x_757_ = lean_nat_add(v___y_749_, v___x_756_);
lean_dec(v___y_749_);
v___x_758_ = lean_array_push(v___x_755_, v___y_752_);
v___x_759_ = lean_nat_add(v___x_757_, v___y_750_);
lean_dec(v___x_757_);
switch(v_version_718_)
{
case 0:
{
lean_object* v___x_760_; 
v___x_760_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4));
v___y_724_ = v___x_759_;
v___y_725_ = v___x_758_;
v___y_726_ = v___x_760_;
goto v___jp_723_;
}
case 1:
{
lean_object* v___x_761_; 
v___x_761_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5));
v___y_724_ = v___x_759_;
v___y_725_ = v___x_758_;
v___y_726_ = v___x_761_;
goto v___jp_723_;
}
case 2:
{
lean_object* v___x_762_; 
v___x_762_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6));
v___y_724_ = v___x_759_;
v___y_725_ = v___x_758_;
v___y_726_ = v___x_762_;
goto v___jp_723_;
}
default: 
{
lean_object* v___x_763_; 
v___x_763_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7));
v___y_724_ = v___x_759_;
v___y_725_ = v___x_758_;
v___y_726_ = v___x_763_;
goto v___jp_723_;
}
}
}
v___jp_764_:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = lean_string_append(v___y_770_, v___y_765_);
lean_dec_ref(v___y_765_);
v___x_773_ = lean_string_append(v___x_772_, v___y_771_);
lean_dec_ref(v___y_771_);
v___y_749_ = v___y_766_;
v___y_750_ = v___y_767_;
v___y_751_ = v___y_768_;
v___y_752_ = v___y_769_;
v___y_753_ = v___x_773_;
goto v___jp_748_;
}
v___jp_774_:
{
switch(lean_obj_tag(v_port_777_))
{
case 0:
{
lean_object* v___x_782_; 
v___x_782_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_765_ = v___y_781_;
v___y_766_ = v___y_775_;
v___y_767_ = v___y_776_;
v___y_768_ = v___y_778_;
v___y_769_ = v___y_779_;
v___y_770_ = v___y_780_;
v___y_771_ = v___x_782_;
goto v___jp_764_;
}
case 1:
{
lean_object* v___x_783_; 
v___x_783_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___y_765_ = v___y_781_;
v___y_766_ = v___y_775_;
v___y_767_ = v___y_776_;
v___y_768_ = v___y_778_;
v___y_769_ = v___y_779_;
v___y_770_ = v___y_780_;
v___y_771_ = v___x_783_;
goto v___jp_764_;
}
default: 
{
uint16_t v_port_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v_port_784_ = lean_ctor_get_uint16(v_port_777_, 0);
lean_dec_ref_known(v_port_777_, 0);
v___x_785_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_786_ = lean_uint16_to_nat(v_port_784_);
v___x_787_ = l_Nat_reprFast(v___x_786_);
v___x_788_ = lean_string_append(v___x_785_, v___x_787_);
lean_dec_ref(v___x_787_);
v___y_765_ = v___y_781_;
v___y_766_ = v___y_775_;
v___y_767_ = v___y_776_;
v___y_768_ = v___y_778_;
v___y_769_ = v___y_779_;
v___y_770_ = v___y_780_;
v___y_771_ = v___x_788_;
goto v___jp_764_;
}
}
}
v___jp_789_:
{
switch(lean_obj_tag(v_host_793_))
{
case 0:
{
lean_object* v_name_797_; 
v_name_797_ = lean_ctor_get(v_host_793_, 0);
lean_inc_ref(v_name_797_);
lean_dec_ref_known(v_host_793_, 1);
v___y_775_ = v___y_790_;
v___y_776_ = v___y_791_;
v_port_777_ = v_port_794_;
v___y_778_ = v___y_792_;
v___y_779_ = v___y_795_;
v___y_780_ = v___y_796_;
v___y_781_ = v_name_797_;
goto v___jp_774_;
}
case 1:
{
lean_object* v_ipv4_798_; lean_object* v___x_799_; 
v_ipv4_798_ = lean_ctor_get(v_host_793_, 0);
lean_inc_ref(v_ipv4_798_);
lean_dec_ref_known(v_host_793_, 1);
v___x_799_ = lean_uv_ntop_v4(v_ipv4_798_);
lean_dec_ref(v_ipv4_798_);
v___y_775_ = v___y_790_;
v___y_776_ = v___y_791_;
v_port_777_ = v_port_794_;
v___y_778_ = v___y_792_;
v___y_779_ = v___y_795_;
v___y_780_ = v___y_796_;
v___y_781_ = v___x_799_;
goto v___jp_774_;
}
default: 
{
lean_object* v_ipv6_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v_ipv6_800_ = lean_ctor_get(v_host_793_, 0);
lean_inc_ref(v_ipv6_800_);
lean_dec_ref_known(v_host_793_, 1);
v___x_801_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9));
v___x_802_ = lean_uv_ntop_v6(v_ipv6_800_);
lean_dec_ref(v_ipv6_800_);
v___x_803_ = lean_string_append(v___x_801_, v___x_802_);
lean_dec_ref(v___x_802_);
v___x_804_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10));
v___x_805_ = lean_string_append(v___x_803_, v___x_804_);
v___y_775_ = v___y_790_;
v___y_776_ = v___y_791_;
v_port_777_ = v_port_794_;
v___y_778_ = v___y_792_;
v___y_779_ = v___y_795_;
v___y_780_ = v___y_796_;
v___y_781_ = v___x_805_;
goto v___jp_774_;
}
}
}
v___jp_806_:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_816_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_817_ = lean_string_append(v___y_812_, v___x_816_);
v___x_818_ = lean_string_append(v___x_817_, v___y_809_);
lean_dec_ref(v___y_809_);
v___x_819_ = lean_string_append(v___x_818_, v___y_807_);
lean_dec_ref(v___y_807_);
v___x_820_ = lean_string_append(v___x_819_, v___y_811_);
lean_dec_ref(v___y_811_);
v___x_821_ = lean_string_append(v___x_820_, v___y_815_);
lean_dec_ref(v___y_815_);
v___y_749_ = v___y_808_;
v___y_750_ = v___y_810_;
v___y_751_ = v___y_813_;
v___y_752_ = v___y_814_;
v___y_753_ = v___x_821_;
goto v___jp_748_;
}
v___jp_822_:
{
lean_object* v_queryPart_832_; 
v_queryPart_832_ = l_Std_Http_URI_Query_formatOption(v___y_824_);
if (lean_obj_tag(v___y_823_) == 0)
{
lean_object* v___x_833_; 
v___x_833_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_807_ = v___y_831_;
v___y_808_ = v___y_826_;
v___y_809_ = v___y_825_;
v___y_810_ = v___y_827_;
v___y_811_ = v_queryPart_832_;
v___y_812_ = v___y_828_;
v___y_813_ = v___y_829_;
v___y_814_ = v___y_830_;
v___y_815_ = v___x_833_;
goto v___jp_806_;
}
else
{
lean_object* v_val_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v_val_834_ = lean_ctor_get(v___y_823_, 0);
lean_inc(v_val_834_);
lean_dec_ref_known(v___y_823_, 1);
v___x_835_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11));
v___x_836_ = l_Std_Http_URI_EncodedFragment_encode(v_val_834_);
lean_dec(v_val_834_);
v___x_837_ = lean_string_from_utf8_unchecked(v___x_836_);
v___x_838_ = lean_string_append(v___x_835_, v___x_837_);
lean_dec_ref(v___x_837_);
v___y_807_ = v___y_831_;
v___y_808_ = v___y_826_;
v___y_809_ = v___y_825_;
v___y_810_ = v___y_827_;
v___y_811_ = v_queryPart_832_;
v___y_812_ = v___y_828_;
v___y_813_ = v___y_829_;
v___y_814_ = v___y_830_;
v___y_815_ = v___x_838_;
goto v___jp_806_;
}
}
v___jp_839_:
{
lean_object* v_queryStr_846_; lean_object* v___x_847_; 
v_queryStr_846_ = l_Std_Http_URI_Query_formatOption(v___y_842_);
v___x_847_ = lean_string_append(v___y_845_, v_queryStr_846_);
lean_dec_ref(v_queryStr_846_);
v___y_749_ = v___y_840_;
v___y_750_ = v___y_841_;
v___y_751_ = v___y_843_;
v___y_752_ = v___y_844_;
v___y_753_ = v___x_847_;
goto v___jp_748_;
}
v___jp_848_:
{
lean_object* v_segments_858_; uint8_t v_absolute_859_; lean_object* v___x_860_; lean_object* v___x_861_; size_t v_sz_862_; size_t v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v_result_866_; 
v_segments_858_ = lean_ctor_get(v___y_855_, 0);
lean_inc_ref(v_segments_858_);
v_absolute_859_ = lean_ctor_get_uint8(v___y_855_, sizeof(void*)*1);
lean_dec_ref(v___y_855_);
v___x_860_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12));
v___x_861_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22));
v_sz_862_ = lean_array_size(v_segments_858_);
v___x_863_ = ((size_t)0ULL);
v___x_864_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_861_, v___f_721_, v_sz_862_, v___x_863_, v_segments_858_);
v___x_865_ = lean_array_to_list(v___x_864_);
v_result_866_ = l_String_intercalate(v___x_860_, v___x_865_);
if (v_absolute_859_ == 0)
{
v___y_823_ = v___y_850_;
v___y_824_ = v___y_849_;
v___y_825_ = v___y_857_;
v___y_826_ = v___y_851_;
v___y_827_ = v___y_852_;
v___y_828_ = v___y_853_;
v___y_829_ = v___y_854_;
v___y_830_ = v___y_856_;
v___y_831_ = v_result_866_;
goto v___jp_822_;
}
else
{
lean_object* v___x_867_; 
v___x_867_ = lean_string_append(v___x_860_, v_result_866_);
lean_dec_ref(v_result_866_);
v___y_823_ = v___y_850_;
v___y_824_ = v___y_849_;
v___y_825_ = v___y_857_;
v___y_826_ = v___y_851_;
v___y_827_ = v___y_852_;
v___y_828_ = v___y_853_;
v___y_829_ = v___y_854_;
v___y_830_ = v___y_856_;
v___y_831_ = v___x_867_;
goto v___jp_822_;
}
}
v___jp_868_:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_881_ = lean_string_append(v___y_875_, v___y_874_);
lean_dec_ref(v___y_874_);
v___x_882_ = lean_string_append(v___x_881_, v___y_880_);
lean_dec_ref(v___y_880_);
lean_inc_ref(v___y_871_);
v___x_883_ = lean_string_append(v___y_871_, v___x_882_);
lean_dec_ref(v___x_882_);
v___y_849_ = v___y_870_;
v___y_850_ = v___y_869_;
v___y_851_ = v___y_872_;
v___y_852_ = v___y_873_;
v___y_853_ = v___y_876_;
v___y_854_ = v___y_877_;
v___y_855_ = v___y_879_;
v___y_856_ = v___y_878_;
v___y_857_ = v___x_883_;
goto v___jp_848_;
}
v___jp_884_:
{
switch(lean_obj_tag(v_port_891_))
{
case 0:
{
lean_object* v___x_897_; 
v___x_897_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_869_ = v___y_886_;
v___y_870_ = v___y_885_;
v___y_871_ = v___y_887_;
v___y_872_ = v___y_888_;
v___y_873_ = v___y_890_;
v___y_874_ = v___y_896_;
v___y_875_ = v___y_889_;
v___y_876_ = v___y_892_;
v___y_877_ = v___y_893_;
v___y_878_ = v___y_895_;
v___y_879_ = v___y_894_;
v___y_880_ = v___x_897_;
goto v___jp_868_;
}
case 1:
{
lean_object* v___x_898_; 
v___x_898_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___y_869_ = v___y_886_;
v___y_870_ = v___y_885_;
v___y_871_ = v___y_887_;
v___y_872_ = v___y_888_;
v___y_873_ = v___y_890_;
v___y_874_ = v___y_896_;
v___y_875_ = v___y_889_;
v___y_876_ = v___y_892_;
v___y_877_ = v___y_893_;
v___y_878_ = v___y_895_;
v___y_879_ = v___y_894_;
v___y_880_ = v___x_898_;
goto v___jp_868_;
}
default: 
{
uint16_t v_port_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v_port_899_ = lean_ctor_get_uint16(v_port_891_, 0);
lean_dec_ref_known(v_port_891_, 0);
v___x_900_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_901_ = lean_uint16_to_nat(v_port_899_);
v___x_902_ = l_Nat_reprFast(v___x_901_);
v___x_903_ = lean_string_append(v___x_900_, v___x_902_);
lean_dec_ref(v___x_902_);
v___y_869_ = v___y_886_;
v___y_870_ = v___y_885_;
v___y_871_ = v___y_887_;
v___y_872_ = v___y_888_;
v___y_873_ = v___y_890_;
v___y_874_ = v___y_896_;
v___y_875_ = v___y_889_;
v___y_876_ = v___y_892_;
v___y_877_ = v___y_893_;
v___y_878_ = v___y_895_;
v___y_879_ = v___y_894_;
v___y_880_ = v___x_903_;
goto v___jp_868_;
}
}
}
v___jp_904_:
{
switch(lean_obj_tag(v_host_910_))
{
case 0:
{
lean_object* v_name_917_; 
v_name_917_ = lean_ctor_get(v_host_910_, 0);
lean_inc_ref(v_name_917_);
lean_dec_ref_known(v_host_910_, 1);
v___y_885_ = v___y_906_;
v___y_886_ = v___y_905_;
v___y_887_ = v___y_907_;
v___y_888_ = v___y_908_;
v___y_889_ = v___y_916_;
v___y_890_ = v___y_909_;
v_port_891_ = v_port_911_;
v___y_892_ = v___y_912_;
v___y_893_ = v___y_913_;
v___y_894_ = v___y_915_;
v___y_895_ = v___y_914_;
v___y_896_ = v_name_917_;
goto v___jp_884_;
}
case 1:
{
lean_object* v_ipv4_918_; lean_object* v___x_919_; 
v_ipv4_918_ = lean_ctor_get(v_host_910_, 0);
lean_inc_ref(v_ipv4_918_);
lean_dec_ref_known(v_host_910_, 1);
v___x_919_ = lean_uv_ntop_v4(v_ipv4_918_);
lean_dec_ref(v_ipv4_918_);
v___y_885_ = v___y_906_;
v___y_886_ = v___y_905_;
v___y_887_ = v___y_907_;
v___y_888_ = v___y_908_;
v___y_889_ = v___y_916_;
v___y_890_ = v___y_909_;
v_port_891_ = v_port_911_;
v___y_892_ = v___y_912_;
v___y_893_ = v___y_913_;
v___y_894_ = v___y_915_;
v___y_895_ = v___y_914_;
v___y_896_ = v___x_919_;
goto v___jp_884_;
}
default: 
{
lean_object* v_ipv6_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v_ipv6_920_ = lean_ctor_get(v_host_910_, 0);
lean_inc_ref(v_ipv6_920_);
lean_dec_ref_known(v_host_910_, 1);
v___x_921_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9));
v___x_922_ = lean_uv_ntop_v6(v_ipv6_920_);
lean_dec_ref(v_ipv6_920_);
v___x_923_ = lean_string_append(v___x_921_, v___x_922_);
lean_dec_ref(v___x_922_);
v___x_924_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10));
v___x_925_ = lean_string_append(v___x_923_, v___x_924_);
v___y_885_ = v___y_906_;
v___y_886_ = v___y_905_;
v___y_887_ = v___y_907_;
v___y_888_ = v___y_908_;
v___y_889_ = v___y_916_;
v___y_890_ = v___y_909_;
v_port_891_ = v_port_911_;
v___y_892_ = v___y_912_;
v___y_893_ = v___y_913_;
v___y_894_ = v___y_915_;
v___y_895_ = v___y_914_;
v___y_896_ = v___x_925_;
goto v___jp_884_;
}
}
}
v___jp_926_:
{
lean_object* v_data_928_; lean_object* v_size_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v_data_928_ = lean_ctor_get(v_buffer_715_, 0);
lean_inc_ref(v_data_928_);
v_size_929_ = lean_ctor_get(v_buffer_715_, 1);
lean_inc(v_size_929_);
lean_dec_ref(v_buffer_715_);
v___x_930_ = lean_string_to_utf8(v___y_927_);
lean_inc_ref(v___x_930_);
v___x_931_ = lean_array_push(v_data_928_, v___x_930_);
v___x_932_ = lean_byte_array_size(v___x_930_);
lean_dec_ref(v___x_930_);
v___x_933_ = lean_nat_add(v_size_929_, v___x_932_);
lean_dec(v_size_929_);
v___x_934_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23));
v___x_935_ = lean_array_push(v___x_931_, v___x_934_);
v___x_936_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24);
v___x_937_ = lean_nat_add(v___x_933_, v___x_936_);
lean_dec(v___x_933_);
switch(lean_obj_tag(v_uri_719_))
{
case 0:
{
lean_object* v_path_938_; lean_object* v_query_939_; lean_object* v_segments_940_; uint8_t v_absolute_941_; lean_object* v___x_942_; lean_object* v___x_943_; size_t v_sz_944_; size_t v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v_result_948_; 
v_path_938_ = lean_ctor_get(v_uri_719_, 0);
lean_inc_ref(v_path_938_);
v_query_939_ = lean_ctor_get(v_uri_719_, 1);
lean_inc(v_query_939_);
lean_dec_ref_known(v_uri_719_, 2);
v_segments_940_ = lean_ctor_get(v_path_938_, 0);
lean_inc_ref(v_segments_940_);
v_absolute_941_ = lean_ctor_get_uint8(v_path_938_, sizeof(void*)*1);
lean_dec_ref(v_path_938_);
v___x_942_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12));
v___x_943_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22));
v_sz_944_ = lean_array_size(v_segments_940_);
v___x_945_ = ((size_t)0ULL);
v___x_946_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_943_, v___f_721_, v_sz_944_, v___x_945_, v_segments_940_);
v___x_947_ = lean_array_to_list(v___x_946_);
v_result_948_ = l_String_intercalate(v___x_942_, v___x_947_);
if (v_absolute_941_ == 0)
{
v___y_840_ = v___x_937_;
v___y_841_ = v___x_936_;
v___y_842_ = v_query_939_;
v___y_843_ = v___x_935_;
v___y_844_ = v___x_934_;
v___y_845_ = v_result_948_;
goto v___jp_839_;
}
else
{
lean_object* v___x_949_; 
v___x_949_ = lean_string_append(v___x_942_, v_result_948_);
lean_dec_ref(v_result_948_);
v___y_840_ = v___x_937_;
v___y_841_ = v___x_936_;
v___y_842_ = v_query_939_;
v___y_843_ = v___x_935_;
v___y_844_ = v___x_934_;
v___y_845_ = v___x_949_;
goto v___jp_839_;
}
}
case 1:
{
lean_object* v_uri_950_; lean_object* v_authority_951_; 
v_uri_950_ = lean_ctor_get(v_uri_719_, 0);
lean_inc_ref(v_uri_950_);
lean_dec_ref_known(v_uri_719_, 1);
v_authority_951_ = lean_ctor_get(v_uri_950_, 1);
if (lean_obj_tag(v_authority_951_) == 0)
{
lean_object* v_scheme_952_; lean_object* v_path_953_; lean_object* v_query_954_; lean_object* v_fragment_955_; lean_object* v___x_956_; 
v_scheme_952_ = lean_ctor_get(v_uri_950_, 0);
lean_inc_ref(v_scheme_952_);
v_path_953_ = lean_ctor_get(v_uri_950_, 2);
lean_inc_ref(v_path_953_);
v_query_954_ = lean_ctor_get(v_uri_950_, 3);
lean_inc(v_query_954_);
v_fragment_955_ = lean_ctor_get(v_uri_950_, 4);
lean_inc(v_fragment_955_);
lean_dec_ref(v_uri_950_);
v___x_956_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_849_ = v_query_954_;
v___y_850_ = v_fragment_955_;
v___y_851_ = v___x_937_;
v___y_852_ = v___x_936_;
v___y_853_ = v_scheme_952_;
v___y_854_ = v___x_935_;
v___y_855_ = v_path_953_;
v___y_856_ = v___x_934_;
v___y_857_ = v___x_956_;
goto v___jp_848_;
}
else
{
lean_object* v_val_957_; lean_object* v_scheme_958_; lean_object* v_path_959_; lean_object* v_query_960_; lean_object* v_fragment_961_; lean_object* v_userInfo_962_; lean_object* v_host_963_; lean_object* v_port_964_; lean_object* v___x_965_; 
v_val_957_ = lean_ctor_get(v_authority_951_, 0);
lean_inc(v_val_957_);
v_scheme_958_ = lean_ctor_get(v_uri_950_, 0);
lean_inc_ref(v_scheme_958_);
v_path_959_ = lean_ctor_get(v_uri_950_, 2);
lean_inc_ref(v_path_959_);
v_query_960_ = lean_ctor_get(v_uri_950_, 3);
lean_inc(v_query_960_);
v_fragment_961_ = lean_ctor_get(v_uri_950_, 4);
lean_inc(v_fragment_961_);
lean_dec_ref(v_uri_950_);
v_userInfo_962_ = lean_ctor_get(v_val_957_, 0);
lean_inc(v_userInfo_962_);
v_host_963_ = lean_ctor_get(v_val_957_, 1);
lean_inc_ref(v_host_963_);
v_port_964_ = lean_ctor_get(v_val_957_, 2);
lean_inc(v_port_964_);
lean_dec(v_val_957_);
v___x_965_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25));
if (lean_obj_tag(v_userInfo_962_) == 0)
{
lean_object* v___x_966_; 
v___x_966_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_905_ = v_fragment_961_;
v___y_906_ = v_query_960_;
v___y_907_ = v___x_965_;
v___y_908_ = v___x_937_;
v___y_909_ = v___x_936_;
v_host_910_ = v_host_963_;
v_port_911_ = v_port_964_;
v___y_912_ = v_scheme_958_;
v___y_913_ = v___x_935_;
v___y_914_ = v___x_934_;
v___y_915_ = v_path_959_;
v___y_916_ = v___x_966_;
goto v___jp_904_;
}
else
{
lean_object* v_val_967_; lean_object* v_password_968_; 
v_val_967_ = lean_ctor_get(v_userInfo_962_, 0);
lean_inc(v_val_967_);
lean_dec_ref_known(v_userInfo_962_, 1);
v_password_968_ = lean_ctor_get(v_val_967_, 1);
if (lean_obj_tag(v_password_968_) == 0)
{
lean_object* v_username_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v_username_969_ = lean_ctor_get(v_val_967_, 0);
lean_inc_ref(v_username_969_);
lean_dec(v_val_967_);
v___x_970_ = lean_string_from_utf8_unchecked(v_username_969_);
v___x_971_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26));
v___x_972_ = lean_string_append(v___x_970_, v___x_971_);
v___y_905_ = v_fragment_961_;
v___y_906_ = v_query_960_;
v___y_907_ = v___x_965_;
v___y_908_ = v___x_937_;
v___y_909_ = v___x_936_;
v_host_910_ = v_host_963_;
v_port_911_ = v_port_964_;
v___y_912_ = v_scheme_958_;
v___y_913_ = v___x_935_;
v___y_914_ = v___x_934_;
v___y_915_ = v_path_959_;
v___y_916_ = v___x_972_;
goto v___jp_904_;
}
else
{
lean_object* v_username_973_; lean_object* v_val_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
lean_inc_ref(v_password_968_);
v_username_973_ = lean_ctor_get(v_val_967_, 0);
lean_inc_ref(v_username_973_);
lean_dec(v_val_967_);
v_val_974_ = lean_ctor_get(v_password_968_, 0);
lean_inc(v_val_974_);
lean_dec_ref_known(v_password_968_, 1);
v___x_975_ = lean_string_from_utf8_unchecked(v_username_973_);
v___x_976_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_977_ = lean_string_append(v___x_975_, v___x_976_);
v___x_978_ = lean_string_from_utf8_unchecked(v_val_974_);
v___x_979_ = lean_string_append(v___x_977_, v___x_978_);
lean_dec_ref(v___x_978_);
v___x_980_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26));
v___x_981_ = lean_string_append(v___x_979_, v___x_980_);
v___y_905_ = v_fragment_961_;
v___y_906_ = v_query_960_;
v___y_907_ = v___x_965_;
v___y_908_ = v___x_937_;
v___y_909_ = v___x_936_;
v_host_910_ = v_host_963_;
v_port_911_ = v_port_964_;
v___y_912_ = v_scheme_958_;
v___y_913_ = v___x_935_;
v___y_914_ = v___x_934_;
v___y_915_ = v_path_959_;
v___y_916_ = v___x_981_;
goto v___jp_904_;
}
}
}
}
case 2:
{
lean_object* v_authority_982_; lean_object* v_userInfo_983_; 
v_authority_982_ = lean_ctor_get(v_uri_719_, 0);
lean_inc_ref(v_authority_982_);
lean_dec_ref_known(v_uri_719_, 1);
v_userInfo_983_ = lean_ctor_get(v_authority_982_, 0);
if (lean_obj_tag(v_userInfo_983_) == 0)
{
lean_object* v_host_984_; lean_object* v_port_985_; lean_object* v___x_986_; 
v_host_984_ = lean_ctor_get(v_authority_982_, 1);
lean_inc_ref(v_host_984_);
v_port_985_ = lean_ctor_get(v_authority_982_, 2);
lean_inc(v_port_985_);
lean_dec_ref(v_authority_982_);
v___x_986_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_790_ = v___x_937_;
v___y_791_ = v___x_936_;
v___y_792_ = v___x_935_;
v_host_793_ = v_host_984_;
v_port_794_ = v_port_985_;
v___y_795_ = v___x_934_;
v___y_796_ = v___x_986_;
goto v___jp_789_;
}
else
{
lean_object* v_val_987_; lean_object* v_password_988_; 
v_val_987_ = lean_ctor_get(v_userInfo_983_, 0);
lean_inc(v_val_987_);
v_password_988_ = lean_ctor_get(v_val_987_, 1);
if (lean_obj_tag(v_password_988_) == 0)
{
lean_object* v_host_989_; lean_object* v_port_990_; lean_object* v_username_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v_host_989_ = lean_ctor_get(v_authority_982_, 1);
lean_inc_ref(v_host_989_);
v_port_990_ = lean_ctor_get(v_authority_982_, 2);
lean_inc(v_port_990_);
lean_dec_ref(v_authority_982_);
v_username_991_ = lean_ctor_get(v_val_987_, 0);
lean_inc_ref(v_username_991_);
lean_dec(v_val_987_);
v___x_992_ = lean_string_from_utf8_unchecked(v_username_991_);
v___x_993_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26));
v___x_994_ = lean_string_append(v___x_992_, v___x_993_);
v___y_790_ = v___x_937_;
v___y_791_ = v___x_936_;
v___y_792_ = v___x_935_;
v_host_793_ = v_host_989_;
v_port_794_ = v_port_990_;
v___y_795_ = v___x_934_;
v___y_796_ = v___x_994_;
goto v___jp_789_;
}
else
{
lean_object* v_host_995_; lean_object* v_port_996_; lean_object* v_username_997_; lean_object* v_val_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
lean_inc_ref(v_password_988_);
v_host_995_ = lean_ctor_get(v_authority_982_, 1);
lean_inc_ref(v_host_995_);
v_port_996_ = lean_ctor_get(v_authority_982_, 2);
lean_inc(v_port_996_);
lean_dec_ref(v_authority_982_);
v_username_997_ = lean_ctor_get(v_val_987_, 0);
lean_inc_ref(v_username_997_);
lean_dec(v_val_987_);
v_val_998_ = lean_ctor_get(v_password_988_, 0);
lean_inc(v_val_998_);
lean_dec_ref_known(v_password_988_, 1);
v___x_999_ = lean_string_from_utf8_unchecked(v_username_997_);
v___x_1000_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_1001_ = lean_string_append(v___x_999_, v___x_1000_);
v___x_1002_ = lean_string_from_utf8_unchecked(v_val_998_);
v___x_1003_ = lean_string_append(v___x_1001_, v___x_1002_);
lean_dec_ref(v___x_1002_);
v___x_1004_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26));
v___x_1005_ = lean_string_append(v___x_1003_, v___x_1004_);
v___y_790_ = v___x_937_;
v___y_791_ = v___x_936_;
v___y_792_ = v___x_935_;
v_host_793_ = v_host_995_;
v_port_794_ = v_port_996_;
v___y_795_ = v___x_934_;
v___y_796_ = v___x_1005_;
goto v___jp_789_;
}
}
}
default: 
{
lean_object* v___x_1006_; 
v___x_1006_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27));
v___y_749_ = v___x_937_;
v___y_750_ = v___x_936_;
v___y_751_ = v___x_935_;
v___y_752_ = v___x_934_;
v___y_753_ = v___x_1006_;
goto v___jp_748_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(lean_object* v_buffer_1047_, lean_object* v_r_1048_){
_start:
{
lean_object* v_status_1049_; uint8_t v_version_1050_; lean_object* v_headers_1051_; lean_object* v___f_1052_; lean_object* v___y_1054_; 
v_status_1049_ = lean_ctor_get(v_r_1048_, 0);
v_version_1050_ = lean_ctor_get_uint8(v_r_1048_, sizeof(void*)*2);
v_headers_1051_ = lean_ctor_get(v_r_1048_, 1);
v___f_1052_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1));
switch(v_version_1050_)
{
case 0:
{
lean_object* v___x_1104_; 
v___x_1104_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4));
v___y_1054_ = v___x_1104_;
goto v___jp_1053_;
}
case 1:
{
lean_object* v___x_1105_; 
v___x_1105_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5));
v___y_1054_ = v___x_1105_;
goto v___jp_1053_;
}
case 2:
{
lean_object* v___x_1106_; 
v___x_1106_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6));
v___y_1054_ = v___x_1106_;
goto v___jp_1053_;
}
default: 
{
lean_object* v___x_1107_; 
v___x_1107_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7));
v___y_1054_ = v___x_1107_;
goto v___jp_1053_;
}
}
v___jp_1053_:
{
lean_object* v_data_1055_; lean_object* v_size_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1103_; 
v_data_1055_ = lean_ctor_get(v_buffer_1047_, 0);
v_size_1056_ = lean_ctor_get(v_buffer_1047_, 1);
v_isSharedCheck_1103_ = !lean_is_exclusive(v_buffer_1047_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1058_ = v_buffer_1047_;
v_isShared_1059_ = v_isSharedCheck_1103_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_size_1056_);
lean_inc(v_data_1055_);
lean_dec(v_buffer_1047_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1103_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; uint16_t v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v_buffer_1089_; 
v___x_1060_ = lean_string_to_utf8(v___y_1054_);
lean_inc_ref(v___x_1060_);
v___x_1061_ = lean_array_push(v_data_1055_, v___x_1060_);
v___x_1062_ = lean_byte_array_size(v___x_1060_);
lean_dec_ref(v___x_1060_);
v___x_1063_ = lean_nat_add(v_size_1056_, v___x_1062_);
lean_dec(v_size_1056_);
v___x_1064_ = lean_unsigned_to_nat(1u);
v___x_1065_ = lean_mk_empty_array_with_capacity(v___x_1064_);
lean_dec_ref(v___x_1065_);
v___x_1066_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23));
v___x_1067_ = lean_array_push(v___x_1061_, v___x_1066_);
v___x_1068_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24);
v___x_1069_ = lean_nat_add(v___x_1063_, v___x_1068_);
lean_dec(v___x_1063_);
v___x_1070_ = l_Std_Http_Status_toCode(v_status_1049_);
v___x_1071_ = lean_uint16_to_nat(v___x_1070_);
v___x_1072_ = l_Nat_reprFast(v___x_1071_);
v___x_1073_ = lean_string_to_utf8(v___x_1072_);
lean_dec_ref(v___x_1072_);
lean_inc_ref(v___x_1073_);
v___x_1074_ = lean_array_push(v___x_1067_, v___x_1073_);
v___x_1075_ = lean_byte_array_size(v___x_1073_);
lean_dec_ref(v___x_1073_);
v___x_1076_ = lean_nat_add(v___x_1069_, v___x_1075_);
lean_dec(v___x_1069_);
v___x_1077_ = lean_array_push(v___x_1074_, v___x_1066_);
v___x_1078_ = lean_nat_add(v___x_1076_, v___x_1068_);
lean_dec(v___x_1076_);
v___x_1079_ = l_Std_Http_Status_reasonPhrase(v_status_1049_);
v___x_1080_ = lean_string_to_utf8(v___x_1079_);
lean_dec_ref(v___x_1079_);
lean_inc_ref(v___x_1080_);
v___x_1081_ = lean_array_push(v___x_1077_, v___x_1080_);
v___x_1082_ = lean_byte_array_size(v___x_1080_);
lean_dec_ref(v___x_1080_);
v___x_1083_ = lean_nat_add(v___x_1078_, v___x_1082_);
lean_dec(v___x_1078_);
v___x_1084_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_1085_ = lean_array_push(v___x_1081_, v___x_1084_);
v___x_1086_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3);
v___x_1087_ = lean_nat_add(v___x_1083_, v___x_1086_);
lean_dec(v___x_1083_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 1, v___x_1087_);
lean_ctor_set(v___x_1058_, 0, v___x_1085_);
v_buffer_1089_ = v___x_1058_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v___x_1087_);
v_buffer_1089_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
lean_object* v_buffer_1090_; lean_object* v_data_1091_; lean_object* v_size_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1101_; 
v_buffer_1090_ = l_Std_Http_Headers_fold___redArg(v_headers_1051_, v_buffer_1089_, v___f_1052_);
v_data_1091_ = lean_ctor_get(v_buffer_1090_, 0);
v_size_1092_ = lean_ctor_get(v_buffer_1090_, 1);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_buffer_1090_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1094_ = v_buffer_1090_;
v_isShared_1095_ = v_isSharedCheck_1101_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_size_1092_);
lean_inc(v_data_1091_);
lean_dec(v_buffer_1090_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1101_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1096_ = lean_array_push(v_data_1091_, v___x_1084_);
v___x_1097_ = lean_nat_add(v_size_1092_, v___x_1086_);
lean_dec(v_size_1092_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 1, v___x_1097_);
lean_ctor_set(v___x_1094_, 0, v___x_1096_);
v___x_1099_ = v___x_1094_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___boxed(lean_object* v_buffer_1108_, lean_object* v_r_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(v_buffer_1108_, v_r_1109_);
lean_dec_ref(v_r_1109_);
return v_res_1110_;
}
}
lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head(uint8_t v_dir_1113_){
_start:
{
if (v_dir_1113_ == 0)
{
lean_object* v___x_1114_; 
v___x_1114_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___closed__0));
return v___x_1114_;
}
else
{
lean_object* v___x_1115_; 
v___x_1115_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___closed__1));
return v___x_1115_;
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_instEncodeV11Head_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_1113_ = stack[0].m_num;
lean_object* v_res_1116_;
v_res_1116_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v_dir_1113_);
stack->m_obj
 = v_res_1116_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___boxed(lean_object* v_dir_1117_){
_start:
{
uint8_t v_dir_boxed_1118_; lean_object* v_res_1119_; 
v_dir_boxed_1118_ = lean_unbox(v_dir_1117_);
v_res_1119_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v_dir_boxed_1118_);
return v_res_1119_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0(void){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; uint8_t v___x_1123_; lean_object* v___x_1124_; 
v___x_1120_ = l_Std_Http_Headers_empty;
v___x_1121_ = lean_box(3);
v___x_1122_ = 1;
v___x_1123_ = 8;
v___x_1124_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1124_, 0, v___x_1121_);
lean_ctor_set(v___x_1124_, 1, v___x_1120_);
lean_ctor_set_uint8(v___x_1124_, sizeof(void*)*2, v___x_1123_);
lean_ctor_set_uint8(v___x_1124_, sizeof(void*)*2 + 1, v___x_1122_);
return v___x_1124_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1(void){
_start:
{
lean_object* v___x_1125_; uint8_t v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1125_ = l_Std_Http_Headers_empty;
v___x_1126_ = 1;
v___x_1127_ = lean_box(4);
v___x_1128_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
lean_ctor_set(v___x_1128_, 1, v___x_1125_);
lean_ctor_set_uint8(v___x_1128_, sizeof(void*)*2, v___x_1126_);
return v___x_1128_;
}
}
lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead(uint8_t v_dir_1129_){
_start:
{
if (v_dir_1129_ == 0)
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0, &l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0_once, _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0);
return v___x_1130_;
}
else
{
lean_object* v___x_1131_; 
v___x_1131_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1, &l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1_once, _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1);
return v___x_1131_;
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_instEmptyCollectionHead_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_1129_ = stack[0].m_num;
lean_object* v_res_1132_;
v_res_1132_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v_dir_1129_);
stack->m_obj
 = v_res_1132_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead___boxed(lean_object* v_dir_1133_){
_start:
{
uint8_t v_dir_boxed_1134_; lean_object* v_res_1135_; 
v_dir_boxed_1134_ = lean_unbox(v_dir_1133_);
v_res_1135_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v_dir_boxed_1134_);
return v_res_1135_;
}
}
lean_object* runtime_initialize_Init_Data_Array(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Protocol_H1_Message(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed__const__1 = _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed__const__1();
lean_mark_persistent(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Protocol_H1_Message(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array(uint8_t builtin);
lean_object* initialize_Std_Http_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Protocol_H1_Message(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Protocol_H1_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Protocol_H1_Message(builtin);
}
#ifdef __cplusplus
}
#endif
