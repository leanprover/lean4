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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Std_Http_Protocol_H1_Direction_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Std_Http_Protocol_H1_Direction_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Std_Http_Protocol_H1_Direction_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_receiving_elim___redArg(lean_object* v_receiving_22_){
_start:
{
lean_inc(v_receiving_22_);
return v_receiving_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_receiving_elim___redArg___boxed(lean_object* v_receiving_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_Http_Protocol_H1_Direction_receiving_elim___redArg(v_receiving_23_);
lean_dec(v_receiving_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_receiving_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_receiving_28_){
_start:
{
lean_inc(v_receiving_28_);
return v_receiving_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_receiving_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_receiving_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Std_Http_Protocol_H1_Direction_receiving_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_receiving_32_);
lean_dec(v_receiving_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_sending_elim___redArg(lean_object* v_sending_35_){
_start:
{
lean_inc(v_sending_35_);
return v_sending_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_sending_elim___redArg___boxed(lean_object* v_sending_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Std_Http_Protocol_H1_Direction_sending_elim___redArg(v_sending_36_);
lean_dec(v_sending_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_sending_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_sending_41_){
_start:
{
lean_inc(v_sending_41_);
return v_sending_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_sending_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_sending_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Std_Http_Protocol_H1_Direction_sending_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_sending_45_);
lean_dec(v_sending_45_);
return v_res_47_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_instBEqDirection_beq(uint8_t v_x_48_, uint8_t v_y_49_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; uint8_t v___x_54_; 
v___x_50_ = lean_box(v_x_48_);
v___x_51_ = lean_obj_tag_nat(v___x_50_);
lean_dec(v___x_50_);
v___x_52_ = lean_box(v_y_49_);
v___x_53_ = lean_obj_tag_nat(v___x_52_);
lean_dec(v___x_52_);
v___x_54_ = lean_nat_dec_eq(v___x_51_, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instBEqDirection_beq___boxed(lean_object* v_x_55_, lean_object* v_y_56_){
_start:
{
uint8_t v_x_24__boxed_57_; uint8_t v_y_25__boxed_58_; uint8_t v_res_59_; lean_object* v_r_60_; 
v_x_24__boxed_57_ = lean_unbox(v_x_55_);
v_y_25__boxed_58_ = lean_unbox(v_y_56_);
v_res_59_ = l_Std_Http_Protocol_H1_instBEqDirection_beq(v_x_24__boxed_57_, v_y_25__boxed_58_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Direction_swap(uint8_t v_x_63_){
_start:
{
if (v_x_63_ == 0)
{
uint8_t v___x_64_; 
v___x_64_ = 1;
return v___x_64_;
}
else
{
uint8_t v___x_65_; 
v___x_65_ = 0;
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_swap___boxed(lean_object* v_x_66_){
_start:
{
uint8_t v_x_18__boxed_67_; uint8_t v_res_68_; lean_object* v_r_69_; 
v_x_18__boxed_67_ = lean_unbox(v_x_66_);
v_res_68_ = l_Std_Http_Protocol_H1_Direction_swap(v_x_18__boxed_67_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_headers(uint8_t v_dir_70_, lean_object* v_m_71_){
_start:
{
lean_object* v_headers_72_; 
v_headers_72_ = lean_ctor_get(v_m_71_, 1);
lean_inc_ref(v_headers_72_);
return v_headers_72_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_headers___boxed(lean_object* v_dir_73_, lean_object* v_m_74_){
_start:
{
uint8_t v_dir_boxed_75_; lean_object* v_res_76_; 
v_dir_boxed_75_ = lean_unbox(v_dir_73_);
v_res_76_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_boxed_75_, v_m_74_);
lean_dec(v_m_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_setHeaders(uint8_t v_dir_77_, lean_object* v_m_78_, lean_object* v_headers_79_){
_start:
{
if (v_dir_77_ == 0)
{
uint8_t v_method_80_; uint8_t v_version_81_; lean_object* v_uri_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_89_; 
v_method_80_ = lean_ctor_get_uint8(v_m_78_, sizeof(void*)*2);
v_version_81_ = lean_ctor_get_uint8(v_m_78_, sizeof(void*)*2 + 1);
v_uri_82_ = lean_ctor_get(v_m_78_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v_m_78_);
if (v_isSharedCheck_89_ == 0)
{
lean_object* v_unused_90_; 
v_unused_90_ = lean_ctor_get(v_m_78_, 1);
lean_dec(v_unused_90_);
v___x_84_ = v_m_78_;
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_uri_82_);
lean_dec(v_m_78_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_87_; 
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 1, v_headers_79_);
v___x_87_ = v___x_84_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_uri_82_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v_headers_79_);
lean_ctor_set_uint8(v_reuseFailAlloc_88_, sizeof(void*)*2, v_method_80_);
lean_ctor_set_uint8(v_reuseFailAlloc_88_, sizeof(void*)*2 + 1, v_version_81_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
else
{
lean_object* v_status_91_; uint8_t v_version_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
v_status_91_ = lean_ctor_get(v_m_78_, 0);
v_version_92_ = lean_ctor_get_uint8(v_m_78_, sizeof(void*)*2);
v_isSharedCheck_99_ = !lean_is_exclusive(v_m_78_);
if (v_isSharedCheck_99_ == 0)
{
lean_object* v_unused_100_; 
v_unused_100_ = lean_ctor_get(v_m_78_, 1);
lean_dec(v_unused_100_);
v___x_94_ = v_m_78_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_status_91_);
lean_dec(v_m_78_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 1, v_headers_79_);
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_status_91_);
lean_ctor_set(v_reuseFailAlloc_98_, 1, v_headers_79_);
lean_ctor_set_uint8(v_reuseFailAlloc_98_, sizeof(void*)*2, v_version_92_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_setHeaders___boxed(lean_object* v_dir_101_, lean_object* v_m_102_, lean_object* v_headers_103_){
_start:
{
uint8_t v_dir_boxed_104_; lean_object* v_res_105_; 
v_dir_boxed_104_ = lean_unbox(v_dir_101_);
v_res_105_ = l_Std_Http_Protocol_H1_Message_Head_setHeaders(v_dir_boxed_104_, v_m_102_, v_headers_103_);
return v_res_105_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Message_Head_version(uint8_t v_dir_106_, lean_object* v_m_107_){
_start:
{
if (v_dir_106_ == 0)
{
uint8_t v_version_108_; 
v_version_108_ = lean_ctor_get_uint8(v_m_107_, sizeof(void*)*2 + 1);
return v_version_108_;
}
else
{
uint8_t v_version_109_; 
v_version_109_ = lean_ctor_get_uint8(v_m_107_, sizeof(void*)*2);
return v_version_109_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_version___boxed(lean_object* v_dir_110_, lean_object* v_m_111_){
_start:
{
uint8_t v_dir_boxed_112_; uint8_t v_res_113_; lean_object* v_r_114_; 
v_dir_boxed_112_ = lean_unbox(v_dir_110_);
v_res_113_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_boxed_112_, v_m_111_);
lean_dec(v_m_111_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg(lean_object* v___x_115_, lean_object* v___x_116_, size_t v_sz_117_, size_t v_i_118_, lean_object* v_bs_119_){
_start:
{
uint8_t v___x_120_; 
v___x_120_ = lean_usize_dec_lt(v_i_118_, v_sz_117_);
if (v___x_120_ == 0)
{
return v_bs_119_;
}
else
{
lean_object* v_entries_121_; lean_object* v___x_122_; lean_object* v_bs_x27_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v_snd_127_; size_t v___x_128_; size_t v___x_129_; lean_object* v___x_130_; 
v_entries_121_ = lean_ctor_get(v___x_115_, 0);
v___x_122_ = lean_unsigned_to_nat(0u);
v_bs_x27_123_ = lean_array_uset(v_bs_119_, v_i_118_, v___x_122_);
v___x_124_ = lean_usize_to_nat(v_i_118_);
v___x_125_ = lean_array_fget_borrowed(v___x_116_, v___x_124_);
lean_dec(v___x_124_);
v___x_126_ = lean_array_fget_borrowed(v_entries_121_, v___x_125_);
v_snd_127_ = lean_ctor_get(v___x_126_, 1);
v___x_128_ = ((size_t)1ULL);
v___x_129_ = lean_usize_add(v_i_118_, v___x_128_);
lean_inc(v_snd_127_);
v___x_130_ = lean_array_uset(v_bs_x27_123_, v_i_118_, v_snd_127_);
v_i_118_ = v___x_129_;
v_bs_119_ = v___x_130_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg___boxed(lean_object* v___x_132_, lean_object* v___x_133_, lean_object* v_sz_134_, lean_object* v_i_135_, lean_object* v_bs_136_){
_start:
{
size_t v_sz_boxed_137_; size_t v_i_boxed_138_; lean_object* v_res_139_; 
v_sz_boxed_137_ = lean_unbox_usize(v_sz_134_);
lean_dec(v_sz_134_);
v_i_boxed_138_ = lean_unbox_usize(v_i_135_);
lean_dec(v_i_135_);
v_res_139_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg(v___x_132_, v___x_133_, v_sz_boxed_137_, v_i_boxed_138_, v_bs_136_);
lean_dec_ref(v___x_133_);
lean_dec_ref(v___x_132_);
return v_res_139_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(lean_object* v_a_140_, lean_object* v_x_141_){
_start:
{
if (lean_obj_tag(v_x_141_) == 0)
{
uint8_t v___x_142_; 
v___x_142_ = 0;
return v___x_142_;
}
else
{
lean_object* v_key_143_; lean_object* v_tail_144_; uint8_t v___x_145_; 
v_key_143_ = lean_ctor_get(v_x_141_, 0);
v_tail_144_ = lean_ctor_get(v_x_141_, 2);
v___x_145_ = lean_string_dec_eq(v_key_143_, v_a_140_);
if (v___x_145_ == 0)
{
v_x_141_ = v_tail_144_;
goto _start;
}
else
{
return v___x_145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg___boxed(lean_object* v_a_147_, lean_object* v_x_148_){
_start:
{
uint8_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_a_147_, v_x_148_);
lean_dec(v_x_148_);
lean_dec_ref(v_a_147_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(lean_object* v_m_151_, lean_object* v_a_152_){
_start:
{
lean_object* v_buckets_153_; lean_object* v___x_154_; uint64_t v___x_155_; uint64_t v___x_156_; uint64_t v___x_157_; uint64_t v_fold_158_; uint64_t v___x_159_; uint64_t v___x_160_; uint64_t v___x_161_; size_t v___x_162_; size_t v___x_163_; size_t v___x_164_; size_t v___x_165_; size_t v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v_buckets_153_ = lean_ctor_get(v_m_151_, 1);
v___x_154_ = lean_array_get_size(v_buckets_153_);
v___x_155_ = lean_string_hash(v_a_152_);
v___x_156_ = 32ULL;
v___x_157_ = lean_uint64_shift_right(v___x_155_, v___x_156_);
v_fold_158_ = lean_uint64_xor(v___x_155_, v___x_157_);
v___x_159_ = 16ULL;
v___x_160_ = lean_uint64_shift_right(v_fold_158_, v___x_159_);
v___x_161_ = lean_uint64_xor(v_fold_158_, v___x_160_);
v___x_162_ = lean_uint64_to_usize(v___x_161_);
v___x_163_ = lean_usize_of_nat(v___x_154_);
v___x_164_ = ((size_t)1ULL);
v___x_165_ = lean_usize_sub(v___x_163_, v___x_164_);
v___x_166_ = lean_usize_land(v___x_162_, v___x_165_);
v___x_167_ = lean_array_uget_borrowed(v_buckets_153_, v___x_166_);
v___x_168_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_a_152_, v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg___boxed(lean_object* v_m_169_, lean_object* v_a_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_m_169_, v_a_170_);
lean_dec_ref(v_a_170_);
lean_dec_ref(v_m_169_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2___redArg(lean_object* v_a_173_, lean_object* v_x_174_){
_start:
{
lean_object* v_key_175_; lean_object* v_value_176_; lean_object* v_tail_177_; uint8_t v___x_178_; 
v_key_175_ = lean_ctor_get(v_x_174_, 0);
v_value_176_ = lean_ctor_get(v_x_174_, 1);
v_tail_177_ = lean_ctor_get(v_x_174_, 2);
v___x_178_ = lean_string_dec_eq(v_key_175_, v_a_173_);
if (v___x_178_ == 0)
{
v_x_174_ = v_tail_177_;
goto _start;
}
else
{
lean_inc(v_value_176_);
return v_value_176_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2___redArg___boxed(lean_object* v_a_180_, lean_object* v_x_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2___redArg(v_a_180_, v_x_181_);
lean_dec(v_x_181_);
lean_dec_ref(v_a_180_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(lean_object* v_m_183_, lean_object* v_a_184_){
_start:
{
lean_object* v_buckets_185_; lean_object* v___x_186_; uint64_t v___x_187_; uint64_t v___x_188_; uint64_t v___x_189_; uint64_t v_fold_190_; uint64_t v___x_191_; uint64_t v___x_192_; uint64_t v___x_193_; size_t v___x_194_; size_t v___x_195_; size_t v___x_196_; size_t v___x_197_; size_t v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_buckets_185_ = lean_ctor_get(v_m_183_, 1);
v___x_186_ = lean_array_get_size(v_buckets_185_);
v___x_187_ = lean_string_hash(v_a_184_);
v___x_188_ = 32ULL;
v___x_189_ = lean_uint64_shift_right(v___x_187_, v___x_188_);
v_fold_190_ = lean_uint64_xor(v___x_187_, v___x_189_);
v___x_191_ = 16ULL;
v___x_192_ = lean_uint64_shift_right(v_fold_190_, v___x_191_);
v___x_193_ = lean_uint64_xor(v_fold_190_, v___x_192_);
v___x_194_ = lean_uint64_to_usize(v___x_193_);
v___x_195_ = lean_usize_of_nat(v___x_186_);
v___x_196_ = ((size_t)1ULL);
v___x_197_ = lean_usize_sub(v___x_195_, v___x_196_);
v___x_198_ = lean_usize_land(v___x_194_, v___x_197_);
v___x_199_ = lean_array_uget_borrowed(v_buckets_185_, v___x_198_);
v___x_200_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2___redArg(v_a_184_, v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg___boxed(lean_object* v_m_201_, lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v_m_201_, v_a_202_);
lean_dec_ref(v_a_202_);
lean_dec_ref(v_m_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize(uint8_t v_dir_210_, lean_object* v_message_211_, uint8_t v_allowEOFBody_212_){
_start:
{
lean_object* v___x_213_; lean_object* v___y_215_; lean_object* v_indexes_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_213_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_210_, v_message_211_);
v_indexes_266_ = lean_ctor_get(v___x_213_, 1);
v___x_267_ = l_Std_Http_Header_Name_contentLength;
v___x_268_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_266_, v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
v___x_269_ = lean_box(0);
v___y_215_ = v___x_269_;
goto v___jp_214_;
}
else
{
lean_object* v___x_270_; size_t v_sz_271_; size_t v___x_272_; lean_object* v_entries_273_; lean_object* v___x_274_; 
v___x_270_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v_indexes_266_, v___x_267_);
v_sz_271_ = lean_array_size(v___x_270_);
v___x_272_ = ((size_t)0ULL);
lean_inc(v___x_270_);
v_entries_273_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg(v___x_213_, v___x_270_, v_sz_271_, v___x_272_, v___x_270_);
lean_dec(v___x_270_);
v___x_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_274_, 0, v_entries_273_);
v___y_215_ = v___x_274_;
goto v___jp_214_;
}
v___jp_214_:
{
lean_object* v_indexes_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v_indexes_216_ = lean_ctor_get(v___x_213_, 1);
v___x_217_ = l_Std_Http_Header_Name_transferEncoding;
v___x_218_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_216_, v___x_217_);
if (v___x_218_ == 0)
{
lean_dec_ref(v___x_213_);
if (lean_obj_tag(v___y_215_) == 0)
{
if (v_allowEOFBody_212_ == 0)
{
lean_object* v___x_219_; 
v___x_219_ = lean_box(0);
return v___x_219_;
}
else
{
lean_object* v___x_220_; 
v___x_220_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1));
return v___x_220_;
}
}
else
{
lean_object* v_val_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_244_; 
v_val_221_ = lean_ctor_get(v___y_215_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___y_215_);
if (v_isSharedCheck_244_ == 0)
{
v___x_223_ = v___y_215_;
v_isShared_224_ = v_isSharedCheck_244_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_val_221_);
lean_dec(v___y_215_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_244_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_225_ = lean_array_get_size(v_val_221_);
v___x_226_ = lean_unsigned_to_nat(1u);
v___x_227_ = lean_nat_dec_eq(v___x_225_, v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; 
lean_del_object(v___x_223_);
lean_dec(v_val_221_);
v___x_228_ = lean_box(0);
return v___x_228_;
}
else
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = lean_array_fget(v_val_221_, v___x_229_);
lean_dec(v_val_221_);
v___x_231_ = l_Std_Http_Header_ContentLength_parse(v___x_230_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v___x_232_; 
lean_del_object(v___x_223_);
v___x_232_ = lean_box(0);
return v___x_232_;
}
else
{
lean_object* v_val_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_243_; 
v_val_233_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_243_ == 0)
{
v___x_235_ = v___x_231_;
v_isShared_236_ = v_isSharedCheck_243_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_val_233_);
lean_dec(v___x_231_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_243_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v_val_233_);
v___x_238_ = v___x_223_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_val_233_);
v___x_238_ = v_reuseFailAlloc_242_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_240_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v___x_238_);
v___x_240_ = v___x_235_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_238_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
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
lean_object* v___x_245_; size_t v_sz_246_; size_t v___x_247_; lean_object* v_entries_248_; lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_245_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v_indexes_216_, v___x_217_);
v_sz_246_ = lean_array_size(v___x_245_);
v___x_247_ = ((size_t)0ULL);
lean_inc(v___x_245_);
v_entries_248_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg(v___x_213_, v___x_245_, v_sz_246_, v___x_247_, v___x_245_);
lean_dec(v___x_245_);
lean_dec_ref(v___x_213_);
v___x_249_ = lean_array_get_size(v_entries_248_);
v___x_250_ = lean_unsigned_to_nat(1u);
v___x_251_ = lean_nat_dec_eq(v___x_249_, v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; 
lean_dec_ref(v_entries_248_);
lean_dec(v___y_215_);
v___x_252_ = lean_box(0);
return v___x_252_;
}
else
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v_te_255_; 
v___x_253_ = lean_unsigned_to_nat(0u);
v___x_254_ = lean_array_fget(v_entries_248_, v___x_253_);
lean_dec_ref(v_entries_248_);
v_te_255_ = l_Std_Http_Header_TransferEncoding_parse(v___x_254_);
if (lean_obj_tag(v_te_255_) == 0)
{
lean_object* v___x_256_; 
lean_dec(v___y_215_);
v___x_256_ = lean_box(0);
return v___x_256_;
}
else
{
lean_object* v_val_257_; uint8_t v___x_258_; 
v_val_257_ = lean_ctor_get(v_te_255_, 0);
lean_inc(v_val_257_);
lean_dec_ref_known(v_te_255_, 1);
v___x_258_ = l_Std_Http_Header_TransferEncoding_isChunked(v_val_257_);
lean_dec(v_val_257_);
if (v___x_258_ == 1)
{
if (lean_obj_tag(v___y_215_) == 0)
{
uint8_t v___x_259_; uint8_t v___x_260_; uint8_t v___x_261_; 
v___x_259_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_210_, v_message_211_);
v___x_260_ = 0;
v___x_261_ = l_Std_Http_instBEqVersion_beq(v___x_259_, v___x_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; 
v___x_262_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__2));
return v___x_262_;
}
else
{
lean_object* v___x_263_; 
v___x_263_ = lean_box(0);
return v___x_263_;
}
}
else
{
lean_object* v___x_264_; 
lean_dec(v___y_215_);
v___x_264_ = lean_box(0);
return v___x_264_;
}
}
else
{
lean_object* v___x_265_; 
lean_dec(v___y_215_);
v___x_265_ = lean_box(0);
return v___x_265_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize___boxed(lean_object* v_dir_275_, lean_object* v_message_276_, lean_object* v_allowEOFBody_277_){
_start:
{
uint8_t v_dir_boxed_278_; uint8_t v_allowEOFBody_boxed_279_; lean_object* v_res_280_; 
v_dir_boxed_278_ = lean_unbox(v_dir_275_);
v_allowEOFBody_boxed_279_ = lean_unbox(v_allowEOFBody_277_);
v_res_280_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v_dir_boxed_278_, v_message_276_, v_allowEOFBody_boxed_279_);
lean_dec(v_message_276_);
return v_res_280_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(lean_object* v_00_u03b2_281_, lean_object* v_m_282_, lean_object* v_a_283_){
_start:
{
uint8_t v___x_284_; 
v___x_284_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_m_282_, v_a_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___boxed(lean_object* v_00_u03b2_285_, lean_object* v_m_286_, lean_object* v_a_287_){
_start:
{
uint8_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(v_00_u03b2_285_, v_m_286_, v_a_287_);
lean_dec_ref(v_a_287_);
lean_dec_ref(v_m_286_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(lean_object* v_00_u03b2_290_, lean_object* v_m_291_, lean_object* v_a_292_, lean_object* v_hma_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v_m_291_, v_a_292_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___boxed(lean_object* v_00_u03b2_295_, lean_object* v_m_296_, lean_object* v_a_297_, lean_object* v_hma_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(v_00_u03b2_295_, v_m_296_, v_a_297_, v_hma_298_);
lean_dec_ref(v_a_297_);
lean_dec_ref(v_m_296_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2(lean_object* v___x_300_, lean_object* v___x_301_, lean_object* v_as_302_, size_t v_sz_303_, size_t v_i_304_, lean_object* v_bs_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg(v___x_300_, v___x_301_, v_sz_303_, v_i_304_, v_bs_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___boxed(lean_object* v___x_307_, lean_object* v___x_308_, lean_object* v_as_309_, lean_object* v_sz_310_, lean_object* v_i_311_, lean_object* v_bs_312_){
_start:
{
size_t v_sz_boxed_313_; size_t v_i_boxed_314_; lean_object* v_res_315_; 
v_sz_boxed_313_ = lean_unbox_usize(v_sz_310_);
lean_dec(v_sz_310_);
v_i_boxed_314_ = lean_unbox_usize(v_i_311_);
lean_dec(v_i_311_);
v_res_315_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2(v___x_307_, v___x_308_, v_as_309_, v_sz_boxed_313_, v_i_boxed_314_, v_bs_312_);
lean_dec_ref(v_as_309_);
lean_dec_ref(v___x_308_);
lean_dec_ref(v___x_307_);
return v_res_315_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0(lean_object* v_00_u03b2_316_, lean_object* v_a_317_, lean_object* v_x_318_){
_start:
{
uint8_t v___x_319_; 
v___x_319_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_a_317_, v_x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_320_, lean_object* v_a_321_, lean_object* v_x_322_){
_start:
{
uint8_t v_res_323_; lean_object* v_r_324_; 
v_res_323_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0(v_00_u03b2_320_, v_a_321_, v_x_322_);
lean_dec(v_x_322_);
lean_dec_ref(v_a_321_);
v_r_324_ = lean_box(v_res_323_);
return v_r_324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2(lean_object* v_00_u03b2_325_, lean_object* v_a_326_, lean_object* v_x_327_, lean_object* v_x_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2___redArg(v_a_326_, v_x_327_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2___boxed(lean_object* v_00_u03b2_330_, lean_object* v_a_331_, lean_object* v_x_332_, lean_object* v_x_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2(v_00_u03b2_330_, v_a_331_, v_x_332_, v_x_333_);
lean_dec(v_x_332_);
lean_dec_ref(v_a_331_);
return v_res_334_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(lean_object* v_as_336_, size_t v_i_337_, size_t v_stop_338_){
_start:
{
uint8_t v___x_339_; 
v___x_339_ = lean_usize_dec_eq(v_i_337_, v_stop_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_340_ = lean_array_uget_borrowed(v_as_336_, v_i_337_);
v___x_341_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___closed__0));
v___x_342_ = lean_string_dec_eq(v___x_340_, v___x_341_);
if (v___x_342_ == 0)
{
size_t v___x_343_; size_t v___x_344_; 
v___x_343_ = ((size_t)1ULL);
v___x_344_ = lean_usize_add(v_i_337_, v___x_343_);
v_i_337_ = v___x_344_;
goto _start;
}
else
{
return v___x_342_;
}
}
else
{
uint8_t v___x_346_; 
v___x_346_ = 0;
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___boxed(lean_object* v_as_347_, lean_object* v_i_348_, lean_object* v_stop_349_){
_start:
{
size_t v_i_boxed_350_; size_t v_stop_boxed_351_; uint8_t v_res_352_; lean_object* v_r_353_; 
v_i_boxed_350_ = lean_unbox_usize(v_i_348_);
lean_dec(v_i_348_);
v_stop_boxed_351_ = lean_unbox_usize(v_stop_349_);
lean_dec(v_stop_349_);
v_res_352_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(v_as_347_, v_i_boxed_350_, v_stop_boxed_351_);
lean_dec_ref(v_as_347_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(lean_object* v_as_355_, size_t v_i_356_, size_t v_stop_357_){
_start:
{
uint8_t v___x_358_; 
v___x_358_ = lean_usize_dec_eq(v_i_356_, v_stop_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_359_ = lean_array_uget_borrowed(v_as_355_, v_i_356_);
v___x_360_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___closed__0));
v___x_361_ = lean_string_dec_eq(v___x_359_, v___x_360_);
if (v___x_361_ == 0)
{
size_t v___x_362_; size_t v___x_363_; 
v___x_362_ = ((size_t)1ULL);
v___x_363_ = lean_usize_add(v_i_356_, v___x_362_);
v_i_356_ = v___x_363_;
goto _start;
}
else
{
return v___x_361_;
}
}
else
{
uint8_t v___x_365_; 
v___x_365_ = 0;
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___boxed(lean_object* v_as_366_, lean_object* v_i_367_, lean_object* v_stop_368_){
_start:
{
size_t v_i_boxed_369_; size_t v_stop_boxed_370_; uint8_t v_res_371_; lean_object* v_r_372_; 
v_i_boxed_369_ = lean_unbox_usize(v_i_367_);
lean_dec(v_i_367_);
v_stop_boxed_370_ = lean_unbox_usize(v_stop_368_);
lean_dec(v_stop_368_);
v_res_371_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(v_as_366_, v_i_boxed_369_, v_stop_boxed_370_);
lean_dec_ref(v_as_366_);
v_r_372_ = lean_box(v_res_371_);
return v_r_372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(lean_object* v_as_373_, size_t v_i_374_, size_t v_stop_375_, lean_object* v_b_376_){
_start:
{
lean_object* v___y_378_; uint8_t v___x_382_; 
v___x_382_ = lean_usize_dec_eq(v_i_374_, v_stop_375_);
if (v___x_382_ == 0)
{
if (lean_obj_tag(v_b_376_) == 0)
{
v___y_378_ = v_b_376_;
goto v___jp_377_;
}
else
{
lean_object* v_val_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_val_383_ = lean_ctor_get(v_b_376_, 0);
lean_inc(v_val_383_);
lean_dec_ref_known(v_b_376_, 1);
v___x_384_ = lean_array_uget_borrowed(v_as_373_, v_i_374_);
lean_inc(v___x_384_);
v___x_385_ = l_Std_Http_Header_Connection_parse(v___x_384_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v___x_386_; 
lean_dec(v_val_383_);
v___x_386_ = lean_box(0);
v___y_378_ = v___x_386_;
goto v___jp_377_;
}
else
{
lean_object* v_val_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_395_; 
v_val_387_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_395_ == 0)
{
v___x_389_ = v___x_385_;
v_isShared_390_ = v_isSharedCheck_395_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_val_387_);
lean_dec(v___x_385_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_395_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_391_ = l_Array_append___redArg(v_val_383_, v_val_387_);
lean_dec(v_val_387_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_391_);
v___x_393_ = v___x_389_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_391_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
v___y_378_ = v___x_393_;
goto v___jp_377_;
}
}
}
}
}
else
{
return v_b_376_;
}
v___jp_377_:
{
size_t v___x_379_; size_t v___x_380_; 
v___x_379_ = ((size_t)1ULL);
v___x_380_ = lean_usize_add(v_i_374_, v___x_379_);
v_i_374_ = v___x_380_;
v_b_376_ = v___y_378_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2___boxed(lean_object* v_as_396_, lean_object* v_i_397_, lean_object* v_stop_398_, lean_object* v_b_399_){
_start:
{
size_t v_i_boxed_400_; size_t v_stop_boxed_401_; lean_object* v_res_402_; 
v_i_boxed_400_ = lean_unbox_usize(v_i_397_);
lean_dec(v_i_397_);
v_stop_boxed_401_ = lean_unbox_usize(v_stop_398_);
lean_dec(v_stop_398_);
v_res_402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_as_396_, v_i_boxed_400_, v_stop_boxed_401_, v_b_399_);
lean_dec_ref(v_as_396_);
return v_res_402_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(uint8_t v_dir_407_, lean_object* v_message_408_){
_start:
{
lean_object* v_val_410_; lean_object* v___y_428_; lean_object* v___x_431_; lean_object* v_indexes_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_431_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_407_, v_message_408_);
v_indexes_432_ = lean_ctor_get(v___x_431_, 1);
v___x_433_ = l_Std_Http_Header_Name_connection;
v___x_434_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_432_, v___x_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; 
lean_dec_ref(v___x_431_);
v___x_435_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0));
v_val_410_ = v___x_435_;
goto v___jp_409_;
}
else
{
lean_object* v___x_436_; size_t v_sz_437_; size_t v___x_438_; lean_object* v_entries_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_436_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v_indexes_432_, v___x_433_);
v_sz_437_ = lean_array_size(v___x_436_);
v___x_438_ = ((size_t)0ULL);
lean_inc(v___x_436_);
v_entries_439_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg(v___x_431_, v___x_436_, v_sz_437_, v___x_438_, v___x_436_);
lean_dec(v___x_436_);
lean_dec_ref(v___x_431_);
v___x_440_ = lean_unsigned_to_nat(0u);
v___x_441_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0));
v___x_442_ = lean_array_get_size(v_entries_439_);
v___x_443_ = lean_nat_dec_lt(v___x_440_, v___x_442_);
if (v___x_443_ == 0)
{
lean_dec_ref(v_entries_439_);
v_val_410_ = v___x_441_;
goto v___jp_409_;
}
else
{
lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_444_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__1));
v___x_445_ = lean_nat_dec_le(v___x_442_, v___x_442_);
if (v___x_445_ == 0)
{
if (v___x_443_ == 0)
{
lean_dec_ref(v_entries_439_);
v_val_410_ = v___x_441_;
goto v___jp_409_;
}
else
{
size_t v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_usize_of_nat(v___x_442_);
v___x_447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_entries_439_, v___x_438_, v___x_446_, v___x_444_);
lean_dec_ref(v_entries_439_);
v___y_428_ = v___x_447_;
goto v___jp_427_;
}
}
else
{
size_t v___x_448_; lean_object* v___x_449_; 
v___x_448_ = lean_usize_of_nat(v___x_442_);
v___x_449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_entries_439_, v___x_438_, v___x_448_, v___x_444_);
lean_dec_ref(v_entries_439_);
v___y_428_ = v___x_449_;
goto v___jp_427_;
}
}
}
v___jp_409_:
{
uint8_t v___x_411_; uint8_t v___x_412_; uint8_t v___x_413_; 
v___x_411_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_407_, v_message_408_);
v___x_412_ = 1;
v___x_413_ = l_Std_Http_instBEqVersion_beq(v___x_411_, v___x_412_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = lean_array_get_size(v_val_410_);
v___x_416_ = lean_nat_dec_lt(v___x_414_, v___x_415_);
if (v___x_416_ == 0)
{
lean_dec_ref(v_val_410_);
return v___x_416_;
}
else
{
if (v___x_416_ == 0)
{
lean_dec_ref(v_val_410_);
return v___x_416_;
}
else
{
size_t v___x_417_; size_t v___x_418_; uint8_t v___x_419_; 
v___x_417_ = ((size_t)0ULL);
v___x_418_ = lean_usize_of_nat(v___x_415_);
v___x_419_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(v_val_410_, v___x_417_, v___x_418_);
lean_dec_ref(v_val_410_);
return v___x_419_;
}
}
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_420_ = lean_unsigned_to_nat(0u);
v___x_421_ = lean_array_get_size(v_val_410_);
v___x_422_ = lean_nat_dec_lt(v___x_420_, v___x_421_);
if (v___x_422_ == 0)
{
lean_dec_ref(v_val_410_);
return v___x_413_;
}
else
{
if (v___x_422_ == 0)
{
lean_dec_ref(v_val_410_);
return v___x_413_;
}
else
{
size_t v___x_423_; size_t v___x_424_; uint8_t v___x_425_; 
v___x_423_ = ((size_t)0ULL);
v___x_424_ = lean_usize_of_nat(v___x_421_);
v___x_425_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(v_val_410_, v___x_423_, v___x_424_);
lean_dec_ref(v_val_410_);
if (v___x_425_ == 0)
{
return v___x_413_;
}
else
{
uint8_t v___x_426_; 
v___x_426_ = 0;
return v___x_426_;
}
}
}
}
}
v___jp_427_:
{
if (lean_obj_tag(v___y_428_) == 0)
{
uint8_t v___x_429_; 
v___x_429_ = 0;
return v___x_429_;
}
else
{
lean_object* v_val_430_; 
v_val_430_ = lean_ctor_get(v___y_428_, 0);
lean_inc(v_val_430_);
lean_dec_ref_known(v___y_428_, 1);
v_val_410_ = v_val_430_;
goto v___jp_409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___boxed(lean_object* v_dir_450_, lean_object* v_message_451_){
_start:
{
uint8_t v_dir_boxed_452_; uint8_t v_res_453_; lean_object* v_r_454_; 
v_dir_boxed_452_ = lean_unbox(v_dir_450_);
v_res_453_ = l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(v_dir_boxed_452_, v_message_451_);
lean_dec(v_message_451_);
v_r_454_ = lean_box(v_res_453_);
return v_r_454_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1___redArg(lean_object* v_x_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Std_Http_Request_instReprHead_repr___redArg(v_x_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1(lean_object* v_x_457_, lean_object* v_prec_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Std_Http_Request_instReprHead_repr___redArg(v_x_457_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1___boxed(lean_object* v_x_460_, lean_object* v_prec_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Std_Http_Protocol_H1_instReprHead___aux__1(v_x_460_, v_prec_461_);
lean_dec(v_prec_461_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3___redArg(lean_object* v_x_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Std_Http_Response_instReprHead_repr___redArg(v_x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3(lean_object* v_x_465_, lean_object* v_prec_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Std_Http_Response_instReprHead_repr___redArg(v_x_465_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3___boxed(lean_object* v_x_468_, lean_object* v_prec_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Std_Http_Protocol_H1_instReprHead___aux__3(v_x_468_, v_prec_469_);
lean_dec(v_prec_469_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead(uint8_t v_dir_473_){
_start:
{
if (v_dir_473_ == 0)
{
lean_object* v___x_474_; 
v___x_474_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprHead___closed__0));
return v___x_474_;
}
else
{
lean_object* v___x_475_; 
v___x_475_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprHead___closed__1));
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___boxed(lean_object* v_dir_476_){
_start:
{
uint8_t v_dir_boxed_477_; lean_object* v_res_478_; 
v_dir_boxed_477_ = lean_unbox(v_dir_476_);
v_res_478_ = l_Std_Http_Protocol_H1_instReprHead(v_dir_boxed_477_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__0(lean_object* v_x_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = lean_string_from_utf8_unchecked(v_x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1(lean_object* v___x_481_, lean_object* v___x_482_, lean_object* v___x_483_, lean_object* v_name_484_, lean_object* v___x_485_, uint32_t v___x_486_, lean_object* v___x_487_, lean_object* v_it_488_, lean_object* v_acc_489_, lean_object* v_hP_490_, lean_object* v_recur_491_){
_start:
{
lean_object* v_it_493_; lean_object* v_out_494_; lean_object* v_it_510_; lean_object* v_startInclusive_511_; lean_object* v_endExclusive_512_; 
if (lean_obj_tag(v_it_488_) == 0)
{
lean_object* v_currPos_524_; lean_object* v_searcher_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_547_; 
v_currPos_524_ = lean_ctor_get(v_it_488_, 0);
v_searcher_525_ = lean_ctor_get(v_it_488_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v_it_488_);
if (v_isSharedCheck_547_ == 0)
{
v___x_527_ = v_it_488_;
v_isShared_528_ = v_isSharedCheck_547_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_searcher_525_);
lean_inc(v_currPos_524_);
lean_dec(v_it_488_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_547_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
uint8_t v_decide_529_; 
v_decide_529_ = lean_nat_dec_eq(v_searcher_525_, v___x_485_);
if (v_decide_529_ == 0)
{
uint32_t v___x_530_; uint8_t v___x_531_; 
lean_dec(v___x_485_);
v___x_530_ = lean_string_utf8_get_fast(v_name_484_, v_searcher_525_);
v___x_531_ = lean_uint32_dec_eq(v___x_530_, v___x_486_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_532_ = lean_string_utf8_next_fast(v_name_484_, v_searcher_525_);
lean_dec(v_searcher_525_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 1, v___x_532_);
v___x_534_ = v___x_527_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_currPos_524_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v___x_532_);
v___x_534_ = v_reuseFailAlloc_536_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_535_; 
v___x_535_ = lean_apply_4(v_recur_491_, v___x_534_, v_acc_489_, lean_box(0), lean_box(0));
return v___x_535_;
}
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v_slice_540_; lean_object* v_nextIt_542_; 
v___x_537_ = lean_string_utf8_next_fast(v_name_484_, v_searcher_525_);
v___x_538_ = lean_nat_sub(v___x_537_, v_searcher_525_);
v___x_539_ = lean_nat_add(v_searcher_525_, v___x_538_);
lean_dec(v___x_538_);
v_slice_540_ = l_String_Slice_subslice_x21(v___x_487_, v_currPos_524_, v_searcher_525_);
lean_inc(v___x_539_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 1, v___x_539_);
lean_ctor_set(v___x_527_, 0, v___x_539_);
v_nextIt_542_ = v___x_527_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v___x_539_);
v_nextIt_542_ = v_reuseFailAlloc_545_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_object* v_startInclusive_543_; lean_object* v_endExclusive_544_; 
v_startInclusive_543_ = lean_ctor_get(v_slice_540_, 0);
lean_inc(v_startInclusive_543_);
v_endExclusive_544_ = lean_ctor_get(v_slice_540_, 1);
lean_inc(v_endExclusive_544_);
lean_dec_ref(v_slice_540_);
v_it_510_ = v_nextIt_542_;
v_startInclusive_511_ = v_startInclusive_543_;
v_endExclusive_512_ = v_endExclusive_544_;
goto v___jp_509_;
}
}
}
else
{
lean_object* v___x_546_; 
lean_del_object(v___x_527_);
lean_dec(v_searcher_525_);
v___x_546_ = lean_box(1);
v_it_510_ = v___x_546_;
v_startInclusive_511_ = v_currPos_524_;
v_endExclusive_512_ = v___x_485_;
goto v___jp_509_;
}
}
}
else
{
lean_dec_ref(v_recur_491_);
lean_dec(v___x_485_);
return v_acc_489_;
}
v___jp_492_:
{
if (lean_obj_tag(v_acc_489_) == 0)
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_495_, 0, v_out_494_);
v___x_496_ = lean_apply_4(v_recur_491_, v_it_493_, v___x_495_, lean_box(0), lean_box(0));
return v___x_496_;
}
else
{
lean_object* v_val_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_508_; 
v_val_497_ = lean_ctor_get(v_acc_489_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v_acc_489_);
if (v_isSharedCheck_508_ == 0)
{
v___x_499_ = v_acc_489_;
v_isShared_500_ = v_isSharedCheck_508_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_val_497_);
lean_dec(v_acc_489_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_508_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_501_ = lean_string_utf8_extract_fast(v___x_481_, v___x_482_, v___x_483_);
v___x_502_ = lean_string_append(v_val_497_, v___x_501_);
lean_dec_ref(v___x_501_);
v___x_503_ = lean_string_append(v___x_502_, v_out_494_);
lean_dec_ref(v_out_494_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_503_);
v___x_505_ = v___x_499_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_507_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_506_; 
v___x_506_ = lean_apply_4(v_recur_491_, v_it_493_, v___x_505_, lean_box(0), lean_box(0));
return v___x_506_;
}
}
}
}
v___jp_509_:
{
lean_object* v___x_513_; uint32_t v___x_514_; uint32_t v___x_515_; uint8_t v___x_516_; 
v___x_513_ = lean_string_utf8_extract_fast(v_name_484_, v_startInclusive_511_, v_endExclusive_512_);
lean_dec(v_endExclusive_512_);
lean_dec(v_startInclusive_511_);
v___x_514_ = lean_string_utf8_get(v___x_513_, v___x_482_);
v___x_515_ = 97;
v___x_516_ = lean_uint32_dec_le(v___x_515_, v___x_514_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; 
v___x_517_ = lean_string_utf8_set(v___x_513_, v___x_482_, v___x_514_);
v_it_493_ = v_it_510_;
v_out_494_ = v___x_517_;
goto v___jp_492_;
}
else
{
uint32_t v___x_518_; uint8_t v___x_519_; 
v___x_518_ = 122;
v___x_519_ = lean_uint32_dec_le(v___x_514_, v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; 
v___x_520_ = lean_string_utf8_set(v___x_513_, v___x_482_, v___x_514_);
v_it_493_ = v_it_510_;
v_out_494_ = v___x_520_;
goto v___jp_492_;
}
else
{
uint32_t v___x_521_; uint32_t v___x_522_; lean_object* v___x_523_; 
v___x_521_ = 4294967264;
v___x_522_ = lean_uint32_add(v___x_514_, v___x_521_);
v___x_523_ = lean_string_utf8_set(v___x_513_, v___x_482_, v___x_522_);
v_it_493_ = v_it_510_;
v_out_494_ = v___x_523_;
goto v___jp_492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1___boxed(lean_object* v___x_548_, lean_object* v___x_549_, lean_object* v___x_550_, lean_object* v_name_551_, lean_object* v___x_552_, lean_object* v___x_553_, lean_object* v___x_554_, lean_object* v_it_555_, lean_object* v_acc_556_, lean_object* v_hP_557_, lean_object* v_recur_558_){
_start:
{
uint32_t v___x_2758__boxed_559_; lean_object* v_res_560_; 
v___x_2758__boxed_559_ = lean_unbox_uint32(v___x_553_);
lean_dec(v___x_553_);
v_res_560_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1(v___x_548_, v___x_549_, v___x_550_, v_name_551_, v___x_552_, v___x_2758__boxed_559_, v___x_554_, v_it_555_, v_acc_556_, v_hP_557_, v_recur_558_);
lean_dec_ref(v___x_554_);
lean_dec_ref(v_name_551_);
lean_dec(v___x_550_);
lean_dec(v___x_549_);
lean_dec_ref(v___x_548_);
return v_res_560_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed__const__1(void){
_start:
{
uint32_t v___x_566_; lean_object* v___x_567_; 
v___x_566_ = 45;
v___x_567_ = lean_box_uint32(v___x_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2(lean_object* v_buf_568_, lean_object* v_name_569_, lean_object* v_value_570_){
_start:
{
lean_object* v___y_572_; lean_object* v___f_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v_it_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___f_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___f_591_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__2));
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = lean_string_utf8_byte_size(v_name_569_);
lean_inc_ref(v_name_569_);
v___x_594_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_594_, 0, v_name_569_);
lean_ctor_set(v___x_594_, 1, v___x_592_);
lean_ctor_set(v___x_594_, 2, v___x_593_);
lean_inc_ref(v___x_594_);
v_it_595_ = l_String_Slice_splitToSubslice___redArg(v___x_594_, v___f_591_);
v___x_596_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__3));
v___x_597_ = lean_unsigned_to_nat(1u);
v___x_598_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed__const__1;
v___f_599_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1___boxed), 11, 7);
lean_closure_set(v___f_599_, 0, v___x_596_);
lean_closure_set(v___f_599_, 1, v___x_592_);
lean_closure_set(v___f_599_, 2, v___x_597_);
lean_closure_set(v___f_599_, 3, v_name_569_);
lean_closure_set(v___f_599_, 4, v___x_593_);
lean_closure_set(v___f_599_, 5, v___x_598_);
lean_closure_set(v___f_599_, 6, v___x_594_);
v___x_600_ = lean_box(0);
v___x_601_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_599_, v_it_595_, v___x_600_, lean_box(0));
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v___x_602_; 
v___x_602_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_572_ = v___x_602_;
goto v___jp_571_;
}
else
{
lean_object* v_val_603_; 
v_val_603_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_val_603_);
lean_dec_ref_known(v___x_601_, 1);
v___y_572_ = v_val_603_;
goto v___jp_571_;
}
v___jp_571_:
{
lean_object* v_data_573_; lean_object* v_size_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_590_; 
v_data_573_ = lean_ctor_get(v_buf_568_, 0);
v_size_574_ = lean_ctor_get(v_buf_568_, 1);
v_isSharedCheck_590_ = !lean_is_exclusive(v_buf_568_);
if (v_isSharedCheck_590_ == 0)
{
v___x_576_ = v_buf_568_;
v_isShared_577_ = v_isSharedCheck_590_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_size_574_);
lean_inc(v_data_573_);
lean_dec(v_buf_568_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_590_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_578_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__0));
v___x_579_ = lean_string_append(v___y_572_, v___x_578_);
v___x_580_ = lean_string_append(v___x_579_, v_value_570_);
v___x_581_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__1));
v___x_582_ = lean_string_append(v___x_580_, v___x_581_);
v___x_583_ = lean_string_to_utf8(v___x_582_);
lean_dec_ref(v___x_582_);
lean_inc_ref(v___x_583_);
v___x_584_ = lean_array_push(v_data_573_, v___x_583_);
v___x_585_ = lean_byte_array_size(v___x_583_);
lean_dec_ref(v___x_583_);
v___x_586_ = lean_nat_add(v_size_574_, v___x_585_);
lean_dec(v_size_574_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 1, v___x_586_);
lean_ctor_set(v___x_576_, 0, v___x_584_);
v___x_588_ = v___x_576_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed(lean_object* v_buf_604_, lean_object* v_name_605_, lean_object* v_value_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2(v_buf_604_, v_name_605_, v_value_606_);
lean_dec_ref(v_value_606_);
return v_res_607_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__1));
v___x_611_ = lean_string_to_utf8(v___x_610_);
return v___x_611_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_613_ = lean_byte_array_size(v___x_612_);
return v___x_613_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23));
v___x_649_ = lean_byte_array_size(v___x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1(lean_object* v_buffer_693_, lean_object* v_req_694_){
_start:
{
uint8_t v_method_695_; uint8_t v_version_696_; lean_object* v_uri_697_; lean_object* v_headers_698_; lean_object* v___f_699_; lean_object* v___f_700_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v_port_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v_host_772_; lean_object* v_port_773_; lean_object* v___y_774_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v_port_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v_host_892_; lean_object* v_port_893_; lean_object* v___y_894_; lean_object* v___y_905_; 
v_method_695_ = lean_ctor_get_uint8(v_req_694_, sizeof(void*)*2);
v_version_696_ = lean_ctor_get_uint8(v_req_694_, sizeof(void*)*2 + 1);
v_uri_697_ = lean_ctor_get(v_req_694_, 0);
lean_inc(v_uri_697_);
v_headers_698_ = lean_ctor_get(v_req_694_, 1);
lean_inc_ref(v_headers_698_);
lean_dec_ref(v_req_694_);
v___f_699_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__0));
v___f_700_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1));
switch(v_method_695_)
{
case 0:
{
lean_object* v___x_985_; 
v___x_985_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28));
v___y_905_ = v___x_985_;
goto v___jp_904_;
}
case 1:
{
lean_object* v___x_986_; 
v___x_986_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29));
v___y_905_ = v___x_986_;
goto v___jp_904_;
}
case 2:
{
lean_object* v___x_987_; 
v___x_987_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30));
v___y_905_ = v___x_987_;
goto v___jp_904_;
}
case 3:
{
lean_object* v___x_988_; 
v___x_988_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31));
v___y_905_ = v___x_988_;
goto v___jp_904_;
}
case 4:
{
lean_object* v___x_989_; 
v___x_989_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32));
v___y_905_ = v___x_989_;
goto v___jp_904_;
}
case 5:
{
lean_object* v___x_990_; 
v___x_990_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33));
v___y_905_ = v___x_990_;
goto v___jp_904_;
}
case 6:
{
lean_object* v___x_991_; 
v___x_991_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34));
v___y_905_ = v___x_991_;
goto v___jp_904_;
}
case 7:
{
lean_object* v___x_992_; 
v___x_992_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35));
v___y_905_ = v___x_992_;
goto v___jp_904_;
}
case 8:
{
lean_object* v___x_993_; 
v___x_993_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36));
v___y_905_ = v___x_993_;
goto v___jp_904_;
}
case 9:
{
lean_object* v___x_994_; 
v___x_994_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37));
v___y_905_ = v___x_994_;
goto v___jp_904_;
}
case 10:
{
lean_object* v___x_995_; 
v___x_995_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38));
v___y_905_ = v___x_995_;
goto v___jp_904_;
}
case 11:
{
lean_object* v___x_996_; 
v___x_996_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39));
v___y_905_ = v___x_996_;
goto v___jp_904_;
}
case 12:
{
lean_object* v___x_997_; 
v___x_997_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40));
v___y_905_ = v___x_997_;
goto v___jp_904_;
}
case 13:
{
lean_object* v___x_998_; 
v___x_998_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41));
v___y_905_ = v___x_998_;
goto v___jp_904_;
}
case 14:
{
lean_object* v___x_999_; 
v___x_999_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42));
v___y_905_ = v___x_999_;
goto v___jp_904_;
}
case 15:
{
lean_object* v___x_1000_; 
v___x_1000_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43));
v___y_905_ = v___x_1000_;
goto v___jp_904_;
}
case 16:
{
lean_object* v___x_1001_; 
v___x_1001_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44));
v___y_905_ = v___x_1001_;
goto v___jp_904_;
}
case 17:
{
lean_object* v___x_1002_; 
v___x_1002_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45));
v___y_905_ = v___x_1002_;
goto v___jp_904_;
}
case 18:
{
lean_object* v___x_1003_; 
v___x_1003_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46));
v___y_905_ = v___x_1003_;
goto v___jp_904_;
}
case 19:
{
lean_object* v___x_1004_; 
v___x_1004_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47));
v___y_905_ = v___x_1004_;
goto v___jp_904_;
}
case 20:
{
lean_object* v___x_1005_; 
v___x_1005_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48));
v___y_905_ = v___x_1005_;
goto v___jp_904_;
}
case 21:
{
lean_object* v___x_1006_; 
v___x_1006_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49));
v___y_905_ = v___x_1006_;
goto v___jp_904_;
}
case 22:
{
lean_object* v___x_1007_; 
v___x_1007_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50));
v___y_905_ = v___x_1007_;
goto v___jp_904_;
}
case 23:
{
lean_object* v___x_1008_; 
v___x_1008_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51));
v___y_905_ = v___x_1008_;
goto v___jp_904_;
}
case 24:
{
lean_object* v___x_1009_; 
v___x_1009_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52));
v___y_905_ = v___x_1009_;
goto v___jp_904_;
}
case 25:
{
lean_object* v___x_1010_; 
v___x_1010_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53));
v___y_905_ = v___x_1010_;
goto v___jp_904_;
}
case 26:
{
lean_object* v___x_1011_; 
v___x_1011_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54));
v___y_905_ = v___x_1011_;
goto v___jp_904_;
}
case 27:
{
lean_object* v___x_1012_; 
v___x_1012_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55));
v___y_905_ = v___x_1012_;
goto v___jp_904_;
}
case 28:
{
lean_object* v___x_1013_; 
v___x_1013_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56));
v___y_905_ = v___x_1013_;
goto v___jp_904_;
}
case 29:
{
lean_object* v___x_1014_; 
v___x_1014_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57));
v___y_905_ = v___x_1014_;
goto v___jp_904_;
}
case 30:
{
lean_object* v___x_1015_; 
v___x_1015_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58));
v___y_905_ = v___x_1015_;
goto v___jp_904_;
}
case 31:
{
lean_object* v___x_1016_; 
v___x_1016_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59));
v___y_905_ = v___x_1016_;
goto v___jp_904_;
}
case 32:
{
lean_object* v___x_1017_; 
v___x_1017_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60));
v___y_905_ = v___x_1017_;
goto v___jp_904_;
}
case 33:
{
lean_object* v___x_1018_; 
v___x_1018_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61));
v___y_905_ = v___x_1018_;
goto v___jp_904_;
}
case 34:
{
lean_object* v___x_1019_; 
v___x_1019_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62));
v___y_905_ = v___x_1019_;
goto v___jp_904_;
}
case 35:
{
lean_object* v___x_1020_; 
v___x_1020_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63));
v___y_905_ = v___x_1020_;
goto v___jp_904_;
}
case 36:
{
lean_object* v___x_1021_; 
v___x_1021_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64));
v___y_905_ = v___x_1021_;
goto v___jp_904_;
}
case 37:
{
lean_object* v___x_1022_; 
v___x_1022_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65));
v___y_905_ = v___x_1022_;
goto v___jp_904_;
}
case 38:
{
lean_object* v___x_1023_; 
v___x_1023_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66));
v___y_905_ = v___x_1023_;
goto v___jp_904_;
}
default: 
{
lean_object* v___x_1024_; 
v___x_1024_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67));
v___y_905_ = v___x_1024_;
goto v___jp_904_;
}
}
v___jp_701_:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v_buffer_713_; lean_object* v_buffer_714_; lean_object* v_data_715_; lean_object* v_size_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_725_; 
v___x_705_ = lean_string_to_utf8(v___y_704_);
lean_inc_ref(v___x_705_);
v___x_706_ = lean_array_push(v___y_703_, v___x_705_);
v___x_707_ = lean_byte_array_size(v___x_705_);
lean_dec_ref(v___x_705_);
v___x_708_ = lean_nat_add(v___y_702_, v___x_707_);
lean_dec(v___y_702_);
v___x_709_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_710_ = lean_array_push(v___x_706_, v___x_709_);
v___x_711_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3);
v___x_712_ = lean_nat_add(v___x_708_, v___x_711_);
lean_dec(v___x_708_);
v_buffer_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_buffer_713_, 0, v___x_710_);
lean_ctor_set(v_buffer_713_, 1, v___x_712_);
v_buffer_714_ = l_Std_Http_Headers_fold___redArg(v_headers_698_, v_buffer_713_, v___f_700_);
lean_dec_ref(v_headers_698_);
v_data_715_ = lean_ctor_get(v_buffer_714_, 0);
v_size_716_ = lean_ctor_get(v_buffer_714_, 1);
v_isSharedCheck_725_ = !lean_is_exclusive(v_buffer_714_);
if (v_isSharedCheck_725_ == 0)
{
v___x_718_ = v_buffer_714_;
v_isShared_719_ = v_isSharedCheck_725_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_size_716_);
lean_inc(v_data_715_);
lean_dec(v_buffer_714_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_725_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_720_ = lean_array_push(v_data_715_, v___x_709_);
v___x_721_ = lean_nat_add(v_size_716_, v___x_711_);
lean_dec(v_size_716_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 1, v___x_721_);
lean_ctor_set(v___x_718_, 0, v___x_720_);
v___x_723_ = v___x_718_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
v___jp_726_:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_732_ = lean_string_to_utf8(v___y_731_);
lean_dec_ref(v___y_731_);
lean_inc_ref(v___x_732_);
v___x_733_ = lean_array_push(v___y_728_, v___x_732_);
v___x_734_ = lean_byte_array_size(v___x_732_);
lean_dec_ref(v___x_732_);
v___x_735_ = lean_nat_add(v___y_729_, v___x_734_);
lean_dec(v___y_729_);
v___x_736_ = lean_array_push(v___x_733_, v___y_727_);
v___x_737_ = lean_nat_add(v___x_735_, v___y_730_);
lean_dec(v___x_735_);
switch(v_version_696_)
{
case 0:
{
lean_object* v___x_738_; 
v___x_738_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4));
v___y_702_ = v___x_737_;
v___y_703_ = v___x_736_;
v___y_704_ = v___x_738_;
goto v___jp_701_;
}
case 1:
{
lean_object* v___x_739_; 
v___x_739_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5));
v___y_702_ = v___x_737_;
v___y_703_ = v___x_736_;
v___y_704_ = v___x_739_;
goto v___jp_701_;
}
case 2:
{
lean_object* v___x_740_; 
v___x_740_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6));
v___y_702_ = v___x_737_;
v___y_703_ = v___x_736_;
v___y_704_ = v___x_740_;
goto v___jp_701_;
}
default: 
{
lean_object* v___x_741_; 
v___x_741_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7));
v___y_702_ = v___x_737_;
v___y_703_ = v___x_736_;
v___y_704_ = v___x_741_;
goto v___jp_701_;
}
}
}
v___jp_742_:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = lean_string_append(v___y_747_, v___y_744_);
lean_dec_ref(v___y_744_);
v___x_751_ = lean_string_append(v___x_750_, v___y_749_);
lean_dec_ref(v___y_749_);
v___y_727_ = v___y_743_;
v___y_728_ = v___y_745_;
v___y_729_ = v___y_746_;
v___y_730_ = v___y_748_;
v___y_731_ = v___x_751_;
goto v___jp_726_;
}
v___jp_752_:
{
switch(lean_obj_tag(v_port_757_))
{
case 0:
{
lean_object* v___x_760_; 
v___x_760_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_743_ = v___y_753_;
v___y_744_ = v___y_759_;
v___y_745_ = v___y_754_;
v___y_746_ = v___y_755_;
v___y_747_ = v___y_756_;
v___y_748_ = v___y_758_;
v___y_749_ = v___x_760_;
goto v___jp_742_;
}
case 1:
{
lean_object* v___x_761_; 
v___x_761_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___y_743_ = v___y_753_;
v___y_744_ = v___y_759_;
v___y_745_ = v___y_754_;
v___y_746_ = v___y_755_;
v___y_747_ = v___y_756_;
v___y_748_ = v___y_758_;
v___y_749_ = v___x_761_;
goto v___jp_742_;
}
default: 
{
uint16_t v_port_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v_port_762_ = lean_ctor_get_uint16(v_port_757_, 0);
lean_dec_ref_known(v_port_757_, 0);
v___x_763_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_764_ = lean_uint16_to_nat(v_port_762_);
v___x_765_ = l_Nat_reprFast(v___x_764_);
v___x_766_ = lean_string_append(v___x_763_, v___x_765_);
lean_dec_ref(v___x_765_);
v___y_743_ = v___y_753_;
v___y_744_ = v___y_759_;
v___y_745_ = v___y_754_;
v___y_746_ = v___y_755_;
v___y_747_ = v___y_756_;
v___y_748_ = v___y_758_;
v___y_749_ = v___x_766_;
goto v___jp_742_;
}
}
}
v___jp_767_:
{
switch(lean_obj_tag(v_host_772_))
{
case 0:
{
lean_object* v_name_775_; 
v_name_775_ = lean_ctor_get(v_host_772_, 0);
lean_inc_ref(v_name_775_);
lean_dec_ref_known(v_host_772_, 1);
v___y_753_ = v___y_768_;
v___y_754_ = v___y_769_;
v___y_755_ = v___y_770_;
v___y_756_ = v___y_774_;
v_port_757_ = v_port_773_;
v___y_758_ = v___y_771_;
v___y_759_ = v_name_775_;
goto v___jp_752_;
}
case 1:
{
lean_object* v_ipv4_776_; lean_object* v___x_777_; 
v_ipv4_776_ = lean_ctor_get(v_host_772_, 0);
lean_inc_ref(v_ipv4_776_);
lean_dec_ref_known(v_host_772_, 1);
v___x_777_ = lean_uv_ntop_v4(v_ipv4_776_);
lean_dec_ref(v_ipv4_776_);
v___y_753_ = v___y_768_;
v___y_754_ = v___y_769_;
v___y_755_ = v___y_770_;
v___y_756_ = v___y_774_;
v_port_757_ = v_port_773_;
v___y_758_ = v___y_771_;
v___y_759_ = v___x_777_;
goto v___jp_752_;
}
default: 
{
lean_object* v_ipv6_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v_ipv6_778_ = lean_ctor_get(v_host_772_, 0);
lean_inc_ref(v_ipv6_778_);
lean_dec_ref_known(v_host_772_, 1);
v___x_779_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9));
v___x_780_ = lean_uv_ntop_v6(v_ipv6_778_);
lean_dec_ref(v_ipv6_778_);
v___x_781_ = lean_string_append(v___x_779_, v___x_780_);
lean_dec_ref(v___x_780_);
v___x_782_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10));
v___x_783_ = lean_string_append(v___x_781_, v___x_782_);
v___y_753_ = v___y_768_;
v___y_754_ = v___y_769_;
v___y_755_ = v___y_770_;
v___y_756_ = v___y_774_;
v_port_757_ = v_port_773_;
v___y_758_ = v___y_771_;
v___y_759_ = v___x_783_;
goto v___jp_752_;
}
}
}
v___jp_784_:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_794_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_795_ = lean_string_append(v___y_788_, v___x_794_);
v___x_796_ = lean_string_append(v___x_795_, v___y_791_);
lean_dec_ref(v___y_791_);
v___x_797_ = lean_string_append(v___x_796_, v___y_785_);
lean_dec_ref(v___y_785_);
v___x_798_ = lean_string_append(v___x_797_, v___y_787_);
lean_dec_ref(v___y_787_);
v___x_799_ = lean_string_append(v___x_798_, v___y_793_);
lean_dec_ref(v___y_793_);
v___y_727_ = v___y_786_;
v___y_728_ = v___y_789_;
v___y_729_ = v___y_790_;
v___y_730_ = v___y_792_;
v___y_731_ = v___x_799_;
goto v___jp_726_;
}
v___jp_800_:
{
lean_object* v_queryPart_810_; 
v_queryPart_810_ = l_Std_Http_URI_Query_formatOption(v___y_807_);
if (lean_obj_tag(v___y_802_) == 0)
{
lean_object* v___x_811_; 
v___x_811_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_785_ = v___y_809_;
v___y_786_ = v___y_801_;
v___y_787_ = v_queryPart_810_;
v___y_788_ = v___y_803_;
v___y_789_ = v___y_804_;
v___y_790_ = v___y_806_;
v___y_791_ = v___y_805_;
v___y_792_ = v___y_808_;
v___y_793_ = v___x_811_;
goto v___jp_784_;
}
else
{
lean_object* v_val_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v_val_812_ = lean_ctor_get(v___y_802_, 0);
lean_inc(v_val_812_);
lean_dec_ref_known(v___y_802_, 1);
v___x_813_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11));
v___x_814_ = l_Std_Http_URI_EncodedFragment_encode(v_val_812_);
lean_dec(v_val_812_);
v___x_815_ = lean_string_from_utf8_unchecked(v___x_814_);
v___x_816_ = lean_string_append(v___x_813_, v___x_815_);
lean_dec_ref(v___x_815_);
v___y_785_ = v___y_809_;
v___y_786_ = v___y_801_;
v___y_787_ = v_queryPart_810_;
v___y_788_ = v___y_803_;
v___y_789_ = v___y_804_;
v___y_790_ = v___y_806_;
v___y_791_ = v___y_805_;
v___y_792_ = v___y_808_;
v___y_793_ = v___x_816_;
goto v___jp_784_;
}
}
v___jp_817_:
{
lean_object* v_queryStr_824_; lean_object* v___x_825_; 
v_queryStr_824_ = l_Std_Http_URI_Query_formatOption(v___y_818_);
v___x_825_ = lean_string_append(v___y_823_, v_queryStr_824_);
lean_dec_ref(v_queryStr_824_);
v___y_727_ = v___y_819_;
v___y_728_ = v___y_820_;
v___y_729_ = v___y_821_;
v___y_730_ = v___y_822_;
v___y_731_ = v___x_825_;
goto v___jp_726_;
}
v___jp_826_:
{
lean_object* v_segments_836_; uint8_t v_absolute_837_; lean_object* v___x_838_; lean_object* v___x_839_; size_t v_sz_840_; size_t v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v_result_844_; 
v_segments_836_ = lean_ctor_get(v___y_827_, 0);
lean_inc_ref(v_segments_836_);
v_absolute_837_ = lean_ctor_get_uint8(v___y_827_, sizeof(void*)*1);
lean_dec_ref(v___y_827_);
v___x_838_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12));
v___x_839_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22));
v_sz_840_ = lean_array_size(v_segments_836_);
v___x_841_ = ((size_t)0ULL);
v___x_842_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_839_, v___f_699_, v_sz_840_, v___x_841_, v_segments_836_);
v___x_843_ = lean_array_to_list(v___x_842_);
v_result_844_ = l_String_intercalate(v___x_838_, v___x_843_);
if (v_absolute_837_ == 0)
{
v___y_801_ = v___y_828_;
v___y_802_ = v___y_829_;
v___y_803_ = v___y_830_;
v___y_804_ = v___y_831_;
v___y_805_ = v___y_835_;
v___y_806_ = v___y_832_;
v___y_807_ = v___y_833_;
v___y_808_ = v___y_834_;
v___y_809_ = v_result_844_;
goto v___jp_800_;
}
else
{
lean_object* v___x_845_; 
v___x_845_ = lean_string_append(v___x_838_, v_result_844_);
lean_dec_ref(v_result_844_);
v___y_801_ = v___y_828_;
v___y_802_ = v___y_829_;
v___y_803_ = v___y_830_;
v___y_804_ = v___y_831_;
v___y_805_ = v___y_835_;
v___y_806_ = v___y_832_;
v___y_807_ = v___y_833_;
v___y_808_ = v___y_834_;
v___y_809_ = v___x_845_;
goto v___jp_800_;
}
}
v___jp_846_:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_859_ = lean_string_append(v___y_857_, v___y_854_);
lean_dec_ref(v___y_854_);
v___x_860_ = lean_string_append(v___x_859_, v___y_858_);
lean_dec_ref(v___y_858_);
lean_inc_ref(v___y_856_);
v___x_861_ = lean_string_append(v___y_856_, v___x_860_);
lean_dec_ref(v___x_860_);
v___y_827_ = v___y_848_;
v___y_828_ = v___y_847_;
v___y_829_ = v___y_849_;
v___y_830_ = v___y_850_;
v___y_831_ = v___y_851_;
v___y_832_ = v___y_852_;
v___y_833_ = v___y_853_;
v___y_834_ = v___y_855_;
v___y_835_ = v___x_861_;
goto v___jp_826_;
}
v___jp_862_:
{
switch(lean_obj_tag(v_port_871_))
{
case 0:
{
lean_object* v___x_875_; 
v___x_875_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_847_ = v___y_864_;
v___y_848_ = v___y_863_;
v___y_849_ = v___y_865_;
v___y_850_ = v___y_866_;
v___y_851_ = v___y_867_;
v___y_852_ = v___y_868_;
v___y_853_ = v___y_869_;
v___y_854_ = v___y_874_;
v___y_855_ = v___y_870_;
v___y_856_ = v___y_873_;
v___y_857_ = v___y_872_;
v___y_858_ = v___x_875_;
goto v___jp_846_;
}
case 1:
{
lean_object* v___x_876_; 
v___x_876_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___y_847_ = v___y_864_;
v___y_848_ = v___y_863_;
v___y_849_ = v___y_865_;
v___y_850_ = v___y_866_;
v___y_851_ = v___y_867_;
v___y_852_ = v___y_868_;
v___y_853_ = v___y_869_;
v___y_854_ = v___y_874_;
v___y_855_ = v___y_870_;
v___y_856_ = v___y_873_;
v___y_857_ = v___y_872_;
v___y_858_ = v___x_876_;
goto v___jp_846_;
}
default: 
{
uint16_t v_port_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v_port_877_ = lean_ctor_get_uint16(v_port_871_, 0);
lean_dec_ref_known(v_port_871_, 0);
v___x_878_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_879_ = lean_uint16_to_nat(v_port_877_);
v___x_880_ = l_Nat_reprFast(v___x_879_);
v___x_881_ = lean_string_append(v___x_878_, v___x_880_);
lean_dec_ref(v___x_880_);
v___y_847_ = v___y_864_;
v___y_848_ = v___y_863_;
v___y_849_ = v___y_865_;
v___y_850_ = v___y_866_;
v___y_851_ = v___y_867_;
v___y_852_ = v___y_868_;
v___y_853_ = v___y_869_;
v___y_854_ = v___y_874_;
v___y_855_ = v___y_870_;
v___y_856_ = v___y_873_;
v___y_857_ = v___y_872_;
v___y_858_ = v___x_881_;
goto v___jp_846_;
}
}
}
v___jp_882_:
{
switch(lean_obj_tag(v_host_892_))
{
case 0:
{
lean_object* v_name_895_; 
v_name_895_ = lean_ctor_get(v_host_892_, 0);
lean_inc_ref(v_name_895_);
lean_dec_ref_known(v_host_892_, 1);
v___y_863_ = v___y_884_;
v___y_864_ = v___y_883_;
v___y_865_ = v___y_885_;
v___y_866_ = v___y_886_;
v___y_867_ = v___y_887_;
v___y_868_ = v___y_888_;
v___y_869_ = v___y_889_;
v___y_870_ = v___y_890_;
v_port_871_ = v_port_893_;
v___y_872_ = v___y_894_;
v___y_873_ = v___y_891_;
v___y_874_ = v_name_895_;
goto v___jp_862_;
}
case 1:
{
lean_object* v_ipv4_896_; lean_object* v___x_897_; 
v_ipv4_896_ = lean_ctor_get(v_host_892_, 0);
lean_inc_ref(v_ipv4_896_);
lean_dec_ref_known(v_host_892_, 1);
v___x_897_ = lean_uv_ntop_v4(v_ipv4_896_);
lean_dec_ref(v_ipv4_896_);
v___y_863_ = v___y_884_;
v___y_864_ = v___y_883_;
v___y_865_ = v___y_885_;
v___y_866_ = v___y_886_;
v___y_867_ = v___y_887_;
v___y_868_ = v___y_888_;
v___y_869_ = v___y_889_;
v___y_870_ = v___y_890_;
v_port_871_ = v_port_893_;
v___y_872_ = v___y_894_;
v___y_873_ = v___y_891_;
v___y_874_ = v___x_897_;
goto v___jp_862_;
}
default: 
{
lean_object* v_ipv6_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v_ipv6_898_ = lean_ctor_get(v_host_892_, 0);
lean_inc_ref(v_ipv6_898_);
lean_dec_ref_known(v_host_892_, 1);
v___x_899_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9));
v___x_900_ = lean_uv_ntop_v6(v_ipv6_898_);
lean_dec_ref(v_ipv6_898_);
v___x_901_ = lean_string_append(v___x_899_, v___x_900_);
lean_dec_ref(v___x_900_);
v___x_902_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10));
v___x_903_ = lean_string_append(v___x_901_, v___x_902_);
v___y_863_ = v___y_884_;
v___y_864_ = v___y_883_;
v___y_865_ = v___y_885_;
v___y_866_ = v___y_886_;
v___y_867_ = v___y_887_;
v___y_868_ = v___y_888_;
v___y_869_ = v___y_889_;
v___y_870_ = v___y_890_;
v_port_871_ = v_port_893_;
v___y_872_ = v___y_894_;
v___y_873_ = v___y_891_;
v___y_874_ = v___x_903_;
goto v___jp_862_;
}
}
}
v___jp_904_:
{
lean_object* v_data_906_; lean_object* v_size_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_data_906_ = lean_ctor_get(v_buffer_693_, 0);
lean_inc_ref(v_data_906_);
v_size_907_ = lean_ctor_get(v_buffer_693_, 1);
lean_inc(v_size_907_);
lean_dec_ref(v_buffer_693_);
v___x_908_ = lean_string_to_utf8(v___y_905_);
lean_inc_ref(v___x_908_);
v___x_909_ = lean_array_push(v_data_906_, v___x_908_);
v___x_910_ = lean_byte_array_size(v___x_908_);
lean_dec_ref(v___x_908_);
v___x_911_ = lean_nat_add(v_size_907_, v___x_910_);
lean_dec(v_size_907_);
v___x_912_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23));
v___x_913_ = lean_array_push(v___x_909_, v___x_912_);
v___x_914_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24);
v___x_915_ = lean_nat_add(v___x_911_, v___x_914_);
lean_dec(v___x_911_);
switch(lean_obj_tag(v_uri_697_))
{
case 0:
{
lean_object* v_path_916_; lean_object* v_query_917_; lean_object* v_segments_918_; uint8_t v_absolute_919_; lean_object* v___x_920_; lean_object* v___x_921_; size_t v_sz_922_; size_t v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v_result_926_; 
v_path_916_ = lean_ctor_get(v_uri_697_, 0);
lean_inc_ref(v_path_916_);
v_query_917_ = lean_ctor_get(v_uri_697_, 1);
lean_inc(v_query_917_);
lean_dec_ref_known(v_uri_697_, 2);
v_segments_918_ = lean_ctor_get(v_path_916_, 0);
lean_inc_ref(v_segments_918_);
v_absolute_919_ = lean_ctor_get_uint8(v_path_916_, sizeof(void*)*1);
lean_dec_ref(v_path_916_);
v___x_920_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12));
v___x_921_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22));
v_sz_922_ = lean_array_size(v_segments_918_);
v___x_923_ = ((size_t)0ULL);
v___x_924_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_921_, v___f_699_, v_sz_922_, v___x_923_, v_segments_918_);
v___x_925_ = lean_array_to_list(v___x_924_);
v_result_926_ = l_String_intercalate(v___x_920_, v___x_925_);
if (v_absolute_919_ == 0)
{
v___y_818_ = v_query_917_;
v___y_819_ = v___x_912_;
v___y_820_ = v___x_913_;
v___y_821_ = v___x_915_;
v___y_822_ = v___x_914_;
v___y_823_ = v_result_926_;
goto v___jp_817_;
}
else
{
lean_object* v___x_927_; 
v___x_927_ = lean_string_append(v___x_920_, v_result_926_);
lean_dec_ref(v_result_926_);
v___y_818_ = v_query_917_;
v___y_819_ = v___x_912_;
v___y_820_ = v___x_913_;
v___y_821_ = v___x_915_;
v___y_822_ = v___x_914_;
v___y_823_ = v___x_927_;
goto v___jp_817_;
}
}
case 1:
{
lean_object* v_uri_928_; lean_object* v_authority_929_; 
v_uri_928_ = lean_ctor_get(v_uri_697_, 0);
lean_inc_ref(v_uri_928_);
lean_dec_ref_known(v_uri_697_, 1);
v_authority_929_ = lean_ctor_get(v_uri_928_, 1);
if (lean_obj_tag(v_authority_929_) == 0)
{
lean_object* v_scheme_930_; lean_object* v_path_931_; lean_object* v_query_932_; lean_object* v_fragment_933_; lean_object* v___x_934_; 
v_scheme_930_ = lean_ctor_get(v_uri_928_, 0);
lean_inc_ref(v_scheme_930_);
v_path_931_ = lean_ctor_get(v_uri_928_, 2);
lean_inc_ref(v_path_931_);
v_query_932_ = lean_ctor_get(v_uri_928_, 3);
lean_inc(v_query_932_);
v_fragment_933_ = lean_ctor_get(v_uri_928_, 4);
lean_inc(v_fragment_933_);
lean_dec_ref(v_uri_928_);
v___x_934_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_827_ = v_path_931_;
v___y_828_ = v___x_912_;
v___y_829_ = v_fragment_933_;
v___y_830_ = v_scheme_930_;
v___y_831_ = v___x_913_;
v___y_832_ = v___x_915_;
v___y_833_ = v_query_932_;
v___y_834_ = v___x_914_;
v___y_835_ = v___x_934_;
goto v___jp_826_;
}
else
{
lean_object* v_val_935_; lean_object* v_scheme_936_; lean_object* v_path_937_; lean_object* v_query_938_; lean_object* v_fragment_939_; lean_object* v_userInfo_940_; lean_object* v_host_941_; lean_object* v_port_942_; lean_object* v___x_943_; 
v_val_935_ = lean_ctor_get(v_authority_929_, 0);
lean_inc(v_val_935_);
v_scheme_936_ = lean_ctor_get(v_uri_928_, 0);
lean_inc_ref(v_scheme_936_);
v_path_937_ = lean_ctor_get(v_uri_928_, 2);
lean_inc_ref(v_path_937_);
v_query_938_ = lean_ctor_get(v_uri_928_, 3);
lean_inc(v_query_938_);
v_fragment_939_ = lean_ctor_get(v_uri_928_, 4);
lean_inc(v_fragment_939_);
lean_dec_ref(v_uri_928_);
v_userInfo_940_ = lean_ctor_get(v_val_935_, 0);
lean_inc(v_userInfo_940_);
v_host_941_ = lean_ctor_get(v_val_935_, 1);
lean_inc_ref(v_host_941_);
v_port_942_ = lean_ctor_get(v_val_935_, 2);
lean_inc(v_port_942_);
lean_dec(v_val_935_);
v___x_943_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25));
if (lean_obj_tag(v_userInfo_940_) == 0)
{
lean_object* v___x_944_; 
v___x_944_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_883_ = v___x_912_;
v___y_884_ = v_path_937_;
v___y_885_ = v_fragment_939_;
v___y_886_ = v_scheme_936_;
v___y_887_ = v___x_913_;
v___y_888_ = v___x_915_;
v___y_889_ = v_query_938_;
v___y_890_ = v___x_914_;
v___y_891_ = v___x_943_;
v_host_892_ = v_host_941_;
v_port_893_ = v_port_942_;
v___y_894_ = v___x_944_;
goto v___jp_882_;
}
else
{
lean_object* v_val_945_; lean_object* v_password_946_; 
v_val_945_ = lean_ctor_get(v_userInfo_940_, 0);
lean_inc(v_val_945_);
lean_dec_ref_known(v_userInfo_940_, 1);
v_password_946_ = lean_ctor_get(v_val_945_, 1);
if (lean_obj_tag(v_password_946_) == 0)
{
lean_object* v_username_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v_username_947_ = lean_ctor_get(v_val_945_, 0);
lean_inc_ref(v_username_947_);
lean_dec(v_val_945_);
v___x_948_ = lean_string_from_utf8_unchecked(v_username_947_);
v___x_949_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26));
v___x_950_ = lean_string_append(v___x_948_, v___x_949_);
v___y_883_ = v___x_912_;
v___y_884_ = v_path_937_;
v___y_885_ = v_fragment_939_;
v___y_886_ = v_scheme_936_;
v___y_887_ = v___x_913_;
v___y_888_ = v___x_915_;
v___y_889_ = v_query_938_;
v___y_890_ = v___x_914_;
v___y_891_ = v___x_943_;
v_host_892_ = v_host_941_;
v_port_893_ = v_port_942_;
v___y_894_ = v___x_950_;
goto v___jp_882_;
}
else
{
lean_object* v_username_951_; lean_object* v_val_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
lean_inc_ref(v_password_946_);
v_username_951_ = lean_ctor_get(v_val_945_, 0);
lean_inc_ref(v_username_951_);
lean_dec(v_val_945_);
v_val_952_ = lean_ctor_get(v_password_946_, 0);
lean_inc(v_val_952_);
lean_dec_ref_known(v_password_946_, 1);
v___x_953_ = lean_string_from_utf8_unchecked(v_username_951_);
v___x_954_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_955_ = lean_string_append(v___x_953_, v___x_954_);
v___x_956_ = lean_string_from_utf8_unchecked(v_val_952_);
v___x_957_ = lean_string_append(v___x_955_, v___x_956_);
lean_dec_ref(v___x_956_);
v___x_958_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26));
v___x_959_ = lean_string_append(v___x_957_, v___x_958_);
v___y_883_ = v___x_912_;
v___y_884_ = v_path_937_;
v___y_885_ = v_fragment_939_;
v___y_886_ = v_scheme_936_;
v___y_887_ = v___x_913_;
v___y_888_ = v___x_915_;
v___y_889_ = v_query_938_;
v___y_890_ = v___x_914_;
v___y_891_ = v___x_943_;
v_host_892_ = v_host_941_;
v_port_893_ = v_port_942_;
v___y_894_ = v___x_959_;
goto v___jp_882_;
}
}
}
}
case 2:
{
lean_object* v_authority_960_; lean_object* v_userInfo_961_; 
v_authority_960_ = lean_ctor_get(v_uri_697_, 0);
lean_inc_ref(v_authority_960_);
lean_dec_ref_known(v_uri_697_, 1);
v_userInfo_961_ = lean_ctor_get(v_authority_960_, 0);
if (lean_obj_tag(v_userInfo_961_) == 0)
{
lean_object* v_host_962_; lean_object* v_port_963_; lean_object* v___x_964_; 
v_host_962_ = lean_ctor_get(v_authority_960_, 1);
lean_inc_ref(v_host_962_);
v_port_963_ = lean_ctor_get(v_authority_960_, 2);
lean_inc(v_port_963_);
lean_dec_ref(v_authority_960_);
v___x_964_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_768_ = v___x_912_;
v___y_769_ = v___x_913_;
v___y_770_ = v___x_915_;
v___y_771_ = v___x_914_;
v_host_772_ = v_host_962_;
v_port_773_ = v_port_963_;
v___y_774_ = v___x_964_;
goto v___jp_767_;
}
else
{
lean_object* v_val_965_; lean_object* v_password_966_; 
v_val_965_ = lean_ctor_get(v_userInfo_961_, 0);
lean_inc(v_val_965_);
v_password_966_ = lean_ctor_get(v_val_965_, 1);
if (lean_obj_tag(v_password_966_) == 0)
{
lean_object* v_host_967_; lean_object* v_port_968_; lean_object* v_username_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v_host_967_ = lean_ctor_get(v_authority_960_, 1);
lean_inc_ref(v_host_967_);
v_port_968_ = lean_ctor_get(v_authority_960_, 2);
lean_inc(v_port_968_);
lean_dec_ref(v_authority_960_);
v_username_969_ = lean_ctor_get(v_val_965_, 0);
lean_inc_ref(v_username_969_);
lean_dec(v_val_965_);
v___x_970_ = lean_string_from_utf8_unchecked(v_username_969_);
v___x_971_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26));
v___x_972_ = lean_string_append(v___x_970_, v___x_971_);
v___y_768_ = v___x_912_;
v___y_769_ = v___x_913_;
v___y_770_ = v___x_915_;
v___y_771_ = v___x_914_;
v_host_772_ = v_host_967_;
v_port_773_ = v_port_968_;
v___y_774_ = v___x_972_;
goto v___jp_767_;
}
else
{
lean_object* v_host_973_; lean_object* v_port_974_; lean_object* v_username_975_; lean_object* v_val_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
lean_inc_ref(v_password_966_);
v_host_973_ = lean_ctor_get(v_authority_960_, 1);
lean_inc_ref(v_host_973_);
v_port_974_ = lean_ctor_get(v_authority_960_, 2);
lean_inc(v_port_974_);
lean_dec_ref(v_authority_960_);
v_username_975_ = lean_ctor_get(v_val_965_, 0);
lean_inc_ref(v_username_975_);
lean_dec(v_val_965_);
v_val_976_ = lean_ctor_get(v_password_966_, 0);
lean_inc(v_val_976_);
lean_dec_ref_known(v_password_966_, 1);
v___x_977_ = lean_string_from_utf8_unchecked(v_username_975_);
v___x_978_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_979_ = lean_string_append(v___x_977_, v___x_978_);
v___x_980_ = lean_string_from_utf8_unchecked(v_val_976_);
v___x_981_ = lean_string_append(v___x_979_, v___x_980_);
lean_dec_ref(v___x_980_);
v___x_982_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26));
v___x_983_ = lean_string_append(v___x_981_, v___x_982_);
v___y_768_ = v___x_912_;
v___y_769_ = v___x_913_;
v___y_770_ = v___x_915_;
v___y_771_ = v___x_914_;
v_host_772_ = v_host_973_;
v_port_773_ = v_port_974_;
v___y_774_ = v___x_983_;
goto v___jp_767_;
}
}
}
default: 
{
lean_object* v___x_984_; 
v___x_984_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27));
v___y_727_ = v___x_912_;
v___y_728_ = v___x_913_;
v___y_729_ = v___x_915_;
v___y_730_ = v___x_914_;
v___y_731_ = v___x_984_;
goto v___jp_726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(lean_object* v_buffer_1025_, lean_object* v_r_1026_){
_start:
{
lean_object* v_status_1027_; uint8_t v_version_1028_; lean_object* v_headers_1029_; lean_object* v___f_1030_; lean_object* v___y_1032_; 
v_status_1027_ = lean_ctor_get(v_r_1026_, 0);
v_version_1028_ = lean_ctor_get_uint8(v_r_1026_, sizeof(void*)*2);
v_headers_1029_ = lean_ctor_get(v_r_1026_, 1);
v___f_1030_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1));
switch(v_version_1028_)
{
case 0:
{
lean_object* v___x_1082_; 
v___x_1082_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4));
v___y_1032_ = v___x_1082_;
goto v___jp_1031_;
}
case 1:
{
lean_object* v___x_1083_; 
v___x_1083_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5));
v___y_1032_ = v___x_1083_;
goto v___jp_1031_;
}
case 2:
{
lean_object* v___x_1084_; 
v___x_1084_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6));
v___y_1032_ = v___x_1084_;
goto v___jp_1031_;
}
default: 
{
lean_object* v___x_1085_; 
v___x_1085_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7));
v___y_1032_ = v___x_1085_;
goto v___jp_1031_;
}
}
v___jp_1031_:
{
lean_object* v_data_1033_; lean_object* v_size_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1081_; 
v_data_1033_ = lean_ctor_get(v_buffer_1025_, 0);
v_size_1034_ = lean_ctor_get(v_buffer_1025_, 1);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_buffer_1025_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1036_ = v_buffer_1025_;
v_isShared_1037_ = v_isSharedCheck_1081_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_size_1034_);
lean_inc(v_data_1033_);
lean_dec(v_buffer_1025_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1081_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; uint16_t v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v_buffer_1067_; 
v___x_1038_ = lean_string_to_utf8(v___y_1032_);
lean_inc_ref(v___x_1038_);
v___x_1039_ = lean_array_push(v_data_1033_, v___x_1038_);
v___x_1040_ = lean_byte_array_size(v___x_1038_);
lean_dec_ref(v___x_1038_);
v___x_1041_ = lean_nat_add(v_size_1034_, v___x_1040_);
lean_dec(v_size_1034_);
v___x_1042_ = lean_unsigned_to_nat(1u);
v___x_1043_ = lean_mk_empty_array_with_capacity(v___x_1042_);
lean_dec_ref(v___x_1043_);
v___x_1044_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23));
v___x_1045_ = lean_array_push(v___x_1039_, v___x_1044_);
v___x_1046_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24);
v___x_1047_ = lean_nat_add(v___x_1041_, v___x_1046_);
lean_dec(v___x_1041_);
v___x_1048_ = l_Std_Http_Status_toCode(v_status_1027_);
v___x_1049_ = lean_uint16_to_nat(v___x_1048_);
v___x_1050_ = l_Nat_reprFast(v___x_1049_);
v___x_1051_ = lean_string_to_utf8(v___x_1050_);
lean_dec_ref(v___x_1050_);
lean_inc_ref(v___x_1051_);
v___x_1052_ = lean_array_push(v___x_1045_, v___x_1051_);
v___x_1053_ = lean_byte_array_size(v___x_1051_);
lean_dec_ref(v___x_1051_);
v___x_1054_ = lean_nat_add(v___x_1047_, v___x_1053_);
lean_dec(v___x_1047_);
v___x_1055_ = lean_array_push(v___x_1052_, v___x_1044_);
v___x_1056_ = lean_nat_add(v___x_1054_, v___x_1046_);
lean_dec(v___x_1054_);
v___x_1057_ = l_Std_Http_Status_reasonPhrase(v_status_1027_);
v___x_1058_ = lean_string_to_utf8(v___x_1057_);
lean_dec_ref(v___x_1057_);
lean_inc_ref(v___x_1058_);
v___x_1059_ = lean_array_push(v___x_1055_, v___x_1058_);
v___x_1060_ = lean_byte_array_size(v___x_1058_);
lean_dec_ref(v___x_1058_);
v___x_1061_ = lean_nat_add(v___x_1056_, v___x_1060_);
lean_dec(v___x_1056_);
v___x_1062_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_1063_ = lean_array_push(v___x_1059_, v___x_1062_);
v___x_1064_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3);
v___x_1065_ = lean_nat_add(v___x_1061_, v___x_1064_);
lean_dec(v___x_1061_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 1, v___x_1065_);
lean_ctor_set(v___x_1036_, 0, v___x_1063_);
v_buffer_1067_ = v___x_1036_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v___x_1065_);
v_buffer_1067_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v_buffer_1068_; lean_object* v_data_1069_; lean_object* v_size_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1079_; 
v_buffer_1068_ = l_Std_Http_Headers_fold___redArg(v_headers_1029_, v_buffer_1067_, v___f_1030_);
v_data_1069_ = lean_ctor_get(v_buffer_1068_, 0);
v_size_1070_ = lean_ctor_get(v_buffer_1068_, 1);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_buffer_1068_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1072_ = v_buffer_1068_;
v_isShared_1073_ = v_isSharedCheck_1079_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_size_1070_);
lean_inc(v_data_1069_);
lean_dec(v_buffer_1068_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1079_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1074_ = lean_array_push(v_data_1069_, v___x_1062_);
v___x_1075_ = lean_nat_add(v_size_1070_, v___x_1064_);
lean_dec(v_size_1070_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 1, v___x_1075_);
lean_ctor_set(v___x_1072_, 0, v___x_1074_);
v___x_1077_ = v___x_1072_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1074_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___boxed(lean_object* v_buffer_1086_, lean_object* v_r_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(v_buffer_1086_, v_r_1087_);
lean_dec_ref(v_r_1087_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head(uint8_t v_dir_1091_){
_start:
{
if (v_dir_1091_ == 0)
{
lean_object* v___x_1092_; 
v___x_1092_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___closed__0));
return v___x_1092_;
}
else
{
lean_object* v___x_1093_; 
v___x_1093_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___closed__1));
return v___x_1093_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___boxed(lean_object* v_dir_1094_){
_start:
{
uint8_t v_dir_boxed_1095_; lean_object* v_res_1096_; 
v_dir_boxed_1095_ = lean_unbox(v_dir_1094_);
v_res_1096_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v_dir_boxed_1095_);
return v_res_1096_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0(void){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; uint8_t v___x_1100_; lean_object* v___x_1101_; 
v___x_1097_ = l_Std_Http_Headers_empty;
v___x_1098_ = lean_box(3);
v___x_1099_ = 1;
v___x_1100_ = 8;
v___x_1101_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1101_, 0, v___x_1098_);
lean_ctor_set(v___x_1101_, 1, v___x_1097_);
lean_ctor_set_uint8(v___x_1101_, sizeof(void*)*2, v___x_1100_);
lean_ctor_set_uint8(v___x_1101_, sizeof(void*)*2 + 1, v___x_1099_);
return v___x_1101_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1(void){
_start:
{
lean_object* v___x_1102_; uint8_t v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1102_ = l_Std_Http_Headers_empty;
v___x_1103_ = 1;
v___x_1104_ = lean_box(4);
v___x_1105_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
lean_ctor_set(v___x_1105_, 1, v___x_1102_);
lean_ctor_set_uint8(v___x_1105_, sizeof(void*)*2, v___x_1103_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead(uint8_t v_dir_1106_){
_start:
{
if (v_dir_1106_ == 0)
{
lean_object* v___x_1107_; 
v___x_1107_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0, &l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0_once, _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0);
return v___x_1107_;
}
else
{
lean_object* v___x_1108_; 
v___x_1108_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1, &l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1_once, _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1);
return v___x_1108_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead___boxed(lean_object* v_dir_1109_){
_start:
{
uint8_t v_dir_boxed_1110_; lean_object* v_res_1111_; 
v_dir_boxed_1110_ = lean_unbox(v_dir_1109_);
v_res_1111_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v_dir_boxed_1110_);
return v_res_1111_;
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
