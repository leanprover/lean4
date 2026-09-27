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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___redArg___lam__0___boxed(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_splitToSubslice___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_byte_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__0_value;
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_ctorIdx(uint8_t v_x_1_){
_start:
{
if (v_x_1_ == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_boxed_5_; lean_object* v_res_6_; 
v_x_boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Std_Http_Protocol_H1_Direction_ctorIdx(v_x_boxed_5_);
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
lean_object* v___x_50_; lean_object* v___x_51_; uint8_t v___x_52_; 
v___x_50_ = l_Std_Http_Protocol_H1_Direction_ctorIdx(v_x_48_);
v___x_51_ = l_Std_Http_Protocol_H1_Direction_ctorIdx(v_y_49_);
v___x_52_ = lean_nat_dec_eq(v___x_50_, v___x_51_);
lean_dec(v___x_51_);
lean_dec(v___x_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instBEqDirection_beq___boxed(lean_object* v_x_53_, lean_object* v_y_54_){
_start:
{
uint8_t v_x_21__boxed_55_; uint8_t v_y_22__boxed_56_; uint8_t v_res_57_; lean_object* v_r_58_; 
v_x_21__boxed_55_ = lean_unbox(v_x_53_);
v_y_22__boxed_56_ = lean_unbox(v_y_54_);
v_res_57_ = l_Std_Http_Protocol_H1_instBEqDirection_beq(v_x_21__boxed_55_, v_y_22__boxed_56_);
v_r_58_ = lean_box(v_res_57_);
return v_r_58_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Direction_swap(uint8_t v_x_61_){
_start:
{
if (v_x_61_ == 0)
{
uint8_t v___x_62_; 
v___x_62_ = 1;
return v___x_62_;
}
else
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_swap___boxed(lean_object* v_x_64_){
_start:
{
uint8_t v_x_18__boxed_65_; uint8_t v_res_66_; lean_object* v_r_67_; 
v_x_18__boxed_65_ = lean_unbox(v_x_64_);
v_res_66_ = l_Std_Http_Protocol_H1_Direction_swap(v_x_18__boxed_65_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_headers(uint8_t v_dir_68_, lean_object* v_m_69_){
_start:
{
lean_object* v_headers_70_; 
v_headers_70_ = lean_ctor_get(v_m_69_, 1);
lean_inc_ref(v_headers_70_);
return v_headers_70_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_headers___boxed(lean_object* v_dir_71_, lean_object* v_m_72_){
_start:
{
uint8_t v_dir_boxed_73_; lean_object* v_res_74_; 
v_dir_boxed_73_ = lean_unbox(v_dir_71_);
v_res_74_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_boxed_73_, v_m_72_);
lean_dec(v_m_72_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_setHeaders(uint8_t v_dir_75_, lean_object* v_m_76_, lean_object* v_headers_77_){
_start:
{
if (v_dir_75_ == 0)
{
uint8_t v_method_78_; uint8_t v_version_79_; lean_object* v_uri_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_87_; 
v_method_78_ = lean_ctor_get_uint8(v_m_76_, sizeof(void*)*2);
v_version_79_ = lean_ctor_get_uint8(v_m_76_, sizeof(void*)*2 + 1);
v_uri_80_ = lean_ctor_get(v_m_76_, 0);
v_isSharedCheck_87_ = !lean_is_exclusive(v_m_76_);
if (v_isSharedCheck_87_ == 0)
{
lean_object* v_unused_88_; 
v_unused_88_ = lean_ctor_get(v_m_76_, 1);
lean_dec(v_unused_88_);
v___x_82_ = v_m_76_;
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_uri_80_);
lean_dec(v_m_76_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_85_; 
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 1, v_headers_77_);
v___x_85_ = v___x_82_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_uri_80_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v_headers_77_);
lean_ctor_set_uint8(v_reuseFailAlloc_86_, sizeof(void*)*2, v_method_78_);
lean_ctor_set_uint8(v_reuseFailAlloc_86_, sizeof(void*)*2 + 1, v_version_79_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
else
{
lean_object* v_status_89_; uint8_t v_version_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_97_; 
v_status_89_ = lean_ctor_get(v_m_76_, 0);
v_version_90_ = lean_ctor_get_uint8(v_m_76_, sizeof(void*)*2);
v_isSharedCheck_97_ = !lean_is_exclusive(v_m_76_);
if (v_isSharedCheck_97_ == 0)
{
lean_object* v_unused_98_; 
v_unused_98_ = lean_ctor_get(v_m_76_, 1);
lean_dec(v_unused_98_);
v___x_92_ = v_m_76_;
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_status_89_);
lean_dec(v_m_76_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_95_; 
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 1, v_headers_77_);
v___x_95_ = v___x_92_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_status_89_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v_headers_77_);
lean_ctor_set_uint8(v_reuseFailAlloc_96_, sizeof(void*)*2, v_version_90_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_setHeaders___boxed(lean_object* v_dir_99_, lean_object* v_m_100_, lean_object* v_headers_101_){
_start:
{
uint8_t v_dir_boxed_102_; lean_object* v_res_103_; 
v_dir_boxed_102_ = lean_unbox(v_dir_99_);
v_res_103_ = l_Std_Http_Protocol_H1_Message_Head_setHeaders(v_dir_boxed_102_, v_m_100_, v_headers_101_);
return v_res_103_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Message_Head_version(uint8_t v_dir_104_, lean_object* v_m_105_){
_start:
{
if (v_dir_104_ == 0)
{
uint8_t v_version_106_; 
v_version_106_ = lean_ctor_get_uint8(v_m_105_, sizeof(void*)*2 + 1);
return v_version_106_;
}
else
{
uint8_t v_version_107_; 
v_version_107_ = lean_ctor_get_uint8(v_m_105_, sizeof(void*)*2);
return v_version_107_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_version___boxed(lean_object* v_dir_108_, lean_object* v_m_109_){
_start:
{
uint8_t v_dir_boxed_110_; uint8_t v_res_111_; lean_object* v_r_112_; 
v_dir_boxed_110_ = lean_unbox(v_dir_108_);
v_res_111_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_boxed_110_, v_m_109_);
lean_dec(v_m_109_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg(lean_object* v___x_113_, lean_object* v___x_114_, size_t v_sz_115_, size_t v_i_116_, lean_object* v_bs_117_){
_start:
{
uint8_t v___x_118_; 
v___x_118_ = lean_usize_dec_lt(v_i_116_, v_sz_115_);
if (v___x_118_ == 0)
{
return v_bs_117_;
}
else
{
lean_object* v_entries_119_; lean_object* v___x_120_; lean_object* v_bs_x27_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v_snd_125_; size_t v___x_126_; size_t v___x_127_; lean_object* v___x_128_; 
v_entries_119_ = lean_ctor_get(v___x_113_, 0);
v___x_120_ = lean_unsigned_to_nat(0u);
v_bs_x27_121_ = lean_array_uset(v_bs_117_, v_i_116_, v___x_120_);
v___x_122_ = lean_usize_to_nat(v_i_116_);
v___x_123_ = lean_array_fget_borrowed(v___x_114_, v___x_122_);
lean_dec(v___x_122_);
v___x_124_ = lean_array_fget_borrowed(v_entries_119_, v___x_123_);
v_snd_125_ = lean_ctor_get(v___x_124_, 1);
v___x_126_ = ((size_t)1ULL);
v___x_127_ = lean_usize_add(v_i_116_, v___x_126_);
lean_inc(v_snd_125_);
v___x_128_ = lean_array_uset(v_bs_x27_121_, v_i_116_, v_snd_125_);
v_i_116_ = v___x_127_;
v_bs_117_ = v___x_128_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg___boxed(lean_object* v___x_130_, lean_object* v___x_131_, lean_object* v_sz_132_, lean_object* v_i_133_, lean_object* v_bs_134_){
_start:
{
size_t v_sz_boxed_135_; size_t v_i_boxed_136_; lean_object* v_res_137_; 
v_sz_boxed_135_ = lean_unbox_usize(v_sz_132_);
lean_dec(v_sz_132_);
v_i_boxed_136_ = lean_unbox_usize(v_i_133_);
lean_dec(v_i_133_);
v_res_137_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg(v___x_130_, v___x_131_, v_sz_boxed_135_, v_i_boxed_136_, v_bs_134_);
lean_dec_ref(v___x_131_);
lean_dec_ref(v___x_130_);
return v_res_137_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(lean_object* v_a_138_, lean_object* v_x_139_){
_start:
{
if (lean_obj_tag(v_x_139_) == 0)
{
uint8_t v___x_140_; 
v___x_140_ = 0;
return v___x_140_;
}
else
{
lean_object* v_key_141_; lean_object* v_tail_142_; uint8_t v___x_143_; 
v_key_141_ = lean_ctor_get(v_x_139_, 0);
v_tail_142_ = lean_ctor_get(v_x_139_, 2);
v___x_143_ = lean_string_dec_eq(v_key_141_, v_a_138_);
if (v___x_143_ == 0)
{
v_x_139_ = v_tail_142_;
goto _start;
}
else
{
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg___boxed(lean_object* v_a_145_, lean_object* v_x_146_){
_start:
{
uint8_t v_res_147_; lean_object* v_r_148_; 
v_res_147_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_a_145_, v_x_146_);
lean_dec(v_x_146_);
lean_dec_ref(v_a_145_);
v_r_148_ = lean_box(v_res_147_);
return v_r_148_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(lean_object* v_m_149_, lean_object* v_a_150_){
_start:
{
lean_object* v_buckets_151_; lean_object* v___x_152_; uint64_t v___x_153_; uint64_t v___x_154_; uint64_t v___x_155_; uint64_t v_fold_156_; uint64_t v___x_157_; uint64_t v___x_158_; uint64_t v___x_159_; size_t v___x_160_; size_t v___x_161_; size_t v___x_162_; size_t v___x_163_; size_t v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; 
v_buckets_151_ = lean_ctor_get(v_m_149_, 1);
v___x_152_ = lean_array_get_size(v_buckets_151_);
v___x_153_ = lean_string_hash(v_a_150_);
v___x_154_ = 32ULL;
v___x_155_ = lean_uint64_shift_right(v___x_153_, v___x_154_);
v_fold_156_ = lean_uint64_xor(v___x_153_, v___x_155_);
v___x_157_ = 16ULL;
v___x_158_ = lean_uint64_shift_right(v_fold_156_, v___x_157_);
v___x_159_ = lean_uint64_xor(v_fold_156_, v___x_158_);
v___x_160_ = lean_uint64_to_usize(v___x_159_);
v___x_161_ = lean_usize_of_nat(v___x_152_);
v___x_162_ = ((size_t)1ULL);
v___x_163_ = lean_usize_sub(v___x_161_, v___x_162_);
v___x_164_ = lean_usize_land(v___x_160_, v___x_163_);
v___x_165_ = lean_array_uget_borrowed(v_buckets_151_, v___x_164_);
v___x_166_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_a_150_, v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg___boxed(lean_object* v_m_167_, lean_object* v_a_168_){
_start:
{
uint8_t v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_m_167_, v_a_168_);
lean_dec_ref(v_a_168_);
lean_dec_ref(v_m_167_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2___redArg(lean_object* v_a_171_, lean_object* v_x_172_){
_start:
{
lean_object* v_key_173_; lean_object* v_value_174_; lean_object* v_tail_175_; uint8_t v___x_176_; 
v_key_173_ = lean_ctor_get(v_x_172_, 0);
v_value_174_ = lean_ctor_get(v_x_172_, 1);
v_tail_175_ = lean_ctor_get(v_x_172_, 2);
v___x_176_ = lean_string_dec_eq(v_key_173_, v_a_171_);
if (v___x_176_ == 0)
{
v_x_172_ = v_tail_175_;
goto _start;
}
else
{
lean_inc(v_value_174_);
return v_value_174_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2___redArg___boxed(lean_object* v_a_178_, lean_object* v_x_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2___redArg(v_a_178_, v_x_179_);
lean_dec(v_x_179_);
lean_dec_ref(v_a_178_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(lean_object* v_m_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_buckets_183_; lean_object* v___x_184_; uint64_t v___x_185_; uint64_t v___x_186_; uint64_t v___x_187_; uint64_t v_fold_188_; uint64_t v___x_189_; uint64_t v___x_190_; uint64_t v___x_191_; size_t v___x_192_; size_t v___x_193_; size_t v___x_194_; size_t v___x_195_; size_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_buckets_183_ = lean_ctor_get(v_m_181_, 1);
v___x_184_ = lean_array_get_size(v_buckets_183_);
v___x_185_ = lean_string_hash(v_a_182_);
v___x_186_ = 32ULL;
v___x_187_ = lean_uint64_shift_right(v___x_185_, v___x_186_);
v_fold_188_ = lean_uint64_xor(v___x_185_, v___x_187_);
v___x_189_ = 16ULL;
v___x_190_ = lean_uint64_shift_right(v_fold_188_, v___x_189_);
v___x_191_ = lean_uint64_xor(v_fold_188_, v___x_190_);
v___x_192_ = lean_uint64_to_usize(v___x_191_);
v___x_193_ = lean_usize_of_nat(v___x_184_);
v___x_194_ = ((size_t)1ULL);
v___x_195_ = lean_usize_sub(v___x_193_, v___x_194_);
v___x_196_ = lean_usize_land(v___x_192_, v___x_195_);
v___x_197_ = lean_array_uget_borrowed(v_buckets_183_, v___x_196_);
v___x_198_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2___redArg(v_a_182_, v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg___boxed(lean_object* v_m_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v_m_199_, v_a_200_);
lean_dec_ref(v_a_200_);
lean_dec_ref(v_m_199_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize(uint8_t v_dir_208_, lean_object* v_message_209_, uint8_t v_allowEOFBody_210_){
_start:
{
lean_object* v___x_211_; lean_object* v___y_213_; lean_object* v_indexes_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_211_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_208_, v_message_209_);
v_indexes_264_ = lean_ctor_get(v___x_211_, 1);
v___x_265_ = l_Std_Http_Header_Name_contentLength;
v___x_266_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_264_, v___x_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; 
v___x_267_ = lean_box(0);
v___y_213_ = v___x_267_;
goto v___jp_212_;
}
else
{
lean_object* v___x_268_; size_t v_sz_269_; size_t v___x_270_; lean_object* v_entries_271_; lean_object* v___x_272_; 
v___x_268_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v_indexes_264_, v___x_265_);
v_sz_269_ = lean_array_size(v___x_268_);
v___x_270_ = ((size_t)0ULL);
lean_inc(v___x_268_);
v_entries_271_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg(v___x_211_, v___x_268_, v_sz_269_, v___x_270_, v___x_268_);
lean_dec(v___x_268_);
v___x_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_272_, 0, v_entries_271_);
v___y_213_ = v___x_272_;
goto v___jp_212_;
}
v___jp_212_:
{
lean_object* v_indexes_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v_indexes_214_ = lean_ctor_get(v___x_211_, 1);
v___x_215_ = l_Std_Http_Header_Name_transferEncoding;
v___x_216_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_214_, v___x_215_);
if (v___x_216_ == 0)
{
lean_dec_ref(v___x_211_);
if (lean_obj_tag(v___y_213_) == 0)
{
if (v_allowEOFBody_210_ == 0)
{
lean_object* v___x_217_; 
v___x_217_ = lean_box(0);
return v___x_217_;
}
else
{
lean_object* v___x_218_; 
v___x_218_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1));
return v___x_218_;
}
}
else
{
lean_object* v_val_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_242_; 
v_val_219_ = lean_ctor_get(v___y_213_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___y_213_);
if (v_isSharedCheck_242_ == 0)
{
v___x_221_ = v___y_213_;
v_isShared_222_ = v_isSharedCheck_242_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_val_219_);
lean_dec(v___y_213_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_242_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_223_ = lean_array_get_size(v_val_219_);
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = lean_nat_dec_eq(v___x_223_, v___x_224_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; 
lean_del_object(v___x_221_);
lean_dec(v_val_219_);
v___x_226_ = lean_box(0);
return v___x_226_;
}
else
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = lean_array_fget(v_val_219_, v___x_227_);
lean_dec(v_val_219_);
v___x_229_ = l_Std_Http_Header_ContentLength_parse(v___x_228_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v___x_230_; 
lean_del_object(v___x_221_);
v___x_230_ = lean_box(0);
return v___x_230_;
}
else
{
lean_object* v_val_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_241_; 
v_val_231_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_241_ == 0)
{
v___x_233_ = v___x_229_;
v_isShared_234_ = v_isSharedCheck_241_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_val_231_);
lean_dec(v___x_229_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_241_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v_val_231_);
v___x_236_ = v___x_221_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_val_231_);
v___x_236_ = v_reuseFailAlloc_240_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_238_; 
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v___x_236_);
v___x_238_ = v___x_233_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
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
lean_object* v___x_243_; size_t v_sz_244_; size_t v___x_245_; lean_object* v_entries_246_; lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_243_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v_indexes_214_, v___x_215_);
v_sz_244_ = lean_array_size(v___x_243_);
v___x_245_ = ((size_t)0ULL);
lean_inc(v___x_243_);
v_entries_246_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg(v___x_211_, v___x_243_, v_sz_244_, v___x_245_, v___x_243_);
lean_dec(v___x_243_);
lean_dec_ref(v___x_211_);
v___x_247_ = lean_array_get_size(v_entries_246_);
v___x_248_ = lean_unsigned_to_nat(1u);
v___x_249_ = lean_nat_dec_eq(v___x_247_, v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; 
lean_dec_ref(v_entries_246_);
lean_dec(v___y_213_);
v___x_250_ = lean_box(0);
return v___x_250_;
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v_te_253_; 
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = lean_array_fget(v_entries_246_, v___x_251_);
lean_dec_ref(v_entries_246_);
v_te_253_ = l_Std_Http_Header_TransferEncoding_parse(v___x_252_);
if (lean_obj_tag(v_te_253_) == 0)
{
lean_object* v___x_254_; 
lean_dec(v___y_213_);
v___x_254_ = lean_box(0);
return v___x_254_;
}
else
{
lean_object* v_val_255_; uint8_t v___x_256_; 
v_val_255_ = lean_ctor_get(v_te_253_, 0);
lean_inc(v_val_255_);
lean_dec_ref_known(v_te_253_, 1);
v___x_256_ = l_Std_Http_Header_TransferEncoding_isChunked(v_val_255_);
lean_dec(v_val_255_);
if (v___x_256_ == 1)
{
if (lean_obj_tag(v___y_213_) == 0)
{
uint8_t v___x_257_; uint8_t v___x_258_; uint8_t v___x_259_; 
v___x_257_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_208_, v_message_209_);
v___x_258_ = 0;
v___x_259_ = l_Std_Http_instBEqVersion_beq(v___x_257_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; 
v___x_260_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__2));
return v___x_260_;
}
else
{
lean_object* v___x_261_; 
v___x_261_ = lean_box(0);
return v___x_261_;
}
}
else
{
lean_object* v___x_262_; 
lean_dec(v___y_213_);
v___x_262_ = lean_box(0);
return v___x_262_;
}
}
else
{
lean_object* v___x_263_; 
lean_dec(v___y_213_);
v___x_263_ = lean_box(0);
return v___x_263_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize___boxed(lean_object* v_dir_273_, lean_object* v_message_274_, lean_object* v_allowEOFBody_275_){
_start:
{
uint8_t v_dir_boxed_276_; uint8_t v_allowEOFBody_boxed_277_; lean_object* v_res_278_; 
v_dir_boxed_276_ = lean_unbox(v_dir_273_);
v_allowEOFBody_boxed_277_ = lean_unbox(v_allowEOFBody_275_);
v_res_278_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v_dir_boxed_276_, v_message_274_, v_allowEOFBody_boxed_277_);
lean_dec(v_message_274_);
return v_res_278_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(lean_object* v_00_u03b2_279_, lean_object* v_m_280_, lean_object* v_a_281_){
_start:
{
uint8_t v___x_282_; 
v___x_282_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_m_280_, v_a_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___boxed(lean_object* v_00_u03b2_283_, lean_object* v_m_284_, lean_object* v_a_285_){
_start:
{
uint8_t v_res_286_; lean_object* v_r_287_; 
v_res_286_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(v_00_u03b2_283_, v_m_284_, v_a_285_);
lean_dec_ref(v_a_285_);
lean_dec_ref(v_m_284_);
v_r_287_ = lean_box(v_res_286_);
return v_r_287_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(lean_object* v_00_u03b2_288_, lean_object* v_m_289_, lean_object* v_a_290_, lean_object* v_hma_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v_m_289_, v_a_290_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___boxed(lean_object* v_00_u03b2_293_, lean_object* v_m_294_, lean_object* v_a_295_, lean_object* v_hma_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(v_00_u03b2_293_, v_m_294_, v_a_295_, v_hma_296_);
lean_dec_ref(v_a_295_);
lean_dec_ref(v_m_294_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2(lean_object* v___x_298_, lean_object* v___x_299_, lean_object* v_as_300_, size_t v_sz_301_, size_t v_i_302_, lean_object* v_bs_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg(v___x_298_, v___x_299_, v_sz_301_, v_i_302_, v_bs_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___boxed(lean_object* v___x_305_, lean_object* v___x_306_, lean_object* v_as_307_, lean_object* v_sz_308_, lean_object* v_i_309_, lean_object* v_bs_310_){
_start:
{
size_t v_sz_boxed_311_; size_t v_i_boxed_312_; lean_object* v_res_313_; 
v_sz_boxed_311_ = lean_unbox_usize(v_sz_308_);
lean_dec(v_sz_308_);
v_i_boxed_312_ = lean_unbox_usize(v_i_309_);
lean_dec(v_i_309_);
v_res_313_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2(v___x_305_, v___x_306_, v_as_307_, v_sz_boxed_311_, v_i_boxed_312_, v_bs_310_);
lean_dec_ref(v_as_307_);
lean_dec_ref(v___x_306_);
lean_dec_ref(v___x_305_);
return v_res_313_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0(lean_object* v_00_u03b2_314_, lean_object* v_a_315_, lean_object* v_x_316_){
_start:
{
uint8_t v___x_317_; 
v___x_317_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_a_315_, v_x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_318_, lean_object* v_a_319_, lean_object* v_x_320_){
_start:
{
uint8_t v_res_321_; lean_object* v_r_322_; 
v_res_321_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0(v_00_u03b2_318_, v_a_319_, v_x_320_);
lean_dec(v_x_320_);
lean_dec_ref(v_a_319_);
v_r_322_ = lean_box(v_res_321_);
return v_r_322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2(lean_object* v_00_u03b2_323_, lean_object* v_a_324_, lean_object* v_x_325_, lean_object* v_x_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2___redArg(v_a_324_, v_x_325_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2___boxed(lean_object* v_00_u03b2_328_, lean_object* v_a_329_, lean_object* v_x_330_, lean_object* v_x_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2(v_00_u03b2_328_, v_a_329_, v_x_330_, v_x_331_);
lean_dec(v_x_330_);
lean_dec_ref(v_a_329_);
return v_res_332_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(lean_object* v_as_334_, size_t v_i_335_, size_t v_stop_336_){
_start:
{
uint8_t v___x_337_; 
v___x_337_ = lean_usize_dec_eq(v_i_335_, v_stop_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_338_ = lean_array_uget_borrowed(v_as_334_, v_i_335_);
v___x_339_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___closed__0));
v___x_340_ = lean_string_dec_eq(v___x_338_, v___x_339_);
if (v___x_340_ == 0)
{
size_t v___x_341_; size_t v___x_342_; 
v___x_341_ = ((size_t)1ULL);
v___x_342_ = lean_usize_add(v_i_335_, v___x_341_);
v_i_335_ = v___x_342_;
goto _start;
}
else
{
return v___x_340_;
}
}
else
{
uint8_t v___x_344_; 
v___x_344_ = 0;
return v___x_344_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___boxed(lean_object* v_as_345_, lean_object* v_i_346_, lean_object* v_stop_347_){
_start:
{
size_t v_i_boxed_348_; size_t v_stop_boxed_349_; uint8_t v_res_350_; lean_object* v_r_351_; 
v_i_boxed_348_ = lean_unbox_usize(v_i_346_);
lean_dec(v_i_346_);
v_stop_boxed_349_ = lean_unbox_usize(v_stop_347_);
lean_dec(v_stop_347_);
v_res_350_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(v_as_345_, v_i_boxed_348_, v_stop_boxed_349_);
lean_dec_ref(v_as_345_);
v_r_351_ = lean_box(v_res_350_);
return v_r_351_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(lean_object* v_as_353_, size_t v_i_354_, size_t v_stop_355_){
_start:
{
uint8_t v___x_356_; 
v___x_356_ = lean_usize_dec_eq(v_i_354_, v_stop_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_357_ = lean_array_uget_borrowed(v_as_353_, v_i_354_);
v___x_358_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___closed__0));
v___x_359_ = lean_string_dec_eq(v___x_357_, v___x_358_);
if (v___x_359_ == 0)
{
size_t v___x_360_; size_t v___x_361_; 
v___x_360_ = ((size_t)1ULL);
v___x_361_ = lean_usize_add(v_i_354_, v___x_360_);
v_i_354_ = v___x_361_;
goto _start;
}
else
{
return v___x_359_;
}
}
else
{
uint8_t v___x_363_; 
v___x_363_ = 0;
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___boxed(lean_object* v_as_364_, lean_object* v_i_365_, lean_object* v_stop_366_){
_start:
{
size_t v_i_boxed_367_; size_t v_stop_boxed_368_; uint8_t v_res_369_; lean_object* v_r_370_; 
v_i_boxed_367_ = lean_unbox_usize(v_i_365_);
lean_dec(v_i_365_);
v_stop_boxed_368_ = lean_unbox_usize(v_stop_366_);
lean_dec(v_stop_366_);
v_res_369_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(v_as_364_, v_i_boxed_367_, v_stop_boxed_368_);
lean_dec_ref(v_as_364_);
v_r_370_ = lean_box(v_res_369_);
return v_r_370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(lean_object* v_as_371_, size_t v_i_372_, size_t v_stop_373_, lean_object* v_b_374_){
_start:
{
lean_object* v___y_376_; uint8_t v___x_380_; 
v___x_380_ = lean_usize_dec_eq(v_i_372_, v_stop_373_);
if (v___x_380_ == 0)
{
if (lean_obj_tag(v_b_374_) == 0)
{
v___y_376_ = v_b_374_;
goto v___jp_375_;
}
else
{
lean_object* v_val_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v_val_381_ = lean_ctor_get(v_b_374_, 0);
lean_inc(v_val_381_);
lean_dec_ref_known(v_b_374_, 1);
v___x_382_ = lean_array_uget_borrowed(v_as_371_, v_i_372_);
lean_inc(v___x_382_);
v___x_383_ = l_Std_Http_Header_Connection_parse(v___x_382_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v___x_384_; 
lean_dec(v_val_381_);
v___x_384_ = lean_box(0);
v___y_376_ = v___x_384_;
goto v___jp_375_;
}
else
{
lean_object* v_val_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_393_; 
v_val_385_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_393_ == 0)
{
v___x_387_ = v___x_383_;
v_isShared_388_ = v_isSharedCheck_393_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_val_385_);
lean_dec(v___x_383_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_393_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; lean_object* v___x_391_; 
v___x_389_ = l_Array_append___redArg(v_val_381_, v_val_385_);
lean_dec(v_val_385_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v___x_389_);
v___x_391_ = v___x_387_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___x_389_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
v___y_376_ = v___x_391_;
goto v___jp_375_;
}
}
}
}
}
else
{
return v_b_374_;
}
v___jp_375_:
{
size_t v___x_377_; size_t v___x_378_; 
v___x_377_ = ((size_t)1ULL);
v___x_378_ = lean_usize_add(v_i_372_, v___x_377_);
v_i_372_ = v___x_378_;
v_b_374_ = v___y_376_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2___boxed(lean_object* v_as_394_, lean_object* v_i_395_, lean_object* v_stop_396_, lean_object* v_b_397_){
_start:
{
size_t v_i_boxed_398_; size_t v_stop_boxed_399_; lean_object* v_res_400_; 
v_i_boxed_398_ = lean_unbox_usize(v_i_395_);
lean_dec(v_i_395_);
v_stop_boxed_399_ = lean_unbox_usize(v_stop_396_);
lean_dec(v_stop_396_);
v_res_400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_as_394_, v_i_boxed_398_, v_stop_boxed_399_, v_b_397_);
lean_dec_ref(v_as_394_);
return v_res_400_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(uint8_t v_dir_405_, lean_object* v_message_406_){
_start:
{
lean_object* v_val_408_; lean_object* v___y_426_; lean_object* v___x_429_; lean_object* v_indexes_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_429_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_405_, v_message_406_);
v_indexes_430_ = lean_ctor_get(v___x_429_, 1);
v___x_431_ = l_Std_Http_Header_Name_connection;
v___x_432_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_430_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; 
lean_dec_ref(v___x_429_);
v___x_433_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0));
v_val_408_ = v___x_433_;
goto v___jp_407_;
}
else
{
lean_object* v___x_434_; size_t v_sz_435_; size_t v___x_436_; lean_object* v_entries_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_434_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v_indexes_430_, v___x_431_);
v_sz_435_ = lean_array_size(v___x_434_);
v___x_436_ = ((size_t)0ULL);
lean_inc(v___x_434_);
v_entries_437_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg(v___x_429_, v___x_434_, v_sz_435_, v___x_436_, v___x_434_);
lean_dec(v___x_434_);
lean_dec_ref(v___x_429_);
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0));
v___x_440_ = lean_array_get_size(v_entries_437_);
v___x_441_ = lean_nat_dec_lt(v___x_438_, v___x_440_);
if (v___x_441_ == 0)
{
lean_dec_ref(v_entries_437_);
v_val_408_ = v___x_439_;
goto v___jp_407_;
}
else
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__1));
v___x_443_ = lean_nat_dec_le(v___x_440_, v___x_440_);
if (v___x_443_ == 0)
{
if (v___x_441_ == 0)
{
lean_dec_ref(v_entries_437_);
v_val_408_ = v___x_439_;
goto v___jp_407_;
}
else
{
size_t v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_usize_of_nat(v___x_440_);
v___x_445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_entries_437_, v___x_436_, v___x_444_, v___x_442_);
lean_dec_ref(v_entries_437_);
v___y_426_ = v___x_445_;
goto v___jp_425_;
}
}
else
{
size_t v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_usize_of_nat(v___x_440_);
v___x_447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_entries_437_, v___x_436_, v___x_446_, v___x_442_);
lean_dec_ref(v_entries_437_);
v___y_426_ = v___x_447_;
goto v___jp_425_;
}
}
}
v___jp_407_:
{
uint8_t v___x_409_; uint8_t v___x_410_; uint8_t v___x_411_; 
v___x_409_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_405_, v_message_406_);
v___x_410_ = 1;
v___x_411_ = l_Std_Http_instBEqVersion_beq(v___x_409_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = lean_array_get_size(v_val_408_);
v___x_414_ = lean_nat_dec_lt(v___x_412_, v___x_413_);
if (v___x_414_ == 0)
{
lean_dec_ref(v_val_408_);
return v___x_414_;
}
else
{
if (v___x_414_ == 0)
{
lean_dec_ref(v_val_408_);
return v___x_414_;
}
else
{
size_t v___x_415_; size_t v___x_416_; uint8_t v___x_417_; 
v___x_415_ = ((size_t)0ULL);
v___x_416_ = lean_usize_of_nat(v___x_413_);
v___x_417_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(v_val_408_, v___x_415_, v___x_416_);
lean_dec_ref(v_val_408_);
return v___x_417_;
}
}
}
else
{
lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = lean_array_get_size(v_val_408_);
v___x_420_ = lean_nat_dec_lt(v___x_418_, v___x_419_);
if (v___x_420_ == 0)
{
lean_dec_ref(v_val_408_);
return v___x_411_;
}
else
{
if (v___x_420_ == 0)
{
lean_dec_ref(v_val_408_);
return v___x_411_;
}
else
{
size_t v___x_421_; size_t v___x_422_; uint8_t v___x_423_; 
v___x_421_ = ((size_t)0ULL);
v___x_422_ = lean_usize_of_nat(v___x_419_);
v___x_423_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(v_val_408_, v___x_421_, v___x_422_);
lean_dec_ref(v_val_408_);
if (v___x_423_ == 0)
{
return v___x_411_;
}
else
{
uint8_t v___x_424_; 
v___x_424_ = 0;
return v___x_424_;
}
}
}
}
}
v___jp_425_:
{
if (lean_obj_tag(v___y_426_) == 0)
{
uint8_t v___x_427_; 
v___x_427_ = 0;
return v___x_427_;
}
else
{
lean_object* v_val_428_; 
v_val_428_ = lean_ctor_get(v___y_426_, 0);
lean_inc(v_val_428_);
lean_dec_ref_known(v___y_426_, 1);
v_val_408_ = v_val_428_;
goto v___jp_407_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___boxed(lean_object* v_dir_448_, lean_object* v_message_449_){
_start:
{
uint8_t v_dir_boxed_450_; uint8_t v_res_451_; lean_object* v_r_452_; 
v_dir_boxed_450_ = lean_unbox(v_dir_448_);
v_res_451_ = l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(v_dir_boxed_450_, v_message_449_);
lean_dec(v_message_449_);
v_r_452_ = lean_box(v_res_451_);
return v_r_452_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1___redArg(lean_object* v_x_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Std_Http_Request_instReprHead_repr___redArg(v_x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1(lean_object* v_x_455_, lean_object* v_prec_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Std_Http_Request_instReprHead_repr___redArg(v_x_455_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1___boxed(lean_object* v_x_458_, lean_object* v_prec_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Std_Http_Protocol_H1_instReprHead___aux__1(v_x_458_, v_prec_459_);
lean_dec(v_prec_459_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3___redArg(lean_object* v_x_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Std_Http_Response_instReprHead_repr___redArg(v_x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3(lean_object* v_x_463_, lean_object* v_prec_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Std_Http_Response_instReprHead_repr___redArg(v_x_463_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3___boxed(lean_object* v_x_466_, lean_object* v_prec_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Std_Http_Protocol_H1_instReprHead___aux__3(v_x_466_, v_prec_467_);
lean_dec(v_prec_467_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead(uint8_t v_dir_471_){
_start:
{
if (v_dir_471_ == 0)
{
lean_object* v___x_472_; 
v___x_472_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprHead___closed__0));
return v___x_472_;
}
else
{
lean_object* v___x_473_; 
v___x_473_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprHead___closed__1));
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___boxed(lean_object* v_dir_474_){
_start:
{
uint8_t v_dir_boxed_475_; lean_object* v_res_476_; 
v_dir_boxed_475_ = lean_unbox(v_dir_474_);
v_res_476_ = l_Std_Http_Protocol_H1_instReprHead(v_dir_boxed_475_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__0(lean_object* v_x_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = lean_string_from_utf8_unchecked(v_x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1(lean_object* v___x_479_, lean_object* v___x_480_, lean_object* v___x_481_, lean_object* v_name_482_, lean_object* v___x_483_, uint32_t v___x_484_, lean_object* v___x_485_, lean_object* v_it_486_, lean_object* v_acc_487_, lean_object* v_hP_488_, lean_object* v_recur_489_){
_start:
{
lean_object* v_it_491_; lean_object* v_out_492_; lean_object* v___y_508_; lean_object* v___y_509_; uint32_t v___y_510_; uint8_t v___y_511_; lean_object* v_it_517_; lean_object* v_startInclusive_518_; lean_object* v_endExclusive_519_; 
if (lean_obj_tag(v_it_486_) == 0)
{
lean_object* v_currPos_526_; lean_object* v_searcher_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_549_; 
v_currPos_526_ = lean_ctor_get(v_it_486_, 0);
v_searcher_527_ = lean_ctor_get(v_it_486_, 1);
v_isSharedCheck_549_ = !lean_is_exclusive(v_it_486_);
if (v_isSharedCheck_549_ == 0)
{
v___x_529_ = v_it_486_;
v_isShared_530_ = v_isSharedCheck_549_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_searcher_527_);
lean_inc(v_currPos_526_);
lean_dec(v_it_486_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_549_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
uint8_t v_decide_531_; 
v_decide_531_ = lean_nat_dec_eq(v_searcher_527_, v___x_483_);
if (v_decide_531_ == 0)
{
uint32_t v___x_532_; uint8_t v___x_533_; 
lean_dec(v___x_483_);
v___x_532_ = lean_string_utf8_get_fast(v_name_482_, v_searcher_527_);
v___x_533_ = lean_uint32_dec_eq(v___x_532_, v___x_484_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_534_ = lean_string_utf8_next_fast(v_name_482_, v_searcher_527_);
lean_dec(v_searcher_527_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 1, v___x_534_);
v___x_536_ = v___x_529_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_currPos_526_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v___x_534_);
v___x_536_ = v_reuseFailAlloc_538_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_537_; 
v___x_537_ = lean_apply_4(v_recur_489_, v___x_536_, v_acc_487_, lean_box(0), lean_box(0));
return v___x_537_;
}
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v_slice_542_; lean_object* v_nextIt_544_; 
v___x_539_ = lean_string_utf8_next_fast(v_name_482_, v_searcher_527_);
v___x_540_ = lean_nat_sub(v___x_539_, v_searcher_527_);
v___x_541_ = lean_nat_add(v_searcher_527_, v___x_540_);
lean_dec(v___x_540_);
v_slice_542_ = l_String_Slice_subslice_x21(v___x_485_, v_currPos_526_, v_searcher_527_);
lean_inc(v___x_541_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 1, v___x_541_);
lean_ctor_set(v___x_529_, 0, v___x_541_);
v_nextIt_544_ = v___x_529_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v___x_541_);
v_nextIt_544_ = v_reuseFailAlloc_547_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v_startInclusive_545_; lean_object* v_endExclusive_546_; 
v_startInclusive_545_ = lean_ctor_get(v_slice_542_, 0);
lean_inc(v_startInclusive_545_);
v_endExclusive_546_ = lean_ctor_get(v_slice_542_, 1);
lean_inc(v_endExclusive_546_);
lean_dec_ref(v_slice_542_);
v_it_517_ = v_nextIt_544_;
v_startInclusive_518_ = v_startInclusive_545_;
v_endExclusive_519_ = v_endExclusive_546_;
goto v___jp_516_;
}
}
}
else
{
lean_object* v___x_548_; 
lean_del_object(v___x_529_);
lean_dec(v_searcher_527_);
v___x_548_ = lean_box(1);
v_it_517_ = v___x_548_;
v_startInclusive_518_ = v_currPos_526_;
v_endExclusive_519_ = v___x_483_;
goto v___jp_516_;
}
}
}
else
{
lean_dec_ref(v_recur_489_);
lean_dec(v___x_483_);
return v_acc_487_;
}
v___jp_490_:
{
if (lean_obj_tag(v_acc_487_) == 0)
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_493_, 0, v_out_492_);
v___x_494_ = lean_apply_4(v_recur_489_, v_it_491_, v___x_493_, lean_box(0), lean_box(0));
return v___x_494_;
}
else
{
lean_object* v_val_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_506_; 
v_val_495_ = lean_ctor_get(v_acc_487_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v_acc_487_);
if (v_isSharedCheck_506_ == 0)
{
v___x_497_ = v_acc_487_;
v_isShared_498_ = v_isSharedCheck_506_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_val_495_);
lean_dec(v_acc_487_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_506_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_499_ = lean_string_utf8_extract_fast(v___x_479_, v___x_480_, v___x_481_);
v___x_500_ = lean_string_append(v_val_495_, v___x_499_);
lean_dec_ref(v___x_499_);
v___x_501_ = lean_string_append(v___x_500_, v_out_492_);
lean_dec_ref(v_out_492_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_501_);
v___x_503_ = v___x_497_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_501_);
v___x_503_ = v_reuseFailAlloc_505_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; 
v___x_504_ = lean_apply_4(v_recur_489_, v_it_491_, v___x_503_, lean_box(0), lean_box(0));
return v___x_504_;
}
}
}
}
v___jp_507_:
{
if (v___y_511_ == 0)
{
lean_object* v___x_512_; 
v___x_512_ = lean_string_utf8_set(v___y_509_, v___x_480_, v___y_510_);
v_it_491_ = v___y_508_;
v_out_492_ = v___x_512_;
goto v___jp_490_;
}
else
{
uint32_t v___x_513_; uint32_t v___x_514_; lean_object* v___x_515_; 
v___x_513_ = 4294967264;
v___x_514_ = lean_uint32_add(v___y_510_, v___x_513_);
v___x_515_ = lean_string_utf8_set(v___y_509_, v___x_480_, v___x_514_);
v_it_491_ = v___y_508_;
v_out_492_ = v___x_515_;
goto v___jp_490_;
}
}
v___jp_516_:
{
lean_object* v___x_520_; uint32_t v___x_521_; uint32_t v___x_522_; uint8_t v___x_523_; 
v___x_520_ = lean_string_utf8_extract_fast(v_name_482_, v_startInclusive_518_, v_endExclusive_519_);
lean_dec(v_endExclusive_519_);
lean_dec(v_startInclusive_518_);
v___x_521_ = lean_string_utf8_get(v___x_520_, v___x_480_);
v___x_522_ = 97;
v___x_523_ = lean_uint32_dec_le(v___x_522_, v___x_521_);
if (v___x_523_ == 0)
{
v___y_508_ = v_it_517_;
v___y_509_ = v___x_520_;
v___y_510_ = v___x_521_;
v___y_511_ = v___x_523_;
goto v___jp_507_;
}
else
{
uint32_t v___x_524_; uint8_t v___x_525_; 
v___x_524_ = 122;
v___x_525_ = lean_uint32_dec_le(v___x_521_, v___x_524_);
v___y_508_ = v_it_517_;
v___y_509_ = v___x_520_;
v___y_510_ = v___x_521_;
v___y_511_ = v___x_525_;
goto v___jp_507_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1___boxed(lean_object* v___x_550_, lean_object* v___x_551_, lean_object* v___x_552_, lean_object* v_name_553_, lean_object* v___x_554_, lean_object* v___x_555_, lean_object* v___x_556_, lean_object* v_it_557_, lean_object* v_acc_558_, lean_object* v_hP_559_, lean_object* v_recur_560_){
_start:
{
uint32_t v___x_2803__boxed_561_; lean_object* v_res_562_; 
v___x_2803__boxed_561_ = lean_unbox_uint32(v___x_555_);
lean_dec(v___x_555_);
v_res_562_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1(v___x_550_, v___x_551_, v___x_552_, v_name_553_, v___x_554_, v___x_2803__boxed_561_, v___x_556_, v_it_557_, v_acc_558_, v_hP_559_, v_recur_560_);
lean_dec_ref(v___x_556_);
lean_dec_ref(v_name_553_);
lean_dec(v___x_552_);
lean_dec(v___x_551_);
lean_dec_ref(v___x_550_);
return v_res_562_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed__const__1(void){
_start:
{
uint32_t v___x_568_; lean_object* v___x_569_; 
v___x_568_ = 45;
v___x_569_ = lean_box_uint32(v___x_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2(lean_object* v_buf_570_, lean_object* v_name_571_, lean_object* v_value_572_){
_start:
{
lean_object* v___y_574_; lean_object* v___f_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v_it_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___f_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___f_593_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__2));
v___x_594_ = lean_unsigned_to_nat(0u);
v___x_595_ = lean_string_utf8_byte_size(v_name_571_);
lean_inc_ref(v_name_571_);
v___x_596_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_596_, 0, v_name_571_);
lean_ctor_set(v___x_596_, 1, v___x_594_);
lean_ctor_set(v___x_596_, 2, v___x_595_);
lean_inc_ref(v___x_596_);
v_it_597_ = l_String_Slice_splitToSubslice___redArg(v___x_596_, v___f_593_);
v___x_598_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__3));
v___x_599_ = lean_unsigned_to_nat(1u);
v___x_600_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed__const__1;
v___f_601_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1___boxed), 11, 7);
lean_closure_set(v___f_601_, 0, v___x_598_);
lean_closure_set(v___f_601_, 1, v___x_594_);
lean_closure_set(v___f_601_, 2, v___x_599_);
lean_closure_set(v___f_601_, 3, v_name_571_);
lean_closure_set(v___f_601_, 4, v___x_595_);
lean_closure_set(v___f_601_, 5, v___x_600_);
lean_closure_set(v___f_601_, 6, v___x_596_);
v___x_602_ = lean_box(0);
v___x_603_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_601_, v_it_597_, v___x_602_, lean_box(0));
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v___x_604_; 
v___x_604_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_574_ = v___x_604_;
goto v___jp_573_;
}
else
{
lean_object* v_val_605_; 
v_val_605_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_val_605_);
lean_dec_ref_known(v___x_603_, 1);
v___y_574_ = v_val_605_;
goto v___jp_573_;
}
v___jp_573_:
{
lean_object* v_data_575_; lean_object* v_size_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_592_; 
v_data_575_ = lean_ctor_get(v_buf_570_, 0);
v_size_576_ = lean_ctor_get(v_buf_570_, 1);
v_isSharedCheck_592_ = !lean_is_exclusive(v_buf_570_);
if (v_isSharedCheck_592_ == 0)
{
v___x_578_ = v_buf_570_;
v_isShared_579_ = v_isSharedCheck_592_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_size_576_);
lean_inc(v_data_575_);
lean_dec(v_buf_570_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_592_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_580_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__0));
v___x_581_ = lean_string_append(v___y_574_, v___x_580_);
v___x_582_ = lean_string_append(v___x_581_, v_value_572_);
v___x_583_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__1));
v___x_584_ = lean_string_append(v___x_582_, v___x_583_);
v___x_585_ = lean_string_to_utf8(v___x_584_);
lean_dec_ref(v___x_584_);
lean_inc_ref(v___x_585_);
v___x_586_ = lean_array_push(v_data_575_, v___x_585_);
v___x_587_ = lean_byte_array_size(v___x_585_);
lean_dec_ref(v___x_585_);
v___x_588_ = lean_nat_add(v_size_576_, v___x_587_);
lean_dec(v_size_576_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 1, v___x_588_);
lean_ctor_set(v___x_578_, 0, v___x_586_);
v___x_590_ = v___x_578_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_586_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v___x_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed(lean_object* v_buf_606_, lean_object* v_name_607_, lean_object* v_value_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2(v_buf_606_, v_name_607_, v_value_608_);
lean_dec_ref(v_value_608_);
return v_res_609_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__1));
v___x_613_ = lean_string_to_utf8(v___x_612_);
return v___x_613_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_615_ = lean_byte_array_size(v___x_614_);
return v___x_615_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23));
v___x_651_ = lean_byte_array_size(v___x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1(lean_object* v_buffer_695_, lean_object* v_req_696_){
_start:
{
uint8_t v_method_697_; uint8_t v_version_698_; lean_object* v_uri_699_; lean_object* v_headers_700_; lean_object* v___f_701_; lean_object* v___f_702_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_755_; lean_object* v_port_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v_host_772_; lean_object* v_port_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v_port_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v_host_888_; lean_object* v_port_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_907_; 
v_method_697_ = lean_ctor_get_uint8(v_req_696_, sizeof(void*)*2);
v_version_698_ = lean_ctor_get_uint8(v_req_696_, sizeof(void*)*2 + 1);
v_uri_699_ = lean_ctor_get(v_req_696_, 0);
lean_inc(v_uri_699_);
v_headers_700_ = lean_ctor_get(v_req_696_, 1);
lean_inc_ref(v_headers_700_);
lean_dec_ref(v_req_696_);
v___f_701_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__0));
v___f_702_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1));
switch(v_method_697_)
{
case 0:
{
lean_object* v___x_987_; 
v___x_987_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28));
v___y_907_ = v___x_987_;
goto v___jp_906_;
}
case 1:
{
lean_object* v___x_988_; 
v___x_988_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29));
v___y_907_ = v___x_988_;
goto v___jp_906_;
}
case 2:
{
lean_object* v___x_989_; 
v___x_989_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30));
v___y_907_ = v___x_989_;
goto v___jp_906_;
}
case 3:
{
lean_object* v___x_990_; 
v___x_990_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31));
v___y_907_ = v___x_990_;
goto v___jp_906_;
}
case 4:
{
lean_object* v___x_991_; 
v___x_991_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32));
v___y_907_ = v___x_991_;
goto v___jp_906_;
}
case 5:
{
lean_object* v___x_992_; 
v___x_992_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33));
v___y_907_ = v___x_992_;
goto v___jp_906_;
}
case 6:
{
lean_object* v___x_993_; 
v___x_993_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34));
v___y_907_ = v___x_993_;
goto v___jp_906_;
}
case 7:
{
lean_object* v___x_994_; 
v___x_994_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35));
v___y_907_ = v___x_994_;
goto v___jp_906_;
}
case 8:
{
lean_object* v___x_995_; 
v___x_995_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36));
v___y_907_ = v___x_995_;
goto v___jp_906_;
}
case 9:
{
lean_object* v___x_996_; 
v___x_996_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37));
v___y_907_ = v___x_996_;
goto v___jp_906_;
}
case 10:
{
lean_object* v___x_997_; 
v___x_997_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38));
v___y_907_ = v___x_997_;
goto v___jp_906_;
}
case 11:
{
lean_object* v___x_998_; 
v___x_998_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39));
v___y_907_ = v___x_998_;
goto v___jp_906_;
}
case 12:
{
lean_object* v___x_999_; 
v___x_999_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40));
v___y_907_ = v___x_999_;
goto v___jp_906_;
}
case 13:
{
lean_object* v___x_1000_; 
v___x_1000_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41));
v___y_907_ = v___x_1000_;
goto v___jp_906_;
}
case 14:
{
lean_object* v___x_1001_; 
v___x_1001_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42));
v___y_907_ = v___x_1001_;
goto v___jp_906_;
}
case 15:
{
lean_object* v___x_1002_; 
v___x_1002_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43));
v___y_907_ = v___x_1002_;
goto v___jp_906_;
}
case 16:
{
lean_object* v___x_1003_; 
v___x_1003_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44));
v___y_907_ = v___x_1003_;
goto v___jp_906_;
}
case 17:
{
lean_object* v___x_1004_; 
v___x_1004_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45));
v___y_907_ = v___x_1004_;
goto v___jp_906_;
}
case 18:
{
lean_object* v___x_1005_; 
v___x_1005_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46));
v___y_907_ = v___x_1005_;
goto v___jp_906_;
}
case 19:
{
lean_object* v___x_1006_; 
v___x_1006_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47));
v___y_907_ = v___x_1006_;
goto v___jp_906_;
}
case 20:
{
lean_object* v___x_1007_; 
v___x_1007_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48));
v___y_907_ = v___x_1007_;
goto v___jp_906_;
}
case 21:
{
lean_object* v___x_1008_; 
v___x_1008_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49));
v___y_907_ = v___x_1008_;
goto v___jp_906_;
}
case 22:
{
lean_object* v___x_1009_; 
v___x_1009_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50));
v___y_907_ = v___x_1009_;
goto v___jp_906_;
}
case 23:
{
lean_object* v___x_1010_; 
v___x_1010_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51));
v___y_907_ = v___x_1010_;
goto v___jp_906_;
}
case 24:
{
lean_object* v___x_1011_; 
v___x_1011_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52));
v___y_907_ = v___x_1011_;
goto v___jp_906_;
}
case 25:
{
lean_object* v___x_1012_; 
v___x_1012_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53));
v___y_907_ = v___x_1012_;
goto v___jp_906_;
}
case 26:
{
lean_object* v___x_1013_; 
v___x_1013_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54));
v___y_907_ = v___x_1013_;
goto v___jp_906_;
}
case 27:
{
lean_object* v___x_1014_; 
v___x_1014_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55));
v___y_907_ = v___x_1014_;
goto v___jp_906_;
}
case 28:
{
lean_object* v___x_1015_; 
v___x_1015_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56));
v___y_907_ = v___x_1015_;
goto v___jp_906_;
}
case 29:
{
lean_object* v___x_1016_; 
v___x_1016_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57));
v___y_907_ = v___x_1016_;
goto v___jp_906_;
}
case 30:
{
lean_object* v___x_1017_; 
v___x_1017_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58));
v___y_907_ = v___x_1017_;
goto v___jp_906_;
}
case 31:
{
lean_object* v___x_1018_; 
v___x_1018_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59));
v___y_907_ = v___x_1018_;
goto v___jp_906_;
}
case 32:
{
lean_object* v___x_1019_; 
v___x_1019_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60));
v___y_907_ = v___x_1019_;
goto v___jp_906_;
}
case 33:
{
lean_object* v___x_1020_; 
v___x_1020_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61));
v___y_907_ = v___x_1020_;
goto v___jp_906_;
}
case 34:
{
lean_object* v___x_1021_; 
v___x_1021_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62));
v___y_907_ = v___x_1021_;
goto v___jp_906_;
}
case 35:
{
lean_object* v___x_1022_; 
v___x_1022_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63));
v___y_907_ = v___x_1022_;
goto v___jp_906_;
}
case 36:
{
lean_object* v___x_1023_; 
v___x_1023_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64));
v___y_907_ = v___x_1023_;
goto v___jp_906_;
}
case 37:
{
lean_object* v___x_1024_; 
v___x_1024_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65));
v___y_907_ = v___x_1024_;
goto v___jp_906_;
}
case 38:
{
lean_object* v___x_1025_; 
v___x_1025_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66));
v___y_907_ = v___x_1025_;
goto v___jp_906_;
}
default: 
{
lean_object* v___x_1026_; 
v___x_1026_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67));
v___y_907_ = v___x_1026_;
goto v___jp_906_;
}
}
v___jp_703_:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v_buffer_715_; lean_object* v_buffer_716_; lean_object* v_data_717_; lean_object* v_size_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_727_; 
v___x_707_ = lean_string_to_utf8(v___y_706_);
lean_inc_ref(v___x_707_);
v___x_708_ = lean_array_push(v___y_705_, v___x_707_);
v___x_709_ = lean_byte_array_size(v___x_707_);
lean_dec_ref(v___x_707_);
v___x_710_ = lean_nat_add(v___y_704_, v___x_709_);
lean_dec(v___y_704_);
v___x_711_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_712_ = lean_array_push(v___x_708_, v___x_711_);
v___x_713_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3);
v___x_714_ = lean_nat_add(v___x_710_, v___x_713_);
lean_dec(v___x_710_);
v_buffer_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_buffer_715_, 0, v___x_712_);
lean_ctor_set(v_buffer_715_, 1, v___x_714_);
v_buffer_716_ = l_Std_Http_Headers_fold___redArg(v_headers_700_, v_buffer_715_, v___f_702_);
lean_dec_ref(v_headers_700_);
v_data_717_ = lean_ctor_get(v_buffer_716_, 0);
v_size_718_ = lean_ctor_get(v_buffer_716_, 1);
v_isSharedCheck_727_ = !lean_is_exclusive(v_buffer_716_);
if (v_isSharedCheck_727_ == 0)
{
v___x_720_ = v_buffer_716_;
v_isShared_721_ = v_isSharedCheck_727_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_size_718_);
lean_inc(v_data_717_);
lean_dec(v_buffer_716_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_727_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_722_ = lean_array_push(v_data_717_, v___x_711_);
v___x_723_ = lean_nat_add(v_size_718_, v___x_713_);
lean_dec(v_size_718_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 1, v___x_723_);
lean_ctor_set(v___x_720_, 0, v___x_722_);
v___x_725_ = v___x_720_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
v___jp_728_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_734_ = lean_string_to_utf8(v___y_733_);
lean_dec_ref(v___y_733_);
lean_inc_ref(v___x_734_);
v___x_735_ = lean_array_push(v___y_732_, v___x_734_);
v___x_736_ = lean_byte_array_size(v___x_734_);
lean_dec_ref(v___x_734_);
v___x_737_ = lean_nat_add(v___y_729_, v___x_736_);
lean_dec(v___y_729_);
v___x_738_ = lean_array_push(v___x_735_, v___y_731_);
v___x_739_ = lean_nat_add(v___x_737_, v___y_730_);
lean_dec(v___x_737_);
switch(v_version_698_)
{
case 0:
{
lean_object* v___x_740_; 
v___x_740_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4));
v___y_704_ = v___x_739_;
v___y_705_ = v___x_738_;
v___y_706_ = v___x_740_;
goto v___jp_703_;
}
case 1:
{
lean_object* v___x_741_; 
v___x_741_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5));
v___y_704_ = v___x_739_;
v___y_705_ = v___x_738_;
v___y_706_ = v___x_741_;
goto v___jp_703_;
}
case 2:
{
lean_object* v___x_742_; 
v___x_742_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6));
v___y_704_ = v___x_739_;
v___y_705_ = v___x_738_;
v___y_706_ = v___x_742_;
goto v___jp_703_;
}
default: 
{
lean_object* v___x_743_; 
v___x_743_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7));
v___y_704_ = v___x_739_;
v___y_705_ = v___x_738_;
v___y_706_ = v___x_743_;
goto v___jp_703_;
}
}
}
v___jp_744_:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_string_append(v___y_749_, v___y_750_);
lean_dec_ref(v___y_750_);
v___x_753_ = lean_string_append(v___x_752_, v___y_751_);
lean_dec_ref(v___y_751_);
v___y_729_ = v___y_745_;
v___y_730_ = v___y_746_;
v___y_731_ = v___y_747_;
v___y_732_ = v___y_748_;
v___y_733_ = v___x_753_;
goto v___jp_728_;
}
v___jp_754_:
{
switch(lean_obj_tag(v_port_756_))
{
case 0:
{
lean_object* v___x_762_; 
v___x_762_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_745_ = v___y_755_;
v___y_746_ = v___y_757_;
v___y_747_ = v___y_758_;
v___y_748_ = v___y_759_;
v___y_749_ = v___y_760_;
v___y_750_ = v___y_761_;
v___y_751_ = v___x_762_;
goto v___jp_744_;
}
case 1:
{
lean_object* v___x_763_; 
v___x_763_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___y_745_ = v___y_755_;
v___y_746_ = v___y_757_;
v___y_747_ = v___y_758_;
v___y_748_ = v___y_759_;
v___y_749_ = v___y_760_;
v___y_750_ = v___y_761_;
v___y_751_ = v___x_763_;
goto v___jp_744_;
}
default: 
{
uint16_t v_port_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v_port_764_ = lean_ctor_get_uint16(v_port_756_, 0);
lean_dec_ref_known(v_port_756_, 0);
v___x_765_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_766_ = lean_uint16_to_nat(v_port_764_);
v___x_767_ = l_Nat_reprFast(v___x_766_);
v___x_768_ = lean_string_append(v___x_765_, v___x_767_);
lean_dec_ref(v___x_767_);
v___y_745_ = v___y_755_;
v___y_746_ = v___y_757_;
v___y_747_ = v___y_758_;
v___y_748_ = v___y_759_;
v___y_749_ = v___y_760_;
v___y_750_ = v___y_761_;
v___y_751_ = v___x_768_;
goto v___jp_744_;
}
}
}
v___jp_769_:
{
switch(lean_obj_tag(v_host_772_))
{
case 0:
{
lean_object* v_name_777_; 
v_name_777_ = lean_ctor_get(v_host_772_, 0);
lean_inc_ref(v_name_777_);
lean_dec_ref_known(v_host_772_, 1);
v___y_755_ = v___y_770_;
v_port_756_ = v_port_773_;
v___y_757_ = v___y_771_;
v___y_758_ = v___y_774_;
v___y_759_ = v___y_775_;
v___y_760_ = v___y_776_;
v___y_761_ = v_name_777_;
goto v___jp_754_;
}
case 1:
{
lean_object* v_ipv4_778_; lean_object* v___x_779_; 
v_ipv4_778_ = lean_ctor_get(v_host_772_, 0);
lean_inc_ref(v_ipv4_778_);
lean_dec_ref_known(v_host_772_, 1);
v___x_779_ = lean_uv_ntop_v4(v_ipv4_778_);
lean_dec_ref(v_ipv4_778_);
v___y_755_ = v___y_770_;
v_port_756_ = v_port_773_;
v___y_757_ = v___y_771_;
v___y_758_ = v___y_774_;
v___y_759_ = v___y_775_;
v___y_760_ = v___y_776_;
v___y_761_ = v___x_779_;
goto v___jp_754_;
}
default: 
{
lean_object* v_ipv6_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_ipv6_780_ = lean_ctor_get(v_host_772_, 0);
lean_inc_ref(v_ipv6_780_);
lean_dec_ref_known(v_host_772_, 1);
v___x_781_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9));
v___x_782_ = lean_uv_ntop_v6(v_ipv6_780_);
lean_dec_ref(v_ipv6_780_);
v___x_783_ = lean_string_append(v___x_781_, v___x_782_);
lean_dec_ref(v___x_782_);
v___x_784_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10));
v___x_785_ = lean_string_append(v___x_783_, v___x_784_);
v___y_755_ = v___y_770_;
v_port_756_ = v_port_773_;
v___y_757_ = v___y_771_;
v___y_758_ = v___y_774_;
v___y_759_ = v___y_775_;
v___y_760_ = v___y_776_;
v___y_761_ = v___x_785_;
goto v___jp_754_;
}
}
}
v___jp_786_:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_796_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_797_ = lean_string_append(v___y_787_, v___x_796_);
v___x_798_ = lean_string_append(v___x_797_, v___y_793_);
lean_dec_ref(v___y_793_);
v___x_799_ = lean_string_append(v___x_798_, v___y_794_);
lean_dec_ref(v___y_794_);
v___x_800_ = lean_string_append(v___x_799_, v___y_789_);
lean_dec_ref(v___y_789_);
v___x_801_ = lean_string_append(v___x_800_, v___y_795_);
lean_dec_ref(v___y_795_);
v___y_729_ = v___y_788_;
v___y_730_ = v___y_790_;
v___y_731_ = v___y_791_;
v___y_732_ = v___y_792_;
v___y_733_ = v___x_801_;
goto v___jp_728_;
}
v___jp_802_:
{
lean_object* v_queryPart_812_; 
v_queryPart_812_ = l_Std_Http_URI_Query_formatOption(v___y_809_);
if (lean_obj_tag(v___y_810_) == 0)
{
lean_object* v___x_813_; 
v___x_813_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_787_ = v___y_803_;
v___y_788_ = v___y_804_;
v___y_789_ = v_queryPart_812_;
v___y_790_ = v___y_805_;
v___y_791_ = v___y_806_;
v___y_792_ = v___y_808_;
v___y_793_ = v___y_807_;
v___y_794_ = v___y_811_;
v___y_795_ = v___x_813_;
goto v___jp_786_;
}
else
{
lean_object* v_val_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v_val_814_ = lean_ctor_get(v___y_810_, 0);
lean_inc(v_val_814_);
lean_dec_ref_known(v___y_810_, 1);
v___x_815_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11));
v___x_816_ = l_Std_Http_URI_EncodedFragment_encode(v_val_814_);
lean_dec(v_val_814_);
v___x_817_ = lean_string_from_utf8_unchecked(v___x_816_);
v___x_818_ = lean_string_append(v___x_815_, v___x_817_);
lean_dec_ref(v___x_817_);
v___y_787_ = v___y_803_;
v___y_788_ = v___y_804_;
v___y_789_ = v_queryPart_812_;
v___y_790_ = v___y_805_;
v___y_791_ = v___y_806_;
v___y_792_ = v___y_808_;
v___y_793_ = v___y_807_;
v___y_794_ = v___y_811_;
v___y_795_ = v___x_818_;
goto v___jp_786_;
}
}
v___jp_819_:
{
lean_object* v_queryStr_826_; lean_object* v___x_827_; 
v_queryStr_826_ = l_Std_Http_URI_Query_formatOption(v___y_824_);
v___x_827_ = lean_string_append(v___y_825_, v_queryStr_826_);
lean_dec_ref(v_queryStr_826_);
v___y_729_ = v___y_820_;
v___y_730_ = v___y_821_;
v___y_731_ = v___y_822_;
v___y_732_ = v___y_823_;
v___y_733_ = v___x_827_;
goto v___jp_728_;
}
v___jp_828_:
{
lean_object* v_segments_838_; uint8_t v_absolute_839_; lean_object* v___x_840_; lean_object* v___x_841_; size_t v_sz_842_; size_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v_result_846_; 
v_segments_838_ = lean_ctor_get(v___y_834_, 0);
lean_inc_ref(v_segments_838_);
v_absolute_839_ = lean_ctor_get_uint8(v___y_834_, sizeof(void*)*1);
lean_dec_ref(v___y_834_);
v___x_840_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12));
v___x_841_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22));
v_sz_842_ = lean_array_size(v_segments_838_);
v___x_843_ = ((size_t)0ULL);
v___x_844_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_841_, v___f_701_, v_sz_842_, v___x_843_, v_segments_838_);
v___x_845_ = lean_array_to_list(v___x_844_);
v_result_846_ = l_String_intercalate(v___x_840_, v___x_845_);
if (v_absolute_839_ == 0)
{
v___y_803_ = v___y_829_;
v___y_804_ = v___y_830_;
v___y_805_ = v___y_831_;
v___y_806_ = v___y_832_;
v___y_807_ = v___y_837_;
v___y_808_ = v___y_833_;
v___y_809_ = v___y_835_;
v___y_810_ = v___y_836_;
v___y_811_ = v_result_846_;
goto v___jp_802_;
}
else
{
lean_object* v___x_847_; 
v___x_847_ = lean_string_append(v___x_840_, v_result_846_);
lean_dec_ref(v_result_846_);
v___y_803_ = v___y_829_;
v___y_804_ = v___y_830_;
v___y_805_ = v___y_831_;
v___y_806_ = v___y_832_;
v___y_807_ = v___y_837_;
v___y_808_ = v___y_833_;
v___y_809_ = v___y_835_;
v___y_810_ = v___y_836_;
v___y_811_ = v___x_847_;
goto v___jp_802_;
}
}
v___jp_848_:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_861_ = lean_string_append(v___y_857_, v___y_852_);
lean_dec_ref(v___y_852_);
v___x_862_ = lean_string_append(v___x_861_, v___y_860_);
lean_dec_ref(v___y_860_);
lean_inc_ref(v___y_856_);
v___x_863_ = lean_string_append(v___y_856_, v___x_862_);
lean_dec_ref(v___x_862_);
v___y_829_ = v___y_849_;
v___y_830_ = v___y_850_;
v___y_831_ = v___y_851_;
v___y_832_ = v___y_853_;
v___y_833_ = v___y_854_;
v___y_834_ = v___y_855_;
v___y_835_ = v___y_858_;
v___y_836_ = v___y_859_;
v___y_837_ = v___x_863_;
goto v___jp_828_;
}
v___jp_864_:
{
switch(lean_obj_tag(v_port_867_))
{
case 0:
{
lean_object* v___x_877_; 
v___x_877_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_849_ = v___y_865_;
v___y_850_ = v___y_866_;
v___y_851_ = v___y_868_;
v___y_852_ = v___y_876_;
v___y_853_ = v___y_869_;
v___y_854_ = v___y_870_;
v___y_855_ = v___y_871_;
v___y_856_ = v___y_873_;
v___y_857_ = v___y_872_;
v___y_858_ = v___y_874_;
v___y_859_ = v___y_875_;
v___y_860_ = v___x_877_;
goto v___jp_848_;
}
case 1:
{
lean_object* v___x_878_; 
v___x_878_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___y_849_ = v___y_865_;
v___y_850_ = v___y_866_;
v___y_851_ = v___y_868_;
v___y_852_ = v___y_876_;
v___y_853_ = v___y_869_;
v___y_854_ = v___y_870_;
v___y_855_ = v___y_871_;
v___y_856_ = v___y_873_;
v___y_857_ = v___y_872_;
v___y_858_ = v___y_874_;
v___y_859_ = v___y_875_;
v___y_860_ = v___x_878_;
goto v___jp_848_;
}
default: 
{
uint16_t v_port_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v_port_879_ = lean_ctor_get_uint16(v_port_867_, 0);
lean_dec_ref_known(v_port_867_, 0);
v___x_880_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_881_ = lean_uint16_to_nat(v_port_879_);
v___x_882_ = l_Nat_reprFast(v___x_881_);
v___x_883_ = lean_string_append(v___x_880_, v___x_882_);
lean_dec_ref(v___x_882_);
v___y_849_ = v___y_865_;
v___y_850_ = v___y_866_;
v___y_851_ = v___y_868_;
v___y_852_ = v___y_876_;
v___y_853_ = v___y_869_;
v___y_854_ = v___y_870_;
v___y_855_ = v___y_871_;
v___y_856_ = v___y_873_;
v___y_857_ = v___y_872_;
v___y_858_ = v___y_874_;
v___y_859_ = v___y_875_;
v___y_860_ = v___x_883_;
goto v___jp_848_;
}
}
}
v___jp_884_:
{
switch(lean_obj_tag(v_host_888_))
{
case 0:
{
lean_object* v_name_897_; 
v_name_897_ = lean_ctor_get(v_host_888_, 0);
lean_inc_ref(v_name_897_);
lean_dec_ref_known(v_host_888_, 1);
v___y_865_ = v___y_885_;
v___y_866_ = v___y_886_;
v_port_867_ = v_port_889_;
v___y_868_ = v___y_887_;
v___y_869_ = v___y_890_;
v___y_870_ = v___y_891_;
v___y_871_ = v___y_892_;
v___y_872_ = v___y_896_;
v___y_873_ = v___y_893_;
v___y_874_ = v___y_894_;
v___y_875_ = v___y_895_;
v___y_876_ = v_name_897_;
goto v___jp_864_;
}
case 1:
{
lean_object* v_ipv4_898_; lean_object* v___x_899_; 
v_ipv4_898_ = lean_ctor_get(v_host_888_, 0);
lean_inc_ref(v_ipv4_898_);
lean_dec_ref_known(v_host_888_, 1);
v___x_899_ = lean_uv_ntop_v4(v_ipv4_898_);
lean_dec_ref(v_ipv4_898_);
v___y_865_ = v___y_885_;
v___y_866_ = v___y_886_;
v_port_867_ = v_port_889_;
v___y_868_ = v___y_887_;
v___y_869_ = v___y_890_;
v___y_870_ = v___y_891_;
v___y_871_ = v___y_892_;
v___y_872_ = v___y_896_;
v___y_873_ = v___y_893_;
v___y_874_ = v___y_894_;
v___y_875_ = v___y_895_;
v___y_876_ = v___x_899_;
goto v___jp_864_;
}
default: 
{
lean_object* v_ipv6_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v_ipv6_900_ = lean_ctor_get(v_host_888_, 0);
lean_inc_ref(v_ipv6_900_);
lean_dec_ref_known(v_host_888_, 1);
v___x_901_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9));
v___x_902_ = lean_uv_ntop_v6(v_ipv6_900_);
lean_dec_ref(v_ipv6_900_);
v___x_903_ = lean_string_append(v___x_901_, v___x_902_);
lean_dec_ref(v___x_902_);
v___x_904_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10));
v___x_905_ = lean_string_append(v___x_903_, v___x_904_);
v___y_865_ = v___y_885_;
v___y_866_ = v___y_886_;
v_port_867_ = v_port_889_;
v___y_868_ = v___y_887_;
v___y_869_ = v___y_890_;
v___y_870_ = v___y_891_;
v___y_871_ = v___y_892_;
v___y_872_ = v___y_896_;
v___y_873_ = v___y_893_;
v___y_874_ = v___y_894_;
v___y_875_ = v___y_895_;
v___y_876_ = v___x_905_;
goto v___jp_864_;
}
}
}
v___jp_906_:
{
lean_object* v_data_908_; lean_object* v_size_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v_data_908_ = lean_ctor_get(v_buffer_695_, 0);
lean_inc_ref(v_data_908_);
v_size_909_ = lean_ctor_get(v_buffer_695_, 1);
lean_inc(v_size_909_);
lean_dec_ref(v_buffer_695_);
v___x_910_ = lean_string_to_utf8(v___y_907_);
lean_inc_ref(v___x_910_);
v___x_911_ = lean_array_push(v_data_908_, v___x_910_);
v___x_912_ = lean_byte_array_size(v___x_910_);
lean_dec_ref(v___x_910_);
v___x_913_ = lean_nat_add(v_size_909_, v___x_912_);
lean_dec(v_size_909_);
v___x_914_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23));
v___x_915_ = lean_array_push(v___x_911_, v___x_914_);
v___x_916_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24);
v___x_917_ = lean_nat_add(v___x_913_, v___x_916_);
lean_dec(v___x_913_);
switch(lean_obj_tag(v_uri_699_))
{
case 0:
{
lean_object* v_path_918_; lean_object* v_query_919_; lean_object* v_segments_920_; uint8_t v_absolute_921_; lean_object* v___x_922_; lean_object* v___x_923_; size_t v_sz_924_; size_t v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v_result_928_; 
v_path_918_ = lean_ctor_get(v_uri_699_, 0);
lean_inc_ref(v_path_918_);
v_query_919_ = lean_ctor_get(v_uri_699_, 1);
lean_inc(v_query_919_);
lean_dec_ref_known(v_uri_699_, 2);
v_segments_920_ = lean_ctor_get(v_path_918_, 0);
lean_inc_ref(v_segments_920_);
v_absolute_921_ = lean_ctor_get_uint8(v_path_918_, sizeof(void*)*1);
lean_dec_ref(v_path_918_);
v___x_922_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12));
v___x_923_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22));
v_sz_924_ = lean_array_size(v_segments_920_);
v___x_925_ = ((size_t)0ULL);
v___x_926_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_923_, v___f_701_, v_sz_924_, v___x_925_, v_segments_920_);
v___x_927_ = lean_array_to_list(v___x_926_);
v_result_928_ = l_String_intercalate(v___x_922_, v___x_927_);
if (v_absolute_921_ == 0)
{
v___y_820_ = v___x_917_;
v___y_821_ = v___x_916_;
v___y_822_ = v___x_914_;
v___y_823_ = v___x_915_;
v___y_824_ = v_query_919_;
v___y_825_ = v_result_928_;
goto v___jp_819_;
}
else
{
lean_object* v___x_929_; 
v___x_929_ = lean_string_append(v___x_922_, v_result_928_);
lean_dec_ref(v_result_928_);
v___y_820_ = v___x_917_;
v___y_821_ = v___x_916_;
v___y_822_ = v___x_914_;
v___y_823_ = v___x_915_;
v___y_824_ = v_query_919_;
v___y_825_ = v___x_929_;
goto v___jp_819_;
}
}
case 1:
{
lean_object* v_uri_930_; lean_object* v_authority_931_; 
v_uri_930_ = lean_ctor_get(v_uri_699_, 0);
lean_inc_ref(v_uri_930_);
lean_dec_ref_known(v_uri_699_, 1);
v_authority_931_ = lean_ctor_get(v_uri_930_, 1);
if (lean_obj_tag(v_authority_931_) == 0)
{
lean_object* v_scheme_932_; lean_object* v_path_933_; lean_object* v_query_934_; lean_object* v_fragment_935_; lean_object* v___x_936_; 
v_scheme_932_ = lean_ctor_get(v_uri_930_, 0);
lean_inc_ref(v_scheme_932_);
v_path_933_ = lean_ctor_get(v_uri_930_, 2);
lean_inc_ref(v_path_933_);
v_query_934_ = lean_ctor_get(v_uri_930_, 3);
lean_inc(v_query_934_);
v_fragment_935_ = lean_ctor_get(v_uri_930_, 4);
lean_inc(v_fragment_935_);
lean_dec_ref(v_uri_930_);
v___x_936_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_829_ = v_scheme_932_;
v___y_830_ = v___x_917_;
v___y_831_ = v___x_916_;
v___y_832_ = v___x_914_;
v___y_833_ = v___x_915_;
v___y_834_ = v_path_933_;
v___y_835_ = v_query_934_;
v___y_836_ = v_fragment_935_;
v___y_837_ = v___x_936_;
goto v___jp_828_;
}
else
{
lean_object* v_val_937_; lean_object* v_scheme_938_; lean_object* v_path_939_; lean_object* v_query_940_; lean_object* v_fragment_941_; lean_object* v_userInfo_942_; lean_object* v_host_943_; lean_object* v_port_944_; lean_object* v___x_945_; 
v_val_937_ = lean_ctor_get(v_authority_931_, 0);
lean_inc(v_val_937_);
v_scheme_938_ = lean_ctor_get(v_uri_930_, 0);
lean_inc_ref(v_scheme_938_);
v_path_939_ = lean_ctor_get(v_uri_930_, 2);
lean_inc_ref(v_path_939_);
v_query_940_ = lean_ctor_get(v_uri_930_, 3);
lean_inc(v_query_940_);
v_fragment_941_ = lean_ctor_get(v_uri_930_, 4);
lean_inc(v_fragment_941_);
lean_dec_ref(v_uri_930_);
v_userInfo_942_ = lean_ctor_get(v_val_937_, 0);
lean_inc(v_userInfo_942_);
v_host_943_ = lean_ctor_get(v_val_937_, 1);
lean_inc_ref(v_host_943_);
v_port_944_ = lean_ctor_get(v_val_937_, 2);
lean_inc(v_port_944_);
lean_dec(v_val_937_);
v___x_945_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25));
if (lean_obj_tag(v_userInfo_942_) == 0)
{
lean_object* v___x_946_; 
v___x_946_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_885_ = v_scheme_938_;
v___y_886_ = v___x_917_;
v___y_887_ = v___x_916_;
v_host_888_ = v_host_943_;
v_port_889_ = v_port_944_;
v___y_890_ = v___x_914_;
v___y_891_ = v___x_915_;
v___y_892_ = v_path_939_;
v___y_893_ = v___x_945_;
v___y_894_ = v_query_940_;
v___y_895_ = v_fragment_941_;
v___y_896_ = v___x_946_;
goto v___jp_884_;
}
else
{
lean_object* v_val_947_; lean_object* v_password_948_; 
v_val_947_ = lean_ctor_get(v_userInfo_942_, 0);
lean_inc(v_val_947_);
lean_dec_ref_known(v_userInfo_942_, 1);
v_password_948_ = lean_ctor_get(v_val_947_, 1);
if (lean_obj_tag(v_password_948_) == 0)
{
lean_object* v_username_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v_username_949_ = lean_ctor_get(v_val_947_, 0);
lean_inc_ref(v_username_949_);
lean_dec(v_val_947_);
v___x_950_ = lean_string_from_utf8_unchecked(v_username_949_);
v___x_951_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26));
v___x_952_ = lean_string_append(v___x_950_, v___x_951_);
v___y_885_ = v_scheme_938_;
v___y_886_ = v___x_917_;
v___y_887_ = v___x_916_;
v_host_888_ = v_host_943_;
v_port_889_ = v_port_944_;
v___y_890_ = v___x_914_;
v___y_891_ = v___x_915_;
v___y_892_ = v_path_939_;
v___y_893_ = v___x_945_;
v___y_894_ = v_query_940_;
v___y_895_ = v_fragment_941_;
v___y_896_ = v___x_952_;
goto v___jp_884_;
}
else
{
lean_object* v_username_953_; lean_object* v_val_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
lean_inc_ref(v_password_948_);
v_username_953_ = lean_ctor_get(v_val_947_, 0);
lean_inc_ref(v_username_953_);
lean_dec(v_val_947_);
v_val_954_ = lean_ctor_get(v_password_948_, 0);
lean_inc(v_val_954_);
lean_dec_ref_known(v_password_948_, 1);
v___x_955_ = lean_string_from_utf8_unchecked(v_username_953_);
v___x_956_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_957_ = lean_string_append(v___x_955_, v___x_956_);
v___x_958_ = lean_string_from_utf8_unchecked(v_val_954_);
v___x_959_ = lean_string_append(v___x_957_, v___x_958_);
lean_dec_ref(v___x_958_);
v___x_960_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26));
v___x_961_ = lean_string_append(v___x_959_, v___x_960_);
v___y_885_ = v_scheme_938_;
v___y_886_ = v___x_917_;
v___y_887_ = v___x_916_;
v_host_888_ = v_host_943_;
v_port_889_ = v_port_944_;
v___y_890_ = v___x_914_;
v___y_891_ = v___x_915_;
v___y_892_ = v_path_939_;
v___y_893_ = v___x_945_;
v___y_894_ = v_query_940_;
v___y_895_ = v_fragment_941_;
v___y_896_ = v___x_961_;
goto v___jp_884_;
}
}
}
}
case 2:
{
lean_object* v_authority_962_; lean_object* v_userInfo_963_; 
v_authority_962_ = lean_ctor_get(v_uri_699_, 0);
lean_inc_ref(v_authority_962_);
lean_dec_ref_known(v_uri_699_, 1);
v_userInfo_963_ = lean_ctor_get(v_authority_962_, 0);
if (lean_obj_tag(v_userInfo_963_) == 0)
{
lean_object* v_host_964_; lean_object* v_port_965_; lean_object* v___x_966_; 
v_host_964_ = lean_ctor_get(v_authority_962_, 1);
lean_inc_ref(v_host_964_);
v_port_965_ = lean_ctor_get(v_authority_962_, 2);
lean_inc(v_port_965_);
lean_dec_ref(v_authority_962_);
v___x_966_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_770_ = v___x_917_;
v___y_771_ = v___x_916_;
v_host_772_ = v_host_964_;
v_port_773_ = v_port_965_;
v___y_774_ = v___x_914_;
v___y_775_ = v___x_915_;
v___y_776_ = v___x_966_;
goto v___jp_769_;
}
else
{
lean_object* v_val_967_; lean_object* v_password_968_; 
v_val_967_ = lean_ctor_get(v_userInfo_963_, 0);
lean_inc(v_val_967_);
v_password_968_ = lean_ctor_get(v_val_967_, 1);
if (lean_obj_tag(v_password_968_) == 0)
{
lean_object* v_host_969_; lean_object* v_port_970_; lean_object* v_username_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v_host_969_ = lean_ctor_get(v_authority_962_, 1);
lean_inc_ref(v_host_969_);
v_port_970_ = lean_ctor_get(v_authority_962_, 2);
lean_inc(v_port_970_);
lean_dec_ref(v_authority_962_);
v_username_971_ = lean_ctor_get(v_val_967_, 0);
lean_inc_ref(v_username_971_);
lean_dec(v_val_967_);
v___x_972_ = lean_string_from_utf8_unchecked(v_username_971_);
v___x_973_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26));
v___x_974_ = lean_string_append(v___x_972_, v___x_973_);
v___y_770_ = v___x_917_;
v___y_771_ = v___x_916_;
v_host_772_ = v_host_969_;
v_port_773_ = v_port_970_;
v___y_774_ = v___x_914_;
v___y_775_ = v___x_915_;
v___y_776_ = v___x_974_;
goto v___jp_769_;
}
else
{
lean_object* v_host_975_; lean_object* v_port_976_; lean_object* v_username_977_; lean_object* v_val_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
lean_inc_ref(v_password_968_);
v_host_975_ = lean_ctor_get(v_authority_962_, 1);
lean_inc_ref(v_host_975_);
v_port_976_ = lean_ctor_get(v_authority_962_, 2);
lean_inc(v_port_976_);
lean_dec_ref(v_authority_962_);
v_username_977_ = lean_ctor_get(v_val_967_, 0);
lean_inc_ref(v_username_977_);
lean_dec(v_val_967_);
v_val_978_ = lean_ctor_get(v_password_968_, 0);
lean_inc(v_val_978_);
lean_dec_ref_known(v_password_968_, 1);
v___x_979_ = lean_string_from_utf8_unchecked(v_username_977_);
v___x_980_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_981_ = lean_string_append(v___x_979_, v___x_980_);
v___x_982_ = lean_string_from_utf8_unchecked(v_val_978_);
v___x_983_ = lean_string_append(v___x_981_, v___x_982_);
lean_dec_ref(v___x_982_);
v___x_984_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26));
v___x_985_ = lean_string_append(v___x_983_, v___x_984_);
v___y_770_ = v___x_917_;
v___y_771_ = v___x_916_;
v_host_772_ = v_host_975_;
v_port_773_ = v_port_976_;
v___y_774_ = v___x_914_;
v___y_775_ = v___x_915_;
v___y_776_ = v___x_985_;
goto v___jp_769_;
}
}
}
default: 
{
lean_object* v___x_986_; 
v___x_986_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27));
v___y_729_ = v___x_917_;
v___y_730_ = v___x_916_;
v___y_731_ = v___x_914_;
v___y_732_ = v___x_915_;
v___y_733_ = v___x_986_;
goto v___jp_728_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___lam__0(lean_object* v___x_1027_, lean_object* v___x_1028_, lean_object* v___x_1029_, lean_object* v_name_1030_, lean_object* v___x_1031_, uint32_t v___x_1032_, lean_object* v___x_1033_, lean_object* v_it_1034_, lean_object* v_acc_1035_, lean_object* v_hP_1036_, lean_object* v_recur_1037_){
_start:
{
lean_object* v_it_1039_; lean_object* v_out_1040_; lean_object* v___y_1056_; uint32_t v___y_1057_; lean_object* v___y_1058_; uint8_t v___y_1059_; lean_object* v_it_1065_; lean_object* v_startInclusive_1066_; lean_object* v_endExclusive_1067_; 
if (lean_obj_tag(v_it_1034_) == 0)
{
lean_object* v_currPos_1074_; lean_object* v_searcher_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1097_; 
v_currPos_1074_ = lean_ctor_get(v_it_1034_, 0);
v_searcher_1075_ = lean_ctor_get(v_it_1034_, 1);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_it_1034_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1077_ = v_it_1034_;
v_isShared_1078_ = v_isSharedCheck_1097_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_searcher_1075_);
lean_inc(v_currPos_1074_);
lean_dec(v_it_1034_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1097_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
uint8_t v_decide_1079_; 
v_decide_1079_ = lean_nat_dec_eq(v_searcher_1075_, v___x_1031_);
if (v_decide_1079_ == 0)
{
uint32_t v___x_1080_; uint8_t v___x_1081_; 
lean_dec(v___x_1031_);
v___x_1080_ = lean_string_utf8_get_fast(v_name_1030_, v_searcher_1075_);
v___x_1081_ = lean_uint32_dec_eq(v___x_1080_, v___x_1032_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1082_ = lean_string_utf8_next_fast(v_name_1030_, v_searcher_1075_);
lean_dec(v_searcher_1075_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 1, v___x_1082_);
v___x_1084_ = v___x_1077_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_currPos_1074_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1085_; 
v___x_1085_ = lean_apply_4(v_recur_1037_, v___x_1084_, v_acc_1035_, lean_box(0), lean_box(0));
return v___x_1085_;
}
}
else
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v_slice_1090_; lean_object* v_nextIt_1092_; 
v___x_1087_ = lean_string_utf8_next_fast(v_name_1030_, v_searcher_1075_);
v___x_1088_ = lean_nat_sub(v___x_1087_, v_searcher_1075_);
v___x_1089_ = lean_nat_add(v_searcher_1075_, v___x_1088_);
lean_dec(v___x_1088_);
v_slice_1090_ = l_String_Slice_subslice_x21(v___x_1033_, v_currPos_1074_, v_searcher_1075_);
lean_inc(v___x_1089_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 1, v___x_1089_);
lean_ctor_set(v___x_1077_, 0, v___x_1089_);
v_nextIt_1092_ = v___x_1077_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1089_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v___x_1089_);
v_nextIt_1092_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
lean_object* v_startInclusive_1093_; lean_object* v_endExclusive_1094_; 
v_startInclusive_1093_ = lean_ctor_get(v_slice_1090_, 0);
lean_inc(v_startInclusive_1093_);
v_endExclusive_1094_ = lean_ctor_get(v_slice_1090_, 1);
lean_inc(v_endExclusive_1094_);
lean_dec_ref(v_slice_1090_);
v_it_1065_ = v_nextIt_1092_;
v_startInclusive_1066_ = v_startInclusive_1093_;
v_endExclusive_1067_ = v_endExclusive_1094_;
goto v___jp_1064_;
}
}
}
else
{
lean_object* v___x_1096_; 
lean_del_object(v___x_1077_);
lean_dec(v_searcher_1075_);
v___x_1096_ = lean_box(1);
v_it_1065_ = v___x_1096_;
v_startInclusive_1066_ = v_currPos_1074_;
v_endExclusive_1067_ = v___x_1031_;
goto v___jp_1064_;
}
}
}
else
{
lean_dec_ref(v_recur_1037_);
lean_dec(v___x_1031_);
return v_acc_1035_;
}
v___jp_1038_:
{
if (lean_obj_tag(v_acc_1035_) == 0)
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1041_, 0, v_out_1040_);
v___x_1042_ = lean_apply_4(v_recur_1037_, v_it_1039_, v___x_1041_, lean_box(0), lean_box(0));
return v___x_1042_;
}
else
{
lean_object* v_val_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1054_; 
v_val_1043_ = lean_ctor_get(v_acc_1035_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_acc_1035_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1045_ = v_acc_1035_;
v_isShared_1046_ = v_isSharedCheck_1054_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_val_1043_);
lean_dec(v_acc_1035_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1054_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1047_ = lean_string_utf8_extract_fast(v___x_1027_, v___x_1028_, v___x_1029_);
v___x_1048_ = lean_string_append(v_val_1043_, v___x_1047_);
lean_dec_ref(v___x_1047_);
v___x_1049_ = lean_string_append(v___x_1048_, v_out_1040_);
lean_dec_ref(v_out_1040_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 0, v___x_1049_);
v___x_1051_ = v___x_1045_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1052_; 
v___x_1052_ = lean_apply_4(v_recur_1037_, v_it_1039_, v___x_1051_, lean_box(0), lean_box(0));
return v___x_1052_;
}
}
}
}
v___jp_1055_:
{
if (v___y_1059_ == 0)
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_string_utf8_set(v___y_1056_, v___x_1028_, v___y_1057_);
v_it_1039_ = v___y_1058_;
v_out_1040_ = v___x_1060_;
goto v___jp_1038_;
}
else
{
uint32_t v___x_1061_; uint32_t v___x_1062_; lean_object* v___x_1063_; 
v___x_1061_ = 4294967264;
v___x_1062_ = lean_uint32_add(v___y_1057_, v___x_1061_);
v___x_1063_ = lean_string_utf8_set(v___y_1056_, v___x_1028_, v___x_1062_);
v_it_1039_ = v___y_1058_;
v_out_1040_ = v___x_1063_;
goto v___jp_1038_;
}
}
v___jp_1064_:
{
lean_object* v___x_1068_; uint32_t v___x_1069_; uint32_t v___x_1070_; uint8_t v___x_1071_; 
v___x_1068_ = lean_string_utf8_extract_fast(v_name_1030_, v_startInclusive_1066_, v_endExclusive_1067_);
lean_dec(v_endExclusive_1067_);
lean_dec(v_startInclusive_1066_);
v___x_1069_ = lean_string_utf8_get(v___x_1068_, v___x_1028_);
v___x_1070_ = 97;
v___x_1071_ = lean_uint32_dec_le(v___x_1070_, v___x_1069_);
if (v___x_1071_ == 0)
{
v___y_1056_ = v___x_1068_;
v___y_1057_ = v___x_1069_;
v___y_1058_ = v_it_1065_;
v___y_1059_ = v___x_1071_;
goto v___jp_1055_;
}
else
{
uint32_t v___x_1072_; uint8_t v___x_1073_; 
v___x_1072_ = 122;
v___x_1073_ = lean_uint32_dec_le(v___x_1069_, v___x_1072_);
v___y_1056_ = v___x_1068_;
v___y_1057_ = v___x_1069_;
v___y_1058_ = v_it_1065_;
v___y_1059_ = v___x_1073_;
goto v___jp_1055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___lam__0___boxed(lean_object* v___x_1098_, lean_object* v___x_1099_, lean_object* v___x_1100_, lean_object* v_name_1101_, lean_object* v___x_1102_, lean_object* v___x_1103_, lean_object* v___x_1104_, lean_object* v_it_1105_, lean_object* v_acc_1106_, lean_object* v_hP_1107_, lean_object* v_recur_1108_){
_start:
{
uint32_t v___x_1220__boxed_1109_; lean_object* v_res_1110_; 
v___x_1220__boxed_1109_ = lean_unbox_uint32(v___x_1103_);
lean_dec(v___x_1103_);
v_res_1110_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___lam__0(v___x_1098_, v___x_1099_, v___x_1100_, v_name_1101_, v___x_1102_, v___x_1220__boxed_1109_, v___x_1104_, v_it_1105_, v_acc_1106_, v_hP_1107_, v_recur_1108_);
lean_dec_ref(v___x_1104_);
lean_dec_ref(v_name_1101_);
lean_dec(v___x_1100_);
lean_dec(v___x_1099_);
lean_dec_ref(v___x_1098_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___lam__1(lean_object* v_buf_1111_, lean_object* v_name_1112_, lean_object* v_value_1113_){
_start:
{
lean_object* v___y_1115_; lean_object* v___f_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v_it_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___f_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___f_1134_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__2));
v___x_1135_ = lean_unsigned_to_nat(0u);
v___x_1136_ = lean_string_utf8_byte_size(v_name_1112_);
lean_inc_ref(v_name_1112_);
v___x_1137_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1137_, 0, v_name_1112_);
lean_ctor_set(v___x_1137_, 1, v___x_1135_);
lean_ctor_set(v___x_1137_, 2, v___x_1136_);
lean_inc_ref(v___x_1137_);
v_it_1138_ = l_String_Slice_splitToSubslice___redArg(v___x_1137_, v___f_1134_);
v___x_1139_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__3));
v___x_1140_ = lean_unsigned_to_nat(1u);
v___x_1141_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed__const__1;
v___f_1142_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___lam__0___boxed), 11, 7);
lean_closure_set(v___f_1142_, 0, v___x_1139_);
lean_closure_set(v___f_1142_, 1, v___x_1135_);
lean_closure_set(v___f_1142_, 2, v___x_1140_);
lean_closure_set(v___f_1142_, 3, v_name_1112_);
lean_closure_set(v___f_1142_, 4, v___x_1136_);
lean_closure_set(v___f_1142_, 5, v___x_1141_);
lean_closure_set(v___f_1142_, 6, v___x_1137_);
v___x_1143_ = lean_box(0);
v___x_1144_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1142_, v_it_1138_, v___x_1143_, lean_box(0));
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v___x_1145_; 
v___x_1145_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_1115_ = v___x_1145_;
goto v___jp_1114_;
}
else
{
lean_object* v_val_1146_; 
v_val_1146_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_val_1146_);
lean_dec_ref_known(v___x_1144_, 1);
v___y_1115_ = v_val_1146_;
goto v___jp_1114_;
}
v___jp_1114_:
{
lean_object* v_data_1116_; lean_object* v_size_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1133_; 
v_data_1116_ = lean_ctor_get(v_buf_1111_, 0);
v_size_1117_ = lean_ctor_get(v_buf_1111_, 1);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_buf_1111_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1119_ = v_buf_1111_;
v_isShared_1120_ = v_isSharedCheck_1133_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_size_1117_);
lean_inc(v_data_1116_);
lean_dec(v_buf_1111_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1133_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___x_1121_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__0));
v___x_1122_ = lean_string_append(v___y_1115_, v___x_1121_);
v___x_1123_ = lean_string_append(v___x_1122_, v_value_1113_);
v___x_1124_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__1));
v___x_1125_ = lean_string_append(v___x_1123_, v___x_1124_);
v___x_1126_ = lean_string_to_utf8(v___x_1125_);
lean_dec_ref(v___x_1125_);
lean_inc_ref(v___x_1126_);
v___x_1127_ = lean_array_push(v_data_1116_, v___x_1126_);
v___x_1128_ = lean_byte_array_size(v___x_1126_);
lean_dec_ref(v___x_1126_);
v___x_1129_ = lean_nat_add(v_size_1117_, v___x_1128_);
lean_dec(v_size_1117_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 1, v___x_1129_);
lean_ctor_set(v___x_1119_, 0, v___x_1127_);
v___x_1131_ = v___x_1119_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___lam__1___boxed(lean_object* v_buf_1147_, lean_object* v_name_1148_, lean_object* v_value_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___lam__1(v_buf_1147_, v_name_1148_, v_value_1149_);
lean_dec_ref(v_value_1149_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(lean_object* v_buffer_1152_, lean_object* v_r_1153_){
_start:
{
lean_object* v_status_1154_; uint8_t v_version_1155_; lean_object* v_headers_1156_; lean_object* v___f_1157_; lean_object* v___y_1159_; 
v_status_1154_ = lean_ctor_get(v_r_1153_, 0);
v_version_1155_ = lean_ctor_get_uint8(v_r_1153_, sizeof(void*)*2);
v_headers_1156_ = lean_ctor_get(v_r_1153_, 1);
v___f_1157_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__0));
switch(v_version_1155_)
{
case 0:
{
lean_object* v___x_1207_; 
v___x_1207_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4));
v___y_1159_ = v___x_1207_;
goto v___jp_1158_;
}
case 1:
{
lean_object* v___x_1208_; 
v___x_1208_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5));
v___y_1159_ = v___x_1208_;
goto v___jp_1158_;
}
case 2:
{
lean_object* v___x_1209_; 
v___x_1209_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6));
v___y_1159_ = v___x_1209_;
goto v___jp_1158_;
}
default: 
{
lean_object* v___x_1210_; 
v___x_1210_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7));
v___y_1159_ = v___x_1210_;
goto v___jp_1158_;
}
}
v___jp_1158_:
{
lean_object* v_data_1160_; lean_object* v_size_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1206_; 
v_data_1160_ = lean_ctor_get(v_buffer_1152_, 0);
v_size_1161_ = lean_ctor_get(v_buffer_1152_, 1);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_buffer_1152_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1163_ = v_buffer_1152_;
v_isShared_1164_ = v_isSharedCheck_1206_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_size_1161_);
lean_inc(v_data_1160_);
lean_dec(v_buffer_1152_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1206_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; uint16_t v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v_buffer_1192_; 
v___x_1165_ = lean_string_to_utf8(v___y_1159_);
lean_inc_ref(v___x_1165_);
v___x_1166_ = lean_array_push(v_data_1160_, v___x_1165_);
v___x_1167_ = lean_byte_array_size(v___x_1165_);
lean_dec_ref(v___x_1165_);
v___x_1168_ = lean_nat_add(v_size_1161_, v___x_1167_);
lean_dec(v_size_1161_);
v___x_1169_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23));
v___x_1170_ = lean_array_push(v___x_1166_, v___x_1169_);
v___x_1171_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24);
v___x_1172_ = lean_nat_add(v___x_1168_, v___x_1171_);
lean_dec(v___x_1168_);
v___x_1173_ = l_Std_Http_Status_toCode(v_status_1154_);
v___x_1174_ = lean_uint16_to_nat(v___x_1173_);
v___x_1175_ = l_Nat_reprFast(v___x_1174_);
v___x_1176_ = lean_string_to_utf8(v___x_1175_);
lean_dec_ref(v___x_1175_);
lean_inc_ref(v___x_1176_);
v___x_1177_ = lean_array_push(v___x_1170_, v___x_1176_);
v___x_1178_ = lean_byte_array_size(v___x_1176_);
lean_dec_ref(v___x_1176_);
v___x_1179_ = lean_nat_add(v___x_1172_, v___x_1178_);
lean_dec(v___x_1172_);
v___x_1180_ = lean_array_push(v___x_1177_, v___x_1169_);
v___x_1181_ = lean_nat_add(v___x_1179_, v___x_1171_);
lean_dec(v___x_1179_);
v___x_1182_ = l_Std_Http_Status_reasonPhrase(v_status_1154_);
v___x_1183_ = lean_string_to_utf8(v___x_1182_);
lean_dec_ref(v___x_1182_);
lean_inc_ref(v___x_1183_);
v___x_1184_ = lean_array_push(v___x_1180_, v___x_1183_);
v___x_1185_ = lean_byte_array_size(v___x_1183_);
lean_dec_ref(v___x_1183_);
v___x_1186_ = lean_nat_add(v___x_1181_, v___x_1185_);
lean_dec(v___x_1181_);
v___x_1187_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_1188_ = lean_array_push(v___x_1184_, v___x_1187_);
v___x_1189_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3);
v___x_1190_ = lean_nat_add(v___x_1186_, v___x_1189_);
lean_dec(v___x_1186_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 1, v___x_1190_);
lean_ctor_set(v___x_1163_, 0, v___x_1188_);
v_buffer_1192_ = v___x_1163_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1188_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v___x_1190_);
v_buffer_1192_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
lean_object* v_buffer_1193_; lean_object* v_data_1194_; lean_object* v_size_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1204_; 
v_buffer_1193_ = l_Std_Http_Headers_fold___redArg(v_headers_1156_, v_buffer_1192_, v___f_1157_);
v_data_1194_ = lean_ctor_get(v_buffer_1193_, 0);
v_size_1195_ = lean_ctor_get(v_buffer_1193_, 1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_buffer_1193_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1197_ = v_buffer_1193_;
v_isShared_1198_ = v_isSharedCheck_1204_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_size_1195_);
lean_inc(v_data_1194_);
lean_dec(v_buffer_1193_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1204_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1199_ = lean_array_push(v_data_1194_, v___x_1187_);
v___x_1200_ = lean_nat_add(v_size_1195_, v___x_1189_);
lean_dec(v_size_1195_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 1, v___x_1200_);
lean_ctor_set(v___x_1197_, 0, v___x_1199_);
v___x_1202_ = v___x_1197_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1199_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___boxed(lean_object* v_buffer_1211_, lean_object* v_r_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(v_buffer_1211_, v_r_1212_);
lean_dec_ref(v_r_1212_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head(uint8_t v_dir_1216_){
_start:
{
if (v_dir_1216_ == 0)
{
lean_object* v___x_1217_; 
v___x_1217_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___closed__0));
return v___x_1217_;
}
else
{
lean_object* v___x_1218_; 
v___x_1218_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___closed__1));
return v___x_1218_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___boxed(lean_object* v_dir_1219_){
_start:
{
uint8_t v_dir_boxed_1220_; lean_object* v_res_1221_; 
v_dir_boxed_1220_ = lean_unbox(v_dir_1219_);
v_res_1221_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v_dir_boxed_1220_);
return v_res_1221_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; uint8_t v___x_1225_; lean_object* v___x_1226_; 
v___x_1222_ = l_Std_Http_Headers_empty;
v___x_1223_ = lean_box(3);
v___x_1224_ = 1;
v___x_1225_ = 8;
v___x_1226_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1226_, 0, v___x_1223_);
lean_ctor_set(v___x_1226_, 1, v___x_1222_);
lean_ctor_set_uint8(v___x_1226_, sizeof(void*)*2, v___x_1225_);
lean_ctor_set_uint8(v___x_1226_, sizeof(void*)*2 + 1, v___x_1224_);
return v___x_1226_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1(void){
_start:
{
lean_object* v___x_1227_; uint8_t v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1227_ = l_Std_Http_Headers_empty;
v___x_1228_ = 1;
v___x_1229_ = lean_box(4);
v___x_1230_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
lean_ctor_set(v___x_1230_, 1, v___x_1227_);
lean_ctor_set_uint8(v___x_1230_, sizeof(void*)*2, v___x_1228_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead(uint8_t v_dir_1231_){
_start:
{
if (v_dir_1231_ == 0)
{
lean_object* v___x_1232_; 
v___x_1232_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0, &l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0_once, _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0);
return v___x_1232_;
}
else
{
lean_object* v___x_1233_; 
v___x_1233_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1, &l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1_once, _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1);
return v___x_1233_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead___boxed(lean_object* v_dir_1234_){
_start:
{
uint8_t v_dir_boxed_1235_; lean_object* v_res_1236_; 
v_dir_boxed_1235_ = lean_unbox(v_dir_1234_);
v_res_1236_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v_dir_boxed_1235_);
return v_res_1236_;
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
