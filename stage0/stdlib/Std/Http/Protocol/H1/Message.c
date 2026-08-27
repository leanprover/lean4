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
uint8_t lean_uint32_to_uint8(uint32_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_byte_array_mk(lean_object*);
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
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_splitToSubslice___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
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
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__2 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__2_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__3 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__3_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5_value;
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
static lean_once_cell_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23;
static lean_once_cell_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24;
static lean_once_cell_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "//"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ACL"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "BASELINE-CONTROL"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "BIND"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CHECKIN"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CHECKOUT"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CONNECT"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "COPY"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "DELETE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "GET"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "LABEL"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LINK"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LOCK"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MERGE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKACTIVITY"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKCALENDAR"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MKCOL"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "MKREDIRECTREF"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MKWORKSPACE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "MOVE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "OPTIONS"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ORDERPATCH"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PATCH"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "POST"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PRI"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "PROPFIND"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PROPPATCH"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PUT"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "QUERY"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REBIND"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REPORT"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "SEARCH"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "TRACE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNBIND"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "UNCHECKOUT"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLINK"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLOCK"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UPDATE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "UPDATEREDIRECTREF"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "VERSION-CONTROL"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__68 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__68_value;
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
lean_inc_ref(v_indexes_264_);
v___x_265_ = l_Std_Http_Header_Name_contentLength;
v___x_266_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_264_, v___x_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; 
lean_dec_ref(v_indexes_264_);
v___x_267_ = lean_box(0);
v___y_213_ = v___x_267_;
goto v___jp_212_;
}
else
{
lean_object* v___x_268_; size_t v_sz_269_; size_t v___x_270_; lean_object* v_entries_271_; lean_object* v___x_272_; 
v___x_268_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v_indexes_264_, v___x_265_);
lean_dec_ref(v_indexes_264_);
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
lean_inc_ref(v_indexes_214_);
v___x_215_ = l_Std_Http_Header_Name_transferEncoding;
v___x_216_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_214_, v___x_215_);
if (v___x_216_ == 0)
{
lean_dec_ref(v_indexes_214_);
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
lean_dec_ref(v_indexes_214_);
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
lean_inc_ref(v_indexes_430_);
v___x_431_ = l_Std_Http_Header_Name_connection;
v___x_432_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_430_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; 
lean_dec_ref(v_indexes_430_);
lean_dec_ref(v___x_429_);
v___x_433_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0));
v_val_408_ = v___x_433_;
goto v___jp_407_;
}
else
{
lean_object* v___x_434_; size_t v_sz_435_; size_t v___x_436_; lean_object* v_entries_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_434_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v_indexes_430_, v___x_431_);
lean_dec_ref(v_indexes_430_);
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
lean_object* v_it_491_; lean_object* v_out_492_; lean_object* v___y_508_; uint32_t v___y_509_; lean_object* v___y_510_; uint8_t v___y_511_; lean_object* v_it_517_; lean_object* v_startInclusive_518_; lean_object* v_endExclusive_519_; 
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
v___x_512_ = lean_string_utf8_set(v___y_510_, v___x_480_, v___y_509_);
v_it_491_ = v___y_508_;
v_out_492_ = v___x_512_;
goto v___jp_490_;
}
else
{
uint32_t v___x_513_; uint32_t v___x_514_; lean_object* v___x_515_; 
v___x_513_ = 4294967264;
v___x_514_ = lean_uint32_add(v___y_509_, v___x_513_);
v___x_515_ = lean_string_utf8_set(v___y_510_, v___x_480_, v___x_514_);
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
v___y_509_ = v___x_521_;
v___y_510_ = v___x_520_;
v___y_511_ = v___x_523_;
goto v___jp_507_;
}
else
{
uint32_t v___x_524_; uint8_t v___x_525_; 
v___x_524_ = 122;
v___x_525_ = lean_uint32_dec_le(v___x_521_, v___x_524_);
v___y_508_ = v_it_517_;
v___y_509_ = v___x_521_;
v___y_510_ = v___x_520_;
v___y_511_ = v___x_525_;
goto v___jp_507_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1___boxed(lean_object* v___x_550_, lean_object* v___x_551_, lean_object* v___x_552_, lean_object* v_name_553_, lean_object* v___x_554_, lean_object* v___x_555_, lean_object* v___x_556_, lean_object* v_it_557_, lean_object* v_acc_558_, lean_object* v_hP_559_, lean_object* v_recur_560_){
_start:
{
uint32_t v___x_2755__boxed_561_; lean_object* v_res_562_; 
v___x_2755__boxed_561_ = lean_unbox_uint32(v___x_555_);
lean_dec(v___x_555_);
v_res_562_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1(v___x_550_, v___x_551_, v___x_552_, v_name_553_, v___x_554_, v___x_2755__boxed_561_, v___x_556_, v_it_557_, v_acc_558_, v_hP_559_, v_recur_560_);
lean_dec_ref(v___x_556_);
lean_dec_ref(v_name_553_);
lean_dec(v___x_552_);
lean_dec(v___x_551_);
lean_dec_ref(v___x_550_);
return v_res_562_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__3));
v___x_568_ = lean_string_utf8_byte_size(v___x_567_);
return v___x_568_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed__const__1(void){
_start:
{
uint32_t v___x_570_; lean_object* v___x_571_; 
v___x_570_ = 45;
v___x_571_ = lean_box_uint32(v___x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2(lean_object* v_buf_572_, lean_object* v_name_573_, lean_object* v_value_574_){
_start:
{
lean_object* v___y_576_; lean_object* v___f_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v_it_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___f_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___f_595_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__2));
v___x_596_ = lean_unsigned_to_nat(0u);
v___x_597_ = lean_string_utf8_byte_size(v_name_573_);
lean_inc_ref(v_name_573_);
v___x_598_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_598_, 0, v_name_573_);
lean_ctor_set(v___x_598_, 1, v___x_596_);
lean_ctor_set(v___x_598_, 2, v___x_597_);
lean_inc_ref(v___x_598_);
v_it_599_ = l_String_Slice_splitToSubslice___redArg(v___x_598_, v___f_595_);
v___x_600_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__3));
v___x_601_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4);
v___x_602_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed__const__1;
v___f_603_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1___boxed), 11, 7);
lean_closure_set(v___f_603_, 0, v___x_600_);
lean_closure_set(v___f_603_, 1, v___x_596_);
lean_closure_set(v___f_603_, 2, v___x_601_);
lean_closure_set(v___f_603_, 3, v_name_573_);
lean_closure_set(v___f_603_, 4, v___x_597_);
lean_closure_set(v___f_603_, 5, v___x_602_);
lean_closure_set(v___f_603_, 6, v___x_598_);
v___x_604_ = lean_box(0);
v___x_605_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_603_, v_it_599_, v___x_604_, lean_box(0));
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v___x_606_; 
v___x_606_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_576_ = v___x_606_;
goto v___jp_575_;
}
else
{
lean_object* v_val_607_; 
v_val_607_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_val_607_);
lean_dec_ref_known(v___x_605_, 1);
v___y_576_ = v_val_607_;
goto v___jp_575_;
}
v___jp_575_:
{
lean_object* v_data_577_; lean_object* v_size_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_594_; 
v_data_577_ = lean_ctor_get(v_buf_572_, 0);
v_size_578_ = lean_ctor_get(v_buf_572_, 1);
v_isSharedCheck_594_ = !lean_is_exclusive(v_buf_572_);
if (v_isSharedCheck_594_ == 0)
{
v___x_580_ = v_buf_572_;
v_isShared_581_ = v_isSharedCheck_594_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_size_578_);
lean_inc(v_data_577_);
lean_dec(v_buf_572_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_594_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_582_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__0));
v___x_583_ = lean_string_append(v___y_576_, v___x_582_);
v___x_584_ = lean_string_append(v___x_583_, v_value_574_);
v___x_585_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__1));
v___x_586_ = lean_string_append(v___x_584_, v___x_585_);
v___x_587_ = lean_string_to_utf8(v___x_586_);
lean_dec_ref(v___x_586_);
lean_inc_ref(v___x_587_);
v___x_588_ = lean_array_push(v_data_577_, v___x_587_);
v___x_589_ = lean_byte_array_size(v___x_587_);
lean_dec_ref(v___x_587_);
v___x_590_ = lean_nat_add(v_size_578_, v___x_589_);
lean_dec(v_size_578_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v___x_590_);
lean_ctor_set(v___x_580_, 0, v___x_588_);
v___x_592_ = v___x_580_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed(lean_object* v_buf_608_, lean_object* v_name_609_, lean_object* v_value_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2(v_buf_608_, v_name_609_, v_value_610_);
lean_dec_ref(v_value_610_);
return v_res_611_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__1));
v___x_615_ = lean_string_to_utf8(v___x_614_);
return v___x_615_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_617_ = lean_byte_array_size(v___x_616_);
return v___x_617_;
}
}
static uint8_t _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23(void){
_start:
{
uint32_t v___x_646_; uint8_t v___x_647_; 
v___x_646_ = 32;
v___x_647_ = lean_uint32_to_uint8(v___x_646_);
return v___x_647_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24(void){
_start:
{
uint8_t v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_648_ = lean_uint8_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23);
v___x_649_ = lean_unsigned_to_nat(1u);
v___x_650_ = lean_mk_empty_array_with_capacity(v___x_649_);
v___x_651_ = lean_box(v___x_648_);
v___x_652_ = lean_array_push(v___x_650_, v___x_651_);
v___x_653_ = lean_byte_array_mk(v___x_652_);
return v___x_653_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24);
v___x_655_ = lean_byte_array_size(v___x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1(lean_object* v_buffer_699_, lean_object* v_req_700_){
_start:
{
uint8_t v_method_701_; uint8_t v_version_702_; lean_object* v_uri_703_; lean_object* v_headers_704_; lean_object* v___f_705_; lean_object* v___f_706_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v_port_764_; lean_object* v___y_765_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v_host_778_; lean_object* v_port_779_; lean_object* v___y_780_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v_port_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v_host_893_; lean_object* v_port_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_911_; 
v_method_701_ = lean_ctor_get_uint8(v_req_700_, sizeof(void*)*2);
v_version_702_ = lean_ctor_get_uint8(v_req_700_, sizeof(void*)*2 + 1);
v_uri_703_ = lean_ctor_get(v_req_700_, 0);
lean_inc(v_uri_703_);
v_headers_704_ = lean_ctor_get(v_req_700_, 1);
lean_inc_ref(v_headers_704_);
lean_dec_ref(v_req_700_);
v___f_705_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__0));
v___f_706_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1));
switch(v_method_701_)
{
case 0:
{
lean_object* v___x_991_; 
v___x_991_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29));
v___y_911_ = v___x_991_;
goto v___jp_910_;
}
case 1:
{
lean_object* v___x_992_; 
v___x_992_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30));
v___y_911_ = v___x_992_;
goto v___jp_910_;
}
case 2:
{
lean_object* v___x_993_; 
v___x_993_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31));
v___y_911_ = v___x_993_;
goto v___jp_910_;
}
case 3:
{
lean_object* v___x_994_; 
v___x_994_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32));
v___y_911_ = v___x_994_;
goto v___jp_910_;
}
case 4:
{
lean_object* v___x_995_; 
v___x_995_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33));
v___y_911_ = v___x_995_;
goto v___jp_910_;
}
case 5:
{
lean_object* v___x_996_; 
v___x_996_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34));
v___y_911_ = v___x_996_;
goto v___jp_910_;
}
case 6:
{
lean_object* v___x_997_; 
v___x_997_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35));
v___y_911_ = v___x_997_;
goto v___jp_910_;
}
case 7:
{
lean_object* v___x_998_; 
v___x_998_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36));
v___y_911_ = v___x_998_;
goto v___jp_910_;
}
case 8:
{
lean_object* v___x_999_; 
v___x_999_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37));
v___y_911_ = v___x_999_;
goto v___jp_910_;
}
case 9:
{
lean_object* v___x_1000_; 
v___x_1000_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38));
v___y_911_ = v___x_1000_;
goto v___jp_910_;
}
case 10:
{
lean_object* v___x_1001_; 
v___x_1001_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39));
v___y_911_ = v___x_1001_;
goto v___jp_910_;
}
case 11:
{
lean_object* v___x_1002_; 
v___x_1002_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40));
v___y_911_ = v___x_1002_;
goto v___jp_910_;
}
case 12:
{
lean_object* v___x_1003_; 
v___x_1003_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41));
v___y_911_ = v___x_1003_;
goto v___jp_910_;
}
case 13:
{
lean_object* v___x_1004_; 
v___x_1004_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42));
v___y_911_ = v___x_1004_;
goto v___jp_910_;
}
case 14:
{
lean_object* v___x_1005_; 
v___x_1005_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43));
v___y_911_ = v___x_1005_;
goto v___jp_910_;
}
case 15:
{
lean_object* v___x_1006_; 
v___x_1006_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44));
v___y_911_ = v___x_1006_;
goto v___jp_910_;
}
case 16:
{
lean_object* v___x_1007_; 
v___x_1007_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45));
v___y_911_ = v___x_1007_;
goto v___jp_910_;
}
case 17:
{
lean_object* v___x_1008_; 
v___x_1008_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46));
v___y_911_ = v___x_1008_;
goto v___jp_910_;
}
case 18:
{
lean_object* v___x_1009_; 
v___x_1009_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47));
v___y_911_ = v___x_1009_;
goto v___jp_910_;
}
case 19:
{
lean_object* v___x_1010_; 
v___x_1010_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48));
v___y_911_ = v___x_1010_;
goto v___jp_910_;
}
case 20:
{
lean_object* v___x_1011_; 
v___x_1011_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49));
v___y_911_ = v___x_1011_;
goto v___jp_910_;
}
case 21:
{
lean_object* v___x_1012_; 
v___x_1012_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50));
v___y_911_ = v___x_1012_;
goto v___jp_910_;
}
case 22:
{
lean_object* v___x_1013_; 
v___x_1013_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51));
v___y_911_ = v___x_1013_;
goto v___jp_910_;
}
case 23:
{
lean_object* v___x_1014_; 
v___x_1014_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52));
v___y_911_ = v___x_1014_;
goto v___jp_910_;
}
case 24:
{
lean_object* v___x_1015_; 
v___x_1015_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53));
v___y_911_ = v___x_1015_;
goto v___jp_910_;
}
case 25:
{
lean_object* v___x_1016_; 
v___x_1016_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54));
v___y_911_ = v___x_1016_;
goto v___jp_910_;
}
case 26:
{
lean_object* v___x_1017_; 
v___x_1017_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55));
v___y_911_ = v___x_1017_;
goto v___jp_910_;
}
case 27:
{
lean_object* v___x_1018_; 
v___x_1018_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56));
v___y_911_ = v___x_1018_;
goto v___jp_910_;
}
case 28:
{
lean_object* v___x_1019_; 
v___x_1019_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57));
v___y_911_ = v___x_1019_;
goto v___jp_910_;
}
case 29:
{
lean_object* v___x_1020_; 
v___x_1020_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58));
v___y_911_ = v___x_1020_;
goto v___jp_910_;
}
case 30:
{
lean_object* v___x_1021_; 
v___x_1021_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59));
v___y_911_ = v___x_1021_;
goto v___jp_910_;
}
case 31:
{
lean_object* v___x_1022_; 
v___x_1022_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60));
v___y_911_ = v___x_1022_;
goto v___jp_910_;
}
case 32:
{
lean_object* v___x_1023_; 
v___x_1023_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61));
v___y_911_ = v___x_1023_;
goto v___jp_910_;
}
case 33:
{
lean_object* v___x_1024_; 
v___x_1024_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62));
v___y_911_ = v___x_1024_;
goto v___jp_910_;
}
case 34:
{
lean_object* v___x_1025_; 
v___x_1025_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63));
v___y_911_ = v___x_1025_;
goto v___jp_910_;
}
case 35:
{
lean_object* v___x_1026_; 
v___x_1026_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64));
v___y_911_ = v___x_1026_;
goto v___jp_910_;
}
case 36:
{
lean_object* v___x_1027_; 
v___x_1027_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65));
v___y_911_ = v___x_1027_;
goto v___jp_910_;
}
case 37:
{
lean_object* v___x_1028_; 
v___x_1028_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66));
v___y_911_ = v___x_1028_;
goto v___jp_910_;
}
case 38:
{
lean_object* v___x_1029_; 
v___x_1029_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67));
v___y_911_ = v___x_1029_;
goto v___jp_910_;
}
default: 
{
lean_object* v___x_1030_; 
v___x_1030_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__68));
v___y_911_ = v___x_1030_;
goto v___jp_910_;
}
}
v___jp_707_:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v_buffer_719_; lean_object* v_buffer_720_; lean_object* v_data_721_; lean_object* v_size_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_731_; 
v___x_711_ = lean_string_to_utf8(v___y_710_);
lean_inc_ref(v___x_711_);
v___x_712_ = lean_array_push(v___y_709_, v___x_711_);
v___x_713_ = lean_byte_array_size(v___x_711_);
lean_dec_ref(v___x_711_);
v___x_714_ = lean_nat_add(v___y_708_, v___x_713_);
lean_dec(v___y_708_);
v___x_715_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_716_ = lean_array_push(v___x_712_, v___x_715_);
v___x_717_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3);
v___x_718_ = lean_nat_add(v___x_714_, v___x_717_);
lean_dec(v___x_714_);
v_buffer_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_buffer_719_, 0, v___x_716_);
lean_ctor_set(v_buffer_719_, 1, v___x_718_);
v_buffer_720_ = l_Std_Http_Headers_fold___redArg(v_headers_704_, v_buffer_719_, v___f_706_);
lean_dec_ref(v_headers_704_);
v_data_721_ = lean_ctor_get(v_buffer_720_, 0);
v_size_722_ = lean_ctor_get(v_buffer_720_, 1);
v_isSharedCheck_731_ = !lean_is_exclusive(v_buffer_720_);
if (v_isSharedCheck_731_ == 0)
{
v___x_724_ = v_buffer_720_;
v_isShared_725_ = v_isSharedCheck_731_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_size_722_);
lean_inc(v_data_721_);
lean_dec(v_buffer_720_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_731_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_726_ = lean_array_push(v_data_721_, v___x_715_);
v___x_727_ = lean_nat_add(v_size_722_, v___x_717_);
lean_dec(v_size_722_);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 1, v___x_727_);
lean_ctor_set(v___x_724_, 0, v___x_726_);
v___x_729_ = v___x_724_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v___x_727_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
v___jp_732_:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_738_ = lean_string_to_utf8(v___y_737_);
lean_dec_ref(v___y_737_);
lean_inc_ref(v___x_738_);
v___x_739_ = lean_array_push(v___y_736_, v___x_738_);
v___x_740_ = lean_byte_array_size(v___x_738_);
lean_dec_ref(v___x_738_);
v___x_741_ = lean_nat_add(v___y_734_, v___x_740_);
lean_dec(v___y_734_);
v___x_742_ = lean_array_push(v___x_739_, v___y_735_);
v___x_743_ = lean_nat_add(v___x_741_, v___y_733_);
lean_dec(v___x_741_);
switch(v_version_702_)
{
case 0:
{
lean_object* v___x_744_; 
v___x_744_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4));
v___y_708_ = v___x_743_;
v___y_709_ = v___x_742_;
v___y_710_ = v___x_744_;
goto v___jp_707_;
}
case 1:
{
lean_object* v___x_745_; 
v___x_745_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5));
v___y_708_ = v___x_743_;
v___y_709_ = v___x_742_;
v___y_710_ = v___x_745_;
goto v___jp_707_;
}
case 2:
{
lean_object* v___x_746_; 
v___x_746_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6));
v___y_708_ = v___x_743_;
v___y_709_ = v___x_742_;
v___y_710_ = v___x_746_;
goto v___jp_707_;
}
default: 
{
lean_object* v___x_747_; 
v___x_747_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7));
v___y_708_ = v___x_743_;
v___y_709_ = v___x_742_;
v___y_710_ = v___x_747_;
goto v___jp_707_;
}
}
}
v___jp_748_:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_string_append(v___y_754_, v___y_753_);
lean_dec_ref(v___y_753_);
v___x_757_ = lean_string_append(v___x_756_, v___y_755_);
lean_dec_ref(v___y_755_);
v___y_733_ = v___y_750_;
v___y_734_ = v___y_749_;
v___y_735_ = v___y_751_;
v___y_736_ = v___y_752_;
v___y_737_ = v___x_757_;
goto v___jp_732_;
}
v___jp_758_:
{
switch(lean_obj_tag(v_port_764_))
{
case 0:
{
lean_object* v___x_766_; 
v___x_766_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_749_ = v___y_760_;
v___y_750_ = v___y_759_;
v___y_751_ = v___y_761_;
v___y_752_ = v___y_762_;
v___y_753_ = v___y_765_;
v___y_754_ = v___y_763_;
v___y_755_ = v___x_766_;
goto v___jp_748_;
}
case 1:
{
lean_object* v___x_767_; 
v___x_767_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___y_749_ = v___y_760_;
v___y_750_ = v___y_759_;
v___y_751_ = v___y_761_;
v___y_752_ = v___y_762_;
v___y_753_ = v___y_765_;
v___y_754_ = v___y_763_;
v___y_755_ = v___x_767_;
goto v___jp_748_;
}
default: 
{
uint16_t v_port_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_port_768_ = lean_ctor_get_uint16(v_port_764_, 0);
lean_dec_ref_known(v_port_764_, 0);
v___x_769_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_770_ = lean_uint16_to_nat(v_port_768_);
v___x_771_ = l_Nat_reprFast(v___x_770_);
v___x_772_ = lean_string_append(v___x_769_, v___x_771_);
lean_dec_ref(v___x_771_);
v___y_749_ = v___y_760_;
v___y_750_ = v___y_759_;
v___y_751_ = v___y_761_;
v___y_752_ = v___y_762_;
v___y_753_ = v___y_765_;
v___y_754_ = v___y_763_;
v___y_755_ = v___x_772_;
goto v___jp_748_;
}
}
}
v___jp_773_:
{
switch(lean_obj_tag(v_host_778_))
{
case 0:
{
lean_object* v_name_781_; 
v_name_781_ = lean_ctor_get(v_host_778_, 0);
lean_inc_ref(v_name_781_);
lean_dec_ref_known(v_host_778_, 1);
v___y_759_ = v___y_775_;
v___y_760_ = v___y_774_;
v___y_761_ = v___y_776_;
v___y_762_ = v___y_777_;
v___y_763_ = v___y_780_;
v_port_764_ = v_port_779_;
v___y_765_ = v_name_781_;
goto v___jp_758_;
}
case 1:
{
lean_object* v_ipv4_782_; lean_object* v___x_783_; 
v_ipv4_782_ = lean_ctor_get(v_host_778_, 0);
lean_inc_ref(v_ipv4_782_);
lean_dec_ref_known(v_host_778_, 1);
v___x_783_ = lean_uv_ntop_v4(v_ipv4_782_);
lean_dec_ref(v_ipv4_782_);
v___y_759_ = v___y_775_;
v___y_760_ = v___y_774_;
v___y_761_ = v___y_776_;
v___y_762_ = v___y_777_;
v___y_763_ = v___y_780_;
v_port_764_ = v_port_779_;
v___y_765_ = v___x_783_;
goto v___jp_758_;
}
default: 
{
lean_object* v_ipv6_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v_ipv6_784_ = lean_ctor_get(v_host_778_, 0);
lean_inc_ref(v_ipv6_784_);
lean_dec_ref_known(v_host_778_, 1);
v___x_785_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9));
v___x_786_ = lean_uv_ntop_v6(v_ipv6_784_);
lean_dec_ref(v_ipv6_784_);
v___x_787_ = lean_string_append(v___x_785_, v___x_786_);
lean_dec_ref(v___x_786_);
v___x_788_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10));
v___x_789_ = lean_string_append(v___x_787_, v___x_788_);
v___y_759_ = v___y_775_;
v___y_760_ = v___y_774_;
v___y_761_ = v___y_776_;
v___y_762_ = v___y_777_;
v___y_763_ = v___y_780_;
v_port_764_ = v_port_779_;
v___y_765_ = v___x_789_;
goto v___jp_758_;
}
}
}
v___jp_790_:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_800_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_801_ = lean_string_append(v___y_791_, v___x_800_);
v___x_802_ = lean_string_append(v___x_801_, v___y_798_);
lean_dec_ref(v___y_798_);
v___x_803_ = lean_string_append(v___x_802_, v___y_794_);
lean_dec_ref(v___y_794_);
v___x_804_ = lean_string_append(v___x_803_, v___y_797_);
lean_dec_ref(v___y_797_);
v___x_805_ = lean_string_append(v___x_804_, v___y_799_);
lean_dec_ref(v___y_799_);
v___y_733_ = v___y_793_;
v___y_734_ = v___y_792_;
v___y_735_ = v___y_795_;
v___y_736_ = v___y_796_;
v___y_737_ = v___x_805_;
goto v___jp_732_;
}
v___jp_806_:
{
lean_object* v_queryPart_816_; 
v_queryPart_816_ = l_Std_Http_URI_Query_formatOption(v___y_814_);
if (lean_obj_tag(v___y_812_) == 0)
{
lean_object* v___x_817_; 
v___x_817_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_791_ = v___y_807_;
v___y_792_ = v___y_809_;
v___y_793_ = v___y_808_;
v___y_794_ = v___y_815_;
v___y_795_ = v___y_810_;
v___y_796_ = v___y_811_;
v___y_797_ = v_queryPart_816_;
v___y_798_ = v___y_813_;
v___y_799_ = v___x_817_;
goto v___jp_790_;
}
else
{
lean_object* v_val_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v_val_818_ = lean_ctor_get(v___y_812_, 0);
lean_inc(v_val_818_);
lean_dec_ref_known(v___y_812_, 1);
v___x_819_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11));
v___x_820_ = l_Std_Http_URI_EncodedFragment_encode(v_val_818_);
lean_dec(v_val_818_);
v___x_821_ = lean_string_from_utf8_unchecked(v___x_820_);
v___x_822_ = lean_string_append(v___x_819_, v___x_821_);
lean_dec_ref(v___x_821_);
v___y_791_ = v___y_807_;
v___y_792_ = v___y_809_;
v___y_793_ = v___y_808_;
v___y_794_ = v___y_815_;
v___y_795_ = v___y_810_;
v___y_796_ = v___y_811_;
v___y_797_ = v_queryPart_816_;
v___y_798_ = v___y_813_;
v___y_799_ = v___x_822_;
goto v___jp_790_;
}
}
v___jp_823_:
{
lean_object* v_queryStr_830_; lean_object* v___x_831_; 
v_queryStr_830_ = l_Std_Http_URI_Query_formatOption(v___y_826_);
v___x_831_ = lean_string_append(v___y_829_, v_queryStr_830_);
lean_dec_ref(v_queryStr_830_);
v___y_733_ = v___y_825_;
v___y_734_ = v___y_824_;
v___y_735_ = v___y_827_;
v___y_736_ = v___y_828_;
v___y_737_ = v___x_831_;
goto v___jp_732_;
}
v___jp_832_:
{
lean_object* v_segments_842_; uint8_t v_absolute_843_; lean_object* v___x_844_; lean_object* v___x_845_; size_t v_sz_846_; size_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v_result_850_; 
v_segments_842_ = lean_ctor_get(v___y_836_, 0);
lean_inc_ref(v_segments_842_);
v_absolute_843_ = lean_ctor_get_uint8(v___y_836_, sizeof(void*)*1);
lean_dec_ref(v___y_836_);
v___x_844_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12));
v___x_845_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22));
v_sz_846_ = lean_array_size(v_segments_842_);
v___x_847_ = ((size_t)0ULL);
v___x_848_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_845_, v___f_705_, v_sz_846_, v___x_847_, v_segments_842_);
v___x_849_ = lean_array_to_list(v___x_848_);
v_result_850_ = l_String_intercalate(v___x_844_, v___x_849_);
if (v_absolute_843_ == 0)
{
v___y_807_ = v___y_833_;
v___y_808_ = v___y_835_;
v___y_809_ = v___y_834_;
v___y_810_ = v___y_837_;
v___y_811_ = v___y_838_;
v___y_812_ = v___y_839_;
v___y_813_ = v___y_841_;
v___y_814_ = v___y_840_;
v___y_815_ = v_result_850_;
goto v___jp_806_;
}
else
{
lean_object* v___x_851_; 
v___x_851_ = lean_string_append(v___x_844_, v_result_850_);
lean_dec_ref(v_result_850_);
v___y_807_ = v___y_833_;
v___y_808_ = v___y_835_;
v___y_809_ = v___y_834_;
v___y_810_ = v___y_837_;
v___y_811_ = v___y_838_;
v___y_812_ = v___y_839_;
v___y_813_ = v___y_841_;
v___y_814_ = v___y_840_;
v___y_815_ = v___x_851_;
goto v___jp_806_;
}
}
v___jp_852_:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_865_ = lean_string_append(v___y_861_, v___y_853_);
lean_dec_ref(v___y_853_);
v___x_866_ = lean_string_append(v___x_865_, v___y_864_);
lean_dec_ref(v___y_864_);
lean_inc_ref(v___y_859_);
v___x_867_ = lean_string_append(v___y_859_, v___x_866_);
lean_dec_ref(v___x_866_);
v___y_833_ = v___y_854_;
v___y_834_ = v___y_856_;
v___y_835_ = v___y_855_;
v___y_836_ = v___y_857_;
v___y_837_ = v___y_858_;
v___y_838_ = v___y_860_;
v___y_839_ = v___y_862_;
v___y_840_ = v___y_863_;
v___y_841_ = v___x_867_;
goto v___jp_832_;
}
v___jp_868_:
{
switch(lean_obj_tag(v_port_873_))
{
case 0:
{
lean_object* v___x_881_; 
v___x_881_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_853_ = v___y_880_;
v___y_854_ = v___y_869_;
v___y_855_ = v___y_871_;
v___y_856_ = v___y_870_;
v___y_857_ = v___y_872_;
v___y_858_ = v___y_875_;
v___y_859_ = v___y_874_;
v___y_860_ = v___y_877_;
v___y_861_ = v___y_876_;
v___y_862_ = v___y_878_;
v___y_863_ = v___y_879_;
v___y_864_ = v___x_881_;
goto v___jp_852_;
}
case 1:
{
lean_object* v___x_882_; 
v___x_882_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___y_853_ = v___y_880_;
v___y_854_ = v___y_869_;
v___y_855_ = v___y_871_;
v___y_856_ = v___y_870_;
v___y_857_ = v___y_872_;
v___y_858_ = v___y_875_;
v___y_859_ = v___y_874_;
v___y_860_ = v___y_877_;
v___y_861_ = v___y_876_;
v___y_862_ = v___y_878_;
v___y_863_ = v___y_879_;
v___y_864_ = v___x_882_;
goto v___jp_852_;
}
default: 
{
uint16_t v_port_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v_port_883_ = lean_ctor_get_uint16(v_port_873_, 0);
lean_dec_ref_known(v_port_873_, 0);
v___x_884_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_885_ = lean_uint16_to_nat(v_port_883_);
v___x_886_ = l_Nat_reprFast(v___x_885_);
v___x_887_ = lean_string_append(v___x_884_, v___x_886_);
lean_dec_ref(v___x_886_);
v___y_853_ = v___y_880_;
v___y_854_ = v___y_869_;
v___y_855_ = v___y_871_;
v___y_856_ = v___y_870_;
v___y_857_ = v___y_872_;
v___y_858_ = v___y_875_;
v___y_859_ = v___y_874_;
v___y_860_ = v___y_877_;
v___y_861_ = v___y_876_;
v___y_862_ = v___y_878_;
v___y_863_ = v___y_879_;
v___y_864_ = v___x_887_;
goto v___jp_852_;
}
}
}
v___jp_888_:
{
switch(lean_obj_tag(v_host_893_))
{
case 0:
{
lean_object* v_name_901_; 
v_name_901_ = lean_ctor_get(v_host_893_, 0);
lean_inc_ref(v_name_901_);
lean_dec_ref_known(v_host_893_, 1);
v___y_869_ = v___y_889_;
v___y_870_ = v___y_891_;
v___y_871_ = v___y_890_;
v___y_872_ = v___y_892_;
v_port_873_ = v_port_894_;
v___y_874_ = v___y_896_;
v___y_875_ = v___y_895_;
v___y_876_ = v___y_900_;
v___y_877_ = v___y_897_;
v___y_878_ = v___y_898_;
v___y_879_ = v___y_899_;
v___y_880_ = v_name_901_;
goto v___jp_868_;
}
case 1:
{
lean_object* v_ipv4_902_; lean_object* v___x_903_; 
v_ipv4_902_ = lean_ctor_get(v_host_893_, 0);
lean_inc_ref(v_ipv4_902_);
lean_dec_ref_known(v_host_893_, 1);
v___x_903_ = lean_uv_ntop_v4(v_ipv4_902_);
lean_dec_ref(v_ipv4_902_);
v___y_869_ = v___y_889_;
v___y_870_ = v___y_891_;
v___y_871_ = v___y_890_;
v___y_872_ = v___y_892_;
v_port_873_ = v_port_894_;
v___y_874_ = v___y_896_;
v___y_875_ = v___y_895_;
v___y_876_ = v___y_900_;
v___y_877_ = v___y_897_;
v___y_878_ = v___y_898_;
v___y_879_ = v___y_899_;
v___y_880_ = v___x_903_;
goto v___jp_868_;
}
default: 
{
lean_object* v_ipv6_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v_ipv6_904_ = lean_ctor_get(v_host_893_, 0);
lean_inc_ref(v_ipv6_904_);
lean_dec_ref_known(v_host_893_, 1);
v___x_905_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9));
v___x_906_ = lean_uv_ntop_v6(v_ipv6_904_);
lean_dec_ref(v_ipv6_904_);
v___x_907_ = lean_string_append(v___x_905_, v___x_906_);
lean_dec_ref(v___x_906_);
v___x_908_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10));
v___x_909_ = lean_string_append(v___x_907_, v___x_908_);
v___y_869_ = v___y_889_;
v___y_870_ = v___y_891_;
v___y_871_ = v___y_890_;
v___y_872_ = v___y_892_;
v_port_873_ = v_port_894_;
v___y_874_ = v___y_896_;
v___y_875_ = v___y_895_;
v___y_876_ = v___y_900_;
v___y_877_ = v___y_897_;
v___y_878_ = v___y_898_;
v___y_879_ = v___y_899_;
v___y_880_ = v___x_909_;
goto v___jp_868_;
}
}
}
v___jp_910_:
{
lean_object* v_data_912_; lean_object* v_size_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v_data_912_ = lean_ctor_get(v_buffer_699_, 0);
lean_inc_ref(v_data_912_);
v_size_913_ = lean_ctor_get(v_buffer_699_, 1);
lean_inc(v_size_913_);
lean_dec_ref(v_buffer_699_);
v___x_914_ = lean_string_to_utf8(v___y_911_);
lean_inc_ref(v___x_914_);
v___x_915_ = lean_array_push(v_data_912_, v___x_914_);
v___x_916_ = lean_byte_array_size(v___x_914_);
lean_dec_ref(v___x_914_);
v___x_917_ = lean_nat_add(v_size_913_, v___x_916_);
lean_dec(v_size_913_);
v___x_918_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24);
v___x_919_ = lean_array_push(v___x_915_, v___x_918_);
v___x_920_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25);
v___x_921_ = lean_nat_add(v___x_917_, v___x_920_);
lean_dec(v___x_917_);
switch(lean_obj_tag(v_uri_703_))
{
case 0:
{
lean_object* v_path_922_; lean_object* v_query_923_; lean_object* v_segments_924_; uint8_t v_absolute_925_; lean_object* v___x_926_; lean_object* v___x_927_; size_t v_sz_928_; size_t v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v_result_932_; 
v_path_922_ = lean_ctor_get(v_uri_703_, 0);
lean_inc_ref(v_path_922_);
v_query_923_ = lean_ctor_get(v_uri_703_, 1);
lean_inc(v_query_923_);
lean_dec_ref_known(v_uri_703_, 2);
v_segments_924_ = lean_ctor_get(v_path_922_, 0);
lean_inc_ref(v_segments_924_);
v_absolute_925_ = lean_ctor_get_uint8(v_path_922_, sizeof(void*)*1);
lean_dec_ref(v_path_922_);
v___x_926_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12));
v___x_927_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22));
v_sz_928_ = lean_array_size(v_segments_924_);
v___x_929_ = ((size_t)0ULL);
v___x_930_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_927_, v___f_705_, v_sz_928_, v___x_929_, v_segments_924_);
v___x_931_ = lean_array_to_list(v___x_930_);
v_result_932_ = l_String_intercalate(v___x_926_, v___x_931_);
if (v_absolute_925_ == 0)
{
v___y_824_ = v___x_921_;
v___y_825_ = v___x_920_;
v___y_826_ = v_query_923_;
v___y_827_ = v___x_918_;
v___y_828_ = v___x_919_;
v___y_829_ = v_result_932_;
goto v___jp_823_;
}
else
{
lean_object* v___x_933_; 
v___x_933_ = lean_string_append(v___x_926_, v_result_932_);
lean_dec_ref(v_result_932_);
v___y_824_ = v___x_921_;
v___y_825_ = v___x_920_;
v___y_826_ = v_query_923_;
v___y_827_ = v___x_918_;
v___y_828_ = v___x_919_;
v___y_829_ = v___x_933_;
goto v___jp_823_;
}
}
case 1:
{
lean_object* v_uri_934_; lean_object* v_authority_935_; 
v_uri_934_ = lean_ctor_get(v_uri_703_, 0);
lean_inc_ref(v_uri_934_);
lean_dec_ref_known(v_uri_703_, 1);
v_authority_935_ = lean_ctor_get(v_uri_934_, 1);
if (lean_obj_tag(v_authority_935_) == 0)
{
lean_object* v_scheme_936_; lean_object* v_path_937_; lean_object* v_query_938_; lean_object* v_fragment_939_; lean_object* v___x_940_; 
v_scheme_936_ = lean_ctor_get(v_uri_934_, 0);
lean_inc_ref(v_scheme_936_);
v_path_937_ = lean_ctor_get(v_uri_934_, 2);
lean_inc_ref(v_path_937_);
v_query_938_ = lean_ctor_get(v_uri_934_, 3);
lean_inc(v_query_938_);
v_fragment_939_ = lean_ctor_get(v_uri_934_, 4);
lean_inc(v_fragment_939_);
lean_dec_ref(v_uri_934_);
v___x_940_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_833_ = v_scheme_936_;
v___y_834_ = v___x_921_;
v___y_835_ = v___x_920_;
v___y_836_ = v_path_937_;
v___y_837_ = v___x_918_;
v___y_838_ = v___x_919_;
v___y_839_ = v_fragment_939_;
v___y_840_ = v_query_938_;
v___y_841_ = v___x_940_;
goto v___jp_832_;
}
else
{
lean_object* v_val_941_; lean_object* v_scheme_942_; lean_object* v_path_943_; lean_object* v_query_944_; lean_object* v_fragment_945_; lean_object* v_userInfo_946_; lean_object* v_host_947_; lean_object* v_port_948_; lean_object* v___x_949_; 
v_val_941_ = lean_ctor_get(v_authority_935_, 0);
lean_inc(v_val_941_);
v_scheme_942_ = lean_ctor_get(v_uri_934_, 0);
lean_inc_ref(v_scheme_942_);
v_path_943_ = lean_ctor_get(v_uri_934_, 2);
lean_inc_ref(v_path_943_);
v_query_944_ = lean_ctor_get(v_uri_934_, 3);
lean_inc(v_query_944_);
v_fragment_945_ = lean_ctor_get(v_uri_934_, 4);
lean_inc(v_fragment_945_);
lean_dec_ref(v_uri_934_);
v_userInfo_946_ = lean_ctor_get(v_val_941_, 0);
lean_inc(v_userInfo_946_);
v_host_947_ = lean_ctor_get(v_val_941_, 1);
lean_inc_ref(v_host_947_);
v_port_948_ = lean_ctor_get(v_val_941_, 2);
lean_inc(v_port_948_);
lean_dec(v_val_941_);
v___x_949_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26));
if (lean_obj_tag(v_userInfo_946_) == 0)
{
lean_object* v___x_950_; 
v___x_950_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_889_ = v_scheme_942_;
v___y_890_ = v___x_920_;
v___y_891_ = v___x_921_;
v___y_892_ = v_path_943_;
v_host_893_ = v_host_947_;
v_port_894_ = v_port_948_;
v___y_895_ = v___x_918_;
v___y_896_ = v___x_949_;
v___y_897_ = v___x_919_;
v___y_898_ = v_fragment_945_;
v___y_899_ = v_query_944_;
v___y_900_ = v___x_950_;
goto v___jp_888_;
}
else
{
lean_object* v_val_951_; lean_object* v_password_952_; 
v_val_951_ = lean_ctor_get(v_userInfo_946_, 0);
lean_inc(v_val_951_);
lean_dec_ref_known(v_userInfo_946_, 1);
v_password_952_ = lean_ctor_get(v_val_951_, 1);
if (lean_obj_tag(v_password_952_) == 0)
{
lean_object* v_username_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v_username_953_ = lean_ctor_get(v_val_951_, 0);
lean_inc_ref(v_username_953_);
lean_dec(v_val_951_);
v___x_954_ = lean_string_from_utf8_unchecked(v_username_953_);
v___x_955_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27));
v___x_956_ = lean_string_append(v___x_954_, v___x_955_);
v___y_889_ = v_scheme_942_;
v___y_890_ = v___x_920_;
v___y_891_ = v___x_921_;
v___y_892_ = v_path_943_;
v_host_893_ = v_host_947_;
v_port_894_ = v_port_948_;
v___y_895_ = v___x_918_;
v___y_896_ = v___x_949_;
v___y_897_ = v___x_919_;
v___y_898_ = v_fragment_945_;
v___y_899_ = v_query_944_;
v___y_900_ = v___x_956_;
goto v___jp_888_;
}
else
{
lean_object* v_username_957_; lean_object* v_val_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
lean_inc_ref(v_password_952_);
v_username_957_ = lean_ctor_get(v_val_951_, 0);
lean_inc_ref(v_username_957_);
lean_dec(v_val_951_);
v_val_958_ = lean_ctor_get(v_password_952_, 0);
lean_inc(v_val_958_);
lean_dec_ref_known(v_password_952_, 1);
v___x_959_ = lean_string_from_utf8_unchecked(v_username_957_);
v___x_960_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_961_ = lean_string_append(v___x_959_, v___x_960_);
v___x_962_ = lean_string_from_utf8_unchecked(v_val_958_);
v___x_963_ = lean_string_append(v___x_961_, v___x_962_);
lean_dec_ref(v___x_962_);
v___x_964_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27));
v___x_965_ = lean_string_append(v___x_963_, v___x_964_);
v___y_889_ = v_scheme_942_;
v___y_890_ = v___x_920_;
v___y_891_ = v___x_921_;
v___y_892_ = v_path_943_;
v_host_893_ = v_host_947_;
v_port_894_ = v_port_948_;
v___y_895_ = v___x_918_;
v___y_896_ = v___x_949_;
v___y_897_ = v___x_919_;
v___y_898_ = v_fragment_945_;
v___y_899_ = v_query_944_;
v___y_900_ = v___x_965_;
goto v___jp_888_;
}
}
}
}
case 2:
{
lean_object* v_authority_966_; lean_object* v_userInfo_967_; 
v_authority_966_ = lean_ctor_get(v_uri_703_, 0);
lean_inc_ref(v_authority_966_);
lean_dec_ref_known(v_uri_703_, 1);
v_userInfo_967_ = lean_ctor_get(v_authority_966_, 0);
if (lean_obj_tag(v_userInfo_967_) == 0)
{
lean_object* v_host_968_; lean_object* v_port_969_; lean_object* v___x_970_; 
v_host_968_ = lean_ctor_get(v_authority_966_, 1);
lean_inc_ref(v_host_968_);
v_port_969_ = lean_ctor_get(v_authority_966_, 2);
lean_inc(v_port_969_);
lean_dec_ref(v_authority_966_);
v___x_970_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_774_ = v___x_921_;
v___y_775_ = v___x_920_;
v___y_776_ = v___x_918_;
v___y_777_ = v___x_919_;
v_host_778_ = v_host_968_;
v_port_779_ = v_port_969_;
v___y_780_ = v___x_970_;
goto v___jp_773_;
}
else
{
lean_object* v_val_971_; lean_object* v_password_972_; 
v_val_971_ = lean_ctor_get(v_userInfo_967_, 0);
lean_inc(v_val_971_);
v_password_972_ = lean_ctor_get(v_val_971_, 1);
if (lean_obj_tag(v_password_972_) == 0)
{
lean_object* v_host_973_; lean_object* v_port_974_; lean_object* v_username_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v_host_973_ = lean_ctor_get(v_authority_966_, 1);
lean_inc_ref(v_host_973_);
v_port_974_ = lean_ctor_get(v_authority_966_, 2);
lean_inc(v_port_974_);
lean_dec_ref(v_authority_966_);
v_username_975_ = lean_ctor_get(v_val_971_, 0);
lean_inc_ref(v_username_975_);
lean_dec(v_val_971_);
v___x_976_ = lean_string_from_utf8_unchecked(v_username_975_);
v___x_977_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27));
v___x_978_ = lean_string_append(v___x_976_, v___x_977_);
v___y_774_ = v___x_921_;
v___y_775_ = v___x_920_;
v___y_776_ = v___x_918_;
v___y_777_ = v___x_919_;
v_host_778_ = v_host_973_;
v_port_779_ = v_port_974_;
v___y_780_ = v___x_978_;
goto v___jp_773_;
}
else
{
lean_object* v_host_979_; lean_object* v_port_980_; lean_object* v_username_981_; lean_object* v_val_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
lean_inc_ref(v_password_972_);
v_host_979_ = lean_ctor_get(v_authority_966_, 1);
lean_inc_ref(v_host_979_);
v_port_980_ = lean_ctor_get(v_authority_966_, 2);
lean_inc(v_port_980_);
lean_dec_ref(v_authority_966_);
v_username_981_ = lean_ctor_get(v_val_971_, 0);
lean_inc_ref(v_username_981_);
lean_dec(v_val_971_);
v_val_982_ = lean_ctor_get(v_password_972_, 0);
lean_inc(v_val_982_);
lean_dec_ref_known(v_password_972_, 1);
v___x_983_ = lean_string_from_utf8_unchecked(v_username_981_);
v___x_984_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_985_ = lean_string_append(v___x_983_, v___x_984_);
v___x_986_ = lean_string_from_utf8_unchecked(v_val_982_);
v___x_987_ = lean_string_append(v___x_985_, v___x_986_);
lean_dec_ref(v___x_986_);
v___x_988_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27));
v___x_989_ = lean_string_append(v___x_987_, v___x_988_);
v___y_774_ = v___x_921_;
v___y_775_ = v___x_920_;
v___y_776_ = v___x_918_;
v___y_777_ = v___x_919_;
v_host_778_ = v_host_979_;
v_port_779_ = v_port_980_;
v___y_780_ = v___x_989_;
goto v___jp_773_;
}
}
}
default: 
{
lean_object* v___x_990_; 
v___x_990_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28));
v___y_733_ = v___x_920_;
v___y_734_ = v___x_921_;
v___y_735_ = v___x_918_;
v___y_736_ = v___x_919_;
v___y_737_ = v___x_990_;
goto v___jp_732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(lean_object* v_buffer_1031_, lean_object* v_r_1032_){
_start:
{
lean_object* v_status_1033_; uint8_t v_version_1034_; lean_object* v_headers_1035_; lean_object* v___f_1036_; lean_object* v___y_1038_; 
v_status_1033_ = lean_ctor_get(v_r_1032_, 0);
v_version_1034_ = lean_ctor_get_uint8(v_r_1032_, sizeof(void*)*2);
v_headers_1035_ = lean_ctor_get(v_r_1032_, 1);
v___f_1036_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1));
switch(v_version_1034_)
{
case 0:
{
lean_object* v___x_1088_; 
v___x_1088_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4));
v___y_1038_ = v___x_1088_;
goto v___jp_1037_;
}
case 1:
{
lean_object* v___x_1089_; 
v___x_1089_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5));
v___y_1038_ = v___x_1089_;
goto v___jp_1037_;
}
case 2:
{
lean_object* v___x_1090_; 
v___x_1090_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6));
v___y_1038_ = v___x_1090_;
goto v___jp_1037_;
}
default: 
{
lean_object* v___x_1091_; 
v___x_1091_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7));
v___y_1038_ = v___x_1091_;
goto v___jp_1037_;
}
}
v___jp_1037_:
{
lean_object* v_data_1039_; lean_object* v_size_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1087_; 
v_data_1039_ = lean_ctor_get(v_buffer_1031_, 0);
v_size_1040_ = lean_ctor_get(v_buffer_1031_, 1);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_buffer_1031_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1042_ = v_buffer_1031_;
v_isShared_1043_ = v_isSharedCheck_1087_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_size_1040_);
lean_inc(v_data_1039_);
lean_dec(v_buffer_1031_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1087_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; uint16_t v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v_buffer_1073_; 
v___x_1044_ = lean_string_to_utf8(v___y_1038_);
lean_inc_ref(v___x_1044_);
v___x_1045_ = lean_array_push(v_data_1039_, v___x_1044_);
v___x_1046_ = lean_byte_array_size(v___x_1044_);
lean_dec_ref(v___x_1044_);
v___x_1047_ = lean_nat_add(v_size_1040_, v___x_1046_);
lean_dec(v_size_1040_);
v___x_1048_ = lean_unsigned_to_nat(1u);
v___x_1049_ = lean_mk_empty_array_with_capacity(v___x_1048_);
lean_dec_ref(v___x_1049_);
v___x_1050_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24);
v___x_1051_ = lean_array_push(v___x_1045_, v___x_1050_);
v___x_1052_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25);
v___x_1053_ = lean_nat_add(v___x_1047_, v___x_1052_);
lean_dec(v___x_1047_);
v___x_1054_ = l_Std_Http_Status_toCode(v_status_1033_);
v___x_1055_ = lean_uint16_to_nat(v___x_1054_);
v___x_1056_ = l_Nat_reprFast(v___x_1055_);
v___x_1057_ = lean_string_to_utf8(v___x_1056_);
lean_dec_ref(v___x_1056_);
lean_inc_ref(v___x_1057_);
v___x_1058_ = lean_array_push(v___x_1051_, v___x_1057_);
v___x_1059_ = lean_byte_array_size(v___x_1057_);
lean_dec_ref(v___x_1057_);
v___x_1060_ = lean_nat_add(v___x_1053_, v___x_1059_);
lean_dec(v___x_1053_);
v___x_1061_ = lean_array_push(v___x_1058_, v___x_1050_);
v___x_1062_ = lean_nat_add(v___x_1060_, v___x_1052_);
lean_dec(v___x_1060_);
v___x_1063_ = l_Std_Http_Status_reasonPhrase(v_status_1033_);
v___x_1064_ = lean_string_to_utf8(v___x_1063_);
lean_dec_ref(v___x_1063_);
lean_inc_ref(v___x_1064_);
v___x_1065_ = lean_array_push(v___x_1061_, v___x_1064_);
v___x_1066_ = lean_byte_array_size(v___x_1064_);
lean_dec_ref(v___x_1064_);
v___x_1067_ = lean_nat_add(v___x_1062_, v___x_1066_);
lean_dec(v___x_1062_);
v___x_1068_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_1069_ = lean_array_push(v___x_1065_, v___x_1068_);
v___x_1070_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3);
v___x_1071_ = lean_nat_add(v___x_1067_, v___x_1070_);
lean_dec(v___x_1067_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 1, v___x_1071_);
lean_ctor_set(v___x_1042_, 0, v___x_1069_);
v_buffer_1073_ = v___x_1042_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v___x_1071_);
v_buffer_1073_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v_buffer_1074_; lean_object* v_data_1075_; lean_object* v_size_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1085_; 
v_buffer_1074_ = l_Std_Http_Headers_fold___redArg(v_headers_1035_, v_buffer_1073_, v___f_1036_);
v_data_1075_ = lean_ctor_get(v_buffer_1074_, 0);
v_size_1076_ = lean_ctor_get(v_buffer_1074_, 1);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_buffer_1074_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1078_ = v_buffer_1074_;
v_isShared_1079_ = v_isSharedCheck_1085_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_size_1076_);
lean_inc(v_data_1075_);
lean_dec(v_buffer_1074_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1085_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1083_; 
v___x_1080_ = lean_array_push(v_data_1075_, v___x_1068_);
v___x_1081_ = lean_nat_add(v_size_1076_, v___x_1070_);
lean_dec(v_size_1076_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 1, v___x_1081_);
lean_ctor_set(v___x_1078_, 0, v___x_1080_);
v___x_1083_ = v___x_1078_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v___x_1081_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___boxed(lean_object* v_buffer_1092_, lean_object* v_r_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(v_buffer_1092_, v_r_1093_);
lean_dec_ref(v_r_1093_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head(uint8_t v_dir_1097_){
_start:
{
if (v_dir_1097_ == 0)
{
lean_object* v___x_1098_; 
v___x_1098_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___closed__0));
return v___x_1098_;
}
else
{
lean_object* v___x_1099_; 
v___x_1099_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___closed__1));
return v___x_1099_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___boxed(lean_object* v_dir_1100_){
_start:
{
uint8_t v_dir_boxed_1101_; lean_object* v_res_1102_; 
v_dir_boxed_1101_ = lean_unbox(v_dir_1100_);
v_res_1102_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v_dir_boxed_1101_);
return v_res_1102_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; uint8_t v___x_1106_; lean_object* v___x_1107_; 
v___x_1103_ = l_Std_Http_Headers_empty;
v___x_1104_ = lean_box(3);
v___x_1105_ = 1;
v___x_1106_ = 8;
v___x_1107_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1107_, 0, v___x_1104_);
lean_ctor_set(v___x_1107_, 1, v___x_1103_);
lean_ctor_set_uint8(v___x_1107_, sizeof(void*)*2, v___x_1106_);
lean_ctor_set_uint8(v___x_1107_, sizeof(void*)*2 + 1, v___x_1105_);
return v___x_1107_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1(void){
_start:
{
lean_object* v___x_1108_; uint8_t v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1108_ = l_Std_Http_Headers_empty;
v___x_1109_ = 1;
v___x_1110_ = lean_box(4);
v___x_1111_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
lean_ctor_set(v___x_1111_, 1, v___x_1108_);
lean_ctor_set_uint8(v___x_1111_, sizeof(void*)*2, v___x_1109_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead(uint8_t v_dir_1112_){
_start:
{
if (v_dir_1112_ == 0)
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0, &l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0_once, _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0);
return v___x_1113_;
}
else
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1, &l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1_once, _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1);
return v___x_1114_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead___boxed(lean_object* v_dir_1115_){
_start:
{
uint8_t v_dir_boxed_1116_; lean_object* v_res_1117_; 
v_dir_boxed_1116_ = lean_unbox(v_dir_1115_);
v_res_1117_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v_dir_boxed_1116_);
return v_res_1117_;
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
