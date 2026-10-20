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
lean_object* v___x_213_; lean_object* v_indexes_214_; lean_object* v___y_216_; lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_213_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_210_, v_message_211_);
v_indexes_214_ = lean_ctor_get(v___x_213_, 1);
v___x_266_ = l_Std_Http_Header_Name_contentLength;
v___x_267_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_214_, v___x_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; 
v___x_268_ = lean_box(0);
v___y_216_ = v___x_268_;
goto v___jp_215_;
}
else
{
lean_object* v___x_269_; size_t v_sz_270_; size_t v___x_271_; lean_object* v_entries_272_; lean_object* v___x_273_; 
v___x_269_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v_indexes_214_, v___x_266_);
v_sz_270_ = lean_array_size(v___x_269_);
v___x_271_ = ((size_t)0ULL);
lean_inc(v___x_269_);
v_entries_272_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg(v___x_213_, v___x_269_, v_sz_270_, v___x_271_, v___x_269_);
lean_dec(v___x_269_);
v___x_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_273_, 0, v_entries_272_);
v___y_216_ = v___x_273_;
goto v___jp_215_;
}
v___jp_215_:
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = l_Std_Http_Header_Name_transferEncoding;
v___x_218_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_214_, v___x_217_);
if (v___x_218_ == 0)
{
lean_dec_ref(v___x_213_);
if (lean_obj_tag(v___y_216_) == 0)
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
v_val_221_ = lean_ctor_get(v___y_216_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___y_216_);
if (v_isSharedCheck_244_ == 0)
{
v___x_223_ = v___y_216_;
v_isShared_224_ = v_isSharedCheck_244_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_val_221_);
lean_dec(v___y_216_);
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
v___x_245_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v_indexes_214_, v___x_217_);
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
lean_dec(v___y_216_);
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
lean_dec(v___y_216_);
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
if (lean_obj_tag(v___y_216_) == 0)
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
lean_dec(v___y_216_);
v___x_264_ = lean_box(0);
return v___x_264_;
}
}
else
{
lean_object* v___x_265_; 
lean_dec(v___y_216_);
v___x_265_ = lean_box(0);
return v___x_265_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize___boxed(lean_object* v_dir_274_, lean_object* v_message_275_, lean_object* v_allowEOFBody_276_){
_start:
{
uint8_t v_dir_boxed_277_; uint8_t v_allowEOFBody_boxed_278_; lean_object* v_res_279_; 
v_dir_boxed_277_ = lean_unbox(v_dir_274_);
v_allowEOFBody_boxed_278_ = lean_unbox(v_allowEOFBody_276_);
v_res_279_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v_dir_boxed_277_, v_message_275_, v_allowEOFBody_boxed_278_);
lean_dec(v_message_275_);
return v_res_279_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(lean_object* v_00_u03b2_280_, lean_object* v_m_281_, lean_object* v_a_282_){
_start:
{
uint8_t v___x_283_; 
v___x_283_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_m_281_, v_a_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___boxed(lean_object* v_00_u03b2_284_, lean_object* v_m_285_, lean_object* v_a_286_){
_start:
{
uint8_t v_res_287_; lean_object* v_r_288_; 
v_res_287_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(v_00_u03b2_284_, v_m_285_, v_a_286_);
lean_dec_ref(v_a_286_);
lean_dec_ref(v_m_285_);
v_r_288_ = lean_box(v_res_287_);
return v_r_288_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(lean_object* v_00_u03b2_289_, lean_object* v_m_290_, lean_object* v_a_291_, lean_object* v_hma_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v_m_290_, v_a_291_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___boxed(lean_object* v_00_u03b2_294_, lean_object* v_m_295_, lean_object* v_a_296_, lean_object* v_hma_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(v_00_u03b2_294_, v_m_295_, v_a_296_, v_hma_297_);
lean_dec_ref(v_a_296_);
lean_dec_ref(v_m_295_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2(lean_object* v___x_299_, lean_object* v___x_300_, lean_object* v_as_301_, size_t v_sz_302_, size_t v_i_303_, lean_object* v_bs_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg(v___x_299_, v___x_300_, v_sz_302_, v_i_303_, v_bs_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___boxed(lean_object* v___x_306_, lean_object* v___x_307_, lean_object* v_as_308_, lean_object* v_sz_309_, lean_object* v_i_310_, lean_object* v_bs_311_){
_start:
{
size_t v_sz_boxed_312_; size_t v_i_boxed_313_; lean_object* v_res_314_; 
v_sz_boxed_312_ = lean_unbox_usize(v_sz_309_);
lean_dec(v_sz_309_);
v_i_boxed_313_ = lean_unbox_usize(v_i_310_);
lean_dec(v_i_310_);
v_res_314_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2(v___x_306_, v___x_307_, v_as_308_, v_sz_boxed_312_, v_i_boxed_313_, v_bs_311_);
lean_dec_ref(v_as_308_);
lean_dec_ref(v___x_307_);
lean_dec_ref(v___x_306_);
return v_res_314_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0(lean_object* v_00_u03b2_315_, lean_object* v_a_316_, lean_object* v_x_317_){
_start:
{
uint8_t v___x_318_; 
v___x_318_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_a_316_, v_x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_319_, lean_object* v_a_320_, lean_object* v_x_321_){
_start:
{
uint8_t v_res_322_; lean_object* v_r_323_; 
v_res_322_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0(v_00_u03b2_319_, v_a_320_, v_x_321_);
lean_dec(v_x_321_);
lean_dec_ref(v_a_320_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2(lean_object* v_00_u03b2_324_, lean_object* v_a_325_, lean_object* v_x_326_, lean_object* v_x_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2___redArg(v_a_325_, v_x_326_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2___boxed(lean_object* v_00_u03b2_329_, lean_object* v_a_330_, lean_object* v_x_331_, lean_object* v_x_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1_spec__2(v_00_u03b2_329_, v_a_330_, v_x_331_, v_x_332_);
lean_dec(v_x_331_);
lean_dec_ref(v_a_330_);
return v_res_333_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(lean_object* v_as_335_, size_t v_i_336_, size_t v_stop_337_){
_start:
{
uint8_t v___x_338_; 
v___x_338_ = lean_usize_dec_eq(v_i_336_, v_stop_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_339_ = lean_array_uget_borrowed(v_as_335_, v_i_336_);
v___x_340_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___closed__0));
v___x_341_ = lean_string_dec_eq(v___x_339_, v___x_340_);
if (v___x_341_ == 0)
{
size_t v___x_342_; size_t v___x_343_; 
v___x_342_ = ((size_t)1ULL);
v___x_343_ = lean_usize_add(v_i_336_, v___x_342_);
v_i_336_ = v___x_343_;
goto _start;
}
else
{
return v___x_341_;
}
}
else
{
uint8_t v___x_345_; 
v___x_345_ = 0;
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___boxed(lean_object* v_as_346_, lean_object* v_i_347_, lean_object* v_stop_348_){
_start:
{
size_t v_i_boxed_349_; size_t v_stop_boxed_350_; uint8_t v_res_351_; lean_object* v_r_352_; 
v_i_boxed_349_ = lean_unbox_usize(v_i_347_);
lean_dec(v_i_347_);
v_stop_boxed_350_ = lean_unbox_usize(v_stop_348_);
lean_dec(v_stop_348_);
v_res_351_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(v_as_346_, v_i_boxed_349_, v_stop_boxed_350_);
lean_dec_ref(v_as_346_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(lean_object* v_as_354_, size_t v_i_355_, size_t v_stop_356_){
_start:
{
uint8_t v___x_357_; 
v___x_357_ = lean_usize_dec_eq(v_i_355_, v_stop_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_358_ = lean_array_uget_borrowed(v_as_354_, v_i_355_);
v___x_359_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___closed__0));
v___x_360_ = lean_string_dec_eq(v___x_358_, v___x_359_);
if (v___x_360_ == 0)
{
size_t v___x_361_; size_t v___x_362_; 
v___x_361_ = ((size_t)1ULL);
v___x_362_ = lean_usize_add(v_i_355_, v___x_361_);
v_i_355_ = v___x_362_;
goto _start;
}
else
{
return v___x_360_;
}
}
else
{
uint8_t v___x_364_; 
v___x_364_ = 0;
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___boxed(lean_object* v_as_365_, lean_object* v_i_366_, lean_object* v_stop_367_){
_start:
{
size_t v_i_boxed_368_; size_t v_stop_boxed_369_; uint8_t v_res_370_; lean_object* v_r_371_; 
v_i_boxed_368_ = lean_unbox_usize(v_i_366_);
lean_dec(v_i_366_);
v_stop_boxed_369_ = lean_unbox_usize(v_stop_367_);
lean_dec(v_stop_367_);
v_res_370_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(v_as_365_, v_i_boxed_368_, v_stop_boxed_369_);
lean_dec_ref(v_as_365_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(lean_object* v_as_372_, size_t v_i_373_, size_t v_stop_374_, lean_object* v_b_375_){
_start:
{
lean_object* v___y_377_; uint8_t v___x_381_; 
v___x_381_ = lean_usize_dec_eq(v_i_373_, v_stop_374_);
if (v___x_381_ == 0)
{
if (lean_obj_tag(v_b_375_) == 0)
{
v___y_377_ = v_b_375_;
goto v___jp_376_;
}
else
{
lean_object* v_val_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v_val_382_ = lean_ctor_get(v_b_375_, 0);
lean_inc(v_val_382_);
lean_dec_ref_known(v_b_375_, 1);
v___x_383_ = lean_array_uget_borrowed(v_as_372_, v_i_373_);
lean_inc(v___x_383_);
v___x_384_ = l_Std_Http_Header_Connection_parse(v___x_383_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v___x_385_; 
lean_dec(v_val_382_);
v___x_385_ = lean_box(0);
v___y_377_ = v___x_385_;
goto v___jp_376_;
}
else
{
lean_object* v_val_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_394_; 
v_val_386_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_394_ == 0)
{
v___x_388_ = v___x_384_;
v_isShared_389_ = v_isSharedCheck_394_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_val_386_);
lean_dec(v___x_384_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_394_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_390_ = l_Array_append___redArg(v_val_382_, v_val_386_);
lean_dec(v_val_386_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v___x_390_);
v___x_392_ = v___x_388_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_390_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
v___y_377_ = v___x_392_;
goto v___jp_376_;
}
}
}
}
}
else
{
return v_b_375_;
}
v___jp_376_:
{
size_t v___x_378_; size_t v___x_379_; 
v___x_378_ = ((size_t)1ULL);
v___x_379_ = lean_usize_add(v_i_373_, v___x_378_);
v_i_373_ = v___x_379_;
v_b_375_ = v___y_377_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2___boxed(lean_object* v_as_395_, lean_object* v_i_396_, lean_object* v_stop_397_, lean_object* v_b_398_){
_start:
{
size_t v_i_boxed_399_; size_t v_stop_boxed_400_; lean_object* v_res_401_; 
v_i_boxed_399_ = lean_unbox_usize(v_i_396_);
lean_dec(v_i_396_);
v_stop_boxed_400_ = lean_unbox_usize(v_stop_397_);
lean_dec(v_stop_397_);
v_res_401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_as_395_, v_i_boxed_399_, v_stop_boxed_400_, v_b_398_);
lean_dec_ref(v_as_395_);
return v_res_401_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(uint8_t v_dir_406_, lean_object* v_message_407_){
_start:
{
lean_object* v_val_409_; lean_object* v___x_426_; lean_object* v_indexes_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_426_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_406_, v_message_407_);
v_indexes_427_ = lean_ctor_get(v___x_426_, 1);
v___x_428_ = l_Std_Http_Header_Name_connection;
v___x_429_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_427_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; 
lean_dec_ref(v___x_426_);
v___x_430_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0));
v_val_409_ = v___x_430_;
goto v___jp_408_;
}
else
{
lean_object* v___x_431_; size_t v_sz_432_; size_t v___x_433_; lean_object* v_entries_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_431_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v_indexes_427_, v___x_428_);
v_sz_432_ = lean_array_size(v___x_431_);
v___x_433_ = ((size_t)0ULL);
lean_inc(v___x_431_);
v_entries_434_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__2___redArg(v___x_426_, v___x_431_, v_sz_432_, v___x_433_, v___x_431_);
lean_dec(v___x_431_);
lean_dec_ref(v___x_426_);
v___x_435_ = lean_unsigned_to_nat(0u);
v___x_436_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0));
v___x_437_ = lean_array_get_size(v_entries_434_);
v___x_438_ = lean_nat_dec_lt(v___x_435_, v___x_437_);
if (v___x_438_ == 0)
{
lean_dec_ref(v_entries_434_);
v_val_409_ = v___x_436_;
goto v___jp_408_;
}
else
{
lean_object* v___x_439_; size_t v___x_440_; lean_object* v___x_441_; 
v___x_439_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__1));
v___x_440_ = lean_usize_of_nat(v___x_437_);
v___x_441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_entries_434_, v___x_433_, v___x_440_, v___x_439_);
lean_dec_ref(v_entries_434_);
if (lean_obj_tag(v___x_441_) == 0)
{
uint8_t v___x_442_; 
v___x_442_ = 0;
return v___x_442_;
}
else
{
lean_object* v_val_443_; 
v_val_443_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_val_443_);
lean_dec_ref_known(v___x_441_, 1);
v_val_409_ = v_val_443_;
goto v___jp_408_;
}
}
}
v___jp_408_:
{
uint8_t v___x_410_; uint8_t v___x_411_; uint8_t v___x_412_; 
v___x_410_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_406_, v_message_407_);
v___x_411_ = 1;
v___x_412_ = l_Std_Http_instBEqVersion_beq(v___x_410_, v___x_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_413_ = lean_unsigned_to_nat(0u);
v___x_414_ = lean_array_get_size(v_val_409_);
v___x_415_ = lean_nat_dec_lt(v___x_413_, v___x_414_);
if (v___x_415_ == 0)
{
lean_dec_ref(v_val_409_);
return v___x_415_;
}
else
{
if (v___x_415_ == 0)
{
lean_dec_ref(v_val_409_);
return v___x_415_;
}
else
{
size_t v___x_416_; size_t v___x_417_; uint8_t v___x_418_; 
v___x_416_ = ((size_t)0ULL);
v___x_417_ = lean_usize_of_nat(v___x_414_);
v___x_418_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(v_val_409_, v___x_416_, v___x_417_);
lean_dec_ref(v_val_409_);
return v___x_418_;
}
}
}
else
{
lean_object* v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_419_ = lean_unsigned_to_nat(0u);
v___x_420_ = lean_array_get_size(v_val_409_);
v___x_421_ = lean_nat_dec_lt(v___x_419_, v___x_420_);
if (v___x_421_ == 0)
{
lean_dec_ref(v_val_409_);
return v___x_412_;
}
else
{
if (v___x_421_ == 0)
{
lean_dec_ref(v_val_409_);
return v___x_412_;
}
else
{
size_t v___x_422_; size_t v___x_423_; uint8_t v___x_424_; 
v___x_422_ = ((size_t)0ULL);
v___x_423_ = lean_usize_of_nat(v___x_420_);
v___x_424_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(v_val_409_, v___x_422_, v___x_423_);
lean_dec_ref(v_val_409_);
if (v___x_424_ == 0)
{
return v___x_412_;
}
else
{
uint8_t v___x_425_; 
v___x_425_ = 0;
return v___x_425_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___boxed(lean_object* v_dir_444_, lean_object* v_message_445_){
_start:
{
uint8_t v_dir_boxed_446_; uint8_t v_res_447_; lean_object* v_r_448_; 
v_dir_boxed_446_ = lean_unbox(v_dir_444_);
v_res_447_ = l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(v_dir_boxed_446_, v_message_445_);
lean_dec(v_message_445_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1___redArg(lean_object* v_x_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Std_Http_Request_instReprHead_repr___redArg(v_x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1(lean_object* v_x_451_, lean_object* v_prec_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Std_Http_Request_instReprHead_repr___redArg(v_x_451_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1___boxed(lean_object* v_x_454_, lean_object* v_prec_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Std_Http_Protocol_H1_instReprHead___aux__1(v_x_454_, v_prec_455_);
lean_dec(v_prec_455_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3___redArg(lean_object* v_x_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Std_Http_Response_instReprHead_repr___redArg(v_x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3(lean_object* v_x_459_, lean_object* v_prec_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Std_Http_Response_instReprHead_repr___redArg(v_x_459_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3___boxed(lean_object* v_x_462_, lean_object* v_prec_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Std_Http_Protocol_H1_instReprHead___aux__3(v_x_462_, v_prec_463_);
lean_dec(v_prec_463_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead(uint8_t v_dir_467_){
_start:
{
if (v_dir_467_ == 0)
{
lean_object* v___x_468_; 
v___x_468_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprHead___closed__0));
return v___x_468_;
}
else
{
lean_object* v___x_469_; 
v___x_469_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprHead___closed__1));
return v___x_469_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___boxed(lean_object* v_dir_470_){
_start:
{
uint8_t v_dir_boxed_471_; lean_object* v_res_472_; 
v_dir_boxed_471_ = lean_unbox(v_dir_470_);
v_res_472_ = l_Std_Http_Protocol_H1_instReprHead(v_dir_boxed_471_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__0(lean_object* v_x_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = lean_string_from_utf8_unchecked(v_x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1(lean_object* v___x_475_, lean_object* v___x_476_, lean_object* v___x_477_, lean_object* v_name_478_, lean_object* v___x_479_, uint32_t v___x_480_, lean_object* v___x_481_, lean_object* v_it_482_, lean_object* v_acc_483_, lean_object* v_hP_484_, lean_object* v_recur_485_){
_start:
{
lean_object* v_it_487_; lean_object* v_out_488_; lean_object* v_it_504_; lean_object* v_startInclusive_505_; lean_object* v_endExclusive_506_; 
if (lean_obj_tag(v_it_482_) == 0)
{
lean_object* v_currPos_518_; lean_object* v_searcher_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_541_; 
v_currPos_518_ = lean_ctor_get(v_it_482_, 0);
v_searcher_519_ = lean_ctor_get(v_it_482_, 1);
v_isSharedCheck_541_ = !lean_is_exclusive(v_it_482_);
if (v_isSharedCheck_541_ == 0)
{
v___x_521_ = v_it_482_;
v_isShared_522_ = v_isSharedCheck_541_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_searcher_519_);
lean_inc(v_currPos_518_);
lean_dec(v_it_482_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_541_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
uint8_t v_decide_523_; 
v_decide_523_ = lean_nat_dec_eq(v_searcher_519_, v___x_479_);
if (v_decide_523_ == 0)
{
uint32_t v___x_524_; uint8_t v___x_525_; 
lean_dec(v___x_479_);
v___x_524_ = lean_string_utf8_get_fast(v_name_478_, v_searcher_519_);
v___x_525_ = lean_uint32_dec_eq(v___x_524_, v___x_480_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_526_ = lean_string_utf8_next_fast(v_name_478_, v_searcher_519_);
lean_dec(v_searcher_519_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v___x_526_);
v___x_528_ = v___x_521_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_currPos_518_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v___x_526_);
v___x_528_ = v_reuseFailAlloc_530_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_529_; 
v___x_529_ = lean_apply_4(v_recur_485_, v___x_528_, v_acc_483_, lean_box(0), lean_box(0));
return v___x_529_;
}
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v_slice_534_; lean_object* v_nextIt_536_; 
v___x_531_ = lean_string_utf8_next_fast(v_name_478_, v_searcher_519_);
v___x_532_ = lean_nat_sub(v___x_531_, v_searcher_519_);
v___x_533_ = lean_nat_add(v_searcher_519_, v___x_532_);
lean_dec(v___x_532_);
v_slice_534_ = l_String_Slice_subslice_x21(v___x_481_, v_currPos_518_, v_searcher_519_);
lean_inc(v___x_533_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v___x_533_);
lean_ctor_set(v___x_521_, 0, v___x_533_);
v_nextIt_536_ = v___x_521_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_533_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v___x_533_);
v_nextIt_536_ = v_reuseFailAlloc_539_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v_startInclusive_537_; lean_object* v_endExclusive_538_; 
v_startInclusive_537_ = lean_ctor_get(v_slice_534_, 0);
lean_inc(v_startInclusive_537_);
v_endExclusive_538_ = lean_ctor_get(v_slice_534_, 1);
lean_inc(v_endExclusive_538_);
lean_dec_ref(v_slice_534_);
v_it_504_ = v_nextIt_536_;
v_startInclusive_505_ = v_startInclusive_537_;
v_endExclusive_506_ = v_endExclusive_538_;
goto v___jp_503_;
}
}
}
else
{
lean_object* v___x_540_; 
lean_del_object(v___x_521_);
lean_dec(v_searcher_519_);
v___x_540_ = lean_box(1);
v_it_504_ = v___x_540_;
v_startInclusive_505_ = v_currPos_518_;
v_endExclusive_506_ = v___x_479_;
goto v___jp_503_;
}
}
}
else
{
lean_dec_ref(v_recur_485_);
lean_dec(v___x_479_);
return v_acc_483_;
}
v___jp_486_:
{
if (lean_obj_tag(v_acc_483_) == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_489_, 0, v_out_488_);
v___x_490_ = lean_apply_4(v_recur_485_, v_it_487_, v___x_489_, lean_box(0), lean_box(0));
return v___x_490_;
}
else
{
lean_object* v_val_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_502_; 
v_val_491_ = lean_ctor_get(v_acc_483_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v_acc_483_);
if (v_isSharedCheck_502_ == 0)
{
v___x_493_ = v_acc_483_;
v_isShared_494_ = v_isSharedCheck_502_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_val_491_);
lean_dec(v_acc_483_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_502_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_495_ = lean_string_utf8_extract_fast(v___x_475_, v___x_476_, v___x_477_);
v___x_496_ = lean_string_append(v_val_491_, v___x_495_);
lean_dec_ref(v___x_495_);
v___x_497_ = lean_string_append(v___x_496_, v_out_488_);
lean_dec_ref(v_out_488_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_497_);
v___x_499_ = v___x_493_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_497_);
v___x_499_ = v_reuseFailAlloc_501_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_500_; 
v___x_500_ = lean_apply_4(v_recur_485_, v_it_487_, v___x_499_, lean_box(0), lean_box(0));
return v___x_500_;
}
}
}
}
v___jp_503_:
{
lean_object* v___x_507_; uint32_t v___x_508_; uint32_t v___x_509_; uint8_t v___x_510_; 
v___x_507_ = lean_string_utf8_extract_fast(v_name_478_, v_startInclusive_505_, v_endExclusive_506_);
lean_dec(v_endExclusive_506_);
lean_dec(v_startInclusive_505_);
v___x_508_ = lean_string_utf8_get(v___x_507_, v___x_476_);
v___x_509_ = 97;
v___x_510_ = lean_uint32_dec_le(v___x_509_, v___x_508_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; 
v___x_511_ = lean_string_utf8_set(v___x_507_, v___x_476_, v___x_508_);
v_it_487_ = v_it_504_;
v_out_488_ = v___x_511_;
goto v___jp_486_;
}
else
{
uint32_t v___x_512_; uint8_t v___x_513_; 
v___x_512_ = 122;
v___x_513_ = lean_uint32_dec_le(v___x_508_, v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; 
v___x_514_ = lean_string_utf8_set(v___x_507_, v___x_476_, v___x_508_);
v_it_487_ = v_it_504_;
v_out_488_ = v___x_514_;
goto v___jp_486_;
}
else
{
uint32_t v___x_515_; uint32_t v___x_516_; lean_object* v___x_517_; 
v___x_515_ = 4294967264;
v___x_516_ = lean_uint32_add(v___x_508_, v___x_515_);
v___x_517_ = lean_string_utf8_set(v___x_507_, v___x_476_, v___x_516_);
v_it_487_ = v_it_504_;
v_out_488_ = v___x_517_;
goto v___jp_486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1___boxed(lean_object* v___x_542_, lean_object* v___x_543_, lean_object* v___x_544_, lean_object* v_name_545_, lean_object* v___x_546_, lean_object* v___x_547_, lean_object* v___x_548_, lean_object* v_it_549_, lean_object* v_acc_550_, lean_object* v_hP_551_, lean_object* v_recur_552_){
_start:
{
uint32_t v___x_2758__boxed_553_; lean_object* v_res_554_; 
v___x_2758__boxed_553_ = lean_unbox_uint32(v___x_547_);
lean_dec(v___x_547_);
v_res_554_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1(v___x_542_, v___x_543_, v___x_544_, v_name_545_, v___x_546_, v___x_2758__boxed_553_, v___x_548_, v_it_549_, v_acc_550_, v_hP_551_, v_recur_552_);
lean_dec_ref(v___x_548_);
lean_dec_ref(v_name_545_);
lean_dec(v___x_544_);
lean_dec(v___x_543_);
lean_dec_ref(v___x_542_);
return v_res_554_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed__const__1(void){
_start:
{
uint32_t v___x_560_; lean_object* v___x_561_; 
v___x_560_ = 45;
v___x_561_ = lean_box_uint32(v___x_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2(lean_object* v_buf_562_, lean_object* v_name_563_, lean_object* v_value_564_){
_start:
{
lean_object* v___y_566_; lean_object* v___f_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v_it_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___f_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___f_585_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__2));
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_string_utf8_byte_size(v_name_563_);
lean_inc_ref(v_name_563_);
v___x_588_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_588_, 0, v_name_563_);
lean_ctor_set(v___x_588_, 1, v___x_586_);
lean_ctor_set(v___x_588_, 2, v___x_587_);
lean_inc_ref(v___x_588_);
v_it_589_ = l_String_Slice_splitToSubslice___redArg(v___x_588_, v___f_585_);
v___x_590_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__3));
v___x_591_ = lean_unsigned_to_nat(1u);
v___x_592_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed__const__1;
v___f_593_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1___boxed), 11, 7);
lean_closure_set(v___f_593_, 0, v___x_590_);
lean_closure_set(v___f_593_, 1, v___x_586_);
lean_closure_set(v___f_593_, 2, v___x_591_);
lean_closure_set(v___f_593_, 3, v_name_563_);
lean_closure_set(v___f_593_, 4, v___x_587_);
lean_closure_set(v___f_593_, 5, v___x_592_);
lean_closure_set(v___f_593_, 6, v___x_588_);
v___x_594_ = lean_box(0);
v___x_595_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_593_, v_it_589_, v___x_594_, lean_box(0));
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v___x_596_; 
v___x_596_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_566_ = v___x_596_;
goto v___jp_565_;
}
else
{
lean_object* v_val_597_; 
v_val_597_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_val_597_);
lean_dec_ref_known(v___x_595_, 1);
v___y_566_ = v_val_597_;
goto v___jp_565_;
}
v___jp_565_:
{
lean_object* v_data_567_; lean_object* v_size_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_584_; 
v_data_567_ = lean_ctor_get(v_buf_562_, 0);
v_size_568_ = lean_ctor_get(v_buf_562_, 1);
v_isSharedCheck_584_ = !lean_is_exclusive(v_buf_562_);
if (v_isSharedCheck_584_ == 0)
{
v___x_570_ = v_buf_562_;
v_isShared_571_ = v_isSharedCheck_584_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_size_568_);
lean_inc(v_data_567_);
lean_dec(v_buf_562_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_584_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
v___x_572_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__0));
v___x_573_ = lean_string_append(v___y_566_, v___x_572_);
v___x_574_ = lean_string_append(v___x_573_, v_value_564_);
v___x_575_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__1));
v___x_576_ = lean_string_append(v___x_574_, v___x_575_);
v___x_577_ = lean_string_to_utf8(v___x_576_);
lean_inc_ref(v___x_577_);
v___x_578_ = lean_array_push(v_data_567_, v___x_577_);
v___x_579_ = lean_byte_array_size(v___x_577_);
lean_dec_ref(v___x_577_);
v___x_580_ = lean_nat_add(v_size_568_, v___x_579_);
lean_dec(v_size_568_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 1, v___x_580_);
lean_ctor_set(v___x_570_, 0, v___x_578_);
v___x_582_ = v___x_570_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed(lean_object* v_buf_598_, lean_object* v_name_599_, lean_object* v_value_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2(v_buf_598_, v_name_599_, v_value_600_);
lean_dec_ref(v_value_600_);
return v_res_601_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__1));
v___x_605_ = lean_string_to_utf8(v___x_604_);
return v___x_605_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_607_ = lean_byte_array_size(v___x_606_);
return v___x_607_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23));
v___x_643_ = lean_byte_array_size(v___x_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1(lean_object* v_buffer_687_, lean_object* v_req_688_){
_start:
{
uint8_t v_method_689_; uint8_t v_version_690_; lean_object* v_uri_691_; lean_object* v_headers_692_; lean_object* v___f_693_; lean_object* v___f_694_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v_port_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v_host_762_; lean_object* v_port_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v_port_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v_host_884_; lean_object* v_port_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_899_; 
v_method_689_ = lean_ctor_get_uint8(v_req_688_, sizeof(void*)*2);
v_version_690_ = lean_ctor_get_uint8(v_req_688_, sizeof(void*)*2 + 1);
v_uri_691_ = lean_ctor_get(v_req_688_, 0);
lean_inc(v_uri_691_);
v_headers_692_ = lean_ctor_get(v_req_688_, 1);
lean_inc_ref(v_headers_692_);
lean_dec_ref(v_req_688_);
v___f_693_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__0));
v___f_694_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1));
switch(v_method_689_)
{
case 0:
{
lean_object* v___x_979_; 
v___x_979_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28));
v___y_899_ = v___x_979_;
goto v___jp_898_;
}
case 1:
{
lean_object* v___x_980_; 
v___x_980_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29));
v___y_899_ = v___x_980_;
goto v___jp_898_;
}
case 2:
{
lean_object* v___x_981_; 
v___x_981_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30));
v___y_899_ = v___x_981_;
goto v___jp_898_;
}
case 3:
{
lean_object* v___x_982_; 
v___x_982_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31));
v___y_899_ = v___x_982_;
goto v___jp_898_;
}
case 4:
{
lean_object* v___x_983_; 
v___x_983_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32));
v___y_899_ = v___x_983_;
goto v___jp_898_;
}
case 5:
{
lean_object* v___x_984_; 
v___x_984_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33));
v___y_899_ = v___x_984_;
goto v___jp_898_;
}
case 6:
{
lean_object* v___x_985_; 
v___x_985_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34));
v___y_899_ = v___x_985_;
goto v___jp_898_;
}
case 7:
{
lean_object* v___x_986_; 
v___x_986_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35));
v___y_899_ = v___x_986_;
goto v___jp_898_;
}
case 8:
{
lean_object* v___x_987_; 
v___x_987_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36));
v___y_899_ = v___x_987_;
goto v___jp_898_;
}
case 9:
{
lean_object* v___x_988_; 
v___x_988_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37));
v___y_899_ = v___x_988_;
goto v___jp_898_;
}
case 10:
{
lean_object* v___x_989_; 
v___x_989_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38));
v___y_899_ = v___x_989_;
goto v___jp_898_;
}
case 11:
{
lean_object* v___x_990_; 
v___x_990_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39));
v___y_899_ = v___x_990_;
goto v___jp_898_;
}
case 12:
{
lean_object* v___x_991_; 
v___x_991_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40));
v___y_899_ = v___x_991_;
goto v___jp_898_;
}
case 13:
{
lean_object* v___x_992_; 
v___x_992_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41));
v___y_899_ = v___x_992_;
goto v___jp_898_;
}
case 14:
{
lean_object* v___x_993_; 
v___x_993_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42));
v___y_899_ = v___x_993_;
goto v___jp_898_;
}
case 15:
{
lean_object* v___x_994_; 
v___x_994_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43));
v___y_899_ = v___x_994_;
goto v___jp_898_;
}
case 16:
{
lean_object* v___x_995_; 
v___x_995_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44));
v___y_899_ = v___x_995_;
goto v___jp_898_;
}
case 17:
{
lean_object* v___x_996_; 
v___x_996_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45));
v___y_899_ = v___x_996_;
goto v___jp_898_;
}
case 18:
{
lean_object* v___x_997_; 
v___x_997_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46));
v___y_899_ = v___x_997_;
goto v___jp_898_;
}
case 19:
{
lean_object* v___x_998_; 
v___x_998_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47));
v___y_899_ = v___x_998_;
goto v___jp_898_;
}
case 20:
{
lean_object* v___x_999_; 
v___x_999_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48));
v___y_899_ = v___x_999_;
goto v___jp_898_;
}
case 21:
{
lean_object* v___x_1000_; 
v___x_1000_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49));
v___y_899_ = v___x_1000_;
goto v___jp_898_;
}
case 22:
{
lean_object* v___x_1001_; 
v___x_1001_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50));
v___y_899_ = v___x_1001_;
goto v___jp_898_;
}
case 23:
{
lean_object* v___x_1002_; 
v___x_1002_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51));
v___y_899_ = v___x_1002_;
goto v___jp_898_;
}
case 24:
{
lean_object* v___x_1003_; 
v___x_1003_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52));
v___y_899_ = v___x_1003_;
goto v___jp_898_;
}
case 25:
{
lean_object* v___x_1004_; 
v___x_1004_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53));
v___y_899_ = v___x_1004_;
goto v___jp_898_;
}
case 26:
{
lean_object* v___x_1005_; 
v___x_1005_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54));
v___y_899_ = v___x_1005_;
goto v___jp_898_;
}
case 27:
{
lean_object* v___x_1006_; 
v___x_1006_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55));
v___y_899_ = v___x_1006_;
goto v___jp_898_;
}
case 28:
{
lean_object* v___x_1007_; 
v___x_1007_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56));
v___y_899_ = v___x_1007_;
goto v___jp_898_;
}
case 29:
{
lean_object* v___x_1008_; 
v___x_1008_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57));
v___y_899_ = v___x_1008_;
goto v___jp_898_;
}
case 30:
{
lean_object* v___x_1009_; 
v___x_1009_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58));
v___y_899_ = v___x_1009_;
goto v___jp_898_;
}
case 31:
{
lean_object* v___x_1010_; 
v___x_1010_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59));
v___y_899_ = v___x_1010_;
goto v___jp_898_;
}
case 32:
{
lean_object* v___x_1011_; 
v___x_1011_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60));
v___y_899_ = v___x_1011_;
goto v___jp_898_;
}
case 33:
{
lean_object* v___x_1012_; 
v___x_1012_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61));
v___y_899_ = v___x_1012_;
goto v___jp_898_;
}
case 34:
{
lean_object* v___x_1013_; 
v___x_1013_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62));
v___y_899_ = v___x_1013_;
goto v___jp_898_;
}
case 35:
{
lean_object* v___x_1014_; 
v___x_1014_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63));
v___y_899_ = v___x_1014_;
goto v___jp_898_;
}
case 36:
{
lean_object* v___x_1015_; 
v___x_1015_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64));
v___y_899_ = v___x_1015_;
goto v___jp_898_;
}
case 37:
{
lean_object* v___x_1016_; 
v___x_1016_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65));
v___y_899_ = v___x_1016_;
goto v___jp_898_;
}
case 38:
{
lean_object* v___x_1017_; 
v___x_1017_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66));
v___y_899_ = v___x_1017_;
goto v___jp_898_;
}
default: 
{
lean_object* v___x_1018_; 
v___x_1018_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67));
v___y_899_ = v___x_1018_;
goto v___jp_898_;
}
}
v___jp_695_:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v_buffer_707_; lean_object* v_buffer_708_; lean_object* v_data_709_; lean_object* v_size_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_719_; 
lean_inc_ref(v___y_698_);
v___x_699_ = lean_string_to_utf8(v___y_698_);
lean_inc_ref(v___x_699_);
v___x_700_ = lean_array_push(v___y_696_, v___x_699_);
v___x_701_ = lean_byte_array_size(v___x_699_);
lean_dec_ref(v___x_699_);
v___x_702_ = lean_nat_add(v___y_697_, v___x_701_);
lean_dec(v___y_697_);
v___x_703_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_704_ = lean_array_push(v___x_700_, v___x_703_);
v___x_705_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3);
v___x_706_ = lean_nat_add(v___x_702_, v___x_705_);
lean_dec(v___x_702_);
v_buffer_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_buffer_707_, 0, v___x_704_);
lean_ctor_set(v_buffer_707_, 1, v___x_706_);
v_buffer_708_ = l_Std_Http_Headers_fold___redArg(v_headers_692_, v_buffer_707_, v___f_694_);
lean_dec_ref(v_headers_692_);
v_data_709_ = lean_ctor_get(v_buffer_708_, 0);
v_size_710_ = lean_ctor_get(v_buffer_708_, 1);
v_isSharedCheck_719_ = !lean_is_exclusive(v_buffer_708_);
if (v_isSharedCheck_719_ == 0)
{
v___x_712_ = v_buffer_708_;
v_isShared_713_ = v_isSharedCheck_719_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_size_710_);
lean_inc(v_data_709_);
lean_dec(v_buffer_708_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_719_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_714_ = lean_array_push(v_data_709_, v___x_703_);
v___x_715_ = lean_nat_add(v_size_710_, v___x_705_);
lean_dec(v_size_710_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 1, v___x_715_);
lean_ctor_set(v___x_712_, 0, v___x_714_);
v___x_717_ = v___x_712_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
v___jp_720_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_726_ = lean_string_to_utf8(v___y_725_);
lean_inc_ref(v___x_726_);
v___x_727_ = lean_array_push(v___y_724_, v___x_726_);
v___x_728_ = lean_byte_array_size(v___x_726_);
lean_dec_ref(v___x_726_);
v___x_729_ = lean_nat_add(v___y_722_, v___x_728_);
lean_dec(v___y_722_);
v___x_730_ = lean_array_push(v___x_727_, v___y_721_);
v___x_731_ = lean_nat_add(v___x_729_, v___y_723_);
lean_dec(v___x_729_);
switch(v_version_690_)
{
case 0:
{
lean_object* v___x_732_; 
v___x_732_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4));
v___y_696_ = v___x_730_;
v___y_697_ = v___x_731_;
v___y_698_ = v___x_732_;
goto v___jp_695_;
}
case 1:
{
lean_object* v___x_733_; 
v___x_733_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5));
v___y_696_ = v___x_730_;
v___y_697_ = v___x_731_;
v___y_698_ = v___x_733_;
goto v___jp_695_;
}
case 2:
{
lean_object* v___x_734_; 
v___x_734_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6));
v___y_696_ = v___x_730_;
v___y_697_ = v___x_731_;
v___y_698_ = v___x_734_;
goto v___jp_695_;
}
default: 
{
lean_object* v___x_735_; 
v___x_735_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7));
v___y_696_ = v___x_730_;
v___y_697_ = v___x_731_;
v___y_698_ = v___x_735_;
goto v___jp_695_;
}
}
}
v___jp_736_:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = lean_string_append(v___y_737_, v___y_742_);
lean_dec_ref(v___y_742_);
v___x_745_ = lean_string_append(v___x_744_, v___y_743_);
lean_dec_ref(v___y_743_);
v___y_721_ = v___y_739_;
v___y_722_ = v___y_738_;
v___y_723_ = v___y_741_;
v___y_724_ = v___y_740_;
v___y_725_ = v___x_745_;
goto v___jp_720_;
}
v___jp_746_:
{
switch(lean_obj_tag(v_port_747_))
{
case 0:
{
lean_object* v___x_754_; 
v___x_754_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_737_ = v___y_748_;
v___y_738_ = v___y_750_;
v___y_739_ = v___y_749_;
v___y_740_ = v___y_752_;
v___y_741_ = v___y_751_;
v___y_742_ = v___y_753_;
v___y_743_ = v___x_754_;
goto v___jp_736_;
}
case 1:
{
lean_object* v___x_755_; 
v___x_755_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___y_737_ = v___y_748_;
v___y_738_ = v___y_750_;
v___y_739_ = v___y_749_;
v___y_740_ = v___y_752_;
v___y_741_ = v___y_751_;
v___y_742_ = v___y_753_;
v___y_743_ = v___x_755_;
goto v___jp_736_;
}
default: 
{
uint16_t v_port_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v_port_756_ = lean_ctor_get_uint16(v_port_747_, 0);
lean_dec_ref_known(v_port_747_, 0);
v___x_757_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_758_ = lean_uint16_to_nat(v_port_756_);
v___x_759_ = l_Nat_reprFast(v___x_758_);
v___x_760_ = lean_string_append(v___x_757_, v___x_759_);
lean_dec_ref(v___x_759_);
v___y_737_ = v___y_748_;
v___y_738_ = v___y_750_;
v___y_739_ = v___y_749_;
v___y_740_ = v___y_752_;
v___y_741_ = v___y_751_;
v___y_742_ = v___y_753_;
v___y_743_ = v___x_760_;
goto v___jp_736_;
}
}
}
v___jp_761_:
{
switch(lean_obj_tag(v_host_762_))
{
case 0:
{
lean_object* v_name_769_; 
v_name_769_ = lean_ctor_get(v_host_762_, 0);
lean_inc_ref(v_name_769_);
lean_dec_ref_known(v_host_762_, 1);
v_port_747_ = v_port_763_;
v___y_748_ = v___y_768_;
v___y_749_ = v___y_765_;
v___y_750_ = v___y_764_;
v___y_751_ = v___y_767_;
v___y_752_ = v___y_766_;
v___y_753_ = v_name_769_;
goto v___jp_746_;
}
case 1:
{
lean_object* v_ipv4_770_; lean_object* v___x_771_; 
v_ipv4_770_ = lean_ctor_get(v_host_762_, 0);
lean_inc_ref(v_ipv4_770_);
lean_dec_ref_known(v_host_762_, 1);
v___x_771_ = lean_uv_ntop_v4(v_ipv4_770_);
lean_dec_ref(v_ipv4_770_);
v_port_747_ = v_port_763_;
v___y_748_ = v___y_768_;
v___y_749_ = v___y_765_;
v___y_750_ = v___y_764_;
v___y_751_ = v___y_767_;
v___y_752_ = v___y_766_;
v___y_753_ = v___x_771_;
goto v___jp_746_;
}
default: 
{
lean_object* v_ipv6_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v_ipv6_772_ = lean_ctor_get(v_host_762_, 0);
lean_inc_ref(v_ipv6_772_);
lean_dec_ref_known(v_host_762_, 1);
v___x_773_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9));
v___x_774_ = lean_uv_ntop_v6(v_ipv6_772_);
lean_dec_ref(v_ipv6_772_);
v___x_775_ = lean_string_append(v___x_773_, v___x_774_);
lean_dec_ref(v___x_774_);
v___x_776_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10));
v___x_777_ = lean_string_append(v___x_775_, v___x_776_);
v_port_747_ = v_port_763_;
v___y_748_ = v___y_768_;
v___y_749_ = v___y_765_;
v___y_750_ = v___y_764_;
v___y_751_ = v___y_767_;
v___y_752_ = v___y_766_;
v___y_753_ = v___x_777_;
goto v___jp_746_;
}
}
}
v___jp_778_:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_788_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_789_ = lean_string_append(v___y_780_, v___x_788_);
v___x_790_ = lean_string_append(v___x_789_, v___y_781_);
lean_dec_ref(v___y_781_);
v___x_791_ = lean_string_append(v___x_790_, v___y_782_);
lean_dec_ref(v___y_782_);
v___x_792_ = lean_string_append(v___x_791_, v___y_779_);
lean_dec_ref(v___y_779_);
v___x_793_ = lean_string_append(v___x_792_, v___y_787_);
lean_dec_ref(v___y_787_);
v___y_721_ = v___y_784_;
v___y_722_ = v___y_783_;
v___y_723_ = v___y_786_;
v___y_724_ = v___y_785_;
v___y_725_ = v___x_793_;
goto v___jp_720_;
}
v___jp_794_:
{
lean_object* v_queryPart_804_; 
v_queryPart_804_ = l_Std_Http_URI_Query_formatOption(v___y_800_);
if (lean_obj_tag(v___y_797_) == 0)
{
lean_object* v___x_805_; 
v___x_805_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_779_ = v_queryPart_804_;
v___y_780_ = v___y_795_;
v___y_781_ = v___y_796_;
v___y_782_ = v___y_803_;
v___y_783_ = v___y_799_;
v___y_784_ = v___y_798_;
v___y_785_ = v___y_802_;
v___y_786_ = v___y_801_;
v___y_787_ = v___x_805_;
goto v___jp_778_;
}
else
{
lean_object* v_val_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v_val_806_ = lean_ctor_get(v___y_797_, 0);
lean_inc(v_val_806_);
lean_dec_ref_known(v___y_797_, 1);
v___x_807_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11));
v___x_808_ = l_Std_Http_URI_EncodedFragment_encode(v_val_806_);
v___x_809_ = lean_string_from_utf8_unchecked(v___x_808_);
v___x_810_ = lean_string_append(v___x_807_, v___x_809_);
lean_dec_ref(v___x_809_);
v___y_779_ = v_queryPart_804_;
v___y_780_ = v___y_795_;
v___y_781_ = v___y_796_;
v___y_782_ = v___y_803_;
v___y_783_ = v___y_799_;
v___y_784_ = v___y_798_;
v___y_785_ = v___y_802_;
v___y_786_ = v___y_801_;
v___y_787_ = v___x_810_;
goto v___jp_778_;
}
}
v___jp_811_:
{
lean_object* v_queryStr_818_; lean_object* v___x_819_; 
v_queryStr_818_ = l_Std_Http_URI_Query_formatOption(v___y_812_);
v___x_819_ = lean_string_append(v___y_817_, v_queryStr_818_);
lean_dec_ref(v_queryStr_818_);
v___y_721_ = v___y_814_;
v___y_722_ = v___y_813_;
v___y_723_ = v___y_816_;
v___y_724_ = v___y_815_;
v___y_725_ = v___x_819_;
goto v___jp_720_;
}
v___jp_820_:
{
lean_object* v_segments_830_; uint8_t v_absolute_831_; lean_object* v___x_832_; lean_object* v___x_833_; size_t v_sz_834_; size_t v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v_result_838_; 
v_segments_830_ = lean_ctor_get(v___y_822_, 0);
lean_inc_ref(v_segments_830_);
v_absolute_831_ = lean_ctor_get_uint8(v___y_822_, sizeof(void*)*1);
lean_dec_ref(v___y_822_);
v___x_832_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12));
v___x_833_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22));
v_sz_834_ = lean_array_size(v_segments_830_);
v___x_835_ = ((size_t)0ULL);
v___x_836_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_833_, v___f_693_, v_sz_834_, v___x_835_, v_segments_830_);
v___x_837_ = lean_array_to_list(v___x_836_);
v_result_838_ = l_String_intercalate(v___x_832_, v___x_837_);
if (v_absolute_831_ == 0)
{
v___y_795_ = v___y_821_;
v___y_796_ = v___y_829_;
v___y_797_ = v___y_823_;
v___y_798_ = v___y_826_;
v___y_799_ = v___y_825_;
v___y_800_ = v___y_824_;
v___y_801_ = v___y_828_;
v___y_802_ = v___y_827_;
v___y_803_ = v_result_838_;
goto v___jp_794_;
}
else
{
lean_object* v___x_839_; 
v___x_839_ = lean_string_append(v___x_832_, v_result_838_);
lean_dec_ref(v_result_838_);
v___y_795_ = v___y_821_;
v___y_796_ = v___y_829_;
v___y_797_ = v___y_823_;
v___y_798_ = v___y_826_;
v___y_799_ = v___y_825_;
v___y_800_ = v___y_824_;
v___y_801_ = v___y_828_;
v___y_802_ = v___y_827_;
v___y_803_ = v___x_839_;
goto v___jp_794_;
}
}
v___jp_840_:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_853_ = lean_string_append(v___y_843_, v___y_842_);
lean_dec_ref(v___y_842_);
v___x_854_ = lean_string_append(v___x_853_, v___y_852_);
lean_dec_ref(v___y_852_);
lean_inc_ref(v___y_849_);
v___x_855_ = lean_string_append(v___y_849_, v___x_854_);
lean_dec_ref(v___x_854_);
v___y_821_ = v___y_841_;
v___y_822_ = v___y_844_;
v___y_823_ = v___y_845_;
v___y_824_ = v___y_848_;
v___y_825_ = v___y_847_;
v___y_826_ = v___y_846_;
v___y_827_ = v___y_851_;
v___y_828_ = v___y_850_;
v___y_829_ = v___x_855_;
goto v___jp_820_;
}
v___jp_856_:
{
switch(lean_obj_tag(v_port_865_))
{
case 0:
{
lean_object* v___x_869_; 
v___x_869_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_841_ = v___y_857_;
v___y_842_ = v___y_868_;
v___y_843_ = v___y_858_;
v___y_844_ = v___y_859_;
v___y_845_ = v___y_860_;
v___y_846_ = v___y_864_;
v___y_847_ = v___y_863_;
v___y_848_ = v___y_862_;
v___y_849_ = v___y_861_;
v___y_850_ = v___y_867_;
v___y_851_ = v___y_866_;
v___y_852_ = v___x_869_;
goto v___jp_840_;
}
case 1:
{
lean_object* v___x_870_; 
v___x_870_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___y_841_ = v___y_857_;
v___y_842_ = v___y_868_;
v___y_843_ = v___y_858_;
v___y_844_ = v___y_859_;
v___y_845_ = v___y_860_;
v___y_846_ = v___y_864_;
v___y_847_ = v___y_863_;
v___y_848_ = v___y_862_;
v___y_849_ = v___y_861_;
v___y_850_ = v___y_867_;
v___y_851_ = v___y_866_;
v___y_852_ = v___x_870_;
goto v___jp_840_;
}
default: 
{
uint16_t v_port_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v_port_871_ = lean_ctor_get_uint16(v_port_865_, 0);
lean_dec_ref_known(v_port_865_, 0);
v___x_872_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_873_ = lean_uint16_to_nat(v_port_871_);
v___x_874_ = l_Nat_reprFast(v___x_873_);
v___x_875_ = lean_string_append(v___x_872_, v___x_874_);
lean_dec_ref(v___x_874_);
v___y_841_ = v___y_857_;
v___y_842_ = v___y_868_;
v___y_843_ = v___y_858_;
v___y_844_ = v___y_859_;
v___y_845_ = v___y_860_;
v___y_846_ = v___y_864_;
v___y_847_ = v___y_863_;
v___y_848_ = v___y_862_;
v___y_849_ = v___y_861_;
v___y_850_ = v___y_867_;
v___y_851_ = v___y_866_;
v___y_852_ = v___x_875_;
goto v___jp_840_;
}
}
}
v___jp_876_:
{
switch(lean_obj_tag(v_host_884_))
{
case 0:
{
lean_object* v_name_889_; 
v_name_889_ = lean_ctor_get(v_host_884_, 0);
lean_inc_ref(v_name_889_);
lean_dec_ref_known(v_host_884_, 1);
v___y_857_ = v___y_877_;
v___y_858_ = v___y_888_;
v___y_859_ = v___y_878_;
v___y_860_ = v___y_879_;
v___y_861_ = v___y_883_;
v___y_862_ = v___y_882_;
v___y_863_ = v___y_881_;
v___y_864_ = v___y_880_;
v_port_865_ = v_port_885_;
v___y_866_ = v___y_887_;
v___y_867_ = v___y_886_;
v___y_868_ = v_name_889_;
goto v___jp_856_;
}
case 1:
{
lean_object* v_ipv4_890_; lean_object* v___x_891_; 
v_ipv4_890_ = lean_ctor_get(v_host_884_, 0);
lean_inc_ref(v_ipv4_890_);
lean_dec_ref_known(v_host_884_, 1);
v___x_891_ = lean_uv_ntop_v4(v_ipv4_890_);
lean_dec_ref(v_ipv4_890_);
v___y_857_ = v___y_877_;
v___y_858_ = v___y_888_;
v___y_859_ = v___y_878_;
v___y_860_ = v___y_879_;
v___y_861_ = v___y_883_;
v___y_862_ = v___y_882_;
v___y_863_ = v___y_881_;
v___y_864_ = v___y_880_;
v_port_865_ = v_port_885_;
v___y_866_ = v___y_887_;
v___y_867_ = v___y_886_;
v___y_868_ = v___x_891_;
goto v___jp_856_;
}
default: 
{
lean_object* v_ipv6_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_ipv6_892_ = lean_ctor_get(v_host_884_, 0);
lean_inc_ref(v_ipv6_892_);
lean_dec_ref_known(v_host_884_, 1);
v___x_893_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9));
v___x_894_ = lean_uv_ntop_v6(v_ipv6_892_);
lean_dec_ref(v_ipv6_892_);
v___x_895_ = lean_string_append(v___x_893_, v___x_894_);
lean_dec_ref(v___x_894_);
v___x_896_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10));
v___x_897_ = lean_string_append(v___x_895_, v___x_896_);
v___y_857_ = v___y_877_;
v___y_858_ = v___y_888_;
v___y_859_ = v___y_878_;
v___y_860_ = v___y_879_;
v___y_861_ = v___y_883_;
v___y_862_ = v___y_882_;
v___y_863_ = v___y_881_;
v___y_864_ = v___y_880_;
v_port_865_ = v_port_885_;
v___y_866_ = v___y_887_;
v___y_867_ = v___y_886_;
v___y_868_ = v___x_897_;
goto v___jp_856_;
}
}
}
v___jp_898_:
{
lean_object* v_data_900_; lean_object* v_size_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v_data_900_ = lean_ctor_get(v_buffer_687_, 0);
lean_inc_ref(v_data_900_);
v_size_901_ = lean_ctor_get(v_buffer_687_, 1);
lean_inc(v_size_901_);
lean_dec_ref(v_buffer_687_);
lean_inc_ref(v___y_899_);
v___x_902_ = lean_string_to_utf8(v___y_899_);
lean_inc_ref(v___x_902_);
v___x_903_ = lean_array_push(v_data_900_, v___x_902_);
v___x_904_ = lean_byte_array_size(v___x_902_);
lean_dec_ref(v___x_902_);
v___x_905_ = lean_nat_add(v_size_901_, v___x_904_);
lean_dec(v_size_901_);
v___x_906_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23));
v___x_907_ = lean_array_push(v___x_903_, v___x_906_);
v___x_908_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24);
v___x_909_ = lean_nat_add(v___x_905_, v___x_908_);
lean_dec(v___x_905_);
switch(lean_obj_tag(v_uri_691_))
{
case 0:
{
lean_object* v_path_910_; lean_object* v_query_911_; lean_object* v_segments_912_; uint8_t v_absolute_913_; lean_object* v___x_914_; lean_object* v___x_915_; size_t v_sz_916_; size_t v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v_result_920_; 
v_path_910_ = lean_ctor_get(v_uri_691_, 0);
lean_inc_ref(v_path_910_);
v_query_911_ = lean_ctor_get(v_uri_691_, 1);
lean_inc(v_query_911_);
lean_dec_ref_known(v_uri_691_, 2);
v_segments_912_ = lean_ctor_get(v_path_910_, 0);
lean_inc_ref(v_segments_912_);
v_absolute_913_ = lean_ctor_get_uint8(v_path_910_, sizeof(void*)*1);
lean_dec_ref(v_path_910_);
v___x_914_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12));
v___x_915_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22));
v_sz_916_ = lean_array_size(v_segments_912_);
v___x_917_ = ((size_t)0ULL);
v___x_918_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_915_, v___f_693_, v_sz_916_, v___x_917_, v_segments_912_);
v___x_919_ = lean_array_to_list(v___x_918_);
v_result_920_ = l_String_intercalate(v___x_914_, v___x_919_);
if (v_absolute_913_ == 0)
{
v___y_812_ = v_query_911_;
v___y_813_ = v___x_909_;
v___y_814_ = v___x_906_;
v___y_815_ = v___x_907_;
v___y_816_ = v___x_908_;
v___y_817_ = v_result_920_;
goto v___jp_811_;
}
else
{
lean_object* v___x_921_; 
v___x_921_ = lean_string_append(v___x_914_, v_result_920_);
lean_dec_ref(v_result_920_);
v___y_812_ = v_query_911_;
v___y_813_ = v___x_909_;
v___y_814_ = v___x_906_;
v___y_815_ = v___x_907_;
v___y_816_ = v___x_908_;
v___y_817_ = v___x_921_;
goto v___jp_811_;
}
}
case 1:
{
lean_object* v_uri_922_; lean_object* v_authority_923_; 
v_uri_922_ = lean_ctor_get(v_uri_691_, 0);
lean_inc_ref(v_uri_922_);
lean_dec_ref_known(v_uri_691_, 1);
v_authority_923_ = lean_ctor_get(v_uri_922_, 1);
if (lean_obj_tag(v_authority_923_) == 0)
{
lean_object* v_scheme_924_; lean_object* v_path_925_; lean_object* v_query_926_; lean_object* v_fragment_927_; lean_object* v___x_928_; 
v_scheme_924_ = lean_ctor_get(v_uri_922_, 0);
lean_inc_ref(v_scheme_924_);
v_path_925_ = lean_ctor_get(v_uri_922_, 2);
lean_inc_ref(v_path_925_);
v_query_926_ = lean_ctor_get(v_uri_922_, 3);
lean_inc(v_query_926_);
v_fragment_927_ = lean_ctor_get(v_uri_922_, 4);
lean_inc(v_fragment_927_);
lean_dec_ref(v_uri_922_);
v___x_928_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_821_ = v_scheme_924_;
v___y_822_ = v_path_925_;
v___y_823_ = v_fragment_927_;
v___y_824_ = v_query_926_;
v___y_825_ = v___x_909_;
v___y_826_ = v___x_906_;
v___y_827_ = v___x_907_;
v___y_828_ = v___x_908_;
v___y_829_ = v___x_928_;
goto v___jp_820_;
}
else
{
lean_object* v_val_929_; lean_object* v_scheme_930_; lean_object* v_path_931_; lean_object* v_query_932_; lean_object* v_fragment_933_; lean_object* v_userInfo_934_; lean_object* v_host_935_; lean_object* v_port_936_; lean_object* v___x_937_; 
v_val_929_ = lean_ctor_get(v_authority_923_, 0);
lean_inc(v_val_929_);
v_scheme_930_ = lean_ctor_get(v_uri_922_, 0);
lean_inc_ref(v_scheme_930_);
v_path_931_ = lean_ctor_get(v_uri_922_, 2);
lean_inc_ref(v_path_931_);
v_query_932_ = lean_ctor_get(v_uri_922_, 3);
lean_inc(v_query_932_);
v_fragment_933_ = lean_ctor_get(v_uri_922_, 4);
lean_inc(v_fragment_933_);
lean_dec_ref(v_uri_922_);
v_userInfo_934_ = lean_ctor_get(v_val_929_, 0);
lean_inc(v_userInfo_934_);
v_host_935_ = lean_ctor_get(v_val_929_, 1);
lean_inc_ref(v_host_935_);
v_port_936_ = lean_ctor_get(v_val_929_, 2);
lean_inc(v_port_936_);
lean_dec(v_val_929_);
v___x_937_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25));
if (lean_obj_tag(v_userInfo_934_) == 0)
{
lean_object* v___x_938_; 
v___x_938_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v___y_877_ = v_scheme_930_;
v___y_878_ = v_path_931_;
v___y_879_ = v_fragment_933_;
v___y_880_ = v___x_906_;
v___y_881_ = v___x_909_;
v___y_882_ = v_query_932_;
v___y_883_ = v___x_937_;
v_host_884_ = v_host_935_;
v_port_885_ = v_port_936_;
v___y_886_ = v___x_908_;
v___y_887_ = v___x_907_;
v___y_888_ = v___x_938_;
goto v___jp_876_;
}
else
{
lean_object* v_val_939_; lean_object* v_password_940_; 
v_val_939_ = lean_ctor_get(v_userInfo_934_, 0);
lean_inc(v_val_939_);
lean_dec_ref_known(v_userInfo_934_, 1);
v_password_940_ = lean_ctor_get(v_val_939_, 1);
if (lean_obj_tag(v_password_940_) == 0)
{
lean_object* v_username_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v_username_941_ = lean_ctor_get(v_val_939_, 0);
lean_inc_ref(v_username_941_);
lean_dec(v_val_939_);
v___x_942_ = lean_string_from_utf8_unchecked(v_username_941_);
v___x_943_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26));
v___x_944_ = lean_string_append(v___x_942_, v___x_943_);
v___y_877_ = v_scheme_930_;
v___y_878_ = v_path_931_;
v___y_879_ = v_fragment_933_;
v___y_880_ = v___x_906_;
v___y_881_ = v___x_909_;
v___y_882_ = v_query_932_;
v___y_883_ = v___x_937_;
v_host_884_ = v_host_935_;
v_port_885_ = v_port_936_;
v___y_886_ = v___x_908_;
v___y_887_ = v___x_907_;
v___y_888_ = v___x_944_;
goto v___jp_876_;
}
else
{
lean_object* v_username_945_; lean_object* v_val_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
lean_inc_ref(v_password_940_);
v_username_945_ = lean_ctor_get(v_val_939_, 0);
lean_inc_ref(v_username_945_);
lean_dec(v_val_939_);
v_val_946_ = lean_ctor_get(v_password_940_, 0);
lean_inc(v_val_946_);
lean_dec_ref_known(v_password_940_, 1);
v___x_947_ = lean_string_from_utf8_unchecked(v_username_945_);
v___x_948_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_949_ = lean_string_append(v___x_947_, v___x_948_);
v___x_950_ = lean_string_from_utf8_unchecked(v_val_946_);
v___x_951_ = lean_string_append(v___x_949_, v___x_950_);
lean_dec_ref(v___x_950_);
v___x_952_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26));
v___x_953_ = lean_string_append(v___x_951_, v___x_952_);
v___y_877_ = v_scheme_930_;
v___y_878_ = v_path_931_;
v___y_879_ = v_fragment_933_;
v___y_880_ = v___x_906_;
v___y_881_ = v___x_909_;
v___y_882_ = v_query_932_;
v___y_883_ = v___x_937_;
v_host_884_ = v_host_935_;
v_port_885_ = v_port_936_;
v___y_886_ = v___x_908_;
v___y_887_ = v___x_907_;
v___y_888_ = v___x_953_;
goto v___jp_876_;
}
}
}
}
case 2:
{
lean_object* v_authority_954_; lean_object* v_userInfo_955_; 
v_authority_954_ = lean_ctor_get(v_uri_691_, 0);
lean_inc_ref(v_authority_954_);
lean_dec_ref_known(v_uri_691_, 1);
v_userInfo_955_ = lean_ctor_get(v_authority_954_, 0);
if (lean_obj_tag(v_userInfo_955_) == 0)
{
lean_object* v_host_956_; lean_object* v_port_957_; lean_object* v___x_958_; 
v_host_956_ = lean_ctor_get(v_authority_954_, 1);
lean_inc_ref(v_host_956_);
v_port_957_ = lean_ctor_get(v_authority_954_, 2);
lean_inc(v_port_957_);
lean_dec_ref(v_authority_954_);
v___x_958_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4));
v_host_762_ = v_host_956_;
v_port_763_ = v_port_957_;
v___y_764_ = v___x_909_;
v___y_765_ = v___x_906_;
v___y_766_ = v___x_907_;
v___y_767_ = v___x_908_;
v___y_768_ = v___x_958_;
goto v___jp_761_;
}
else
{
lean_object* v_val_959_; lean_object* v_password_960_; 
v_val_959_ = lean_ctor_get(v_userInfo_955_, 0);
lean_inc(v_val_959_);
v_password_960_ = lean_ctor_get(v_val_959_, 1);
if (lean_obj_tag(v_password_960_) == 0)
{
lean_object* v_host_961_; lean_object* v_port_962_; lean_object* v_username_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v_host_961_ = lean_ctor_get(v_authority_954_, 1);
lean_inc_ref(v_host_961_);
v_port_962_ = lean_ctor_get(v_authority_954_, 2);
lean_inc(v_port_962_);
lean_dec_ref(v_authority_954_);
v_username_963_ = lean_ctor_get(v_val_959_, 0);
lean_inc_ref(v_username_963_);
lean_dec(v_val_959_);
v___x_964_ = lean_string_from_utf8_unchecked(v_username_963_);
v___x_965_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26));
v___x_966_ = lean_string_append(v___x_964_, v___x_965_);
v_host_762_ = v_host_961_;
v_port_763_ = v_port_962_;
v___y_764_ = v___x_909_;
v___y_765_ = v___x_906_;
v___y_766_ = v___x_907_;
v___y_767_ = v___x_908_;
v___y_768_ = v___x_966_;
goto v___jp_761_;
}
else
{
lean_object* v_host_967_; lean_object* v_port_968_; lean_object* v_username_969_; lean_object* v_val_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
lean_inc_ref(v_password_960_);
v_host_967_ = lean_ctor_get(v_authority_954_, 1);
lean_inc_ref(v_host_967_);
v_port_968_ = lean_ctor_get(v_authority_954_, 2);
lean_inc(v_port_968_);
lean_dec_ref(v_authority_954_);
v_username_969_ = lean_ctor_get(v_val_959_, 0);
lean_inc_ref(v_username_969_);
lean_dec(v_val_959_);
v_val_970_ = lean_ctor_get(v_password_960_, 0);
lean_inc(v_val_970_);
lean_dec_ref_known(v_password_960_, 1);
v___x_971_ = lean_string_from_utf8_unchecked(v_username_969_);
v___x_972_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_973_ = lean_string_append(v___x_971_, v___x_972_);
v___x_974_ = lean_string_from_utf8_unchecked(v_val_970_);
v___x_975_ = lean_string_append(v___x_973_, v___x_974_);
lean_dec_ref(v___x_974_);
v___x_976_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26));
v___x_977_ = lean_string_append(v___x_975_, v___x_976_);
v_host_762_ = v_host_967_;
v_port_763_ = v_port_968_;
v___y_764_ = v___x_909_;
v___y_765_ = v___x_906_;
v___y_766_ = v___x_907_;
v___y_767_ = v___x_908_;
v___y_768_ = v___x_977_;
goto v___jp_761_;
}
}
}
default: 
{
lean_object* v___x_978_; 
v___x_978_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27));
v___y_721_ = v___x_906_;
v___y_722_ = v___x_909_;
v___y_723_ = v___x_908_;
v___y_724_ = v___x_907_;
v___y_725_ = v___x_978_;
goto v___jp_720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(lean_object* v_buffer_1019_, lean_object* v_r_1020_){
_start:
{
lean_object* v_status_1021_; uint8_t v_version_1022_; lean_object* v_headers_1023_; lean_object* v___f_1024_; lean_object* v___y_1026_; 
v_status_1021_ = lean_ctor_get(v_r_1020_, 0);
v_version_1022_ = lean_ctor_get_uint8(v_r_1020_, sizeof(void*)*2);
v_headers_1023_ = lean_ctor_get(v_r_1020_, 1);
v___f_1024_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1));
switch(v_version_1022_)
{
case 0:
{
lean_object* v___x_1076_; 
v___x_1076_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4));
v___y_1026_ = v___x_1076_;
goto v___jp_1025_;
}
case 1:
{
lean_object* v___x_1077_; 
v___x_1077_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5));
v___y_1026_ = v___x_1077_;
goto v___jp_1025_;
}
case 2:
{
lean_object* v___x_1078_; 
v___x_1078_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6));
v___y_1026_ = v___x_1078_;
goto v___jp_1025_;
}
default: 
{
lean_object* v___x_1079_; 
v___x_1079_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7));
v___y_1026_ = v___x_1079_;
goto v___jp_1025_;
}
}
v___jp_1025_:
{
lean_object* v_data_1027_; lean_object* v_size_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1075_; 
v_data_1027_ = lean_ctor_get(v_buffer_1019_, 0);
v_size_1028_ = lean_ctor_get(v_buffer_1019_, 1);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_buffer_1019_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1030_ = v_buffer_1019_;
v_isShared_1031_ = v_isSharedCheck_1075_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_size_1028_);
lean_inc(v_data_1027_);
lean_dec(v_buffer_1019_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1075_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; uint16_t v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v_buffer_1061_; 
lean_inc_ref(v___y_1026_);
v___x_1032_ = lean_string_to_utf8(v___y_1026_);
lean_inc_ref(v___x_1032_);
v___x_1033_ = lean_array_push(v_data_1027_, v___x_1032_);
v___x_1034_ = lean_byte_array_size(v___x_1032_);
lean_dec_ref(v___x_1032_);
v___x_1035_ = lean_nat_add(v_size_1028_, v___x_1034_);
lean_dec(v_size_1028_);
v___x_1036_ = lean_unsigned_to_nat(1u);
v___x_1037_ = lean_mk_empty_array_with_capacity(v___x_1036_);
lean_dec_ref(v___x_1037_);
v___x_1038_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23));
v___x_1039_ = lean_array_push(v___x_1033_, v___x_1038_);
v___x_1040_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24);
v___x_1041_ = lean_nat_add(v___x_1035_, v___x_1040_);
lean_dec(v___x_1035_);
v___x_1042_ = l_Std_Http_Status_toCode(v_status_1021_);
v___x_1043_ = lean_uint16_to_nat(v___x_1042_);
v___x_1044_ = l_Nat_reprFast(v___x_1043_);
v___x_1045_ = lean_string_to_utf8(v___x_1044_);
lean_inc_ref(v___x_1045_);
v___x_1046_ = lean_array_push(v___x_1039_, v___x_1045_);
v___x_1047_ = lean_byte_array_size(v___x_1045_);
lean_dec_ref(v___x_1045_);
v___x_1048_ = lean_nat_add(v___x_1041_, v___x_1047_);
lean_dec(v___x_1041_);
v___x_1049_ = lean_array_push(v___x_1046_, v___x_1038_);
v___x_1050_ = lean_nat_add(v___x_1048_, v___x_1040_);
lean_dec(v___x_1048_);
v___x_1051_ = l_Std_Http_Status_reasonPhrase(v_status_1021_);
v___x_1052_ = lean_string_to_utf8(v___x_1051_);
lean_inc_ref(v___x_1052_);
v___x_1053_ = lean_array_push(v___x_1049_, v___x_1052_);
v___x_1054_ = lean_byte_array_size(v___x_1052_);
lean_dec_ref(v___x_1052_);
v___x_1055_ = lean_nat_add(v___x_1050_, v___x_1054_);
lean_dec(v___x_1050_);
v___x_1056_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_1057_ = lean_array_push(v___x_1053_, v___x_1056_);
v___x_1058_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3);
v___x_1059_ = lean_nat_add(v___x_1055_, v___x_1058_);
lean_dec(v___x_1055_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 1, v___x_1059_);
lean_ctor_set(v___x_1030_, 0, v___x_1057_);
v_buffer_1061_ = v___x_1030_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1057_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v___x_1059_);
v_buffer_1061_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v_buffer_1062_; lean_object* v_data_1063_; lean_object* v_size_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1073_; 
v_buffer_1062_ = l_Std_Http_Headers_fold___redArg(v_headers_1023_, v_buffer_1061_, v___f_1024_);
v_data_1063_ = lean_ctor_get(v_buffer_1062_, 0);
v_size_1064_ = lean_ctor_get(v_buffer_1062_, 1);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_buffer_1062_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1066_ = v_buffer_1062_;
v_isShared_1067_ = v_isSharedCheck_1073_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_size_1064_);
lean_inc(v_data_1063_);
lean_dec(v_buffer_1062_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1073_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1068_ = lean_array_push(v_data_1063_, v___x_1056_);
v___x_1069_ = lean_nat_add(v_size_1064_, v___x_1058_);
lean_dec(v_size_1064_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 1, v___x_1069_);
lean_ctor_set(v___x_1066_, 0, v___x_1068_);
v___x_1071_ = v___x_1066_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___boxed(lean_object* v_buffer_1080_, lean_object* v_r_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(v_buffer_1080_, v_r_1081_);
lean_dec_ref(v_r_1081_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head(uint8_t v_dir_1085_){
_start:
{
if (v_dir_1085_ == 0)
{
lean_object* v___x_1086_; 
v___x_1086_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___closed__0));
return v___x_1086_;
}
else
{
lean_object* v___x_1087_; 
v___x_1087_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___closed__1));
return v___x_1087_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___boxed(lean_object* v_dir_1088_){
_start:
{
uint8_t v_dir_boxed_1089_; lean_object* v_res_1090_; 
v_dir_boxed_1089_ = lean_unbox(v_dir_1088_);
v_res_1090_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v_dir_boxed_1089_);
return v_res_1090_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; uint8_t v___x_1094_; lean_object* v___x_1095_; 
v___x_1091_ = l_Std_Http_Headers_empty;
v___x_1092_ = lean_box(3);
v___x_1093_ = 1;
v___x_1094_ = 8;
v___x_1095_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1095_, 0, v___x_1092_);
lean_ctor_set(v___x_1095_, 1, v___x_1091_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*2, v___x_1094_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*2 + 1, v___x_1093_);
return v___x_1095_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1(void){
_start:
{
lean_object* v___x_1096_; uint8_t v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1096_ = l_Std_Http_Headers_empty;
v___x_1097_ = 1;
v___x_1098_ = lean_box(4);
v___x_1099_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
lean_ctor_set(v___x_1099_, 1, v___x_1096_);
lean_ctor_set_uint8(v___x_1099_, sizeof(void*)*2, v___x_1097_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead(uint8_t v_dir_1100_){
_start:
{
if (v_dir_1100_ == 0)
{
lean_object* v___x_1101_; 
v___x_1101_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0, &l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0_once, _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0);
return v___x_1101_;
}
else
{
lean_object* v___x_1102_; 
v___x_1102_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1, &l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1_once, _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1);
return v___x_1102_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead___boxed(lean_object* v_dir_1103_){
_start:
{
uint8_t v_dir_boxed_1104_; lean_object* v_res_1105_; 
v_dir_boxed_1104_ = lean_unbox(v_dir_1103_);
v_res_1105_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v_dir_boxed_1104_);
return v_res_1105_;
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
