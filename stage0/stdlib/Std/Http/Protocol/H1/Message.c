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
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Http_Response_instReprHead_repr___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Http_Request_instReprHead_repr___redArg(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Std_Http_Headers_empty;
uint8_t lean_uint32_to_uint8(uint32_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_byte_array_mk(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
uint8_t l_Std_Http_instBEqVersion_beq(uint8_t, uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_connection;
uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0_value;
static const lean_closure_object l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Message_Head_getSize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize___closed__2 = (const lean_object*)&l_Std_Http_Protocol_H1_Message_Head_getSize___closed__2_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Message_Head_getSize___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Message_Head_getSize___closed__2_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize___closed__3 = (const lean_object*)&l_Std_Http_Protocol_H1_Message_Head_getSize___closed__3_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Message_Head_getSize___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize___closed__4 = (const lean_object*)&l_Std_Http_Protocol_H1_Message_Head_getSize___closed__4_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize(uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v_x_17__boxed_55_; uint8_t v_y_18__boxed_56_; uint8_t v_res_57_; lean_object* v_r_58_; 
v_x_17__boxed_55_ = lean_unbox(v_x_53_);
v_y_18__boxed_56_ = lean_unbox(v_y_54_);
v_res_57_ = l_Std_Http_Protocol_H1_instBEqDirection_beq(v_x_17__boxed_55_, v_y_18__boxed_56_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(lean_object* v_a_113_, lean_object* v_x_114_){
_start:
{
lean_object* v_key_115_; lean_object* v_value_116_; lean_object* v_tail_117_; uint8_t v___x_118_; 
v_key_115_ = lean_ctor_get(v_x_114_, 0);
v_value_116_ = lean_ctor_get(v_x_114_, 1);
v_tail_117_ = lean_ctor_get(v_x_114_, 2);
v___x_118_ = lean_string_dec_eq(v_key_115_, v_a_113_);
if (v___x_118_ == 0)
{
v_x_114_ = v_tail_117_;
goto _start;
}
else
{
lean_inc(v_value_116_);
return v_value_116_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg___boxed(lean_object* v_a_120_, lean_object* v_x_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_a_120_, v_x_121_);
lean_dec(v_x_121_);
lean_dec_ref(v_a_120_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(lean_object* v_m_123_, lean_object* v_a_124_){
_start:
{
lean_object* v_buckets_125_; lean_object* v___x_126_; uint64_t v___x_127_; uint64_t v___x_128_; uint64_t v___x_129_; uint64_t v_fold_130_; uint64_t v___x_131_; uint64_t v___x_132_; uint64_t v___x_133_; size_t v___x_134_; size_t v___x_135_; size_t v___x_136_; size_t v___x_137_; size_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v_buckets_125_ = lean_ctor_get(v_m_123_, 1);
v___x_126_ = lean_array_get_size(v_buckets_125_);
v___x_127_ = lean_string_hash(v_a_124_);
v___x_128_ = 32ULL;
v___x_129_ = lean_uint64_shift_right(v___x_127_, v___x_128_);
v_fold_130_ = lean_uint64_xor(v___x_127_, v___x_129_);
v___x_131_ = 16ULL;
v___x_132_ = lean_uint64_shift_right(v_fold_130_, v___x_131_);
v___x_133_ = lean_uint64_xor(v_fold_130_, v___x_132_);
v___x_134_ = lean_uint64_to_usize(v___x_133_);
v___x_135_ = lean_usize_of_nat(v___x_126_);
v___x_136_ = ((size_t)1ULL);
v___x_137_ = lean_usize_sub(v___x_135_, v___x_136_);
v___x_138_ = lean_usize_land(v___x_134_, v___x_137_);
v___x_139_ = lean_array_uget_borrowed(v_buckets_125_, v___x_138_);
v___x_140_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_a_124_, v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg___boxed(lean_object* v_m_141_, lean_object* v_a_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_m_141_, v_a_142_);
lean_dec_ref(v_a_142_);
lean_dec_ref(v_m_141_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(lean_object* v___x_144_, lean_object* v___x_145_, size_t v_sz_146_, size_t v_i_147_, lean_object* v_bs_148_){
_start:
{
uint8_t v___x_149_; 
v___x_149_ = lean_usize_dec_lt(v_i_147_, v_sz_146_);
if (v___x_149_ == 0)
{
return v_bs_148_;
}
else
{
lean_object* v_entries_150_; lean_object* v___x_151_; lean_object* v_bs_x27_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v_snd_156_; size_t v___x_157_; size_t v___x_158_; lean_object* v___x_159_; 
v_entries_150_ = lean_ctor_get(v___x_144_, 0);
v___x_151_ = lean_unsigned_to_nat(0u);
v_bs_x27_152_ = lean_array_uset(v_bs_148_, v_i_147_, v___x_151_);
v___x_153_ = lean_usize_to_nat(v_i_147_);
v___x_154_ = lean_array_fget_borrowed(v___x_145_, v___x_153_);
lean_dec(v___x_153_);
v___x_155_ = lean_array_fget_borrowed(v_entries_150_, v___x_154_);
v_snd_156_ = lean_ctor_get(v___x_155_, 1);
v___x_157_ = ((size_t)1ULL);
v___x_158_ = lean_usize_add(v_i_147_, v___x_157_);
lean_inc(v_snd_156_);
v___x_159_ = lean_array_uset(v_bs_x27_152_, v_i_147_, v_snd_156_);
v_i_147_ = v___x_158_;
v_bs_148_ = v___x_159_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg___boxed(lean_object* v___x_161_, lean_object* v___x_162_, lean_object* v_sz_163_, lean_object* v_i_164_, lean_object* v_bs_165_){
_start:
{
size_t v_sz_boxed_166_; size_t v_i_boxed_167_; lean_object* v_res_168_; 
v_sz_boxed_166_ = lean_unbox_usize(v_sz_163_);
lean_dec(v_sz_163_);
v_i_boxed_167_ = lean_unbox_usize(v_i_164_);
lean_dec(v_i_164_);
v_res_168_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_161_, v___x_162_, v_sz_boxed_166_, v_i_boxed_167_, v_bs_165_);
lean_dec_ref(v___x_162_);
lean_dec_ref(v___x_161_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize(uint8_t v_dir_177_, lean_object* v_message_178_, uint8_t v_allowEOFBody_179_){
_start:
{
lean_object* v___x_180_; lean_object* v___y_182_; lean_object* v___x_235_; lean_object* v___f_236_; lean_object* v___f_237_; uint8_t v___x_238_; 
v___x_180_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_177_, v_message_178_);
v___x_235_ = l_Std_Http_Header_Name_contentLength;
v___f_236_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0));
v___f_237_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1));
v___x_238_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_236_, v___f_237_, v___x_235_, v___x_180_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; 
v___x_239_ = lean_box(0);
v___y_182_ = v___x_239_;
goto v___jp_181_;
}
else
{
lean_object* v_indexes_240_; lean_object* v___x_241_; size_t v_sz_242_; size_t v___x_243_; lean_object* v_entries_244_; lean_object* v___x_245_; 
v_indexes_240_ = lean_ctor_get(v___x_180_, 1);
lean_inc_ref(v_indexes_240_);
v___x_241_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_240_, v___x_235_);
lean_dec_ref(v_indexes_240_);
v_sz_242_ = lean_array_size(v___x_241_);
v___x_243_ = ((size_t)0ULL);
lean_inc(v___x_241_);
v_entries_244_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_180_, v___x_241_, v_sz_242_, v___x_243_, v___x_241_);
lean_dec(v___x_241_);
v___x_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_245_, 0, v_entries_244_);
v___y_182_ = v___x_245_;
goto v___jp_181_;
}
v___jp_181_:
{
lean_object* v___x_183_; lean_object* v___f_184_; lean_object* v___f_185_; uint8_t v___x_186_; 
v___x_183_ = l_Std_Http_Header_Name_transferEncoding;
v___f_184_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0));
v___f_185_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1));
v___x_186_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_184_, v___f_185_, v___x_183_, v___x_180_);
if (v___x_186_ == 0)
{
lean_dec_ref(v___x_180_);
if (lean_obj_tag(v___y_182_) == 0)
{
if (v_allowEOFBody_179_ == 0)
{
lean_object* v___x_187_; 
v___x_187_ = lean_box(0);
return v___x_187_;
}
else
{
lean_object* v___x_188_; 
v___x_188_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__3));
return v___x_188_;
}
}
else
{
lean_object* v_val_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_212_; 
v_val_189_ = lean_ctor_get(v___y_182_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___y_182_);
if (v_isSharedCheck_212_ == 0)
{
v___x_191_ = v___y_182_;
v_isShared_192_ = v_isSharedCheck_212_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_val_189_);
lean_dec(v___y_182_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_212_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_193_ = lean_array_get_size(v_val_189_);
v___x_194_ = lean_unsigned_to_nat(1u);
v___x_195_ = lean_nat_dec_eq(v___x_193_, v___x_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; 
lean_del_object(v___x_191_);
lean_dec(v_val_189_);
v___x_196_ = lean_box(0);
return v___x_196_;
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = lean_array_fget(v_val_189_, v___x_197_);
lean_dec(v_val_189_);
v___x_199_ = l_Std_Http_Header_ContentLength_parse(v___x_198_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v___x_200_; 
lean_del_object(v___x_191_);
v___x_200_ = lean_box(0);
return v___x_200_;
}
else
{
lean_object* v_val_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_211_; 
v_val_201_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_211_ == 0)
{
v___x_203_ = v___x_199_;
v_isShared_204_ = v_isSharedCheck_211_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_val_201_);
lean_dec(v___x_199_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_211_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v_val_201_);
v___x_206_ = v___x_191_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_val_201_);
v___x_206_ = v_reuseFailAlloc_210_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_208_; 
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v___x_206_);
v___x_208_ = v___x_203_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_206_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
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
lean_object* v_indexes_213_; lean_object* v___x_214_; size_t v_sz_215_; size_t v___x_216_; lean_object* v_entries_217_; lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v_indexes_213_ = lean_ctor_get(v___x_180_, 1);
lean_inc_ref(v_indexes_213_);
v___x_214_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_213_, v___x_183_);
lean_dec_ref(v_indexes_213_);
v_sz_215_ = lean_array_size(v___x_214_);
v___x_216_ = ((size_t)0ULL);
lean_inc(v___x_214_);
v_entries_217_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_180_, v___x_214_, v_sz_215_, v___x_216_, v___x_214_);
lean_dec(v___x_214_);
lean_dec_ref(v___x_180_);
v___x_218_ = lean_array_get_size(v_entries_217_);
v___x_219_ = lean_unsigned_to_nat(1u);
v___x_220_ = lean_nat_dec_eq(v___x_218_, v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; 
lean_dec_ref(v_entries_217_);
lean_dec(v___y_182_);
v___x_221_ = lean_box(0);
return v___x_221_;
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v_te_224_; 
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = lean_array_fget(v_entries_217_, v___x_222_);
lean_dec_ref(v_entries_217_);
v_te_224_ = l_Std_Http_Header_TransferEncoding_parse(v___x_223_);
if (lean_obj_tag(v_te_224_) == 0)
{
lean_object* v___x_225_; 
lean_dec(v___y_182_);
v___x_225_ = lean_box(0);
return v___x_225_;
}
else
{
lean_object* v_val_226_; uint8_t v___x_227_; 
v_val_226_ = lean_ctor_get(v_te_224_, 0);
lean_inc(v_val_226_);
lean_dec_ref_known(v_te_224_, 1);
v___x_227_ = l_Std_Http_Header_TransferEncoding_isChunked(v_val_226_);
lean_dec(v_val_226_);
if (v___x_227_ == 1)
{
if (lean_obj_tag(v___y_182_) == 0)
{
uint8_t v___x_228_; uint8_t v___x_229_; uint8_t v___x_230_; 
v___x_228_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_177_, v_message_178_);
v___x_229_ = 0;
v___x_230_ = l_Std_Http_instBEqVersion_beq(v___x_228_, v___x_229_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; 
v___x_231_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__4));
return v___x_231_;
}
else
{
lean_object* v___x_232_; 
v___x_232_ = lean_box(0);
return v___x_232_;
}
}
else
{
lean_object* v___x_233_; 
lean_dec(v___y_182_);
v___x_233_ = lean_box(0);
return v___x_233_;
}
}
else
{
lean_object* v___x_234_; 
lean_dec(v___y_182_);
v___x_234_ = lean_box(0);
return v___x_234_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize___boxed(lean_object* v_dir_246_, lean_object* v_message_247_, lean_object* v_allowEOFBody_248_){
_start:
{
uint8_t v_dir_boxed_249_; uint8_t v_allowEOFBody_boxed_250_; lean_object* v_res_251_; 
v_dir_boxed_249_ = lean_unbox(v_dir_246_);
v_allowEOFBody_boxed_250_ = lean_unbox(v_allowEOFBody_248_);
v_res_251_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v_dir_boxed_249_, v_message_247_, v_allowEOFBody_boxed_250_);
lean_dec(v_message_247_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(lean_object* v_00_u03b2_252_, lean_object* v_m_253_, lean_object* v_a_254_, lean_object* v_hma_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_m_253_, v_a_254_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___boxed(lean_object* v_00_u03b2_257_, lean_object* v_m_258_, lean_object* v_a_259_, lean_object* v_hma_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(v_00_u03b2_257_, v_m_258_, v_a_259_, v_hma_260_);
lean_dec_ref(v_a_259_);
lean_dec_ref(v_m_258_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(lean_object* v___x_262_, lean_object* v___x_263_, lean_object* v_as_264_, size_t v_sz_265_, size_t v_i_266_, lean_object* v_bs_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_262_, v___x_263_, v_sz_265_, v_i_266_, v_bs_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___boxed(lean_object* v___x_269_, lean_object* v___x_270_, lean_object* v_as_271_, lean_object* v_sz_272_, lean_object* v_i_273_, lean_object* v_bs_274_){
_start:
{
size_t v_sz_boxed_275_; size_t v_i_boxed_276_; lean_object* v_res_277_; 
v_sz_boxed_275_ = lean_unbox_usize(v_sz_272_);
lean_dec(v_sz_272_);
v_i_boxed_276_ = lean_unbox_usize(v_i_273_);
lean_dec(v_i_273_);
v_res_277_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(v___x_269_, v___x_270_, v_as_271_, v_sz_boxed_275_, v_i_boxed_276_, v_bs_274_);
lean_dec_ref(v_as_271_);
lean_dec_ref(v___x_270_);
lean_dec_ref(v___x_269_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0(lean_object* v_00_u03b2_278_, lean_object* v_a_279_, lean_object* v_x_280_, lean_object* v_x_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_a_279_, v_x_280_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_283_, lean_object* v_a_284_, lean_object* v_x_285_, lean_object* v_x_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0(v_00_u03b2_283_, v_a_284_, v_x_285_, v_x_286_);
lean_dec(v_x_285_);
lean_dec_ref(v_a_284_);
return v_res_287_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(lean_object* v_as_289_, size_t v_i_290_, size_t v_stop_291_){
_start:
{
uint8_t v___x_292_; 
v___x_292_ = lean_usize_dec_eq(v_i_290_, v_stop_291_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_293_ = lean_array_uget_borrowed(v_as_289_, v_i_290_);
v___x_294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___closed__0));
v___x_295_ = lean_string_dec_eq(v___x_293_, v___x_294_);
if (v___x_295_ == 0)
{
size_t v___x_296_; size_t v___x_297_; 
v___x_296_ = ((size_t)1ULL);
v___x_297_ = lean_usize_add(v_i_290_, v___x_296_);
v_i_290_ = v___x_297_;
goto _start;
}
else
{
return v___x_295_;
}
}
else
{
uint8_t v___x_299_; 
v___x_299_ = 0;
return v___x_299_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___boxed(lean_object* v_as_300_, lean_object* v_i_301_, lean_object* v_stop_302_){
_start:
{
size_t v_i_boxed_303_; size_t v_stop_boxed_304_; uint8_t v_res_305_; lean_object* v_r_306_; 
v_i_boxed_303_ = lean_unbox_usize(v_i_301_);
lean_dec(v_i_301_);
v_stop_boxed_304_ = lean_unbox_usize(v_stop_302_);
lean_dec(v_stop_302_);
v_res_305_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(v_as_300_, v_i_boxed_303_, v_stop_boxed_304_);
lean_dec_ref(v_as_300_);
v_r_306_ = lean_box(v_res_305_);
return v_r_306_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(lean_object* v_as_308_, size_t v_i_309_, size_t v_stop_310_){
_start:
{
uint8_t v___x_311_; 
v___x_311_ = lean_usize_dec_eq(v_i_309_, v_stop_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_312_ = lean_array_uget_borrowed(v_as_308_, v_i_309_);
v___x_313_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___closed__0));
v___x_314_ = lean_string_dec_eq(v___x_312_, v___x_313_);
if (v___x_314_ == 0)
{
size_t v___x_315_; size_t v___x_316_; 
v___x_315_ = ((size_t)1ULL);
v___x_316_ = lean_usize_add(v_i_309_, v___x_315_);
v_i_309_ = v___x_316_;
goto _start;
}
else
{
return v___x_314_;
}
}
else
{
uint8_t v___x_318_; 
v___x_318_ = 0;
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___boxed(lean_object* v_as_319_, lean_object* v_i_320_, lean_object* v_stop_321_){
_start:
{
size_t v_i_boxed_322_; size_t v_stop_boxed_323_; uint8_t v_res_324_; lean_object* v_r_325_; 
v_i_boxed_322_ = lean_unbox_usize(v_i_320_);
lean_dec(v_i_320_);
v_stop_boxed_323_ = lean_unbox_usize(v_stop_321_);
lean_dec(v_stop_321_);
v_res_324_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(v_as_319_, v_i_boxed_322_, v_stop_boxed_323_);
lean_dec_ref(v_as_319_);
v_r_325_ = lean_box(v_res_324_);
return v_r_325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(lean_object* v_as_326_, size_t v_i_327_, size_t v_stop_328_, lean_object* v_b_329_){
_start:
{
lean_object* v___y_331_; uint8_t v___x_335_; 
v___x_335_ = lean_usize_dec_eq(v_i_327_, v_stop_328_);
if (v___x_335_ == 0)
{
if (lean_obj_tag(v_b_329_) == 0)
{
v___y_331_ = v_b_329_;
goto v___jp_330_;
}
else
{
lean_object* v_val_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_val_336_ = lean_ctor_get(v_b_329_, 0);
lean_inc(v_val_336_);
lean_dec_ref_known(v_b_329_, 1);
v___x_337_ = lean_array_uget_borrowed(v_as_326_, v_i_327_);
lean_inc(v___x_337_);
v___x_338_ = l_Std_Http_Header_Connection_parse(v___x_337_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v___x_339_; 
lean_dec(v_val_336_);
v___x_339_ = lean_box(0);
v___y_331_ = v___x_339_;
goto v___jp_330_;
}
else
{
lean_object* v_val_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_348_; 
v_val_340_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_348_ == 0)
{
v___x_342_ = v___x_338_;
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_val_340_);
lean_dec(v___x_338_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; lean_object* v___x_346_; 
v___x_344_ = l_Array_append___redArg(v_val_336_, v_val_340_);
lean_dec(v_val_340_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v___x_344_);
v___x_346_ = v___x_342_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
v___y_331_ = v___x_346_;
goto v___jp_330_;
}
}
}
}
}
else
{
return v_b_329_;
}
v___jp_330_:
{
size_t v___x_332_; size_t v___x_333_; 
v___x_332_ = ((size_t)1ULL);
v___x_333_ = lean_usize_add(v_i_327_, v___x_332_);
v_i_327_ = v___x_333_;
v_b_329_ = v___y_331_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2___boxed(lean_object* v_as_349_, lean_object* v_i_350_, lean_object* v_stop_351_, lean_object* v_b_352_){
_start:
{
size_t v_i_boxed_353_; size_t v_stop_boxed_354_; lean_object* v_res_355_; 
v_i_boxed_353_ = lean_unbox_usize(v_i_350_);
lean_dec(v_i_350_);
v_stop_boxed_354_ = lean_unbox_usize(v_stop_351_);
lean_dec(v_stop_351_);
v_res_355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_as_349_, v_i_boxed_353_, v_stop_boxed_354_, v_b_352_);
lean_dec_ref(v_as_349_);
return v_res_355_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(uint8_t v_dir_360_, lean_object* v_message_361_){
_start:
{
lean_object* v_val_363_; lean_object* v___y_381_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___f_386_; lean_object* v___f_387_; uint8_t v___x_388_; 
v___x_384_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_360_, v_message_361_);
v___x_385_ = l_Std_Http_Header_Name_connection;
v___f_386_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0));
v___f_387_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1));
v___x_388_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_386_, v___f_387_, v___x_385_, v___x_384_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; 
lean_dec_ref(v___x_384_);
v___x_389_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0));
v_val_363_ = v___x_389_;
goto v___jp_362_;
}
else
{
lean_object* v_indexes_390_; lean_object* v___x_391_; size_t v_sz_392_; size_t v___x_393_; lean_object* v_entries_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v_indexes_390_ = lean_ctor_get(v___x_384_, 1);
lean_inc_ref(v_indexes_390_);
v___x_391_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_390_, v___x_385_);
lean_dec_ref(v_indexes_390_);
v_sz_392_ = lean_array_size(v___x_391_);
v___x_393_ = ((size_t)0ULL);
lean_inc(v___x_391_);
v_entries_394_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_384_, v___x_391_, v_sz_392_, v___x_393_, v___x_391_);
lean_dec(v___x_391_);
lean_dec_ref(v___x_384_);
v___x_395_ = lean_unsigned_to_nat(0u);
v___x_396_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0));
v___x_397_ = lean_array_get_size(v_entries_394_);
v___x_398_ = lean_nat_dec_lt(v___x_395_, v___x_397_);
if (v___x_398_ == 0)
{
lean_dec_ref(v_entries_394_);
v_val_363_ = v___x_396_;
goto v___jp_362_;
}
else
{
lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_399_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__1));
v___x_400_ = lean_nat_dec_le(v___x_397_, v___x_397_);
if (v___x_400_ == 0)
{
if (v___x_398_ == 0)
{
lean_dec_ref(v_entries_394_);
v_val_363_ = v___x_396_;
goto v___jp_362_;
}
else
{
size_t v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_usize_of_nat(v___x_397_);
v___x_402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_entries_394_, v___x_393_, v___x_401_, v___x_399_);
lean_dec_ref(v_entries_394_);
v___y_381_ = v___x_402_;
goto v___jp_380_;
}
}
else
{
size_t v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_usize_of_nat(v___x_397_);
v___x_404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_entries_394_, v___x_393_, v___x_403_, v___x_399_);
lean_dec_ref(v_entries_394_);
v___y_381_ = v___x_404_;
goto v___jp_380_;
}
}
}
v___jp_362_:
{
uint8_t v___x_364_; uint8_t v___x_365_; uint8_t v___x_366_; 
v___x_364_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_360_, v_message_361_);
v___x_365_ = 1;
v___x_366_ = l_Std_Http_instBEqVersion_beq(v___x_364_, v___x_365_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_367_ = lean_unsigned_to_nat(0u);
v___x_368_ = lean_array_get_size(v_val_363_);
v___x_369_ = lean_nat_dec_lt(v___x_367_, v___x_368_);
if (v___x_369_ == 0)
{
lean_dec_ref(v_val_363_);
return v___x_366_;
}
else
{
if (v___x_369_ == 0)
{
lean_dec_ref(v_val_363_);
return v___x_366_;
}
else
{
size_t v___x_370_; size_t v___x_371_; uint8_t v___x_372_; 
v___x_370_ = ((size_t)0ULL);
v___x_371_ = lean_usize_of_nat(v___x_368_);
v___x_372_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(v_val_363_, v___x_370_, v___x_371_);
lean_dec_ref(v_val_363_);
return v___x_372_;
}
}
}
else
{
lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_373_ = lean_unsigned_to_nat(0u);
v___x_374_ = lean_array_get_size(v_val_363_);
v___x_375_ = lean_nat_dec_lt(v___x_373_, v___x_374_);
if (v___x_375_ == 0)
{
lean_dec_ref(v_val_363_);
return v___x_366_;
}
else
{
if (v___x_375_ == 0)
{
lean_dec_ref(v_val_363_);
return v___x_366_;
}
else
{
size_t v___x_376_; size_t v___x_377_; uint8_t v___x_378_; 
v___x_376_ = ((size_t)0ULL);
v___x_377_ = lean_usize_of_nat(v___x_374_);
v___x_378_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(v_val_363_, v___x_376_, v___x_377_);
lean_dec_ref(v_val_363_);
if (v___x_378_ == 0)
{
return v___x_366_;
}
else
{
uint8_t v___x_379_; 
v___x_379_ = 0;
return v___x_379_;
}
}
}
}
}
v___jp_380_:
{
if (lean_obj_tag(v___y_381_) == 0)
{
uint8_t v___x_382_; 
v___x_382_ = 0;
return v___x_382_;
}
else
{
lean_object* v_val_383_; 
v_val_383_ = lean_ctor_get(v___y_381_, 0);
lean_inc(v_val_383_);
lean_dec_ref_known(v___y_381_, 1);
v_val_363_ = v_val_383_;
goto v___jp_362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___boxed(lean_object* v_dir_405_, lean_object* v_message_406_){
_start:
{
uint8_t v_dir_boxed_407_; uint8_t v_res_408_; lean_object* v_r_409_; 
v_dir_boxed_407_ = lean_unbox(v_dir_405_);
v_res_408_ = l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(v_dir_boxed_407_, v_message_406_);
lean_dec(v_message_406_);
v_r_409_ = lean_box(v_res_408_);
return v_r_409_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1___redArg(lean_object* v_x_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Std_Http_Request_instReprHead_repr___redArg(v_x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1(lean_object* v_x_412_, lean_object* v_prec_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Std_Http_Request_instReprHead_repr___redArg(v_x_412_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1___boxed(lean_object* v_x_415_, lean_object* v_prec_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Std_Http_Protocol_H1_instReprHead___aux__1(v_x_415_, v_prec_416_);
lean_dec(v_prec_416_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3___redArg(lean_object* v_x_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Std_Http_Response_instReprHead_repr___redArg(v_x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3(lean_object* v_x_420_, lean_object* v_prec_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Std_Http_Response_instReprHead_repr___redArg(v_x_420_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3___boxed(lean_object* v_x_423_, lean_object* v_prec_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Std_Http_Protocol_H1_instReprHead___aux__3(v_x_423_, v_prec_424_);
lean_dec(v_prec_424_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead(uint8_t v_dir_428_){
_start:
{
if (v_dir_428_ == 0)
{
lean_object* v___x_429_; 
v___x_429_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprHead___closed__0));
return v___x_429_;
}
else
{
lean_object* v___x_430_; 
v___x_430_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprHead___closed__1));
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___boxed(lean_object* v_dir_431_){
_start:
{
uint8_t v_dir_boxed_432_; lean_object* v_res_433_; 
v_dir_boxed_432_ = lean_unbox(v_dir_431_);
v_res_433_ = l_Std_Http_Protocol_H1_instReprHead(v_dir_boxed_432_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__0(lean_object* v_x_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = lean_string_from_utf8_unchecked(v_x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1(lean_object* v___x_436_, lean_object* v___x_437_, lean_object* v___x_438_, lean_object* v_name_439_, lean_object* v___x_440_, uint32_t v___x_441_, lean_object* v___x_442_, lean_object* v_it_443_, lean_object* v_acc_444_, lean_object* v_hP_445_, lean_object* v_recur_446_){
_start:
{
lean_object* v_it_448_; lean_object* v_out_449_; lean_object* v_it_465_; lean_object* v_startInclusive_466_; lean_object* v_endExclusive_467_; 
if (lean_obj_tag(v_it_443_) == 0)
{
lean_object* v_currPos_479_; lean_object* v_searcher_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_502_; 
v_currPos_479_ = lean_ctor_get(v_it_443_, 0);
v_searcher_480_ = lean_ctor_get(v_it_443_, 1);
v_isSharedCheck_502_ = !lean_is_exclusive(v_it_443_);
if (v_isSharedCheck_502_ == 0)
{
v___x_482_ = v_it_443_;
v_isShared_483_ = v_isSharedCheck_502_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_searcher_480_);
lean_inc(v_currPos_479_);
lean_dec(v_it_443_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_502_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
uint8_t v___x_484_; 
v___x_484_ = lean_nat_dec_eq(v_searcher_480_, v___x_440_);
if (v___x_484_ == 0)
{
uint32_t v___x_485_; uint8_t v___x_486_; 
lean_dec(v___x_440_);
v___x_485_ = lean_string_utf8_get_fast(v_name_439_, v_searcher_480_);
v___x_486_ = lean_uint32_dec_eq(v___x_485_, v___x_441_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_489_; 
v___x_487_ = lean_string_utf8_next_fast(v_name_439_, v_searcher_480_);
lean_dec(v_searcher_480_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 1, v___x_487_);
v___x_489_ = v___x_482_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_currPos_479_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v___x_487_);
v___x_489_ = v_reuseFailAlloc_491_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_490_; 
v___x_490_ = lean_apply_4(v_recur_446_, v___x_489_, v_acc_444_, lean_box(0), lean_box(0));
return v___x_490_;
}
}
else
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v_slice_495_; lean_object* v_nextIt_497_; 
v___x_492_ = lean_string_utf8_next_fast(v_name_439_, v_searcher_480_);
v___x_493_ = lean_nat_sub(v___x_492_, v_searcher_480_);
v___x_494_ = lean_nat_add(v_searcher_480_, v___x_493_);
lean_dec(v___x_493_);
v_slice_495_ = l_String_Slice_subslice_x21(v___x_442_, v_currPos_479_, v_searcher_480_);
lean_inc(v___x_494_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 1, v___x_494_);
lean_ctor_set(v___x_482_, 0, v___x_494_);
v_nextIt_497_ = v___x_482_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_494_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v___x_494_);
v_nextIt_497_ = v_reuseFailAlloc_500_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
lean_object* v_startInclusive_498_; lean_object* v_endExclusive_499_; 
v_startInclusive_498_ = lean_ctor_get(v_slice_495_, 0);
lean_inc(v_startInclusive_498_);
v_endExclusive_499_ = lean_ctor_get(v_slice_495_, 1);
lean_inc(v_endExclusive_499_);
lean_dec_ref(v_slice_495_);
v_it_465_ = v_nextIt_497_;
v_startInclusive_466_ = v_startInclusive_498_;
v_endExclusive_467_ = v_endExclusive_499_;
goto v___jp_464_;
}
}
}
else
{
lean_object* v___x_501_; 
lean_del_object(v___x_482_);
lean_dec(v_searcher_480_);
v___x_501_ = lean_box(1);
v_it_465_ = v___x_501_;
v_startInclusive_466_ = v_currPos_479_;
v_endExclusive_467_ = v___x_440_;
goto v___jp_464_;
}
}
}
else
{
lean_dec_ref(v_recur_446_);
lean_dec(v___x_440_);
return v_acc_444_;
}
v___jp_447_:
{
if (lean_obj_tag(v_acc_444_) == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_450_, 0, v_out_449_);
v___x_451_ = lean_apply_4(v_recur_446_, v_it_448_, v___x_450_, lean_box(0), lean_box(0));
return v___x_451_;
}
else
{
lean_object* v_val_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_463_; 
v_val_452_ = lean_ctor_get(v_acc_444_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v_acc_444_);
if (v_isSharedCheck_463_ == 0)
{
v___x_454_ = v_acc_444_;
v_isShared_455_ = v_isSharedCheck_463_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_val_452_);
lean_dec(v_acc_444_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_463_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_456_ = lean_string_utf8_extract_fast(v___x_436_, v___x_437_, v___x_438_);
v___x_457_ = lean_string_append(v_val_452_, v___x_456_);
lean_dec_ref(v___x_456_);
v___x_458_ = lean_string_append(v___x_457_, v_out_449_);
lean_dec_ref(v_out_449_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_458_);
v___x_460_ = v___x_454_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_458_);
v___x_460_ = v_reuseFailAlloc_462_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_461_; 
v___x_461_ = lean_apply_4(v_recur_446_, v_it_448_, v___x_460_, lean_box(0), lean_box(0));
return v___x_461_;
}
}
}
}
v___jp_464_:
{
lean_object* v___x_468_; uint32_t v___x_469_; uint32_t v___x_470_; uint8_t v___x_471_; 
v___x_468_ = lean_string_utf8_extract_fast(v_name_439_, v_startInclusive_466_, v_endExclusive_467_);
lean_dec(v_endExclusive_467_);
lean_dec(v_startInclusive_466_);
v___x_469_ = lean_string_utf8_get(v___x_468_, v___x_437_);
v___x_470_ = 97;
v___x_471_ = lean_uint32_dec_le(v___x_470_, v___x_469_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; 
v___x_472_ = lean_string_utf8_set(v___x_468_, v___x_437_, v___x_469_);
v_it_448_ = v_it_465_;
v_out_449_ = v___x_472_;
goto v___jp_447_;
}
else
{
uint32_t v___x_473_; uint8_t v___x_474_; 
v___x_473_ = 122;
v___x_474_ = lean_uint32_dec_le(v___x_469_, v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; 
v___x_475_ = lean_string_utf8_set(v___x_468_, v___x_437_, v___x_469_);
v_it_448_ = v_it_465_;
v_out_449_ = v___x_475_;
goto v___jp_447_;
}
else
{
uint32_t v___x_476_; uint32_t v___x_477_; lean_object* v___x_478_; 
v___x_476_ = 4294967264;
v___x_477_ = lean_uint32_add(v___x_469_, v___x_476_);
v___x_478_ = lean_string_utf8_set(v___x_468_, v___x_437_, v___x_477_);
v_it_448_ = v_it_465_;
v_out_449_ = v___x_478_;
goto v___jp_447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1___boxed(lean_object* v___x_503_, lean_object* v___x_504_, lean_object* v___x_505_, lean_object* v_name_506_, lean_object* v___x_507_, lean_object* v___x_508_, lean_object* v___x_509_, lean_object* v_it_510_, lean_object* v_acc_511_, lean_object* v_hP_512_, lean_object* v_recur_513_){
_start:
{
uint32_t v___x_2699__boxed_514_; lean_object* v_res_515_; 
v___x_2699__boxed_514_ = lean_unbox_uint32(v___x_508_);
lean_dec(v___x_508_);
v_res_515_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1(v___x_503_, v___x_504_, v___x_505_, v_name_506_, v___x_507_, v___x_2699__boxed_514_, v___x_509_, v_it_510_, v_acc_511_, v_hP_512_, v_recur_513_);
lean_dec_ref(v___x_509_);
lean_dec_ref(v_name_506_);
lean_dec(v___x_505_);
lean_dec(v___x_504_);
lean_dec_ref(v___x_503_);
return v_res_515_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__3));
v___x_521_ = lean_string_utf8_byte_size(v___x_520_);
return v___x_521_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed__const__1(void){
_start:
{
uint32_t v___x_523_; lean_object* v___x_524_; 
v___x_523_ = 45;
v___x_524_ = lean_box_uint32(v___x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2(lean_object* v_buf_525_, lean_object* v_name_526_, lean_object* v_value_527_){
_start:
{
lean_object* v___y_529_; lean_object* v___f_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v_it_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___f_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___f_548_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__2));
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = lean_string_utf8_byte_size(v_name_526_);
lean_inc_ref(v_name_526_);
v___x_551_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_551_, 0, v_name_526_);
lean_ctor_set(v___x_551_, 1, v___x_549_);
lean_ctor_set(v___x_551_, 2, v___x_550_);
lean_inc_ref(v___x_551_);
v_it_552_ = l_String_Slice_splitToSubslice___redArg(v___x_551_, v___f_548_);
v___x_553_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__3));
v___x_554_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4);
v___x_555_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed__const__1;
v___f_556_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1___boxed), 11, 7);
lean_closure_set(v___f_556_, 0, v___x_553_);
lean_closure_set(v___f_556_, 1, v___x_549_);
lean_closure_set(v___f_556_, 2, v___x_554_);
lean_closure_set(v___f_556_, 3, v_name_526_);
lean_closure_set(v___f_556_, 4, v___x_550_);
lean_closure_set(v___f_556_, 5, v___x_555_);
lean_closure_set(v___f_556_, 6, v___x_551_);
v___x_557_ = lean_box(0);
v___x_558_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_556_, v_it_552_, v___x_557_, lean_box(0));
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v___x_559_; 
v___x_559_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_529_ = v___x_559_;
goto v___jp_528_;
}
else
{
lean_object* v_val_560_; 
v_val_560_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_val_560_);
lean_dec_ref_known(v___x_558_, 1);
v___y_529_ = v_val_560_;
goto v___jp_528_;
}
v___jp_528_:
{
lean_object* v_data_530_; lean_object* v_size_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_547_; 
v_data_530_ = lean_ctor_get(v_buf_525_, 0);
v_size_531_ = lean_ctor_get(v_buf_525_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v_buf_525_);
if (v_isSharedCheck_547_ == 0)
{
v___x_533_ = v_buf_525_;
v_isShared_534_ = v_isSharedCheck_547_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_size_531_);
lean_inc(v_data_530_);
lean_dec(v_buf_525_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_547_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_535_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__0));
v___x_536_ = lean_string_append(v___y_529_, v___x_535_);
v___x_537_ = lean_string_append(v___x_536_, v_value_527_);
v___x_538_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__1));
v___x_539_ = lean_string_append(v___x_537_, v___x_538_);
v___x_540_ = lean_string_to_utf8(v___x_539_);
lean_dec_ref(v___x_539_);
lean_inc_ref(v___x_540_);
v___x_541_ = lean_array_push(v_data_530_, v___x_540_);
v___x_542_ = lean_byte_array_size(v___x_540_);
lean_dec_ref(v___x_540_);
v___x_543_ = lean_nat_add(v_size_531_, v___x_542_);
lean_dec(v_size_531_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 1, v___x_543_);
lean_ctor_set(v___x_533_, 0, v___x_541_);
v___x_545_ = v___x_533_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v___x_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed(lean_object* v_buf_561_, lean_object* v_name_562_, lean_object* v_value_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2(v_buf_561_, v_name_562_, v_value_563_);
lean_dec_ref(v_value_563_);
return v_res_564_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__1));
v___x_568_ = lean_string_to_utf8(v___x_567_);
return v___x_568_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_570_ = lean_byte_array_size(v___x_569_);
return v___x_570_;
}
}
static uint8_t _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23(void){
_start:
{
uint32_t v___x_599_; uint8_t v___x_600_; 
v___x_599_ = 32;
v___x_600_ = lean_uint32_to_uint8(v___x_599_);
return v___x_600_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24(void){
_start:
{
uint8_t v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_601_ = lean_uint8_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23);
v___x_602_ = lean_unsigned_to_nat(1u);
v___x_603_ = lean_mk_empty_array_with_capacity(v___x_602_);
v___x_604_ = lean_box(v___x_601_);
v___x_605_ = lean_array_push(v___x_603_, v___x_604_);
v___x_606_ = lean_byte_array_mk(v___x_605_);
return v___x_606_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24);
v___x_608_ = lean_byte_array_size(v___x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1(lean_object* v_buffer_652_, lean_object* v_req_653_){
_start:
{
uint8_t v_method_654_; uint8_t v_version_655_; lean_object* v_uri_656_; lean_object* v_headers_657_; lean_object* v___f_658_; lean_object* v___f_659_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v_port_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v_host_729_; lean_object* v_port_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v_port_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v_host_850_; lean_object* v_port_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_864_; 
v_method_654_ = lean_ctor_get_uint8(v_req_653_, sizeof(void*)*2);
v_version_655_ = lean_ctor_get_uint8(v_req_653_, sizeof(void*)*2 + 1);
v_uri_656_ = lean_ctor_get(v_req_653_, 0);
lean_inc(v_uri_656_);
v_headers_657_ = lean_ctor_get(v_req_653_, 1);
lean_inc_ref(v_headers_657_);
lean_dec_ref(v_req_653_);
v___f_658_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__0));
v___f_659_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1));
switch(v_method_654_)
{
case 0:
{
lean_object* v___x_944_; 
v___x_944_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29));
v___y_864_ = v___x_944_;
goto v___jp_863_;
}
case 1:
{
lean_object* v___x_945_; 
v___x_945_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30));
v___y_864_ = v___x_945_;
goto v___jp_863_;
}
case 2:
{
lean_object* v___x_946_; 
v___x_946_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31));
v___y_864_ = v___x_946_;
goto v___jp_863_;
}
case 3:
{
lean_object* v___x_947_; 
v___x_947_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32));
v___y_864_ = v___x_947_;
goto v___jp_863_;
}
case 4:
{
lean_object* v___x_948_; 
v___x_948_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33));
v___y_864_ = v___x_948_;
goto v___jp_863_;
}
case 5:
{
lean_object* v___x_949_; 
v___x_949_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34));
v___y_864_ = v___x_949_;
goto v___jp_863_;
}
case 6:
{
lean_object* v___x_950_; 
v___x_950_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35));
v___y_864_ = v___x_950_;
goto v___jp_863_;
}
case 7:
{
lean_object* v___x_951_; 
v___x_951_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36));
v___y_864_ = v___x_951_;
goto v___jp_863_;
}
case 8:
{
lean_object* v___x_952_; 
v___x_952_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37));
v___y_864_ = v___x_952_;
goto v___jp_863_;
}
case 9:
{
lean_object* v___x_953_; 
v___x_953_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38));
v___y_864_ = v___x_953_;
goto v___jp_863_;
}
case 10:
{
lean_object* v___x_954_; 
v___x_954_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39));
v___y_864_ = v___x_954_;
goto v___jp_863_;
}
case 11:
{
lean_object* v___x_955_; 
v___x_955_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40));
v___y_864_ = v___x_955_;
goto v___jp_863_;
}
case 12:
{
lean_object* v___x_956_; 
v___x_956_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41));
v___y_864_ = v___x_956_;
goto v___jp_863_;
}
case 13:
{
lean_object* v___x_957_; 
v___x_957_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42));
v___y_864_ = v___x_957_;
goto v___jp_863_;
}
case 14:
{
lean_object* v___x_958_; 
v___x_958_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43));
v___y_864_ = v___x_958_;
goto v___jp_863_;
}
case 15:
{
lean_object* v___x_959_; 
v___x_959_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44));
v___y_864_ = v___x_959_;
goto v___jp_863_;
}
case 16:
{
lean_object* v___x_960_; 
v___x_960_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45));
v___y_864_ = v___x_960_;
goto v___jp_863_;
}
case 17:
{
lean_object* v___x_961_; 
v___x_961_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46));
v___y_864_ = v___x_961_;
goto v___jp_863_;
}
case 18:
{
lean_object* v___x_962_; 
v___x_962_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47));
v___y_864_ = v___x_962_;
goto v___jp_863_;
}
case 19:
{
lean_object* v___x_963_; 
v___x_963_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48));
v___y_864_ = v___x_963_;
goto v___jp_863_;
}
case 20:
{
lean_object* v___x_964_; 
v___x_964_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49));
v___y_864_ = v___x_964_;
goto v___jp_863_;
}
case 21:
{
lean_object* v___x_965_; 
v___x_965_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50));
v___y_864_ = v___x_965_;
goto v___jp_863_;
}
case 22:
{
lean_object* v___x_966_; 
v___x_966_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51));
v___y_864_ = v___x_966_;
goto v___jp_863_;
}
case 23:
{
lean_object* v___x_967_; 
v___x_967_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52));
v___y_864_ = v___x_967_;
goto v___jp_863_;
}
case 24:
{
lean_object* v___x_968_; 
v___x_968_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53));
v___y_864_ = v___x_968_;
goto v___jp_863_;
}
case 25:
{
lean_object* v___x_969_; 
v___x_969_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54));
v___y_864_ = v___x_969_;
goto v___jp_863_;
}
case 26:
{
lean_object* v___x_970_; 
v___x_970_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55));
v___y_864_ = v___x_970_;
goto v___jp_863_;
}
case 27:
{
lean_object* v___x_971_; 
v___x_971_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56));
v___y_864_ = v___x_971_;
goto v___jp_863_;
}
case 28:
{
lean_object* v___x_972_; 
v___x_972_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57));
v___y_864_ = v___x_972_;
goto v___jp_863_;
}
case 29:
{
lean_object* v___x_973_; 
v___x_973_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58));
v___y_864_ = v___x_973_;
goto v___jp_863_;
}
case 30:
{
lean_object* v___x_974_; 
v___x_974_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59));
v___y_864_ = v___x_974_;
goto v___jp_863_;
}
case 31:
{
lean_object* v___x_975_; 
v___x_975_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60));
v___y_864_ = v___x_975_;
goto v___jp_863_;
}
case 32:
{
lean_object* v___x_976_; 
v___x_976_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61));
v___y_864_ = v___x_976_;
goto v___jp_863_;
}
case 33:
{
lean_object* v___x_977_; 
v___x_977_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62));
v___y_864_ = v___x_977_;
goto v___jp_863_;
}
case 34:
{
lean_object* v___x_978_; 
v___x_978_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63));
v___y_864_ = v___x_978_;
goto v___jp_863_;
}
case 35:
{
lean_object* v___x_979_; 
v___x_979_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64));
v___y_864_ = v___x_979_;
goto v___jp_863_;
}
case 36:
{
lean_object* v___x_980_; 
v___x_980_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65));
v___y_864_ = v___x_980_;
goto v___jp_863_;
}
case 37:
{
lean_object* v___x_981_; 
v___x_981_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66));
v___y_864_ = v___x_981_;
goto v___jp_863_;
}
case 38:
{
lean_object* v___x_982_; 
v___x_982_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67));
v___y_864_ = v___x_982_;
goto v___jp_863_;
}
default: 
{
lean_object* v___x_983_; 
v___x_983_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__68));
v___y_864_ = v___x_983_;
goto v___jp_863_;
}
}
v___jp_660_:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v_buffer_672_; lean_object* v_buffer_673_; lean_object* v_data_674_; lean_object* v_size_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_684_; 
v___x_664_ = lean_string_to_utf8(v___y_663_);
lean_inc_ref(v___x_664_);
v___x_665_ = lean_array_push(v___y_662_, v___x_664_);
v___x_666_ = lean_byte_array_size(v___x_664_);
lean_dec_ref(v___x_664_);
v___x_667_ = lean_nat_add(v___y_661_, v___x_666_);
lean_dec(v___y_661_);
v___x_668_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_669_ = lean_array_push(v___x_665_, v___x_668_);
v___x_670_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3);
v___x_671_ = lean_nat_add(v___x_667_, v___x_670_);
lean_dec(v___x_667_);
v_buffer_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_buffer_672_, 0, v___x_669_);
lean_ctor_set(v_buffer_672_, 1, v___x_671_);
v_buffer_673_ = l_Std_Http_Headers_fold___redArg(v_headers_657_, v_buffer_672_, v___f_659_);
lean_dec_ref(v_headers_657_);
v_data_674_ = lean_ctor_get(v_buffer_673_, 0);
v_size_675_ = lean_ctor_get(v_buffer_673_, 1);
v_isSharedCheck_684_ = !lean_is_exclusive(v_buffer_673_);
if (v_isSharedCheck_684_ == 0)
{
v___x_677_ = v_buffer_673_;
v_isShared_678_ = v_isSharedCheck_684_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_size_675_);
lean_inc(v_data_674_);
lean_dec(v_buffer_673_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_684_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_682_; 
v___x_679_ = lean_array_push(v_data_674_, v___x_668_);
v___x_680_ = lean_nat_add(v_size_675_, v___x_670_);
lean_dec(v_size_675_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 1, v___x_680_);
lean_ctor_set(v___x_677_, 0, v___x_679_);
v___x_682_ = v___x_677_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_679_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v___x_680_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
v___jp_685_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_691_ = lean_string_to_utf8(v___y_690_);
lean_dec_ref(v___y_690_);
lean_inc_ref(v___x_691_);
v___x_692_ = lean_array_push(v___y_689_, v___x_691_);
v___x_693_ = lean_byte_array_size(v___x_691_);
lean_dec_ref(v___x_691_);
v___x_694_ = lean_nat_add(v___y_688_, v___x_693_);
lean_dec(v___y_688_);
v___x_695_ = lean_array_push(v___x_692_, v___y_687_);
v___x_696_ = lean_nat_add(v___x_694_, v___y_686_);
lean_dec(v___x_694_);
switch(v_version_655_)
{
case 0:
{
lean_object* v___x_697_; 
v___x_697_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4));
v___y_661_ = v___x_696_;
v___y_662_ = v___x_695_;
v___y_663_ = v___x_697_;
goto v___jp_660_;
}
case 1:
{
lean_object* v___x_698_; 
v___x_698_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5));
v___y_661_ = v___x_696_;
v___y_662_ = v___x_695_;
v___y_663_ = v___x_698_;
goto v___jp_660_;
}
case 2:
{
lean_object* v___x_699_; 
v___x_699_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6));
v___y_661_ = v___x_696_;
v___y_662_ = v___x_695_;
v___y_663_ = v___x_699_;
goto v___jp_660_;
}
default: 
{
lean_object* v___x_700_; 
v___x_700_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7));
v___y_661_ = v___x_696_;
v___y_662_ = v___x_695_;
v___y_663_ = v___x_700_;
goto v___jp_660_;
}
}
}
v___jp_701_:
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = lean_string_append(v___y_703_, v___y_702_);
lean_dec_ref(v___y_702_);
v___x_710_ = lean_string_append(v___x_709_, v___y_708_);
lean_dec_ref(v___y_708_);
v___y_686_ = v___y_704_;
v___y_687_ = v___y_705_;
v___y_688_ = v___y_706_;
v___y_689_ = v___y_707_;
v___y_690_ = v___x_710_;
goto v___jp_685_;
}
v___jp_711_:
{
switch(lean_obj_tag(v_port_714_))
{
case 0:
{
lean_object* v___x_719_; 
v___x_719_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_702_ = v___y_718_;
v___y_703_ = v___y_712_;
v___y_704_ = v___y_713_;
v___y_705_ = v___y_715_;
v___y_706_ = v___y_716_;
v___y_707_ = v___y_717_;
v___y_708_ = v___x_719_;
goto v___jp_701_;
}
case 1:
{
lean_object* v___x_720_; 
v___x_720_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___y_702_ = v___y_718_;
v___y_703_ = v___y_712_;
v___y_704_ = v___y_713_;
v___y_705_ = v___y_715_;
v___y_706_ = v___y_716_;
v___y_707_ = v___y_717_;
v___y_708_ = v___x_720_;
goto v___jp_701_;
}
default: 
{
uint16_t v_port_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v_port_721_ = lean_ctor_get_uint16(v_port_714_, 0);
lean_dec_ref_known(v_port_714_, 0);
v___x_722_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_723_ = lean_uint16_to_nat(v_port_721_);
v___x_724_ = l_Nat_reprFast(v___x_723_);
v___x_725_ = lean_string_append(v___x_722_, v___x_724_);
lean_dec_ref(v___x_724_);
v___y_702_ = v___y_718_;
v___y_703_ = v___y_712_;
v___y_704_ = v___y_713_;
v___y_705_ = v___y_715_;
v___y_706_ = v___y_716_;
v___y_707_ = v___y_717_;
v___y_708_ = v___x_725_;
goto v___jp_701_;
}
}
}
v___jp_726_:
{
switch(lean_obj_tag(v_host_729_))
{
case 0:
{
lean_object* v_name_734_; 
v_name_734_ = lean_ctor_get(v_host_729_, 0);
lean_inc_ref(v_name_734_);
lean_dec_ref_known(v_host_729_, 1);
v___y_712_ = v___y_733_;
v___y_713_ = v___y_727_;
v_port_714_ = v_port_730_;
v___y_715_ = v___y_728_;
v___y_716_ = v___y_731_;
v___y_717_ = v___y_732_;
v___y_718_ = v_name_734_;
goto v___jp_711_;
}
case 1:
{
lean_object* v_ipv4_735_; lean_object* v___x_736_; 
v_ipv4_735_ = lean_ctor_get(v_host_729_, 0);
lean_inc_ref(v_ipv4_735_);
lean_dec_ref_known(v_host_729_, 1);
v___x_736_ = lean_uv_ntop_v4(v_ipv4_735_);
lean_dec_ref(v_ipv4_735_);
v___y_712_ = v___y_733_;
v___y_713_ = v___y_727_;
v_port_714_ = v_port_730_;
v___y_715_ = v___y_728_;
v___y_716_ = v___y_731_;
v___y_717_ = v___y_732_;
v___y_718_ = v___x_736_;
goto v___jp_711_;
}
default: 
{
lean_object* v_ipv6_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v_ipv6_737_ = lean_ctor_get(v_host_729_, 0);
lean_inc_ref(v_ipv6_737_);
lean_dec_ref_known(v_host_729_, 1);
v___x_738_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9));
v___x_739_ = lean_uv_ntop_v6(v_ipv6_737_);
lean_dec_ref(v_ipv6_737_);
v___x_740_ = lean_string_append(v___x_738_, v___x_739_);
lean_dec_ref(v___x_739_);
v___x_741_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10));
v___x_742_ = lean_string_append(v___x_740_, v___x_741_);
v___y_712_ = v___y_733_;
v___y_713_ = v___y_727_;
v_port_714_ = v_port_730_;
v___y_715_ = v___y_728_;
v___y_716_ = v___y_731_;
v___y_717_ = v___y_732_;
v___y_718_ = v___x_742_;
goto v___jp_711_;
}
}
}
v___jp_743_:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_753_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_754_ = lean_string_append(v___y_747_, v___x_753_);
v___x_755_ = lean_string_append(v___x_754_, v___y_745_);
lean_dec_ref(v___y_745_);
v___x_756_ = lean_string_append(v___x_755_, v___y_746_);
lean_dec_ref(v___y_746_);
v___x_757_ = lean_string_append(v___x_756_, v___y_744_);
lean_dec_ref(v___y_744_);
v___x_758_ = lean_string_append(v___x_757_, v___y_752_);
lean_dec_ref(v___y_752_);
v___y_686_ = v___y_748_;
v___y_687_ = v___y_749_;
v___y_688_ = v___y_750_;
v___y_689_ = v___y_751_;
v___y_690_ = v___x_758_;
goto v___jp_685_;
}
v___jp_759_:
{
lean_object* v_queryPart_769_; 
v_queryPart_769_ = l_Std_Http_URI_Query_formatOption(v___y_760_);
if (lean_obj_tag(v___y_762_) == 0)
{
lean_object* v___x_770_; 
v___x_770_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_744_ = v_queryPart_769_;
v___y_745_ = v___y_761_;
v___y_746_ = v___y_768_;
v___y_747_ = v___y_763_;
v___y_748_ = v___y_764_;
v___y_749_ = v___y_765_;
v___y_750_ = v___y_766_;
v___y_751_ = v___y_767_;
v___y_752_ = v___x_770_;
goto v___jp_743_;
}
else
{
lean_object* v_val_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v_val_771_ = lean_ctor_get(v___y_762_, 0);
lean_inc(v_val_771_);
lean_dec_ref_known(v___y_762_, 1);
v___x_772_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11));
v___x_773_ = l_Std_Http_URI_EncodedFragment_encode(v_val_771_);
lean_dec(v_val_771_);
v___x_774_ = lean_string_from_utf8_unchecked(v___x_773_);
v___x_775_ = lean_string_append(v___x_772_, v___x_774_);
lean_dec_ref(v___x_774_);
v___y_744_ = v_queryPart_769_;
v___y_745_ = v___y_761_;
v___y_746_ = v___y_768_;
v___y_747_ = v___y_763_;
v___y_748_ = v___y_764_;
v___y_749_ = v___y_765_;
v___y_750_ = v___y_766_;
v___y_751_ = v___y_767_;
v___y_752_ = v___x_775_;
goto v___jp_743_;
}
}
v___jp_776_:
{
lean_object* v_queryStr_783_; lean_object* v___x_784_; 
v_queryStr_783_ = l_Std_Http_URI_Query_formatOption(v___y_777_);
v___x_784_ = lean_string_append(v___y_782_, v_queryStr_783_);
lean_dec_ref(v_queryStr_783_);
v___y_686_ = v___y_778_;
v___y_687_ = v___y_779_;
v___y_688_ = v___y_780_;
v___y_689_ = v___y_781_;
v___y_690_ = v___x_784_;
goto v___jp_685_;
}
v___jp_785_:
{
lean_object* v_segments_795_; uint8_t v_absolute_796_; lean_object* v___x_797_; lean_object* v___x_798_; size_t v_sz_799_; size_t v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v_result_803_; 
v_segments_795_ = lean_ctor_get(v___y_787_, 0);
lean_inc_ref(v_segments_795_);
v_absolute_796_ = lean_ctor_get_uint8(v___y_787_, sizeof(void*)*1);
lean_dec_ref(v___y_787_);
v___x_797_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12));
v___x_798_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22));
v_sz_799_ = lean_array_size(v_segments_795_);
v___x_800_ = ((size_t)0ULL);
v___x_801_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_798_, v___f_658_, v_sz_799_, v___x_800_, v_segments_795_);
v___x_802_ = lean_array_to_list(v___x_801_);
v_result_803_ = l_String_intercalate(v___x_797_, v___x_802_);
if (v_absolute_796_ == 0)
{
v___y_760_ = v___y_786_;
v___y_761_ = v___y_794_;
v___y_762_ = v___y_788_;
v___y_763_ = v___y_789_;
v___y_764_ = v___y_790_;
v___y_765_ = v___y_791_;
v___y_766_ = v___y_792_;
v___y_767_ = v___y_793_;
v___y_768_ = v_result_803_;
goto v___jp_759_;
}
else
{
lean_object* v___x_804_; 
v___x_804_ = lean_string_append(v___x_797_, v_result_803_);
lean_dec_ref(v_result_803_);
v___y_760_ = v___y_786_;
v___y_761_ = v___y_794_;
v___y_762_ = v___y_788_;
v___y_763_ = v___y_789_;
v___y_764_ = v___y_790_;
v___y_765_ = v___y_791_;
v___y_766_ = v___y_792_;
v___y_767_ = v___y_793_;
v___y_768_ = v___x_804_;
goto v___jp_759_;
}
}
v___jp_805_:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_818_ = lean_string_append(v___y_807_, v___y_814_);
lean_dec_ref(v___y_814_);
v___x_819_ = lean_string_append(v___x_818_, v___y_817_);
lean_dec_ref(v___y_817_);
lean_inc_ref(v___y_813_);
v___x_820_ = lean_string_append(v___y_813_, v___x_819_);
lean_dec_ref(v___x_819_);
v___y_786_ = v___y_806_;
v___y_787_ = v___y_808_;
v___y_788_ = v___y_809_;
v___y_789_ = v___y_810_;
v___y_790_ = v___y_811_;
v___y_791_ = v___y_812_;
v___y_792_ = v___y_815_;
v___y_793_ = v___y_816_;
v___y_794_ = v___x_820_;
goto v___jp_785_;
}
v___jp_821_:
{
switch(lean_obj_tag(v_port_830_))
{
case 0:
{
lean_object* v___x_834_; 
v___x_834_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_806_ = v___y_822_;
v___y_807_ = v___y_823_;
v___y_808_ = v___y_824_;
v___y_809_ = v___y_825_;
v___y_810_ = v___y_826_;
v___y_811_ = v___y_827_;
v___y_812_ = v___y_828_;
v___y_813_ = v___y_829_;
v___y_814_ = v___y_833_;
v___y_815_ = v___y_831_;
v___y_816_ = v___y_832_;
v___y_817_ = v___x_834_;
goto v___jp_805_;
}
case 1:
{
lean_object* v___x_835_; 
v___x_835_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___y_806_ = v___y_822_;
v___y_807_ = v___y_823_;
v___y_808_ = v___y_824_;
v___y_809_ = v___y_825_;
v___y_810_ = v___y_826_;
v___y_811_ = v___y_827_;
v___y_812_ = v___y_828_;
v___y_813_ = v___y_829_;
v___y_814_ = v___y_833_;
v___y_815_ = v___y_831_;
v___y_816_ = v___y_832_;
v___y_817_ = v___x_835_;
goto v___jp_805_;
}
default: 
{
uint16_t v_port_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v_port_836_ = lean_ctor_get_uint16(v_port_830_, 0);
lean_dec_ref_known(v_port_830_, 0);
v___x_837_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_838_ = lean_uint16_to_nat(v_port_836_);
v___x_839_ = l_Nat_reprFast(v___x_838_);
v___x_840_ = lean_string_append(v___x_837_, v___x_839_);
lean_dec_ref(v___x_839_);
v___y_806_ = v___y_822_;
v___y_807_ = v___y_823_;
v___y_808_ = v___y_824_;
v___y_809_ = v___y_825_;
v___y_810_ = v___y_826_;
v___y_811_ = v___y_827_;
v___y_812_ = v___y_828_;
v___y_813_ = v___y_829_;
v___y_814_ = v___y_833_;
v___y_815_ = v___y_831_;
v___y_816_ = v___y_832_;
v___y_817_ = v___x_840_;
goto v___jp_805_;
}
}
}
v___jp_841_:
{
switch(lean_obj_tag(v_host_850_))
{
case 0:
{
lean_object* v_name_854_; 
v_name_854_ = lean_ctor_get(v_host_850_, 0);
lean_inc_ref(v_name_854_);
lean_dec_ref_known(v_host_850_, 1);
v___y_822_ = v___y_842_;
v___y_823_ = v___y_853_;
v___y_824_ = v___y_843_;
v___y_825_ = v___y_844_;
v___y_826_ = v___y_845_;
v___y_827_ = v___y_846_;
v___y_828_ = v___y_847_;
v___y_829_ = v___y_848_;
v_port_830_ = v_port_851_;
v___y_831_ = v___y_849_;
v___y_832_ = v___y_852_;
v___y_833_ = v_name_854_;
goto v___jp_821_;
}
case 1:
{
lean_object* v_ipv4_855_; lean_object* v___x_856_; 
v_ipv4_855_ = lean_ctor_get(v_host_850_, 0);
lean_inc_ref(v_ipv4_855_);
lean_dec_ref_known(v_host_850_, 1);
v___x_856_ = lean_uv_ntop_v4(v_ipv4_855_);
lean_dec_ref(v_ipv4_855_);
v___y_822_ = v___y_842_;
v___y_823_ = v___y_853_;
v___y_824_ = v___y_843_;
v___y_825_ = v___y_844_;
v___y_826_ = v___y_845_;
v___y_827_ = v___y_846_;
v___y_828_ = v___y_847_;
v___y_829_ = v___y_848_;
v_port_830_ = v_port_851_;
v___y_831_ = v___y_849_;
v___y_832_ = v___y_852_;
v___y_833_ = v___x_856_;
goto v___jp_821_;
}
default: 
{
lean_object* v_ipv6_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v_ipv6_857_ = lean_ctor_get(v_host_850_, 0);
lean_inc_ref(v_ipv6_857_);
lean_dec_ref_known(v_host_850_, 1);
v___x_858_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9));
v___x_859_ = lean_uv_ntop_v6(v_ipv6_857_);
lean_dec_ref(v_ipv6_857_);
v___x_860_ = lean_string_append(v___x_858_, v___x_859_);
lean_dec_ref(v___x_859_);
v___x_861_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10));
v___x_862_ = lean_string_append(v___x_860_, v___x_861_);
v___y_822_ = v___y_842_;
v___y_823_ = v___y_853_;
v___y_824_ = v___y_843_;
v___y_825_ = v___y_844_;
v___y_826_ = v___y_845_;
v___y_827_ = v___y_846_;
v___y_828_ = v___y_847_;
v___y_829_ = v___y_848_;
v_port_830_ = v_port_851_;
v___y_831_ = v___y_849_;
v___y_832_ = v___y_852_;
v___y_833_ = v___x_862_;
goto v___jp_821_;
}
}
}
v___jp_863_:
{
lean_object* v_data_865_; lean_object* v_size_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v_data_865_ = lean_ctor_get(v_buffer_652_, 0);
lean_inc_ref(v_data_865_);
v_size_866_ = lean_ctor_get(v_buffer_652_, 1);
lean_inc(v_size_866_);
lean_dec_ref(v_buffer_652_);
v___x_867_ = lean_string_to_utf8(v___y_864_);
lean_inc_ref(v___x_867_);
v___x_868_ = lean_array_push(v_data_865_, v___x_867_);
v___x_869_ = lean_byte_array_size(v___x_867_);
lean_dec_ref(v___x_867_);
v___x_870_ = lean_nat_add(v_size_866_, v___x_869_);
lean_dec(v_size_866_);
v___x_871_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24);
v___x_872_ = lean_array_push(v___x_868_, v___x_871_);
v___x_873_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25);
v___x_874_ = lean_nat_add(v___x_870_, v___x_873_);
lean_dec(v___x_870_);
switch(lean_obj_tag(v_uri_656_))
{
case 0:
{
lean_object* v_path_875_; lean_object* v_query_876_; lean_object* v_segments_877_; uint8_t v_absolute_878_; lean_object* v___x_879_; lean_object* v___x_880_; size_t v_sz_881_; size_t v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v_result_885_; 
v_path_875_ = lean_ctor_get(v_uri_656_, 0);
lean_inc_ref(v_path_875_);
v_query_876_ = lean_ctor_get(v_uri_656_, 1);
lean_inc(v_query_876_);
lean_dec_ref_known(v_uri_656_, 2);
v_segments_877_ = lean_ctor_get(v_path_875_, 0);
lean_inc_ref(v_segments_877_);
v_absolute_878_ = lean_ctor_get_uint8(v_path_875_, sizeof(void*)*1);
lean_dec_ref(v_path_875_);
v___x_879_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12));
v___x_880_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22));
v_sz_881_ = lean_array_size(v_segments_877_);
v___x_882_ = ((size_t)0ULL);
v___x_883_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_880_, v___f_658_, v_sz_881_, v___x_882_, v_segments_877_);
v___x_884_ = lean_array_to_list(v___x_883_);
v_result_885_ = l_String_intercalate(v___x_879_, v___x_884_);
if (v_absolute_878_ == 0)
{
v___y_777_ = v_query_876_;
v___y_778_ = v___x_873_;
v___y_779_ = v___x_871_;
v___y_780_ = v___x_874_;
v___y_781_ = v___x_872_;
v___y_782_ = v_result_885_;
goto v___jp_776_;
}
else
{
lean_object* v___x_886_; 
v___x_886_ = lean_string_append(v___x_879_, v_result_885_);
lean_dec_ref(v_result_885_);
v___y_777_ = v_query_876_;
v___y_778_ = v___x_873_;
v___y_779_ = v___x_871_;
v___y_780_ = v___x_874_;
v___y_781_ = v___x_872_;
v___y_782_ = v___x_886_;
goto v___jp_776_;
}
}
case 1:
{
lean_object* v_uri_887_; lean_object* v_authority_888_; 
v_uri_887_ = lean_ctor_get(v_uri_656_, 0);
lean_inc_ref(v_uri_887_);
lean_dec_ref_known(v_uri_656_, 1);
v_authority_888_ = lean_ctor_get(v_uri_887_, 1);
if (lean_obj_tag(v_authority_888_) == 0)
{
lean_object* v_scheme_889_; lean_object* v_path_890_; lean_object* v_query_891_; lean_object* v_fragment_892_; lean_object* v___x_893_; 
v_scheme_889_ = lean_ctor_get(v_uri_887_, 0);
lean_inc_ref(v_scheme_889_);
v_path_890_ = lean_ctor_get(v_uri_887_, 2);
lean_inc_ref(v_path_890_);
v_query_891_ = lean_ctor_get(v_uri_887_, 3);
lean_inc(v_query_891_);
v_fragment_892_ = lean_ctor_get(v_uri_887_, 4);
lean_inc(v_fragment_892_);
lean_dec_ref(v_uri_887_);
v___x_893_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_786_ = v_query_891_;
v___y_787_ = v_path_890_;
v___y_788_ = v_fragment_892_;
v___y_789_ = v_scheme_889_;
v___y_790_ = v___x_873_;
v___y_791_ = v___x_871_;
v___y_792_ = v___x_874_;
v___y_793_ = v___x_872_;
v___y_794_ = v___x_893_;
goto v___jp_785_;
}
else
{
lean_object* v_val_894_; lean_object* v_scheme_895_; lean_object* v_path_896_; lean_object* v_query_897_; lean_object* v_fragment_898_; lean_object* v_userInfo_899_; lean_object* v_host_900_; lean_object* v_port_901_; lean_object* v___x_902_; 
v_val_894_ = lean_ctor_get(v_authority_888_, 0);
lean_inc(v_val_894_);
v_scheme_895_ = lean_ctor_get(v_uri_887_, 0);
lean_inc_ref(v_scheme_895_);
v_path_896_ = lean_ctor_get(v_uri_887_, 2);
lean_inc_ref(v_path_896_);
v_query_897_ = lean_ctor_get(v_uri_887_, 3);
lean_inc(v_query_897_);
v_fragment_898_ = lean_ctor_get(v_uri_887_, 4);
lean_inc(v_fragment_898_);
lean_dec_ref(v_uri_887_);
v_userInfo_899_ = lean_ctor_get(v_val_894_, 0);
lean_inc(v_userInfo_899_);
v_host_900_ = lean_ctor_get(v_val_894_, 1);
lean_inc_ref(v_host_900_);
v_port_901_ = lean_ctor_get(v_val_894_, 2);
lean_inc(v_port_901_);
lean_dec(v_val_894_);
v___x_902_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26));
if (lean_obj_tag(v_userInfo_899_) == 0)
{
lean_object* v___x_903_; 
v___x_903_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_842_ = v_query_897_;
v___y_843_ = v_path_896_;
v___y_844_ = v_fragment_898_;
v___y_845_ = v_scheme_895_;
v___y_846_ = v___x_873_;
v___y_847_ = v___x_871_;
v___y_848_ = v___x_902_;
v___y_849_ = v___x_874_;
v_host_850_ = v_host_900_;
v_port_851_ = v_port_901_;
v___y_852_ = v___x_872_;
v___y_853_ = v___x_903_;
goto v___jp_841_;
}
else
{
lean_object* v_val_904_; lean_object* v_password_905_; 
v_val_904_ = lean_ctor_get(v_userInfo_899_, 0);
lean_inc(v_val_904_);
lean_dec_ref_known(v_userInfo_899_, 1);
v_password_905_ = lean_ctor_get(v_val_904_, 1);
if (lean_obj_tag(v_password_905_) == 0)
{
lean_object* v_username_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v_username_906_ = lean_ctor_get(v_val_904_, 0);
lean_inc_ref(v_username_906_);
lean_dec(v_val_904_);
v___x_907_ = lean_string_from_utf8_unchecked(v_username_906_);
v___x_908_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27));
v___x_909_ = lean_string_append(v___x_907_, v___x_908_);
v___y_842_ = v_query_897_;
v___y_843_ = v_path_896_;
v___y_844_ = v_fragment_898_;
v___y_845_ = v_scheme_895_;
v___y_846_ = v___x_873_;
v___y_847_ = v___x_871_;
v___y_848_ = v___x_902_;
v___y_849_ = v___x_874_;
v_host_850_ = v_host_900_;
v_port_851_ = v_port_901_;
v___y_852_ = v___x_872_;
v___y_853_ = v___x_909_;
goto v___jp_841_;
}
else
{
lean_object* v_username_910_; lean_object* v_val_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
lean_inc_ref(v_password_905_);
v_username_910_ = lean_ctor_get(v_val_904_, 0);
lean_inc_ref(v_username_910_);
lean_dec(v_val_904_);
v_val_911_ = lean_ctor_get(v_password_905_, 0);
lean_inc(v_val_911_);
lean_dec_ref_known(v_password_905_, 1);
v___x_912_ = lean_string_from_utf8_unchecked(v_username_910_);
v___x_913_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_914_ = lean_string_append(v___x_912_, v___x_913_);
v___x_915_ = lean_string_from_utf8_unchecked(v_val_911_);
v___x_916_ = lean_string_append(v___x_914_, v___x_915_);
lean_dec_ref(v___x_915_);
v___x_917_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27));
v___x_918_ = lean_string_append(v___x_916_, v___x_917_);
v___y_842_ = v_query_897_;
v___y_843_ = v_path_896_;
v___y_844_ = v_fragment_898_;
v___y_845_ = v_scheme_895_;
v___y_846_ = v___x_873_;
v___y_847_ = v___x_871_;
v___y_848_ = v___x_902_;
v___y_849_ = v___x_874_;
v_host_850_ = v_host_900_;
v_port_851_ = v_port_901_;
v___y_852_ = v___x_872_;
v___y_853_ = v___x_918_;
goto v___jp_841_;
}
}
}
}
case 2:
{
lean_object* v_authority_919_; lean_object* v_userInfo_920_; 
v_authority_919_ = lean_ctor_get(v_uri_656_, 0);
lean_inc_ref(v_authority_919_);
lean_dec_ref_known(v_uri_656_, 1);
v_userInfo_920_ = lean_ctor_get(v_authority_919_, 0);
if (lean_obj_tag(v_userInfo_920_) == 0)
{
lean_object* v_host_921_; lean_object* v_port_922_; lean_object* v___x_923_; 
v_host_921_ = lean_ctor_get(v_authority_919_, 1);
lean_inc_ref(v_host_921_);
v_port_922_ = lean_ctor_get(v_authority_919_, 2);
lean_inc(v_port_922_);
lean_dec_ref(v_authority_919_);
v___x_923_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_727_ = v___x_873_;
v___y_728_ = v___x_871_;
v_host_729_ = v_host_921_;
v_port_730_ = v_port_922_;
v___y_731_ = v___x_874_;
v___y_732_ = v___x_872_;
v___y_733_ = v___x_923_;
goto v___jp_726_;
}
else
{
lean_object* v_val_924_; lean_object* v_password_925_; 
v_val_924_ = lean_ctor_get(v_userInfo_920_, 0);
lean_inc(v_val_924_);
v_password_925_ = lean_ctor_get(v_val_924_, 1);
if (lean_obj_tag(v_password_925_) == 0)
{
lean_object* v_host_926_; lean_object* v_port_927_; lean_object* v_username_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v_host_926_ = lean_ctor_get(v_authority_919_, 1);
lean_inc_ref(v_host_926_);
v_port_927_ = lean_ctor_get(v_authority_919_, 2);
lean_inc(v_port_927_);
lean_dec_ref(v_authority_919_);
v_username_928_ = lean_ctor_get(v_val_924_, 0);
lean_inc_ref(v_username_928_);
lean_dec(v_val_924_);
v___x_929_ = lean_string_from_utf8_unchecked(v_username_928_);
v___x_930_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27));
v___x_931_ = lean_string_append(v___x_929_, v___x_930_);
v___y_727_ = v___x_873_;
v___y_728_ = v___x_871_;
v_host_729_ = v_host_926_;
v_port_730_ = v_port_927_;
v___y_731_ = v___x_874_;
v___y_732_ = v___x_872_;
v___y_733_ = v___x_931_;
goto v___jp_726_;
}
else
{
lean_object* v_host_932_; lean_object* v_port_933_; lean_object* v_username_934_; lean_object* v_val_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
lean_inc_ref(v_password_925_);
v_host_932_ = lean_ctor_get(v_authority_919_, 1);
lean_inc_ref(v_host_932_);
v_port_933_ = lean_ctor_get(v_authority_919_, 2);
lean_inc(v_port_933_);
lean_dec_ref(v_authority_919_);
v_username_934_ = lean_ctor_get(v_val_924_, 0);
lean_inc_ref(v_username_934_);
lean_dec(v_val_924_);
v_val_935_ = lean_ctor_get(v_password_925_, 0);
lean_inc(v_val_935_);
lean_dec_ref_known(v_password_925_, 1);
v___x_936_ = lean_string_from_utf8_unchecked(v_username_934_);
v___x_937_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_938_ = lean_string_append(v___x_936_, v___x_937_);
v___x_939_ = lean_string_from_utf8_unchecked(v_val_935_);
v___x_940_ = lean_string_append(v___x_938_, v___x_939_);
lean_dec_ref(v___x_939_);
v___x_941_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27));
v___x_942_ = lean_string_append(v___x_940_, v___x_941_);
v___y_727_ = v___x_873_;
v___y_728_ = v___x_871_;
v_host_729_ = v_host_932_;
v_port_730_ = v_port_933_;
v___y_731_ = v___x_874_;
v___y_732_ = v___x_872_;
v___y_733_ = v___x_942_;
goto v___jp_726_;
}
}
}
default: 
{
lean_object* v___x_943_; 
v___x_943_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28));
v___y_686_ = v___x_873_;
v___y_687_ = v___x_871_;
v___y_688_ = v___x_874_;
v___y_689_ = v___x_872_;
v___y_690_ = v___x_943_;
goto v___jp_685_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(lean_object* v_buffer_984_, lean_object* v_r_985_){
_start:
{
lean_object* v_status_986_; uint8_t v_version_987_; lean_object* v_headers_988_; lean_object* v___f_989_; lean_object* v___y_991_; 
v_status_986_ = lean_ctor_get(v_r_985_, 0);
v_version_987_ = lean_ctor_get_uint8(v_r_985_, sizeof(void*)*2);
v_headers_988_ = lean_ctor_get(v_r_985_, 1);
v___f_989_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1));
switch(v_version_987_)
{
case 0:
{
lean_object* v___x_1041_; 
v___x_1041_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4));
v___y_991_ = v___x_1041_;
goto v___jp_990_;
}
case 1:
{
lean_object* v___x_1042_; 
v___x_1042_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5));
v___y_991_ = v___x_1042_;
goto v___jp_990_;
}
case 2:
{
lean_object* v___x_1043_; 
v___x_1043_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6));
v___y_991_ = v___x_1043_;
goto v___jp_990_;
}
default: 
{
lean_object* v___x_1044_; 
v___x_1044_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7));
v___y_991_ = v___x_1044_;
goto v___jp_990_;
}
}
v___jp_990_:
{
lean_object* v_data_992_; lean_object* v_size_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1040_; 
v_data_992_ = lean_ctor_get(v_buffer_984_, 0);
v_size_993_ = lean_ctor_get(v_buffer_984_, 1);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_buffer_984_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_995_ = v_buffer_984_;
v_isShared_996_ = v_isSharedCheck_1040_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_size_993_);
lean_inc(v_data_992_);
lean_dec(v_buffer_984_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1040_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; uint16_t v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v_buffer_1026_; 
v___x_997_ = lean_string_to_utf8(v___y_991_);
lean_inc_ref(v___x_997_);
v___x_998_ = lean_array_push(v_data_992_, v___x_997_);
v___x_999_ = lean_byte_array_size(v___x_997_);
lean_dec_ref(v___x_997_);
v___x_1000_ = lean_nat_add(v_size_993_, v___x_999_);
lean_dec(v_size_993_);
v___x_1001_ = lean_unsigned_to_nat(1u);
v___x_1002_ = lean_mk_empty_array_with_capacity(v___x_1001_);
lean_dec_ref(v___x_1002_);
v___x_1003_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24);
v___x_1004_ = lean_array_push(v___x_998_, v___x_1003_);
v___x_1005_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25);
v___x_1006_ = lean_nat_add(v___x_1000_, v___x_1005_);
lean_dec(v___x_1000_);
v___x_1007_ = l_Std_Http_Status_toCode(v_status_986_);
v___x_1008_ = lean_uint16_to_nat(v___x_1007_);
v___x_1009_ = l_Nat_reprFast(v___x_1008_);
v___x_1010_ = lean_string_to_utf8(v___x_1009_);
lean_dec_ref(v___x_1009_);
lean_inc_ref(v___x_1010_);
v___x_1011_ = lean_array_push(v___x_1004_, v___x_1010_);
v___x_1012_ = lean_byte_array_size(v___x_1010_);
lean_dec_ref(v___x_1010_);
v___x_1013_ = lean_nat_add(v___x_1006_, v___x_1012_);
lean_dec(v___x_1006_);
v___x_1014_ = lean_array_push(v___x_1011_, v___x_1003_);
v___x_1015_ = lean_nat_add(v___x_1013_, v___x_1005_);
lean_dec(v___x_1013_);
v___x_1016_ = l_Std_Http_Status_reasonPhrase(v_status_986_);
v___x_1017_ = lean_string_to_utf8(v___x_1016_);
lean_dec_ref(v___x_1016_);
lean_inc_ref(v___x_1017_);
v___x_1018_ = lean_array_push(v___x_1014_, v___x_1017_);
v___x_1019_ = lean_byte_array_size(v___x_1017_);
lean_dec_ref(v___x_1017_);
v___x_1020_ = lean_nat_add(v___x_1015_, v___x_1019_);
lean_dec(v___x_1015_);
v___x_1021_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_1022_ = lean_array_push(v___x_1018_, v___x_1021_);
v___x_1023_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3);
v___x_1024_ = lean_nat_add(v___x_1020_, v___x_1023_);
lean_dec(v___x_1020_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 1, v___x_1024_);
lean_ctor_set(v___x_995_, 0, v___x_1022_);
v_buffer_1026_ = v___x_995_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1022_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v___x_1024_);
v_buffer_1026_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v_buffer_1027_; lean_object* v_data_1028_; lean_object* v_size_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1038_; 
v_buffer_1027_ = l_Std_Http_Headers_fold___redArg(v_headers_988_, v_buffer_1026_, v___f_989_);
v_data_1028_ = lean_ctor_get(v_buffer_1027_, 0);
v_size_1029_ = lean_ctor_get(v_buffer_1027_, 1);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_buffer_1027_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1031_ = v_buffer_1027_;
v_isShared_1032_ = v_isSharedCheck_1038_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_size_1029_);
lean_inc(v_data_1028_);
lean_dec(v_buffer_1027_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1038_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1036_; 
v___x_1033_ = lean_array_push(v_data_1028_, v___x_1021_);
v___x_1034_ = lean_nat_add(v_size_1029_, v___x_1023_);
lean_dec(v_size_1029_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 1, v___x_1034_);
lean_ctor_set(v___x_1031_, 0, v___x_1033_);
v___x_1036_ = v___x_1031_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1033_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v___x_1034_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___boxed(lean_object* v_buffer_1045_, lean_object* v_r_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(v_buffer_1045_, v_r_1046_);
lean_dec_ref(v_r_1046_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head(uint8_t v_dir_1050_){
_start:
{
if (v_dir_1050_ == 0)
{
lean_object* v___x_1051_; 
v___x_1051_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___closed__0));
return v___x_1051_;
}
else
{
lean_object* v___x_1052_; 
v___x_1052_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___closed__1));
return v___x_1052_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___boxed(lean_object* v_dir_1053_){
_start:
{
uint8_t v_dir_boxed_1054_; lean_object* v_res_1055_; 
v_dir_boxed_1054_ = lean_unbox(v_dir_1053_);
v_res_1055_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v_dir_boxed_1054_);
return v_res_1055_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; uint8_t v___x_1059_; lean_object* v___x_1060_; 
v___x_1056_ = l_Std_Http_Headers_empty;
v___x_1057_ = lean_box(3);
v___x_1058_ = 1;
v___x_1059_ = 8;
v___x_1060_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1060_, 0, v___x_1057_);
lean_ctor_set(v___x_1060_, 1, v___x_1056_);
lean_ctor_set_uint8(v___x_1060_, sizeof(void*)*2, v___x_1059_);
lean_ctor_set_uint8(v___x_1060_, sizeof(void*)*2 + 1, v___x_1058_);
return v___x_1060_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1(void){
_start:
{
lean_object* v___x_1061_; uint8_t v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1061_ = l_Std_Http_Headers_empty;
v___x_1062_ = 1;
v___x_1063_ = lean_box(4);
v___x_1064_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
lean_ctor_set(v___x_1064_, 1, v___x_1061_);
lean_ctor_set_uint8(v___x_1064_, sizeof(void*)*2, v___x_1062_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead(uint8_t v_dir_1065_){
_start:
{
if (v_dir_1065_ == 0)
{
lean_object* v___x_1066_; 
v___x_1066_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0, &l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0_once, _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0);
return v___x_1066_;
}
else
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1, &l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1_once, _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1);
return v___x_1067_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead___boxed(lean_object* v_dir_1068_){
_start:
{
uint8_t v_dir_boxed_1069_; lean_object* v_res_1070_; 
v_dir_boxed_1069_ = lean_unbox(v_dir_1068_);
v_res_1070_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v_dir_boxed_1069_);
return v_res_1070_;
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
