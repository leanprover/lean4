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
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Http_Response_instReprHead_repr___redArg(lean_object*);
lean_object* l_Std_Http_Request_instReprHead_repr___redArg(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Std_Http_Headers_empty;
uint8_t lean_uint32_to_uint8(uint32_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_byte_array_mk(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "keep-alive"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___closed__0_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "close"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___closed__0_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_m_113_, lean_object* v_query_114_, lean_object* v_x_115_, lean_object* v_x_116_, lean_object* v_x_117_){
_start:
{
lean_object* v_zero_118_; uint8_t v_isZero_119_; 
v_zero_118_ = lean_unsigned_to_nat(0u);
v_isZero_119_ = lean_nat_dec_eq(v_x_116_, v_zero_118_);
if (v_isZero_119_ == 1)
{
lean_dec(v_x_117_);
lean_dec(v_x_116_);
if (lean_obj_tag(v_x_115_) == 0)
{
lean_object* v___x_120_; 
v___x_120_ = lean_box(2);
return v___x_120_;
}
else
{
lean_object* v_val_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
v_val_121_ = lean_ctor_get(v_x_115_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v_x_115_);
if (v_isSharedCheck_128_ == 0)
{
v___x_123_ = v_x_115_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_val_121_);
lean_dec(v_x_115_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_val_121_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
else
{
lean_object* v_keyArray_129_; lean_object* v_valueArray_130_; lean_object* v___x_131_; uint8_t v_isSome_132_; 
v_keyArray_129_ = lean_ctor_get(v_m_113_, 1);
v_valueArray_130_ = lean_ctor_get(v_m_113_, 2);
v___x_131_ = lean_array_fget_borrowed(v_keyArray_129_, v_x_117_);
v_isSome_132_ = lean_noption_is_some(v___x_131_);
if (v_isSome_132_ == 0)
{
lean_dec(v_x_116_);
if (lean_obj_tag(v_x_115_) == 0)
{
lean_object* v___x_133_; 
v___x_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_133_, 0, v_x_117_);
return v___x_133_;
}
else
{
lean_object* v_val_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_141_; 
lean_dec(v_x_117_);
v_val_134_ = lean_ctor_get(v_x_115_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v_x_115_);
if (v_isSharedCheck_141_ == 0)
{
v___x_136_ = v_x_115_;
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_val_134_);
lean_dec(v_x_115_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_139_; 
if (v_isShared_137_ == 0)
{
v___x_139_ = v___x_136_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_val_134_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
else
{
lean_object* v_one_142_; lean_object* v_n_143_; lean_object* v___y_145_; 
v_one_142_ = lean_unsigned_to_nat(1u);
v_n_143_ = lean_nat_sub(v_x_116_, v_one_142_);
lean_dec(v_x_116_);
if (v_isSome_132_ == 0)
{
goto v___jp_151_;
}
else
{
lean_object* v___x_153_; uint8_t v_isSome_154_; 
v___x_153_ = lean_array_fget_borrowed(v_valueArray_130_, v_x_117_);
v_isSome_154_ = lean_noption_is_some(v___x_153_);
if (v_isSome_154_ == 0)
{
goto v___jp_151_;
}
else
{
lean_object* v_val_155_; uint8_t v___x_156_; 
lean_inc(v___x_131_);
v_val_155_ = lean_noption_get(v___x_131_);
v___x_156_ = lean_string_dec_eq(v_val_155_, v_query_114_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
lean_dec(v_val_155_);
v___x_157_ = lean_array_get_size(v_keyArray_129_);
v___x_158_ = lean_nat_add(v_x_117_, v_one_142_);
lean_dec(v_x_117_);
v___x_159_ = lean_nat_dec_lt(v___x_158_, v___x_157_);
if (v___x_159_ == 0)
{
lean_dec(v___x_158_);
v_x_116_ = v_n_143_;
v_x_117_ = v_zero_118_;
goto _start;
}
else
{
v_x_116_ = v_n_143_;
v_x_117_ = v___x_158_;
goto _start;
}
}
else
{
lean_object* v_val_162_; lean_object* v___x_163_; 
lean_dec(v_n_143_);
lean_dec(v_x_115_);
lean_inc(v___x_153_);
v_val_162_ = lean_noption_get(v___x_153_);
v___x_163_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_163_, 0, v_x_117_);
lean_ctor_set(v___x_163_, 1, v_val_155_);
lean_ctor_set(v___x_163_, 2, v_val_162_);
return v___x_163_;
}
}
}
v___jp_144_:
{
lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_146_ = lean_array_get_size(v_keyArray_129_);
v___x_147_ = lean_nat_add(v_x_117_, v_one_142_);
lean_dec(v_x_117_);
v___x_148_ = lean_nat_dec_lt(v___x_147_, v___x_146_);
if (v___x_148_ == 0)
{
lean_dec(v___x_147_);
v_x_115_ = v___y_145_;
v_x_116_ = v_n_143_;
v_x_117_ = v_zero_118_;
goto _start;
}
else
{
v_x_115_ = v___y_145_;
v_x_116_ = v_n_143_;
v_x_117_ = v___x_147_;
goto _start;
}
}
v___jp_151_:
{
if (lean_obj_tag(v_x_115_) == 0)
{
lean_object* v___x_152_; 
lean_inc(v_x_117_);
v___x_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_152_, 0, v_x_117_);
v___y_145_ = v___x_152_;
goto v___jp_144_;
}
else
{
v___y_145_ = v_x_115_;
goto v___jp_144_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_m_164_, lean_object* v_query_165_, lean_object* v_x_166_, lean_object* v_x_167_, lean_object* v_x_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0_spec__1_spec__3___redArg(v_m_164_, v_query_165_, v_x_166_, v_x_167_, v_x_168_);
lean_dec_ref(v_query_165_);
lean_dec_ref(v_m_164_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0_spec__1___redArg(lean_object* v_m_170_, lean_object* v_query_171_){
_start:
{
lean_object* v_keyArray_172_; lean_object* v___x_173_; uint64_t v___x_174_; uint64_t v___x_175_; uint64_t v___x_176_; uint64_t v_fold_177_; uint64_t v___x_178_; uint64_t v___x_179_; uint64_t v___x_180_; size_t v___x_181_; size_t v___x_182_; size_t v___x_183_; size_t v___x_184_; size_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v_keyArray_172_ = lean_ctor_get(v_m_170_, 1);
v___x_173_ = lean_array_get_size(v_keyArray_172_);
v___x_174_ = lean_string_hash(v_query_171_);
v___x_175_ = 32ULL;
v___x_176_ = lean_uint64_shift_right(v___x_174_, v___x_175_);
v_fold_177_ = lean_uint64_xor(v___x_174_, v___x_176_);
v___x_178_ = 16ULL;
v___x_179_ = lean_uint64_shift_right(v_fold_177_, v___x_178_);
v___x_180_ = lean_uint64_xor(v_fold_177_, v___x_179_);
v___x_181_ = lean_uint64_to_usize(v___x_180_);
v___x_182_ = lean_usize_of_nat(v___x_173_);
v___x_183_ = ((size_t)1ULL);
v___x_184_ = lean_usize_sub(v___x_182_, v___x_183_);
v___x_185_ = lean_usize_land(v___x_181_, v___x_184_);
v___x_186_ = lean_usize_to_nat(v___x_185_);
v___x_187_ = lean_box(0);
v___x_188_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0_spec__1_spec__3___redArg(v_m_170_, v_query_171_, v___x_187_, v___x_173_, v___x_186_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_189_, lean_object* v_query_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0_spec__1___redArg(v_m_189_, v_query_190_);
lean_dec_ref(v_query_190_);
lean_dec_ref(v_m_189_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(lean_object* v_m_192_, lean_object* v_query_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0_spec__1___redArg(v_m_192_, v_query_193_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_index_195_; lean_object* v_key_196_; lean_object* v_value_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
v_index_195_ = lean_ctor_get(v___x_194_, 0);
v_key_196_ = lean_ctor_get(v___x_194_, 1);
v_value_197_ = lean_ctor_get(v___x_194_, 2);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_194_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_value_197_);
lean_inc(v_key_196_);
lean_inc(v_index_195_);
lean_dec(v___x_194_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_index_195_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_key_196_);
lean_ctor_set(v_reuseFailAlloc_203_, 2, v_value_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
else
{
lean_object* v___x_205_; 
lean_dec(v___x_194_);
v___x_205_ = lean_box(1);
return v___x_205_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg___boxed(lean_object* v_m_206_, lean_object* v_query_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_m_206_, v_query_207_);
lean_dec_ref(v_query_207_);
lean_dec_ref(v_m_206_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(lean_object* v_m_209_, lean_object* v_a_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_m_209_, v_a_210_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_value_212_; lean_object* v___x_213_; 
v_value_212_ = lean_ctor_get(v___x_211_, 2);
lean_inc(v_value_212_);
lean_dec_ref_known(v___x_211_, 3);
v___x_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_213_, 0, v_value_212_);
return v___x_213_;
}
else
{
lean_object* v___x_214_; 
v___x_214_ = lean_box(0);
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg___boxed(lean_object* v_m_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_m_215_, v_a_216_);
lean_dec_ref(v_a_216_);
lean_dec_ref(v_m_215_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(lean_object* v___x_218_, lean_object* v_val_219_, size_t v_sz_220_, size_t v_i_221_, lean_object* v_bs_222_){
_start:
{
uint8_t v___x_223_; 
v___x_223_ = lean_usize_dec_lt(v_i_221_, v_sz_220_);
if (v___x_223_ == 0)
{
return v_bs_222_;
}
else
{
lean_object* v_entries_224_; lean_object* v___x_225_; lean_object* v_bs_x27_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v_snd_230_; size_t v___x_231_; size_t v___x_232_; lean_object* v___x_233_; 
v_entries_224_ = lean_ctor_get(v___x_218_, 0);
v___x_225_ = lean_unsigned_to_nat(0u);
v_bs_x27_226_ = lean_array_uset(v_bs_222_, v_i_221_, v___x_225_);
v___x_227_ = lean_usize_to_nat(v_i_221_);
v___x_228_ = lean_array_fget_borrowed(v_val_219_, v___x_227_);
lean_dec(v___x_227_);
v___x_229_ = lean_array_fget_borrowed(v_entries_224_, v___x_228_);
v_snd_230_ = lean_ctor_get(v___x_229_, 1);
v___x_231_ = ((size_t)1ULL);
v___x_232_ = lean_usize_add(v_i_221_, v___x_231_);
lean_inc(v_snd_230_);
v___x_233_ = lean_array_uset(v_bs_x27_226_, v_i_221_, v_snd_230_);
v_i_221_ = v___x_232_;
v_bs_222_ = v___x_233_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg___boxed(lean_object* v___x_235_, lean_object* v_val_236_, lean_object* v_sz_237_, lean_object* v_i_238_, lean_object* v_bs_239_){
_start:
{
size_t v_sz_boxed_240_; size_t v_i_boxed_241_; lean_object* v_res_242_; 
v_sz_boxed_240_ = lean_unbox_usize(v_sz_237_);
lean_dec(v_sz_237_);
v_i_boxed_241_ = lean_unbox_usize(v_i_238_);
lean_dec(v_i_238_);
v_res_242_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_235_, v_val_236_, v_sz_boxed_240_, v_i_boxed_241_, v_bs_239_);
lean_dec_ref(v_val_236_);
lean_dec_ref(v___x_235_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize(uint8_t v_dir_251_, lean_object* v_message_252_, uint8_t v_allowEOFBody_253_){
_start:
{
lean_object* v___x_254_; lean_object* v___y_256_; lean_object* v___x_310_; lean_object* v___f_311_; lean_object* v___f_312_; uint8_t v___x_313_; 
v___x_254_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_251_, v_message_252_);
v___x_310_ = l_Std_Http_Header_Name_contentLength;
v___f_311_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0));
v___f_312_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1));
v___x_313_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_311_, v___f_312_, v___x_310_, v___x_254_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; 
v___x_314_ = lean_box(0);
v___y_256_ = v___x_314_;
goto v___jp_255_;
}
else
{
lean_object* v_indexes_315_; lean_object* v___x_316_; lean_object* v_val_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_327_; 
v_indexes_315_ = lean_ctor_get(v___x_254_, 1);
lean_inc_ref(v_indexes_315_);
v___x_316_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_315_, v___x_310_);
lean_dec_ref(v_indexes_315_);
v_val_317_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_327_ == 0)
{
v___x_319_ = v___x_316_;
v_isShared_320_ = v_isSharedCheck_327_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_val_317_);
lean_dec(v___x_316_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_327_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
size_t v_sz_321_; size_t v___x_322_; lean_object* v_entries_323_; lean_object* v___x_325_; 
v_sz_321_ = lean_array_size(v_val_317_);
v___x_322_ = ((size_t)0ULL);
lean_inc(v_val_317_);
v_entries_323_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_254_, v_val_317_, v_sz_321_, v___x_322_, v_val_317_);
lean_dec(v_val_317_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v_entries_323_);
v___x_325_ = v___x_319_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_entries_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
v___y_256_ = v___x_325_;
goto v___jp_255_;
}
}
}
v___jp_255_:
{
lean_object* v___x_257_; lean_object* v___f_258_; lean_object* v___f_259_; uint8_t v___x_260_; 
v___x_257_ = l_Std_Http_Header_Name_transferEncoding;
v___f_258_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0));
v___f_259_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1));
v___x_260_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_258_, v___f_259_, v___x_257_, v___x_254_);
if (v___x_260_ == 0)
{
lean_dec_ref(v___x_254_);
if (lean_obj_tag(v___y_256_) == 0)
{
if (v_allowEOFBody_253_ == 0)
{
lean_object* v___x_261_; 
v___x_261_ = lean_box(0);
return v___x_261_;
}
else
{
lean_object* v___x_262_; 
v___x_262_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__3));
return v___x_262_;
}
}
else
{
lean_object* v_val_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_286_; 
v_val_263_ = lean_ctor_get(v___y_256_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___y_256_);
if (v_isSharedCheck_286_ == 0)
{
v___x_265_ = v___y_256_;
v_isShared_266_ = v_isSharedCheck_286_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_val_263_);
lean_dec(v___y_256_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_286_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_267_ = lean_array_get_size(v_val_263_);
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = lean_nat_dec_eq(v___x_267_, v___x_268_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; 
lean_del_object(v___x_265_);
lean_dec(v_val_263_);
v___x_270_ = lean_box(0);
return v___x_270_;
}
else
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = lean_unsigned_to_nat(0u);
v___x_272_ = lean_array_fget(v_val_263_, v___x_271_);
lean_dec(v_val_263_);
v___x_273_ = l_Std_Http_Header_ContentLength_parse(v___x_272_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v___x_274_; 
lean_del_object(v___x_265_);
v___x_274_ = lean_box(0);
return v___x_274_;
}
else
{
lean_object* v_val_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_285_; 
v_val_275_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_285_ == 0)
{
v___x_277_ = v___x_273_;
v_isShared_278_ = v_isSharedCheck_285_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_val_275_);
lean_dec(v___x_273_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_285_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v_val_275_);
v___x_280_ = v___x_265_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_val_275_);
v___x_280_ = v_reuseFailAlloc_284_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
lean_object* v___x_282_; 
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 0, v___x_280_);
v___x_282_ = v___x_277_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
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
lean_object* v_indexes_287_; lean_object* v___x_288_; lean_object* v_val_289_; size_t v_sz_290_; size_t v___x_291_; lean_object* v_entries_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v_indexes_287_ = lean_ctor_get(v___x_254_, 1);
lean_inc_ref(v_indexes_287_);
v___x_288_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_287_, v___x_257_);
lean_dec_ref(v_indexes_287_);
v_val_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc_n(v_val_289_, 2);
lean_dec(v___x_288_);
v_sz_290_ = lean_array_size(v_val_289_);
v___x_291_ = ((size_t)0ULL);
v_entries_292_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_254_, v_val_289_, v_sz_290_, v___x_291_, v_val_289_);
lean_dec(v_val_289_);
lean_dec_ref(v___x_254_);
v___x_293_ = lean_array_get_size(v_entries_292_);
v___x_294_ = lean_unsigned_to_nat(1u);
v___x_295_ = lean_nat_dec_eq(v___x_293_, v___x_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; 
lean_dec_ref(v_entries_292_);
lean_dec(v___y_256_);
v___x_296_ = lean_box(0);
return v___x_296_;
}
else
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v_te_299_; 
v___x_297_ = lean_unsigned_to_nat(0u);
v___x_298_ = lean_array_fget(v_entries_292_, v___x_297_);
lean_dec_ref(v_entries_292_);
v_te_299_ = l_Std_Http_Header_TransferEncoding_parse(v___x_298_);
if (lean_obj_tag(v_te_299_) == 0)
{
lean_object* v___x_300_; 
lean_dec(v___y_256_);
v___x_300_ = lean_box(0);
return v___x_300_;
}
else
{
lean_object* v_val_301_; uint8_t v___x_302_; 
v_val_301_ = lean_ctor_get(v_te_299_, 0);
lean_inc(v_val_301_);
lean_dec_ref_known(v_te_299_, 1);
v___x_302_ = l_Std_Http_Header_TransferEncoding_isChunked(v_val_301_);
lean_dec(v_val_301_);
if (v___x_302_ == 1)
{
if (lean_obj_tag(v___y_256_) == 0)
{
uint8_t v___x_303_; uint8_t v___x_304_; uint8_t v___x_305_; 
v___x_303_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_251_, v_message_252_);
v___x_304_ = 0;
v___x_305_ = l_Std_Http_instBEqVersion_beq(v___x_303_, v___x_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; 
v___x_306_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__4));
return v___x_306_;
}
else
{
lean_object* v___x_307_; 
v___x_307_ = lean_box(0);
return v___x_307_;
}
}
else
{
lean_object* v___x_308_; 
lean_dec(v___y_256_);
v___x_308_ = lean_box(0);
return v___x_308_;
}
}
else
{
lean_object* v___x_309_; 
lean_dec(v___y_256_);
v___x_309_ = lean_box(0);
return v___x_309_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize___boxed(lean_object* v_dir_328_, lean_object* v_message_329_, lean_object* v_allowEOFBody_330_){
_start:
{
uint8_t v_dir_boxed_331_; uint8_t v_allowEOFBody_boxed_332_; lean_object* v_res_333_; 
v_dir_boxed_331_ = lean_unbox(v_dir_328_);
v_allowEOFBody_boxed_332_ = lean_unbox(v_allowEOFBody_330_);
v_res_333_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v_dir_boxed_331_, v_message_329_, v_allowEOFBody_boxed_332_);
lean_dec(v_message_329_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(lean_object* v_00_u03b2_334_, lean_object* v_m_335_, lean_object* v_a_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_m_335_, v_a_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___boxed(lean_object* v_00_u03b2_338_, lean_object* v_m_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(v_00_u03b2_338_, v_m_339_, v_a_340_);
lean_dec_ref(v_a_340_);
lean_dec_ref(v_m_339_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(lean_object* v___x_342_, lean_object* v_val_343_, lean_object* v_as_344_, size_t v_sz_345_, size_t v_i_346_, lean_object* v_bs_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_342_, v_val_343_, v_sz_345_, v_i_346_, v_bs_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___boxed(lean_object* v___x_349_, lean_object* v_val_350_, lean_object* v_as_351_, lean_object* v_sz_352_, lean_object* v_i_353_, lean_object* v_bs_354_){
_start:
{
size_t v_sz_boxed_355_; size_t v_i_boxed_356_; lean_object* v_res_357_; 
v_sz_boxed_355_ = lean_unbox_usize(v_sz_352_);
lean_dec(v_sz_352_);
v_i_boxed_356_ = lean_unbox_usize(v_i_353_);
lean_dec(v_i_353_);
v_res_357_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(v___x_349_, v_val_350_, v_as_351_, v_sz_boxed_355_, v_i_boxed_356_, v_bs_354_);
lean_dec_ref(v_as_351_);
lean_dec_ref(v_val_350_);
lean_dec_ref(v___x_349_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0(lean_object* v_00_u03b2_358_, lean_object* v_m_359_, lean_object* v_query_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_m_359_, v_query_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_362_, lean_object* v_m_363_, lean_object* v_query_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0(v_00_u03b2_362_, v_m_363_, v_query_364_);
lean_dec_ref(v_query_364_);
lean_dec_ref(v_m_363_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_366_, lean_object* v_m_367_, lean_object* v_query_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0_spec__1___redArg(v_m_367_, v_query_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_370_, lean_object* v_m_371_, lean_object* v_query_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0_spec__1(v_00_u03b2_370_, v_m_371_, v_query_372_);
lean_dec_ref(v_query_372_);
lean_dec_ref(v_m_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_374_, lean_object* v_m_375_, lean_object* v_query_376_, lean_object* v_x_377_, lean_object* v_x_378_, lean_object* v_x_379_, lean_object* v_x_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0_spec__1_spec__3___redArg(v_m_375_, v_query_376_, v_x_377_, v_x_378_, v_x_379_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_382_, lean_object* v_m_383_, lean_object* v_query_384_, lean_object* v_x_385_, lean_object* v_x_386_, lean_object* v_x_387_, lean_object* v_x_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_382_, v_m_383_, v_query_384_, v_x_385_, v_x_386_, v_x_387_, v_x_388_);
lean_dec_ref(v_query_384_);
lean_dec_ref(v_m_383_);
return v_res_389_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(lean_object* v_as_391_, size_t v_i_392_, size_t v_stop_393_){
_start:
{
uint8_t v___x_394_; 
v___x_394_ = lean_usize_dec_eq(v_i_392_, v_stop_393_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_395_ = lean_array_uget_borrowed(v_as_391_, v_i_392_);
v___x_396_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___closed__0));
v___x_397_ = lean_string_dec_eq(v___x_395_, v___x_396_);
if (v___x_397_ == 0)
{
size_t v___x_398_; size_t v___x_399_; 
v___x_398_ = ((size_t)1ULL);
v___x_399_ = lean_usize_add(v_i_392_, v___x_398_);
v_i_392_ = v___x_399_;
goto _start;
}
else
{
return v___x_397_;
}
}
else
{
uint8_t v___x_401_; 
v___x_401_ = 0;
return v___x_401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___boxed(lean_object* v_as_402_, lean_object* v_i_403_, lean_object* v_stop_404_){
_start:
{
size_t v_i_boxed_405_; size_t v_stop_boxed_406_; uint8_t v_res_407_; lean_object* v_r_408_; 
v_i_boxed_405_ = lean_unbox_usize(v_i_403_);
lean_dec(v_i_403_);
v_stop_boxed_406_ = lean_unbox_usize(v_stop_404_);
lean_dec(v_stop_404_);
v_res_407_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(v_as_402_, v_i_boxed_405_, v_stop_boxed_406_);
lean_dec_ref(v_as_402_);
v_r_408_ = lean_box(v_res_407_);
return v_r_408_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(lean_object* v_as_410_, size_t v_i_411_, size_t v_stop_412_){
_start:
{
uint8_t v___x_413_; 
v___x_413_ = lean_usize_dec_eq(v_i_411_, v_stop_412_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_414_ = lean_array_uget_borrowed(v_as_410_, v_i_411_);
v___x_415_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___closed__0));
v___x_416_ = lean_string_dec_eq(v___x_414_, v___x_415_);
if (v___x_416_ == 0)
{
size_t v___x_417_; size_t v___x_418_; 
v___x_417_ = ((size_t)1ULL);
v___x_418_ = lean_usize_add(v_i_411_, v___x_417_);
v_i_411_ = v___x_418_;
goto _start;
}
else
{
return v___x_416_;
}
}
else
{
uint8_t v___x_420_; 
v___x_420_ = 0;
return v___x_420_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___boxed(lean_object* v_as_421_, lean_object* v_i_422_, lean_object* v_stop_423_){
_start:
{
size_t v_i_boxed_424_; size_t v_stop_boxed_425_; uint8_t v_res_426_; lean_object* v_r_427_; 
v_i_boxed_424_ = lean_unbox_usize(v_i_422_);
lean_dec(v_i_422_);
v_stop_boxed_425_ = lean_unbox_usize(v_stop_423_);
lean_dec(v_stop_423_);
v_res_426_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(v_as_421_, v_i_boxed_424_, v_stop_boxed_425_);
lean_dec_ref(v_as_421_);
v_r_427_ = lean_box(v_res_426_);
return v_r_427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(lean_object* v_as_428_, size_t v_i_429_, size_t v_stop_430_, lean_object* v_b_431_){
_start:
{
lean_object* v___y_433_; uint8_t v___x_437_; 
v___x_437_ = lean_usize_dec_eq(v_i_429_, v_stop_430_);
if (v___x_437_ == 0)
{
if (lean_obj_tag(v_b_431_) == 0)
{
v___y_433_ = v_b_431_;
goto v___jp_432_;
}
else
{
lean_object* v_val_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v_val_438_ = lean_ctor_get(v_b_431_, 0);
lean_inc(v_val_438_);
lean_dec_ref_known(v_b_431_, 1);
v___x_439_ = lean_array_uget_borrowed(v_as_428_, v_i_429_);
lean_inc(v___x_439_);
v___x_440_ = l_Std_Http_Header_Connection_parse(v___x_439_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v___x_441_; 
lean_dec(v_val_438_);
v___x_441_ = lean_box(0);
v___y_433_ = v___x_441_;
goto v___jp_432_;
}
else
{
lean_object* v_val_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_450_; 
v_val_442_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_450_ == 0)
{
v___x_444_ = v___x_440_;
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_val_442_);
lean_dec(v___x_440_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_446_ = l_Array_append___redArg(v_val_438_, v_val_442_);
lean_dec(v_val_442_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_446_);
v___x_448_ = v___x_444_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
v___y_433_ = v___x_448_;
goto v___jp_432_;
}
}
}
}
}
else
{
return v_b_431_;
}
v___jp_432_:
{
size_t v___x_434_; size_t v___x_435_; 
v___x_434_ = ((size_t)1ULL);
v___x_435_ = lean_usize_add(v_i_429_, v___x_434_);
v_i_429_ = v___x_435_;
v_b_431_ = v___y_433_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2___boxed(lean_object* v_as_451_, lean_object* v_i_452_, lean_object* v_stop_453_, lean_object* v_b_454_){
_start:
{
size_t v_i_boxed_455_; size_t v_stop_boxed_456_; lean_object* v_res_457_; 
v_i_boxed_455_ = lean_unbox_usize(v_i_452_);
lean_dec(v_i_452_);
v_stop_boxed_456_ = lean_unbox_usize(v_stop_453_);
lean_dec(v_stop_453_);
v_res_457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_as_451_, v_i_boxed_455_, v_stop_boxed_456_, v_b_454_);
lean_dec_ref(v_as_451_);
return v_res_457_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(uint8_t v_dir_462_, lean_object* v_message_463_){
_start:
{
lean_object* v_val_465_; lean_object* v___y_483_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___f_488_; lean_object* v___f_489_; uint8_t v___x_490_; 
v___x_486_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_462_, v_message_463_);
v___x_487_ = l_Std_Http_Header_Name_connection;
v___f_488_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0));
v___f_489_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1));
v___x_490_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_488_, v___f_489_, v___x_487_, v___x_486_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; 
lean_dec_ref(v___x_486_);
v___x_491_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0));
v_val_465_ = v___x_491_;
goto v___jp_464_;
}
else
{
lean_object* v_indexes_492_; lean_object* v___x_493_; lean_object* v_val_494_; size_t v_sz_495_; size_t v___x_496_; lean_object* v_entries_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v_indexes_492_ = lean_ctor_get(v___x_486_, 1);
lean_inc_ref(v_indexes_492_);
v___x_493_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_492_, v___x_487_);
lean_dec_ref(v_indexes_492_);
v_val_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc_n(v_val_494_, 2);
lean_dec(v___x_493_);
v_sz_495_ = lean_array_size(v_val_494_);
v___x_496_ = ((size_t)0ULL);
v_entries_497_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_486_, v_val_494_, v_sz_495_, v___x_496_, v_val_494_);
lean_dec(v_val_494_);
lean_dec_ref(v___x_486_);
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0));
v___x_500_ = lean_array_get_size(v_entries_497_);
v___x_501_ = lean_nat_dec_lt(v___x_498_, v___x_500_);
if (v___x_501_ == 0)
{
lean_dec_ref(v_entries_497_);
v_val_465_ = v___x_499_;
goto v___jp_464_;
}
else
{
lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_502_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__1));
v___x_503_ = lean_nat_dec_le(v___x_500_, v___x_500_);
if (v___x_503_ == 0)
{
if (v___x_501_ == 0)
{
lean_dec_ref(v_entries_497_);
v_val_465_ = v___x_499_;
goto v___jp_464_;
}
else
{
size_t v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_usize_of_nat(v___x_500_);
v___x_505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_entries_497_, v___x_496_, v___x_504_, v___x_502_);
lean_dec_ref(v_entries_497_);
v___y_483_ = v___x_505_;
goto v___jp_482_;
}
}
else
{
size_t v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_usize_of_nat(v___x_500_);
v___x_507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_entries_497_, v___x_496_, v___x_506_, v___x_502_);
lean_dec_ref(v_entries_497_);
v___y_483_ = v___x_507_;
goto v___jp_482_;
}
}
}
v___jp_464_:
{
uint8_t v___x_466_; uint8_t v___x_467_; uint8_t v___x_468_; 
v___x_466_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_462_, v_message_463_);
v___x_467_ = 1;
v___x_468_ = l_Std_Http_instBEqVersion_beq(v___x_466_, v___x_467_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_469_ = lean_unsigned_to_nat(0u);
v___x_470_ = lean_array_get_size(v_val_465_);
v___x_471_ = lean_nat_dec_lt(v___x_469_, v___x_470_);
if (v___x_471_ == 0)
{
lean_dec_ref(v_val_465_);
return v___x_468_;
}
else
{
if (v___x_471_ == 0)
{
lean_dec_ref(v_val_465_);
return v___x_468_;
}
else
{
size_t v___x_472_; size_t v___x_473_; uint8_t v___x_474_; 
v___x_472_ = ((size_t)0ULL);
v___x_473_ = lean_usize_of_nat(v___x_470_);
v___x_474_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(v_val_465_, v___x_472_, v___x_473_);
lean_dec_ref(v_val_465_);
return v___x_474_;
}
}
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_475_ = lean_unsigned_to_nat(0u);
v___x_476_ = lean_array_get_size(v_val_465_);
v___x_477_ = lean_nat_dec_lt(v___x_475_, v___x_476_);
if (v___x_477_ == 0)
{
lean_dec_ref(v_val_465_);
return v___x_468_;
}
else
{
if (v___x_477_ == 0)
{
lean_dec_ref(v_val_465_);
return v___x_468_;
}
else
{
size_t v___x_478_; size_t v___x_479_; uint8_t v___x_480_; 
v___x_478_ = ((size_t)0ULL);
v___x_479_ = lean_usize_of_nat(v___x_476_);
v___x_480_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(v_val_465_, v___x_478_, v___x_479_);
lean_dec_ref(v_val_465_);
if (v___x_480_ == 0)
{
return v___x_468_;
}
else
{
uint8_t v___x_481_; 
v___x_481_ = 0;
return v___x_481_;
}
}
}
}
}
v___jp_482_:
{
if (lean_obj_tag(v___y_483_) == 0)
{
uint8_t v___x_484_; 
v___x_484_ = 0;
return v___x_484_;
}
else
{
lean_object* v_val_485_; 
v_val_485_ = lean_ctor_get(v___y_483_, 0);
lean_inc(v_val_485_);
lean_dec_ref_known(v___y_483_, 1);
v_val_465_ = v_val_485_;
goto v___jp_464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___boxed(lean_object* v_dir_508_, lean_object* v_message_509_){
_start:
{
uint8_t v_dir_boxed_510_; uint8_t v_res_511_; lean_object* v_r_512_; 
v_dir_boxed_510_ = lean_unbox(v_dir_508_);
v_res_511_ = l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(v_dir_boxed_510_, v_message_509_);
lean_dec(v_message_509_);
v_r_512_ = lean_box(v_res_511_);
return v_r_512_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1___redArg(lean_object* v_x_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Std_Http_Request_instReprHead_repr___redArg(v_x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1(lean_object* v_x_515_, lean_object* v_prec_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Std_Http_Request_instReprHead_repr___redArg(v_x_515_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1___boxed(lean_object* v_x_518_, lean_object* v_prec_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Std_Http_Protocol_H1_instReprHead___aux__1(v_x_518_, v_prec_519_);
lean_dec(v_prec_519_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3___redArg(lean_object* v_x_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Std_Http_Response_instReprHead_repr___redArg(v_x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3(lean_object* v_x_523_, lean_object* v_prec_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Std_Http_Response_instReprHead_repr___redArg(v_x_523_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3___boxed(lean_object* v_x_526_, lean_object* v_prec_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Std_Http_Protocol_H1_instReprHead___aux__3(v_x_526_, v_prec_527_);
lean_dec(v_prec_527_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead(uint8_t v_dir_531_){
_start:
{
if (v_dir_531_ == 0)
{
lean_object* v___x_532_; 
v___x_532_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprHead___closed__0));
return v___x_532_;
}
else
{
lean_object* v___x_533_; 
v___x_533_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprHead___closed__1));
return v___x_533_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___boxed(lean_object* v_dir_534_){
_start:
{
uint8_t v_dir_boxed_535_; lean_object* v_res_536_; 
v_dir_boxed_535_ = lean_unbox(v_dir_534_);
v_res_536_ = l_Std_Http_Protocol_H1_instReprHead(v_dir_boxed_535_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__0(lean_object* v_x_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = lean_string_from_utf8_unchecked(v_x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1(lean_object* v___x_539_, lean_object* v___x_540_, lean_object* v___x_541_, lean_object* v_name_542_, lean_object* v___x_543_, uint32_t v___x_544_, lean_object* v___x_545_, lean_object* v_it_546_, lean_object* v_acc_547_, lean_object* v_hP_548_, lean_object* v_recur_549_){
_start:
{
lean_object* v_it_551_; lean_object* v_out_552_; lean_object* v_it_568_; lean_object* v_startInclusive_569_; lean_object* v_endExclusive_570_; 
if (lean_obj_tag(v_it_546_) == 0)
{
lean_object* v_currPos_582_; lean_object* v_searcher_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_605_; 
v_currPos_582_ = lean_ctor_get(v_it_546_, 0);
v_searcher_583_ = lean_ctor_get(v_it_546_, 1);
v_isSharedCheck_605_ = !lean_is_exclusive(v_it_546_);
if (v_isSharedCheck_605_ == 0)
{
v___x_585_ = v_it_546_;
v_isShared_586_ = v_isSharedCheck_605_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_searcher_583_);
lean_inc(v_currPos_582_);
lean_dec(v_it_546_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_605_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
uint8_t v___x_587_; 
v___x_587_ = lean_nat_dec_eq(v_searcher_583_, v___x_543_);
if (v___x_587_ == 0)
{
uint32_t v___x_588_; uint8_t v___x_589_; 
lean_dec(v___x_543_);
v___x_588_ = lean_string_utf8_get_fast(v_name_542_, v_searcher_583_);
v___x_589_ = lean_uint32_dec_eq(v___x_588_, v___x_544_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_590_ = lean_string_utf8_next_fast(v_name_542_, v_searcher_583_);
lean_dec(v_searcher_583_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 1, v___x_590_);
v___x_592_ = v___x_585_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_currPos_582_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v___x_590_);
v___x_592_ = v_reuseFailAlloc_594_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_593_; 
v___x_593_ = lean_apply_4(v_recur_549_, v___x_592_, v_acc_547_, lean_box(0), lean_box(0));
return v___x_593_;
}
}
else
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v_slice_598_; lean_object* v_nextIt_600_; 
v___x_595_ = lean_string_utf8_next_fast(v_name_542_, v_searcher_583_);
v___x_596_ = lean_nat_sub(v___x_595_, v_searcher_583_);
v___x_597_ = lean_nat_add(v_searcher_583_, v___x_596_);
lean_dec(v___x_596_);
v_slice_598_ = l_String_Slice_subslice_x21(v___x_545_, v_currPos_582_, v_searcher_583_);
lean_inc(v___x_597_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 1, v___x_597_);
lean_ctor_set(v___x_585_, 0, v___x_597_);
v_nextIt_600_ = v___x_585_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v___x_597_);
v_nextIt_600_ = v_reuseFailAlloc_603_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v_startInclusive_601_; lean_object* v_endExclusive_602_; 
v_startInclusive_601_ = lean_ctor_get(v_slice_598_, 0);
lean_inc(v_startInclusive_601_);
v_endExclusive_602_ = lean_ctor_get(v_slice_598_, 1);
lean_inc(v_endExclusive_602_);
lean_dec_ref(v_slice_598_);
v_it_568_ = v_nextIt_600_;
v_startInclusive_569_ = v_startInclusive_601_;
v_endExclusive_570_ = v_endExclusive_602_;
goto v___jp_567_;
}
}
}
else
{
lean_object* v___x_604_; 
lean_del_object(v___x_585_);
lean_dec(v_searcher_583_);
v___x_604_ = lean_box(1);
v_it_568_ = v___x_604_;
v_startInclusive_569_ = v_currPos_582_;
v_endExclusive_570_ = v___x_543_;
goto v___jp_567_;
}
}
}
else
{
lean_dec_ref(v_recur_549_);
lean_dec(v___x_543_);
return v_acc_547_;
}
v___jp_550_:
{
if (lean_obj_tag(v_acc_547_) == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_553_, 0, v_out_552_);
v___x_554_ = lean_apply_4(v_recur_549_, v_it_551_, v___x_553_, lean_box(0), lean_box(0));
return v___x_554_;
}
else
{
lean_object* v_val_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_566_; 
v_val_555_ = lean_ctor_get(v_acc_547_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v_acc_547_);
if (v_isSharedCheck_566_ == 0)
{
v___x_557_ = v_acc_547_;
v_isShared_558_ = v_isSharedCheck_566_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_val_555_);
lean_dec(v_acc_547_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_566_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_559_ = lean_string_utf8_extract_fast(v___x_539_, v___x_540_, v___x_541_);
v___x_560_ = lean_string_append(v_val_555_, v___x_559_);
lean_dec_ref(v___x_559_);
v___x_561_ = lean_string_append(v___x_560_, v_out_552_);
lean_dec_ref(v_out_552_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_561_);
v___x_563_ = v___x_557_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_561_);
v___x_563_ = v_reuseFailAlloc_565_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_564_; 
v___x_564_ = lean_apply_4(v_recur_549_, v_it_551_, v___x_563_, lean_box(0), lean_box(0));
return v___x_564_;
}
}
}
}
v___jp_567_:
{
lean_object* v___x_571_; uint32_t v___x_572_; uint32_t v___x_573_; uint8_t v___x_574_; 
v___x_571_ = lean_string_utf8_extract_fast(v_name_542_, v_startInclusive_569_, v_endExclusive_570_);
lean_dec(v_endExclusive_570_);
lean_dec(v_startInclusive_569_);
v___x_572_ = lean_string_utf8_get(v___x_571_, v___x_540_);
v___x_573_ = 97;
v___x_574_ = lean_uint32_dec_le(v___x_573_, v___x_572_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; 
v___x_575_ = lean_string_utf8_set(v___x_571_, v___x_540_, v___x_572_);
v_it_551_ = v_it_568_;
v_out_552_ = v___x_575_;
goto v___jp_550_;
}
else
{
uint32_t v___x_576_; uint8_t v___x_577_; 
v___x_576_ = 122;
v___x_577_ = lean_uint32_dec_le(v___x_572_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; 
v___x_578_ = lean_string_utf8_set(v___x_571_, v___x_540_, v___x_572_);
v_it_551_ = v_it_568_;
v_out_552_ = v___x_578_;
goto v___jp_550_;
}
else
{
uint32_t v___x_579_; uint32_t v___x_580_; lean_object* v___x_581_; 
v___x_579_ = 4294967264;
v___x_580_ = lean_uint32_add(v___x_572_, v___x_579_);
v___x_581_ = lean_string_utf8_set(v___x_571_, v___x_540_, v___x_580_);
v_it_551_ = v_it_568_;
v_out_552_ = v___x_581_;
goto v___jp_550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1___boxed(lean_object* v___x_606_, lean_object* v___x_607_, lean_object* v___x_608_, lean_object* v_name_609_, lean_object* v___x_610_, lean_object* v___x_611_, lean_object* v___x_612_, lean_object* v_it_613_, lean_object* v_acc_614_, lean_object* v_hP_615_, lean_object* v_recur_616_){
_start:
{
uint32_t v___x_2699__boxed_617_; lean_object* v_res_618_; 
v___x_2699__boxed_617_ = lean_unbox_uint32(v___x_611_);
lean_dec(v___x_611_);
v_res_618_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1(v___x_606_, v___x_607_, v___x_608_, v_name_609_, v___x_610_, v___x_2699__boxed_617_, v___x_612_, v_it_613_, v_acc_614_, v_hP_615_, v_recur_616_);
lean_dec_ref(v___x_612_);
lean_dec_ref(v_name_609_);
lean_dec(v___x_608_);
lean_dec(v___x_607_);
lean_dec_ref(v___x_606_);
return v_res_618_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__3));
v___x_624_ = lean_string_utf8_byte_size(v___x_623_);
return v___x_624_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed__const__1(void){
_start:
{
uint32_t v___x_626_; lean_object* v___x_627_; 
v___x_626_ = 45;
v___x_627_ = lean_box_uint32(v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2(lean_object* v_buf_628_, lean_object* v_name_629_, lean_object* v_value_630_){
_start:
{
lean_object* v___y_632_; lean_object* v___f_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v_it_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___f_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___f_651_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__2));
v___x_652_ = lean_unsigned_to_nat(0u);
v___x_653_ = lean_string_utf8_byte_size(v_name_629_);
lean_inc_ref(v_name_629_);
v___x_654_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_654_, 0, v_name_629_);
lean_ctor_set(v___x_654_, 1, v___x_652_);
lean_ctor_set(v___x_654_, 2, v___x_653_);
lean_inc_ref(v___x_654_);
v_it_655_ = l_String_Slice_splitToSubslice___redArg(v___x_654_, v___f_651_);
v___x_656_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__3));
v___x_657_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4);
v___x_658_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed__const__1;
v___f_659_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1___boxed), 11, 7);
lean_closure_set(v___f_659_, 0, v___x_656_);
lean_closure_set(v___f_659_, 1, v___x_652_);
lean_closure_set(v___f_659_, 2, v___x_657_);
lean_closure_set(v___f_659_, 3, v_name_629_);
lean_closure_set(v___f_659_, 4, v___x_653_);
lean_closure_set(v___f_659_, 5, v___x_658_);
lean_closure_set(v___f_659_, 6, v___x_654_);
v___x_660_ = lean_box(0);
v___x_661_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_659_, v_it_655_, v___x_660_, lean_box(0));
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v___x_662_; 
v___x_662_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_632_ = v___x_662_;
goto v___jp_631_;
}
else
{
lean_object* v_val_663_; 
v_val_663_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_val_663_);
lean_dec_ref_known(v___x_661_, 1);
v___y_632_ = v_val_663_;
goto v___jp_631_;
}
v___jp_631_:
{
lean_object* v_data_633_; lean_object* v_size_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_650_; 
v_data_633_ = lean_ctor_get(v_buf_628_, 0);
v_size_634_ = lean_ctor_get(v_buf_628_, 1);
v_isSharedCheck_650_ = !lean_is_exclusive(v_buf_628_);
if (v_isSharedCheck_650_ == 0)
{
v___x_636_ = v_buf_628_;
v_isShared_637_ = v_isSharedCheck_650_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_size_634_);
lean_inc(v_data_633_);
lean_dec(v_buf_628_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_650_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_648_; 
v___x_638_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__0));
v___x_639_ = lean_string_append(v___y_632_, v___x_638_);
v___x_640_ = lean_string_append(v___x_639_, v_value_630_);
v___x_641_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__1));
v___x_642_ = lean_string_append(v___x_640_, v___x_641_);
v___x_643_ = lean_string_to_utf8(v___x_642_);
lean_dec_ref(v___x_642_);
lean_inc_ref(v___x_643_);
v___x_644_ = lean_array_push(v_data_633_, v___x_643_);
v___x_645_ = lean_byte_array_size(v___x_643_);
lean_dec_ref(v___x_643_);
v___x_646_ = lean_nat_add(v_size_634_, v___x_645_);
lean_dec(v_size_634_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v___x_646_);
lean_ctor_set(v___x_636_, 0, v___x_644_);
v___x_648_ = v___x_636_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_644_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v___x_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed(lean_object* v_buf_664_, lean_object* v_name_665_, lean_object* v_value_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2(v_buf_664_, v_name_665_, v_value_666_);
lean_dec_ref(v_value_666_);
return v_res_667_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__1));
v___x_671_ = lean_string_to_utf8(v___x_670_);
return v___x_671_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_673_ = lean_byte_array_size(v___x_672_);
return v___x_673_;
}
}
static uint8_t _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23(void){
_start:
{
uint32_t v___x_702_; uint8_t v___x_703_; 
v___x_702_ = 32;
v___x_703_ = lean_uint32_to_uint8(v___x_702_);
return v___x_703_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24(void){
_start:
{
uint8_t v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_704_ = lean_uint8_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23);
v___x_705_ = lean_unsigned_to_nat(1u);
v___x_706_ = lean_mk_empty_array_with_capacity(v___x_705_);
v___x_707_ = lean_box(v___x_704_);
v___x_708_ = lean_array_push(v___x_706_, v___x_707_);
v___x_709_ = lean_byte_array_mk(v___x_708_);
return v___x_709_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24);
v___x_711_ = lean_byte_array_size(v___x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1(lean_object* v_buffer_755_, lean_object* v_req_756_){
_start:
{
uint8_t v_method_757_; uint8_t v_version_758_; lean_object* v_uri_759_; lean_object* v_headers_760_; lean_object* v___f_761_; lean_object* v___f_762_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v_port_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v_host_833_; lean_object* v_port_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_925_; lean_object* v_port_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v_host_945_; lean_object* v_port_946_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_967_; 
v_method_757_ = lean_ctor_get_uint8(v_req_756_, sizeof(void*)*2);
v_version_758_ = lean_ctor_get_uint8(v_req_756_, sizeof(void*)*2 + 1);
v_uri_759_ = lean_ctor_get(v_req_756_, 0);
lean_inc(v_uri_759_);
v_headers_760_ = lean_ctor_get(v_req_756_, 1);
lean_inc_ref(v_headers_760_);
lean_dec_ref(v_req_756_);
v___f_761_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__0));
v___f_762_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1));
switch(v_method_757_)
{
case 0:
{
lean_object* v___x_1047_; 
v___x_1047_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29));
v___y_967_ = v___x_1047_;
goto v___jp_966_;
}
case 1:
{
lean_object* v___x_1048_; 
v___x_1048_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30));
v___y_967_ = v___x_1048_;
goto v___jp_966_;
}
case 2:
{
lean_object* v___x_1049_; 
v___x_1049_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31));
v___y_967_ = v___x_1049_;
goto v___jp_966_;
}
case 3:
{
lean_object* v___x_1050_; 
v___x_1050_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32));
v___y_967_ = v___x_1050_;
goto v___jp_966_;
}
case 4:
{
lean_object* v___x_1051_; 
v___x_1051_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33));
v___y_967_ = v___x_1051_;
goto v___jp_966_;
}
case 5:
{
lean_object* v___x_1052_; 
v___x_1052_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34));
v___y_967_ = v___x_1052_;
goto v___jp_966_;
}
case 6:
{
lean_object* v___x_1053_; 
v___x_1053_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35));
v___y_967_ = v___x_1053_;
goto v___jp_966_;
}
case 7:
{
lean_object* v___x_1054_; 
v___x_1054_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36));
v___y_967_ = v___x_1054_;
goto v___jp_966_;
}
case 8:
{
lean_object* v___x_1055_; 
v___x_1055_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37));
v___y_967_ = v___x_1055_;
goto v___jp_966_;
}
case 9:
{
lean_object* v___x_1056_; 
v___x_1056_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38));
v___y_967_ = v___x_1056_;
goto v___jp_966_;
}
case 10:
{
lean_object* v___x_1057_; 
v___x_1057_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39));
v___y_967_ = v___x_1057_;
goto v___jp_966_;
}
case 11:
{
lean_object* v___x_1058_; 
v___x_1058_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40));
v___y_967_ = v___x_1058_;
goto v___jp_966_;
}
case 12:
{
lean_object* v___x_1059_; 
v___x_1059_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41));
v___y_967_ = v___x_1059_;
goto v___jp_966_;
}
case 13:
{
lean_object* v___x_1060_; 
v___x_1060_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42));
v___y_967_ = v___x_1060_;
goto v___jp_966_;
}
case 14:
{
lean_object* v___x_1061_; 
v___x_1061_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43));
v___y_967_ = v___x_1061_;
goto v___jp_966_;
}
case 15:
{
lean_object* v___x_1062_; 
v___x_1062_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44));
v___y_967_ = v___x_1062_;
goto v___jp_966_;
}
case 16:
{
lean_object* v___x_1063_; 
v___x_1063_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45));
v___y_967_ = v___x_1063_;
goto v___jp_966_;
}
case 17:
{
lean_object* v___x_1064_; 
v___x_1064_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46));
v___y_967_ = v___x_1064_;
goto v___jp_966_;
}
case 18:
{
lean_object* v___x_1065_; 
v___x_1065_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47));
v___y_967_ = v___x_1065_;
goto v___jp_966_;
}
case 19:
{
lean_object* v___x_1066_; 
v___x_1066_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48));
v___y_967_ = v___x_1066_;
goto v___jp_966_;
}
case 20:
{
lean_object* v___x_1067_; 
v___x_1067_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49));
v___y_967_ = v___x_1067_;
goto v___jp_966_;
}
case 21:
{
lean_object* v___x_1068_; 
v___x_1068_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50));
v___y_967_ = v___x_1068_;
goto v___jp_966_;
}
case 22:
{
lean_object* v___x_1069_; 
v___x_1069_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51));
v___y_967_ = v___x_1069_;
goto v___jp_966_;
}
case 23:
{
lean_object* v___x_1070_; 
v___x_1070_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52));
v___y_967_ = v___x_1070_;
goto v___jp_966_;
}
case 24:
{
lean_object* v___x_1071_; 
v___x_1071_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53));
v___y_967_ = v___x_1071_;
goto v___jp_966_;
}
case 25:
{
lean_object* v___x_1072_; 
v___x_1072_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54));
v___y_967_ = v___x_1072_;
goto v___jp_966_;
}
case 26:
{
lean_object* v___x_1073_; 
v___x_1073_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55));
v___y_967_ = v___x_1073_;
goto v___jp_966_;
}
case 27:
{
lean_object* v___x_1074_; 
v___x_1074_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56));
v___y_967_ = v___x_1074_;
goto v___jp_966_;
}
case 28:
{
lean_object* v___x_1075_; 
v___x_1075_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57));
v___y_967_ = v___x_1075_;
goto v___jp_966_;
}
case 29:
{
lean_object* v___x_1076_; 
v___x_1076_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58));
v___y_967_ = v___x_1076_;
goto v___jp_966_;
}
case 30:
{
lean_object* v___x_1077_; 
v___x_1077_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59));
v___y_967_ = v___x_1077_;
goto v___jp_966_;
}
case 31:
{
lean_object* v___x_1078_; 
v___x_1078_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60));
v___y_967_ = v___x_1078_;
goto v___jp_966_;
}
case 32:
{
lean_object* v___x_1079_; 
v___x_1079_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61));
v___y_967_ = v___x_1079_;
goto v___jp_966_;
}
case 33:
{
lean_object* v___x_1080_; 
v___x_1080_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62));
v___y_967_ = v___x_1080_;
goto v___jp_966_;
}
case 34:
{
lean_object* v___x_1081_; 
v___x_1081_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63));
v___y_967_ = v___x_1081_;
goto v___jp_966_;
}
case 35:
{
lean_object* v___x_1082_; 
v___x_1082_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64));
v___y_967_ = v___x_1082_;
goto v___jp_966_;
}
case 36:
{
lean_object* v___x_1083_; 
v___x_1083_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65));
v___y_967_ = v___x_1083_;
goto v___jp_966_;
}
case 37:
{
lean_object* v___x_1084_; 
v___x_1084_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66));
v___y_967_ = v___x_1084_;
goto v___jp_966_;
}
case 38:
{
lean_object* v___x_1085_; 
v___x_1085_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67));
v___y_967_ = v___x_1085_;
goto v___jp_966_;
}
default: 
{
lean_object* v___x_1086_; 
v___x_1086_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__68));
v___y_967_ = v___x_1086_;
goto v___jp_966_;
}
}
v___jp_763_:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v_buffer_775_; lean_object* v_buffer_776_; lean_object* v_data_777_; lean_object* v_size_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_787_; 
v___x_767_ = lean_string_to_utf8(v___y_766_);
lean_inc_ref(v___x_767_);
v___x_768_ = lean_array_push(v___y_765_, v___x_767_);
v___x_769_ = lean_byte_array_size(v___x_767_);
lean_dec_ref(v___x_767_);
v___x_770_ = lean_nat_add(v___y_764_, v___x_769_);
lean_dec(v___y_764_);
v___x_771_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_772_ = lean_array_push(v___x_768_, v___x_771_);
v___x_773_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3);
v___x_774_ = lean_nat_add(v___x_770_, v___x_773_);
lean_dec(v___x_770_);
v_buffer_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_buffer_775_, 0, v___x_772_);
lean_ctor_set(v_buffer_775_, 1, v___x_774_);
v_buffer_776_ = l_Std_Http_Headers_fold___redArg(v_headers_760_, v_buffer_775_, v___f_762_);
lean_dec_ref(v_headers_760_);
v_data_777_ = lean_ctor_get(v_buffer_776_, 0);
v_size_778_ = lean_ctor_get(v_buffer_776_, 1);
v_isSharedCheck_787_ = !lean_is_exclusive(v_buffer_776_);
if (v_isSharedCheck_787_ == 0)
{
v___x_780_ = v_buffer_776_;
v_isShared_781_ = v_isSharedCheck_787_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_size_778_);
lean_inc(v_data_777_);
lean_dec(v_buffer_776_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_787_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_782_ = lean_array_push(v_data_777_, v___x_771_);
v___x_783_ = lean_nat_add(v_size_778_, v___x_773_);
lean_dec(v_size_778_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 1, v___x_783_);
lean_ctor_set(v___x_780_, 0, v___x_782_);
v___x_785_ = v___x_780_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v___x_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
v___jp_788_:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_794_ = lean_string_to_utf8(v___y_793_);
lean_dec_ref(v___y_793_);
lean_inc_ref(v___x_794_);
v___x_795_ = lean_array_push(v___y_792_, v___x_794_);
v___x_796_ = lean_byte_array_size(v___x_794_);
lean_dec_ref(v___x_794_);
v___x_797_ = lean_nat_add(v___y_790_, v___x_796_);
lean_dec(v___y_790_);
v___x_798_ = lean_array_push(v___x_795_, v___y_789_);
v___x_799_ = lean_nat_add(v___x_797_, v___y_791_);
lean_dec(v___x_797_);
switch(v_version_758_)
{
case 0:
{
lean_object* v___x_800_; 
v___x_800_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4));
v___y_764_ = v___x_799_;
v___y_765_ = v___x_798_;
v___y_766_ = v___x_800_;
goto v___jp_763_;
}
case 1:
{
lean_object* v___x_801_; 
v___x_801_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5));
v___y_764_ = v___x_799_;
v___y_765_ = v___x_798_;
v___y_766_ = v___x_801_;
goto v___jp_763_;
}
case 2:
{
lean_object* v___x_802_; 
v___x_802_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6));
v___y_764_ = v___x_799_;
v___y_765_ = v___x_798_;
v___y_766_ = v___x_802_;
goto v___jp_763_;
}
default: 
{
lean_object* v___x_803_; 
v___x_803_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7));
v___y_764_ = v___x_799_;
v___y_765_ = v___x_798_;
v___y_766_ = v___x_803_;
goto v___jp_763_;
}
}
}
v___jp_804_:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = lean_string_append(v___y_807_, v___y_805_);
lean_dec_ref(v___y_805_);
v___x_813_ = lean_string_append(v___x_812_, v___y_811_);
lean_dec_ref(v___y_811_);
v___y_789_ = v___y_806_;
v___y_790_ = v___y_808_;
v___y_791_ = v___y_809_;
v___y_792_ = v___y_810_;
v___y_793_ = v___x_813_;
goto v___jp_788_;
}
v___jp_814_:
{
switch(lean_obj_tag(v_port_819_))
{
case 0:
{
lean_object* v___x_822_; 
v___x_822_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_805_ = v___y_821_;
v___y_806_ = v___y_815_;
v___y_807_ = v___y_816_;
v___y_808_ = v___y_817_;
v___y_809_ = v___y_818_;
v___y_810_ = v___y_820_;
v___y_811_ = v___x_822_;
goto v___jp_804_;
}
case 1:
{
lean_object* v___x_823_; 
v___x_823_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___y_805_ = v___y_821_;
v___y_806_ = v___y_815_;
v___y_807_ = v___y_816_;
v___y_808_ = v___y_817_;
v___y_809_ = v___y_818_;
v___y_810_ = v___y_820_;
v___y_811_ = v___x_823_;
goto v___jp_804_;
}
default: 
{
uint16_t v_port_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v_port_824_ = lean_ctor_get_uint16(v_port_819_, 0);
lean_dec_ref_known(v_port_819_, 0);
v___x_825_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_826_ = lean_uint16_to_nat(v_port_824_);
v___x_827_ = l_Nat_reprFast(v___x_826_);
v___x_828_ = lean_string_append(v___x_825_, v___x_827_);
lean_dec_ref(v___x_827_);
v___y_805_ = v___y_821_;
v___y_806_ = v___y_815_;
v___y_807_ = v___y_816_;
v___y_808_ = v___y_817_;
v___y_809_ = v___y_818_;
v___y_810_ = v___y_820_;
v___y_811_ = v___x_828_;
goto v___jp_804_;
}
}
}
v___jp_829_:
{
switch(lean_obj_tag(v_host_833_))
{
case 0:
{
lean_object* v_name_837_; 
v_name_837_ = lean_ctor_get(v_host_833_, 0);
lean_inc_ref(v_name_837_);
lean_dec_ref_known(v_host_833_, 1);
v___y_815_ = v___y_830_;
v___y_816_ = v___y_836_;
v___y_817_ = v___y_831_;
v___y_818_ = v___y_832_;
v_port_819_ = v_port_834_;
v___y_820_ = v___y_835_;
v___y_821_ = v_name_837_;
goto v___jp_814_;
}
case 1:
{
lean_object* v_ipv4_838_; lean_object* v___x_839_; 
v_ipv4_838_ = lean_ctor_get(v_host_833_, 0);
lean_inc_ref(v_ipv4_838_);
lean_dec_ref_known(v_host_833_, 1);
v___x_839_ = lean_uv_ntop_v4(v_ipv4_838_);
lean_dec_ref(v_ipv4_838_);
v___y_815_ = v___y_830_;
v___y_816_ = v___y_836_;
v___y_817_ = v___y_831_;
v___y_818_ = v___y_832_;
v_port_819_ = v_port_834_;
v___y_820_ = v___y_835_;
v___y_821_ = v___x_839_;
goto v___jp_814_;
}
default: 
{
lean_object* v_ipv6_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v_ipv6_840_ = lean_ctor_get(v_host_833_, 0);
lean_inc_ref(v_ipv6_840_);
lean_dec_ref_known(v_host_833_, 1);
v___x_841_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9));
v___x_842_ = lean_uv_ntop_v6(v_ipv6_840_);
lean_dec_ref(v_ipv6_840_);
v___x_843_ = lean_string_append(v___x_841_, v___x_842_);
lean_dec_ref(v___x_842_);
v___x_844_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10));
v___x_845_ = lean_string_append(v___x_843_, v___x_844_);
v___y_815_ = v___y_830_;
v___y_816_ = v___y_836_;
v___y_817_ = v___y_831_;
v___y_818_ = v___y_832_;
v_port_819_ = v_port_834_;
v___y_820_ = v___y_835_;
v___y_821_ = v___x_845_;
goto v___jp_814_;
}
}
}
v___jp_846_:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_856_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_857_ = lean_string_append(v___y_849_, v___x_856_);
v___x_858_ = lean_string_append(v___x_857_, v___y_854_);
lean_dec_ref(v___y_854_);
v___x_859_ = lean_string_append(v___x_858_, v___y_852_);
lean_dec_ref(v___y_852_);
v___x_860_ = lean_string_append(v___x_859_, v___y_851_);
lean_dec_ref(v___y_851_);
v___x_861_ = lean_string_append(v___x_860_, v___y_855_);
lean_dec_ref(v___y_855_);
v___y_789_ = v___y_847_;
v___y_790_ = v___y_848_;
v___y_791_ = v___y_850_;
v___y_792_ = v___y_853_;
v___y_793_ = v___x_861_;
goto v___jp_788_;
}
v___jp_862_:
{
lean_object* v_queryPart_872_; 
v_queryPart_872_ = l_Std_Http_URI_Query_formatOption(v___y_866_);
if (lean_obj_tag(v___y_868_) == 0)
{
lean_object* v___x_873_; 
v___x_873_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_847_ = v___y_863_;
v___y_848_ = v___y_864_;
v___y_849_ = v___y_865_;
v___y_850_ = v___y_867_;
v___y_851_ = v_queryPart_872_;
v___y_852_ = v___y_871_;
v___y_853_ = v___y_869_;
v___y_854_ = v___y_870_;
v___y_855_ = v___x_873_;
goto v___jp_846_;
}
else
{
lean_object* v_val_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v_val_874_ = lean_ctor_get(v___y_868_, 0);
lean_inc(v_val_874_);
lean_dec_ref_known(v___y_868_, 1);
v___x_875_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11));
v___x_876_ = l_Std_Http_URI_EncodedFragment_encode(v_val_874_);
lean_dec(v_val_874_);
v___x_877_ = lean_string_from_utf8_unchecked(v___x_876_);
v___x_878_ = lean_string_append(v___x_875_, v___x_877_);
lean_dec_ref(v___x_877_);
v___y_847_ = v___y_863_;
v___y_848_ = v___y_864_;
v___y_849_ = v___y_865_;
v___y_850_ = v___y_867_;
v___y_851_ = v_queryPart_872_;
v___y_852_ = v___y_871_;
v___y_853_ = v___y_869_;
v___y_854_ = v___y_870_;
v___y_855_ = v___x_878_;
goto v___jp_846_;
}
}
v___jp_879_:
{
lean_object* v_queryStr_886_; lean_object* v___x_887_; 
v_queryStr_886_ = l_Std_Http_URI_Query_formatOption(v___y_881_);
v___x_887_ = lean_string_append(v___y_885_, v_queryStr_886_);
lean_dec_ref(v_queryStr_886_);
v___y_789_ = v___y_880_;
v___y_790_ = v___y_882_;
v___y_791_ = v___y_883_;
v___y_792_ = v___y_884_;
v___y_793_ = v___x_887_;
goto v___jp_788_;
}
v___jp_888_:
{
lean_object* v_segments_898_; uint8_t v_absolute_899_; lean_object* v___x_900_; lean_object* v___x_901_; size_t v_sz_902_; size_t v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v_result_906_; 
v_segments_898_ = lean_ctor_get(v___y_896_, 0);
lean_inc_ref(v_segments_898_);
v_absolute_899_ = lean_ctor_get_uint8(v___y_896_, sizeof(void*)*1);
lean_dec_ref(v___y_896_);
v___x_900_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12));
v___x_901_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22));
v_sz_902_ = lean_array_size(v_segments_898_);
v___x_903_ = ((size_t)0ULL);
v___x_904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_901_, v___f_761_, v_sz_902_, v___x_903_, v_segments_898_);
v___x_905_ = lean_array_to_list(v___x_904_);
v_result_906_ = l_String_intercalate(v___x_900_, v___x_905_);
if (v_absolute_899_ == 0)
{
v___y_863_ = v___y_889_;
v___y_864_ = v___y_890_;
v___y_865_ = v___y_891_;
v___y_866_ = v___y_892_;
v___y_867_ = v___y_893_;
v___y_868_ = v___y_894_;
v___y_869_ = v___y_895_;
v___y_870_ = v___y_897_;
v___y_871_ = v_result_906_;
goto v___jp_862_;
}
else
{
lean_object* v___x_907_; 
v___x_907_ = lean_string_append(v___x_900_, v_result_906_);
lean_dec_ref(v_result_906_);
v___y_863_ = v___y_889_;
v___y_864_ = v___y_890_;
v___y_865_ = v___y_891_;
v___y_866_ = v___y_892_;
v___y_867_ = v___y_893_;
v___y_868_ = v___y_894_;
v___y_869_ = v___y_895_;
v___y_870_ = v___y_897_;
v___y_871_ = v___x_907_;
goto v___jp_862_;
}
}
v___jp_908_:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_921_ = lean_string_append(v___y_909_, v___y_910_);
lean_dec_ref(v___y_910_);
v___x_922_ = lean_string_append(v___x_921_, v___y_920_);
lean_dec_ref(v___y_920_);
lean_inc_ref(v___y_911_);
v___x_923_ = lean_string_append(v___y_911_, v___x_922_);
lean_dec_ref(v___x_922_);
v___y_889_ = v___y_912_;
v___y_890_ = v___y_913_;
v___y_891_ = v___y_914_;
v___y_892_ = v___y_915_;
v___y_893_ = v___y_916_;
v___y_894_ = v___y_917_;
v___y_895_ = v___y_918_;
v___y_896_ = v___y_919_;
v___y_897_ = v___x_923_;
goto v___jp_888_;
}
v___jp_924_:
{
switch(lean_obj_tag(v_port_926_))
{
case 0:
{
lean_object* v___x_937_; 
v___x_937_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_909_ = v___y_925_;
v___y_910_ = v___y_936_;
v___y_911_ = v___y_927_;
v___y_912_ = v___y_928_;
v___y_913_ = v___y_929_;
v___y_914_ = v___y_930_;
v___y_915_ = v___y_931_;
v___y_916_ = v___y_932_;
v___y_917_ = v___y_933_;
v___y_918_ = v___y_934_;
v___y_919_ = v___y_935_;
v___y_920_ = v___x_937_;
goto v___jp_908_;
}
case 1:
{
lean_object* v___x_938_; 
v___x_938_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___y_909_ = v___y_925_;
v___y_910_ = v___y_936_;
v___y_911_ = v___y_927_;
v___y_912_ = v___y_928_;
v___y_913_ = v___y_929_;
v___y_914_ = v___y_930_;
v___y_915_ = v___y_931_;
v___y_916_ = v___y_932_;
v___y_917_ = v___y_933_;
v___y_918_ = v___y_934_;
v___y_919_ = v___y_935_;
v___y_920_ = v___x_938_;
goto v___jp_908_;
}
default: 
{
uint16_t v_port_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v_port_939_ = lean_ctor_get_uint16(v_port_926_, 0);
lean_dec_ref_known(v_port_926_, 0);
v___x_940_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_941_ = lean_uint16_to_nat(v_port_939_);
v___x_942_ = l_Nat_reprFast(v___x_941_);
v___x_943_ = lean_string_append(v___x_940_, v___x_942_);
lean_dec_ref(v___x_942_);
v___y_909_ = v___y_925_;
v___y_910_ = v___y_936_;
v___y_911_ = v___y_927_;
v___y_912_ = v___y_928_;
v___y_913_ = v___y_929_;
v___y_914_ = v___y_930_;
v___y_915_ = v___y_931_;
v___y_916_ = v___y_932_;
v___y_917_ = v___y_933_;
v___y_918_ = v___y_934_;
v___y_919_ = v___y_935_;
v___y_920_ = v___x_943_;
goto v___jp_908_;
}
}
}
v___jp_944_:
{
switch(lean_obj_tag(v_host_945_))
{
case 0:
{
lean_object* v_name_957_; 
v_name_957_ = lean_ctor_get(v_host_945_, 0);
lean_inc_ref(v_name_957_);
lean_dec_ref_known(v_host_945_, 1);
v___y_925_ = v___y_956_;
v_port_926_ = v_port_946_;
v___y_927_ = v___y_947_;
v___y_928_ = v___y_948_;
v___y_929_ = v___y_949_;
v___y_930_ = v___y_950_;
v___y_931_ = v___y_951_;
v___y_932_ = v___y_952_;
v___y_933_ = v___y_953_;
v___y_934_ = v___y_954_;
v___y_935_ = v___y_955_;
v___y_936_ = v_name_957_;
goto v___jp_924_;
}
case 1:
{
lean_object* v_ipv4_958_; lean_object* v___x_959_; 
v_ipv4_958_ = lean_ctor_get(v_host_945_, 0);
lean_inc_ref(v_ipv4_958_);
lean_dec_ref_known(v_host_945_, 1);
v___x_959_ = lean_uv_ntop_v4(v_ipv4_958_);
lean_dec_ref(v_ipv4_958_);
v___y_925_ = v___y_956_;
v_port_926_ = v_port_946_;
v___y_927_ = v___y_947_;
v___y_928_ = v___y_948_;
v___y_929_ = v___y_949_;
v___y_930_ = v___y_950_;
v___y_931_ = v___y_951_;
v___y_932_ = v___y_952_;
v___y_933_ = v___y_953_;
v___y_934_ = v___y_954_;
v___y_935_ = v___y_955_;
v___y_936_ = v___x_959_;
goto v___jp_924_;
}
default: 
{
lean_object* v_ipv6_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v_ipv6_960_ = lean_ctor_get(v_host_945_, 0);
lean_inc_ref(v_ipv6_960_);
lean_dec_ref_known(v_host_945_, 1);
v___x_961_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9));
v___x_962_ = lean_uv_ntop_v6(v_ipv6_960_);
lean_dec_ref(v_ipv6_960_);
v___x_963_ = lean_string_append(v___x_961_, v___x_962_);
lean_dec_ref(v___x_962_);
v___x_964_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10));
v___x_965_ = lean_string_append(v___x_963_, v___x_964_);
v___y_925_ = v___y_956_;
v_port_926_ = v_port_946_;
v___y_927_ = v___y_947_;
v___y_928_ = v___y_948_;
v___y_929_ = v___y_949_;
v___y_930_ = v___y_950_;
v___y_931_ = v___y_951_;
v___y_932_ = v___y_952_;
v___y_933_ = v___y_953_;
v___y_934_ = v___y_954_;
v___y_935_ = v___y_955_;
v___y_936_ = v___x_965_;
goto v___jp_924_;
}
}
}
v___jp_966_:
{
lean_object* v_data_968_; lean_object* v_size_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v_data_968_ = lean_ctor_get(v_buffer_755_, 0);
lean_inc_ref(v_data_968_);
v_size_969_ = lean_ctor_get(v_buffer_755_, 1);
lean_inc(v_size_969_);
lean_dec_ref(v_buffer_755_);
v___x_970_ = lean_string_to_utf8(v___y_967_);
lean_inc_ref(v___x_970_);
v___x_971_ = lean_array_push(v_data_968_, v___x_970_);
v___x_972_ = lean_byte_array_size(v___x_970_);
lean_dec_ref(v___x_970_);
v___x_973_ = lean_nat_add(v_size_969_, v___x_972_);
lean_dec(v_size_969_);
v___x_974_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24);
v___x_975_ = lean_array_push(v___x_971_, v___x_974_);
v___x_976_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25);
v___x_977_ = lean_nat_add(v___x_973_, v___x_976_);
lean_dec(v___x_973_);
switch(lean_obj_tag(v_uri_759_))
{
case 0:
{
lean_object* v_path_978_; lean_object* v_query_979_; lean_object* v_segments_980_; uint8_t v_absolute_981_; lean_object* v___x_982_; lean_object* v___x_983_; size_t v_sz_984_; size_t v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v_result_988_; 
v_path_978_ = lean_ctor_get(v_uri_759_, 0);
lean_inc_ref(v_path_978_);
v_query_979_ = lean_ctor_get(v_uri_759_, 1);
lean_inc(v_query_979_);
lean_dec_ref_known(v_uri_759_, 2);
v_segments_980_ = lean_ctor_get(v_path_978_, 0);
lean_inc_ref(v_segments_980_);
v_absolute_981_ = lean_ctor_get_uint8(v_path_978_, sizeof(void*)*1);
lean_dec_ref(v_path_978_);
v___x_982_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12));
v___x_983_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22));
v_sz_984_ = lean_array_size(v_segments_980_);
v___x_985_ = ((size_t)0ULL);
v___x_986_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_983_, v___f_761_, v_sz_984_, v___x_985_, v_segments_980_);
v___x_987_ = lean_array_to_list(v___x_986_);
v_result_988_ = l_String_intercalate(v___x_982_, v___x_987_);
if (v_absolute_981_ == 0)
{
v___y_880_ = v___x_974_;
v___y_881_ = v_query_979_;
v___y_882_ = v___x_977_;
v___y_883_ = v___x_976_;
v___y_884_ = v___x_975_;
v___y_885_ = v_result_988_;
goto v___jp_879_;
}
else
{
lean_object* v___x_989_; 
v___x_989_ = lean_string_append(v___x_982_, v_result_988_);
lean_dec_ref(v_result_988_);
v___y_880_ = v___x_974_;
v___y_881_ = v_query_979_;
v___y_882_ = v___x_977_;
v___y_883_ = v___x_976_;
v___y_884_ = v___x_975_;
v___y_885_ = v___x_989_;
goto v___jp_879_;
}
}
case 1:
{
lean_object* v_uri_990_; lean_object* v_authority_991_; 
v_uri_990_ = lean_ctor_get(v_uri_759_, 0);
lean_inc_ref(v_uri_990_);
lean_dec_ref_known(v_uri_759_, 1);
v_authority_991_ = lean_ctor_get(v_uri_990_, 1);
if (lean_obj_tag(v_authority_991_) == 0)
{
lean_object* v_scheme_992_; lean_object* v_path_993_; lean_object* v_query_994_; lean_object* v_fragment_995_; lean_object* v___x_996_; 
v_scheme_992_ = lean_ctor_get(v_uri_990_, 0);
lean_inc_ref(v_scheme_992_);
v_path_993_ = lean_ctor_get(v_uri_990_, 2);
lean_inc_ref(v_path_993_);
v_query_994_ = lean_ctor_get(v_uri_990_, 3);
lean_inc(v_query_994_);
v_fragment_995_ = lean_ctor_get(v_uri_990_, 4);
lean_inc(v_fragment_995_);
lean_dec_ref(v_uri_990_);
v___x_996_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_889_ = v___x_974_;
v___y_890_ = v___x_977_;
v___y_891_ = v_scheme_992_;
v___y_892_ = v_query_994_;
v___y_893_ = v___x_976_;
v___y_894_ = v_fragment_995_;
v___y_895_ = v___x_975_;
v___y_896_ = v_path_993_;
v___y_897_ = v___x_996_;
goto v___jp_888_;
}
else
{
lean_object* v_val_997_; lean_object* v_scheme_998_; lean_object* v_path_999_; lean_object* v_query_1000_; lean_object* v_fragment_1001_; lean_object* v_userInfo_1002_; lean_object* v_host_1003_; lean_object* v_port_1004_; lean_object* v___x_1005_; 
v_val_997_ = lean_ctor_get(v_authority_991_, 0);
lean_inc(v_val_997_);
v_scheme_998_ = lean_ctor_get(v_uri_990_, 0);
lean_inc_ref(v_scheme_998_);
v_path_999_ = lean_ctor_get(v_uri_990_, 2);
lean_inc_ref(v_path_999_);
v_query_1000_ = lean_ctor_get(v_uri_990_, 3);
lean_inc(v_query_1000_);
v_fragment_1001_ = lean_ctor_get(v_uri_990_, 4);
lean_inc(v_fragment_1001_);
lean_dec_ref(v_uri_990_);
v_userInfo_1002_ = lean_ctor_get(v_val_997_, 0);
lean_inc(v_userInfo_1002_);
v_host_1003_ = lean_ctor_get(v_val_997_, 1);
lean_inc_ref(v_host_1003_);
v_port_1004_ = lean_ctor_get(v_val_997_, 2);
lean_inc(v_port_1004_);
lean_dec(v_val_997_);
v___x_1005_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26));
if (lean_obj_tag(v_userInfo_1002_) == 0)
{
lean_object* v___x_1006_; 
v___x_1006_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v_host_945_ = v_host_1003_;
v_port_946_ = v_port_1004_;
v___y_947_ = v___x_1005_;
v___y_948_ = v___x_974_;
v___y_949_ = v___x_977_;
v___y_950_ = v_scheme_998_;
v___y_951_ = v_query_1000_;
v___y_952_ = v___x_976_;
v___y_953_ = v_fragment_1001_;
v___y_954_ = v___x_975_;
v___y_955_ = v_path_999_;
v___y_956_ = v___x_1006_;
goto v___jp_944_;
}
else
{
lean_object* v_val_1007_; lean_object* v_password_1008_; 
v_val_1007_ = lean_ctor_get(v_userInfo_1002_, 0);
lean_inc(v_val_1007_);
lean_dec_ref_known(v_userInfo_1002_, 1);
v_password_1008_ = lean_ctor_get(v_val_1007_, 1);
if (lean_obj_tag(v_password_1008_) == 0)
{
lean_object* v_username_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_username_1009_ = lean_ctor_get(v_val_1007_, 0);
lean_inc_ref(v_username_1009_);
lean_dec(v_val_1007_);
v___x_1010_ = lean_string_from_utf8_unchecked(v_username_1009_);
v___x_1011_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27));
v___x_1012_ = lean_string_append(v___x_1010_, v___x_1011_);
v_host_945_ = v_host_1003_;
v_port_946_ = v_port_1004_;
v___y_947_ = v___x_1005_;
v___y_948_ = v___x_974_;
v___y_949_ = v___x_977_;
v___y_950_ = v_scheme_998_;
v___y_951_ = v_query_1000_;
v___y_952_ = v___x_976_;
v___y_953_ = v_fragment_1001_;
v___y_954_ = v___x_975_;
v___y_955_ = v_path_999_;
v___y_956_ = v___x_1012_;
goto v___jp_944_;
}
else
{
lean_object* v_username_1013_; lean_object* v_val_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
lean_inc_ref(v_password_1008_);
v_username_1013_ = lean_ctor_get(v_val_1007_, 0);
lean_inc_ref(v_username_1013_);
lean_dec(v_val_1007_);
v_val_1014_ = lean_ctor_get(v_password_1008_, 0);
lean_inc(v_val_1014_);
lean_dec_ref_known(v_password_1008_, 1);
v___x_1015_ = lean_string_from_utf8_unchecked(v_username_1013_);
v___x_1016_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_1017_ = lean_string_append(v___x_1015_, v___x_1016_);
v___x_1018_ = lean_string_from_utf8_unchecked(v_val_1014_);
v___x_1019_ = lean_string_append(v___x_1017_, v___x_1018_);
lean_dec_ref(v___x_1018_);
v___x_1020_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27));
v___x_1021_ = lean_string_append(v___x_1019_, v___x_1020_);
v_host_945_ = v_host_1003_;
v_port_946_ = v_port_1004_;
v___y_947_ = v___x_1005_;
v___y_948_ = v___x_974_;
v___y_949_ = v___x_977_;
v___y_950_ = v_scheme_998_;
v___y_951_ = v_query_1000_;
v___y_952_ = v___x_976_;
v___y_953_ = v_fragment_1001_;
v___y_954_ = v___x_975_;
v___y_955_ = v_path_999_;
v___y_956_ = v___x_1021_;
goto v___jp_944_;
}
}
}
}
case 2:
{
lean_object* v_authority_1022_; lean_object* v_userInfo_1023_; 
v_authority_1022_ = lean_ctor_get(v_uri_759_, 0);
lean_inc_ref(v_authority_1022_);
lean_dec_ref_known(v_uri_759_, 1);
v_userInfo_1023_ = lean_ctor_get(v_authority_1022_, 0);
if (lean_obj_tag(v_userInfo_1023_) == 0)
{
lean_object* v_host_1024_; lean_object* v_port_1025_; lean_object* v___x_1026_; 
v_host_1024_ = lean_ctor_get(v_authority_1022_, 1);
lean_inc_ref(v_host_1024_);
v_port_1025_ = lean_ctor_get(v_authority_1022_, 2);
lean_inc(v_port_1025_);
lean_dec_ref(v_authority_1022_);
v___x_1026_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_830_ = v___x_974_;
v___y_831_ = v___x_977_;
v___y_832_ = v___x_976_;
v_host_833_ = v_host_1024_;
v_port_834_ = v_port_1025_;
v___y_835_ = v___x_975_;
v___y_836_ = v___x_1026_;
goto v___jp_829_;
}
else
{
lean_object* v_val_1027_; lean_object* v_password_1028_; 
v_val_1027_ = lean_ctor_get(v_userInfo_1023_, 0);
lean_inc(v_val_1027_);
v_password_1028_ = lean_ctor_get(v_val_1027_, 1);
if (lean_obj_tag(v_password_1028_) == 0)
{
lean_object* v_host_1029_; lean_object* v_port_1030_; lean_object* v_username_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v_host_1029_ = lean_ctor_get(v_authority_1022_, 1);
lean_inc_ref(v_host_1029_);
v_port_1030_ = lean_ctor_get(v_authority_1022_, 2);
lean_inc(v_port_1030_);
lean_dec_ref(v_authority_1022_);
v_username_1031_ = lean_ctor_get(v_val_1027_, 0);
lean_inc_ref(v_username_1031_);
lean_dec(v_val_1027_);
v___x_1032_ = lean_string_from_utf8_unchecked(v_username_1031_);
v___x_1033_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27));
v___x_1034_ = lean_string_append(v___x_1032_, v___x_1033_);
v___y_830_ = v___x_974_;
v___y_831_ = v___x_977_;
v___y_832_ = v___x_976_;
v_host_833_ = v_host_1029_;
v_port_834_ = v_port_1030_;
v___y_835_ = v___x_975_;
v___y_836_ = v___x_1034_;
goto v___jp_829_;
}
else
{
lean_object* v_host_1035_; lean_object* v_port_1036_; lean_object* v_username_1037_; lean_object* v_val_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
lean_inc_ref(v_password_1028_);
v_host_1035_ = lean_ctor_get(v_authority_1022_, 1);
lean_inc_ref(v_host_1035_);
v_port_1036_ = lean_ctor_get(v_authority_1022_, 2);
lean_inc(v_port_1036_);
lean_dec_ref(v_authority_1022_);
v_username_1037_ = lean_ctor_get(v_val_1027_, 0);
lean_inc_ref(v_username_1037_);
lean_dec(v_val_1027_);
v_val_1038_ = lean_ctor_get(v_password_1028_, 0);
lean_inc(v_val_1038_);
lean_dec_ref_known(v_password_1028_, 1);
v___x_1039_ = lean_string_from_utf8_unchecked(v_username_1037_);
v___x_1040_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_1041_ = lean_string_append(v___x_1039_, v___x_1040_);
v___x_1042_ = lean_string_from_utf8_unchecked(v_val_1038_);
v___x_1043_ = lean_string_append(v___x_1041_, v___x_1042_);
lean_dec_ref(v___x_1042_);
v___x_1044_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27));
v___x_1045_ = lean_string_append(v___x_1043_, v___x_1044_);
v___y_830_ = v___x_974_;
v___y_831_ = v___x_977_;
v___y_832_ = v___x_976_;
v_host_833_ = v_host_1035_;
v_port_834_ = v_port_1036_;
v___y_835_ = v___x_975_;
v___y_836_ = v___x_1045_;
goto v___jp_829_;
}
}
}
default: 
{
lean_object* v___x_1046_; 
v___x_1046_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28));
v___y_789_ = v___x_974_;
v___y_790_ = v___x_977_;
v___y_791_ = v___x_976_;
v___y_792_ = v___x_975_;
v___y_793_ = v___x_1046_;
goto v___jp_788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(lean_object* v_buffer_1087_, lean_object* v_r_1088_){
_start:
{
lean_object* v_status_1089_; uint8_t v_version_1090_; lean_object* v_headers_1091_; lean_object* v___f_1092_; lean_object* v___y_1094_; 
v_status_1089_ = lean_ctor_get(v_r_1088_, 0);
v_version_1090_ = lean_ctor_get_uint8(v_r_1088_, sizeof(void*)*2);
v_headers_1091_ = lean_ctor_get(v_r_1088_, 1);
v___f_1092_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1));
switch(v_version_1090_)
{
case 0:
{
lean_object* v___x_1144_; 
v___x_1144_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4));
v___y_1094_ = v___x_1144_;
goto v___jp_1093_;
}
case 1:
{
lean_object* v___x_1145_; 
v___x_1145_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5));
v___y_1094_ = v___x_1145_;
goto v___jp_1093_;
}
case 2:
{
lean_object* v___x_1146_; 
v___x_1146_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6));
v___y_1094_ = v___x_1146_;
goto v___jp_1093_;
}
default: 
{
lean_object* v___x_1147_; 
v___x_1147_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7));
v___y_1094_ = v___x_1147_;
goto v___jp_1093_;
}
}
v___jp_1093_:
{
lean_object* v_data_1095_; lean_object* v_size_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1143_; 
v_data_1095_ = lean_ctor_get(v_buffer_1087_, 0);
v_size_1096_ = lean_ctor_get(v_buffer_1087_, 1);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_buffer_1087_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1098_ = v_buffer_1087_;
v_isShared_1099_ = v_isSharedCheck_1143_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_size_1096_);
lean_inc(v_data_1095_);
lean_dec(v_buffer_1087_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1143_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; uint16_t v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v_buffer_1129_; 
v___x_1100_ = lean_string_to_utf8(v___y_1094_);
lean_inc_ref(v___x_1100_);
v___x_1101_ = lean_array_push(v_data_1095_, v___x_1100_);
v___x_1102_ = lean_byte_array_size(v___x_1100_);
lean_dec_ref(v___x_1100_);
v___x_1103_ = lean_nat_add(v_size_1096_, v___x_1102_);
lean_dec(v_size_1096_);
v___x_1104_ = lean_unsigned_to_nat(1u);
v___x_1105_ = lean_mk_empty_array_with_capacity(v___x_1104_);
lean_dec_ref(v___x_1105_);
v___x_1106_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24);
v___x_1107_ = lean_array_push(v___x_1101_, v___x_1106_);
v___x_1108_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25);
v___x_1109_ = lean_nat_add(v___x_1103_, v___x_1108_);
lean_dec(v___x_1103_);
v___x_1110_ = l_Std_Http_Status_toCode(v_status_1089_);
v___x_1111_ = lean_uint16_to_nat(v___x_1110_);
v___x_1112_ = l_Nat_reprFast(v___x_1111_);
v___x_1113_ = lean_string_to_utf8(v___x_1112_);
lean_dec_ref(v___x_1112_);
lean_inc_ref(v___x_1113_);
v___x_1114_ = lean_array_push(v___x_1107_, v___x_1113_);
v___x_1115_ = lean_byte_array_size(v___x_1113_);
lean_dec_ref(v___x_1113_);
v___x_1116_ = lean_nat_add(v___x_1109_, v___x_1115_);
lean_dec(v___x_1109_);
v___x_1117_ = lean_array_push(v___x_1114_, v___x_1106_);
v___x_1118_ = lean_nat_add(v___x_1116_, v___x_1108_);
lean_dec(v___x_1116_);
v___x_1119_ = l_Std_Http_Status_reasonPhrase(v_status_1089_);
v___x_1120_ = lean_string_to_utf8(v___x_1119_);
lean_dec_ref(v___x_1119_);
lean_inc_ref(v___x_1120_);
v___x_1121_ = lean_array_push(v___x_1117_, v___x_1120_);
v___x_1122_ = lean_byte_array_size(v___x_1120_);
lean_dec_ref(v___x_1120_);
v___x_1123_ = lean_nat_add(v___x_1118_, v___x_1122_);
lean_dec(v___x_1118_);
v___x_1124_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_1125_ = lean_array_push(v___x_1121_, v___x_1124_);
v___x_1126_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3);
v___x_1127_ = lean_nat_add(v___x_1123_, v___x_1126_);
lean_dec(v___x_1123_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 1, v___x_1127_);
lean_ctor_set(v___x_1098_, 0, v___x_1125_);
v_buffer_1129_ = v___x_1098_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1125_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v___x_1127_);
v_buffer_1129_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v_buffer_1130_; lean_object* v_data_1131_; lean_object* v_size_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1141_; 
v_buffer_1130_ = l_Std_Http_Headers_fold___redArg(v_headers_1091_, v_buffer_1129_, v___f_1092_);
v_data_1131_ = lean_ctor_get(v_buffer_1130_, 0);
v_size_1132_ = lean_ctor_get(v_buffer_1130_, 1);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_buffer_1130_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1134_ = v_buffer_1130_;
v_isShared_1135_ = v_isSharedCheck_1141_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_size_1132_);
lean_inc(v_data_1131_);
lean_dec(v_buffer_1130_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1141_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1136_ = lean_array_push(v_data_1131_, v___x_1124_);
v___x_1137_ = lean_nat_add(v_size_1132_, v___x_1126_);
lean_dec(v_size_1132_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 1, v___x_1137_);
lean_ctor_set(v___x_1134_, 0, v___x_1136_);
v___x_1139_ = v___x_1134_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___boxed(lean_object* v_buffer_1148_, lean_object* v_r_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(v_buffer_1148_, v_r_1149_);
lean_dec_ref(v_r_1149_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head(uint8_t v_dir_1153_){
_start:
{
if (v_dir_1153_ == 0)
{
lean_object* v___x_1154_; 
v___x_1154_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___closed__0));
return v___x_1154_;
}
else
{
lean_object* v___x_1155_; 
v___x_1155_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___closed__1));
return v___x_1155_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___boxed(lean_object* v_dir_1156_){
_start:
{
uint8_t v_dir_boxed_1157_; lean_object* v_res_1158_; 
v_dir_boxed_1157_ = lean_unbox(v_dir_1156_);
v_res_1158_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v_dir_boxed_1157_);
return v_res_1158_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0(void){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; uint8_t v___x_1162_; lean_object* v___x_1163_; 
v___x_1159_ = l_Std_Http_Headers_empty;
v___x_1160_ = lean_box(3);
v___x_1161_ = 1;
v___x_1162_ = 8;
v___x_1163_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1163_, 0, v___x_1160_);
lean_ctor_set(v___x_1163_, 1, v___x_1159_);
lean_ctor_set_uint8(v___x_1163_, sizeof(void*)*2, v___x_1162_);
lean_ctor_set_uint8(v___x_1163_, sizeof(void*)*2 + 1, v___x_1161_);
return v___x_1163_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1(void){
_start:
{
lean_object* v___x_1164_; uint8_t v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1164_ = l_Std_Http_Headers_empty;
v___x_1165_ = 1;
v___x_1166_ = lean_box(4);
v___x_1167_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
lean_ctor_set(v___x_1167_, 1, v___x_1164_);
lean_ctor_set_uint8(v___x_1167_, sizeof(void*)*2, v___x_1165_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead(uint8_t v_dir_1168_){
_start:
{
if (v_dir_1168_ == 0)
{
lean_object* v___x_1169_; 
v___x_1169_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0, &l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0_once, _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0);
return v___x_1169_;
}
else
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1, &l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1_once, _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1);
return v___x_1170_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead___boxed(lean_object* v_dir_1171_){
_start:
{
uint8_t v_dir_boxed_1172_; lean_object* v_res_1173_; 
v_dir_boxed_1172_ = lean_unbox(v_dir_1171_);
v_res_1173_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v_dir_boxed_1172_);
return v_res_1173_;
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
