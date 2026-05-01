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
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Http_Response_instReprHead_repr___redArg(lean_object*);
lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed(lean_object*);
lean_object* l_Std_Http_Request_instReprHead_repr___redArg(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Std_Http_Headers_empty;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* l_String_Slice_splitToSubslice___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_URI_Query_formatQueryParam(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
lean_object* lean_byte_array_mk(lean_object*);
uint16_t l_Std_Http_Status_toCode(lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Std_Http_Status_reasonPhrase(lean_object*);
lean_object* l_Std_Http_Headers_fold___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Std_Http_URI_EncodedFragment_encode(lean_object*);
lean_object* lean_uv_ntop_v4(lean_object*);
lean_object* lean_uv_ntop_v6(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
uint8_t l_Std_Http_instBEqVersion_beq(uint8_t, uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_connection;
uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__0_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__1_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__2 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__2_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__3 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__3_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__4;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___boxed__const__1;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__0_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3;
static lean_once_cell_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.0"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.1"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/2.0"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/3.0"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "&"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__13 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__13_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__17 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__17_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__18 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__18_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__19 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__19_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__20 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__20_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__21 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__21_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16_value),((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__17_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23_value),((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__18_value),((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__19_value),((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__20_value),((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__21_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_value),((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26;
static lean_once_cell_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27;
static lean_once_cell_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "//"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ACL"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "BASELINE-CONTROL"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "BIND"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CHECKIN"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CHECKOUT"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CONNECT"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "COPY"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "DELETE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "GET"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "LABEL"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LINK"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LOCK"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MERGE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKACTIVITY"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKCALENDAR"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MKCOL"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "MKREDIRECTREF"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MKWORKSPACE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "MOVE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "OPTIONS"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ORDERPATCH"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PATCH"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "POST"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PRI"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "PROPFIND"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PROPPATCH"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PUT"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "QUERY"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REBIND"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REPORT"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "SEARCH"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "TRACE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNBIND"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "UNCHECKOUT"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLINK"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLOCK"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__68 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__68_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UPDATE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__69 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__69_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "UPDATEREDIRECTREF"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__70 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__70_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "VERSION-CONTROL"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__71 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__71_value;
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_toCtorIdx(uint8_t v_x_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Std_Http_Protocol_H1_Direction_ctorIdx(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_toCtorIdx___boxed(lean_object* v_x_9_){
_start:
{
uint8_t v_x_4__boxed_10_; lean_object* v_res_11_; 
v_x_4__boxed_10_ = lean_unbox(v_x_9_);
v_res_11_ = l_Std_Http_Protocol_H1_Direction_toCtorIdx(v_x_4__boxed_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_ctorElim___redArg(lean_object* v_k_12_){
_start:
{
lean_inc(v_k_12_);
return v_k_12_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_ctorElim___redArg___boxed(lean_object* v_k_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_Http_Protocol_H1_Direction_ctorElim___redArg(v_k_13_);
lean_dec(v_k_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, uint8_t v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_inc(v_k_19_);
return v_k_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_ctorElim___boxed(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
uint8_t v_t_boxed_25_; lean_object* v_res_26_; 
v_t_boxed_25_ = lean_unbox(v_t_22_);
v_res_26_ = l_Std_Http_Protocol_H1_Direction_ctorElim(v_motive_20_, v_ctorIdx_21_, v_t_boxed_25_, v_h_23_, v_k_24_);
lean_dec(v_k_24_);
lean_dec(v_ctorIdx_21_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_receiving_elim___redArg(lean_object* v_receiving_27_){
_start:
{
lean_inc(v_receiving_27_);
return v_receiving_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_receiving_elim___redArg___boxed(lean_object* v_receiving_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Std_Http_Protocol_H1_Direction_receiving_elim___redArg(v_receiving_28_);
lean_dec(v_receiving_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_receiving_elim(lean_object* v_motive_30_, uint8_t v_t_31_, lean_object* v_h_32_, lean_object* v_receiving_33_){
_start:
{
lean_inc(v_receiving_33_);
return v_receiving_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_receiving_elim___boxed(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_receiving_37_){
_start:
{
uint8_t v_t_boxed_38_; lean_object* v_res_39_; 
v_t_boxed_38_ = lean_unbox(v_t_35_);
v_res_39_ = l_Std_Http_Protocol_H1_Direction_receiving_elim(v_motive_34_, v_t_boxed_38_, v_h_36_, v_receiving_37_);
lean_dec(v_receiving_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_sending_elim___redArg(lean_object* v_sending_40_){
_start:
{
lean_inc(v_sending_40_);
return v_sending_40_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_sending_elim___redArg___boxed(lean_object* v_sending_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Std_Http_Protocol_H1_Direction_sending_elim___redArg(v_sending_41_);
lean_dec(v_sending_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_sending_elim(lean_object* v_motive_43_, uint8_t v_t_44_, lean_object* v_h_45_, lean_object* v_sending_46_){
_start:
{
lean_inc(v_sending_46_);
return v_sending_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_sending_elim___boxed(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_sending_50_){
_start:
{
uint8_t v_t_boxed_51_; lean_object* v_res_52_; 
v_t_boxed_51_ = lean_unbox(v_t_48_);
v_res_52_ = l_Std_Http_Protocol_H1_Direction_sending_elim(v_motive_47_, v_t_boxed_51_, v_h_49_, v_sending_50_);
lean_dec(v_sending_50_);
return v_res_52_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_instBEqDirection_beq(uint8_t v_x_53_, uint8_t v_y_54_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_55_ = l_Std_Http_Protocol_H1_Direction_ctorIdx(v_x_53_);
v___x_56_ = l_Std_Http_Protocol_H1_Direction_ctorIdx(v_y_54_);
v___x_57_ = lean_nat_dec_eq(v___x_55_, v___x_56_);
lean_dec(v___x_56_);
lean_dec(v___x_55_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instBEqDirection_beq___boxed(lean_object* v_x_58_, lean_object* v_y_59_){
_start:
{
uint8_t v_x_17__boxed_60_; uint8_t v_y_18__boxed_61_; uint8_t v_res_62_; lean_object* v_r_63_; 
v_x_17__boxed_60_ = lean_unbox(v_x_58_);
v_y_18__boxed_61_ = lean_unbox(v_y_59_);
v_res_62_ = l_Std_Http_Protocol_H1_instBEqDirection_beq(v_x_17__boxed_60_, v_y_18__boxed_61_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Direction_swap(uint8_t v_x_66_){
_start:
{
if (v_x_66_ == 0)
{
uint8_t v___x_67_; 
v___x_67_ = 1;
return v___x_67_;
}
else
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Direction_swap___boxed(lean_object* v_x_69_){
_start:
{
uint8_t v_x_18__boxed_70_; uint8_t v_res_71_; lean_object* v_r_72_; 
v_x_18__boxed_70_ = lean_unbox(v_x_69_);
v_res_71_ = l_Std_Http_Protocol_H1_Direction_swap(v_x_18__boxed_70_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_headers(uint8_t v_dir_73_, lean_object* v_m_74_){
_start:
{
lean_object* v_headers_75_; 
v_headers_75_ = lean_ctor_get(v_m_74_, 1);
lean_inc_ref(v_headers_75_);
return v_headers_75_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_headers___boxed(lean_object* v_dir_76_, lean_object* v_m_77_){
_start:
{
uint8_t v_dir_boxed_78_; lean_object* v_res_79_; 
v_dir_boxed_78_ = lean_unbox(v_dir_76_);
v_res_79_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_boxed_78_, v_m_77_);
lean_dec(v_m_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_setHeaders(uint8_t v_dir_80_, lean_object* v_m_81_, lean_object* v_headers_82_){
_start:
{
if (v_dir_80_ == 0)
{
uint8_t v_method_83_; uint8_t v_version_84_; lean_object* v_uri_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_92_; 
v_method_83_ = lean_ctor_get_uint8(v_m_81_, sizeof(void*)*2);
v_version_84_ = lean_ctor_get_uint8(v_m_81_, sizeof(void*)*2 + 1);
v_uri_85_ = lean_ctor_get(v_m_81_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v_m_81_);
if (v_isSharedCheck_92_ == 0)
{
lean_object* v_unused_93_; 
v_unused_93_ = lean_ctor_get(v_m_81_, 1);
lean_dec(v_unused_93_);
v___x_87_ = v_m_81_;
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_uri_85_);
lean_dec(v_m_81_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_90_; 
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 1, v_headers_82_);
v___x_90_ = v___x_87_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_uri_85_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v_headers_82_);
lean_ctor_set_uint8(v_reuseFailAlloc_91_, sizeof(void*)*2, v_method_83_);
lean_ctor_set_uint8(v_reuseFailAlloc_91_, sizeof(void*)*2 + 1, v_version_84_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
else
{
lean_object* v_status_94_; uint8_t v_version_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_102_; 
v_status_94_ = lean_ctor_get(v_m_81_, 0);
v_version_95_ = lean_ctor_get_uint8(v_m_81_, sizeof(void*)*2);
v_isSharedCheck_102_ = !lean_is_exclusive(v_m_81_);
if (v_isSharedCheck_102_ == 0)
{
lean_object* v_unused_103_; 
v_unused_103_ = lean_ctor_get(v_m_81_, 1);
lean_dec(v_unused_103_);
v___x_97_ = v_m_81_;
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_status_94_);
lean_dec(v_m_81_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 1, v_headers_82_);
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_status_94_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_headers_82_);
lean_ctor_set_uint8(v_reuseFailAlloc_101_, sizeof(void*)*2, v_version_95_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_setHeaders___boxed(lean_object* v_dir_104_, lean_object* v_m_105_, lean_object* v_headers_106_){
_start:
{
uint8_t v_dir_boxed_107_; lean_object* v_res_108_; 
v_dir_boxed_107_ = lean_unbox(v_dir_104_);
v_res_108_ = l_Std_Http_Protocol_H1_Message_Head_setHeaders(v_dir_boxed_107_, v_m_105_, v_headers_106_);
return v_res_108_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Message_Head_version(uint8_t v_dir_109_, lean_object* v_m_110_){
_start:
{
if (v_dir_109_ == 0)
{
uint8_t v_version_111_; 
v_version_111_ = lean_ctor_get_uint8(v_m_110_, sizeof(void*)*2 + 1);
return v_version_111_;
}
else
{
uint8_t v_version_112_; 
v_version_112_ = lean_ctor_get_uint8(v_m_110_, sizeof(void*)*2);
return v_version_112_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_version___boxed(lean_object* v_dir_113_, lean_object* v_m_114_){
_start:
{
uint8_t v_dir_boxed_115_; uint8_t v_res_116_; lean_object* v_r_117_; 
v_dir_boxed_115_ = lean_unbox(v_dir_113_);
v_res_116_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_boxed_115_, v_m_114_);
lean_dec(v_m_114_);
v_r_117_ = lean_box(v_res_116_);
return v_r_117_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(lean_object* v_a_118_, lean_object* v_x_119_){
_start:
{
lean_object* v_key_120_; lean_object* v_value_121_; lean_object* v_tail_122_; uint8_t v___x_123_; 
v_key_120_ = lean_ctor_get(v_x_119_, 0);
v_value_121_ = lean_ctor_get(v_x_119_, 1);
v_tail_122_ = lean_ctor_get(v_x_119_, 2);
v___x_123_ = lean_string_dec_eq(v_key_120_, v_a_118_);
if (v___x_123_ == 0)
{
v_x_119_ = v_tail_122_;
goto _start;
}
else
{
lean_inc(v_value_121_);
return v_value_121_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg___boxed(lean_object* v_a_125_, lean_object* v_x_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_a_125_, v_x_126_);
lean_dec(v_x_126_);
lean_dec_ref(v_a_125_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(lean_object* v_m_128_, lean_object* v_a_129_){
_start:
{
lean_object* v_buckets_130_; lean_object* v___x_131_; uint64_t v___x_132_; uint64_t v___x_133_; uint64_t v___x_134_; uint64_t v_fold_135_; uint64_t v___x_136_; uint64_t v___x_137_; uint64_t v___x_138_; size_t v___x_139_; size_t v___x_140_; size_t v___x_141_; size_t v___x_142_; size_t v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v_buckets_130_ = lean_ctor_get(v_m_128_, 1);
v___x_131_ = lean_array_get_size(v_buckets_130_);
v___x_132_ = lean_string_hash(v_a_129_);
v___x_133_ = 32ULL;
v___x_134_ = lean_uint64_shift_right(v___x_132_, v___x_133_);
v_fold_135_ = lean_uint64_xor(v___x_132_, v___x_134_);
v___x_136_ = 16ULL;
v___x_137_ = lean_uint64_shift_right(v_fold_135_, v___x_136_);
v___x_138_ = lean_uint64_xor(v_fold_135_, v___x_137_);
v___x_139_ = lean_uint64_to_usize(v___x_138_);
v___x_140_ = lean_usize_of_nat(v___x_131_);
v___x_141_ = ((size_t)1ULL);
v___x_142_ = lean_usize_sub(v___x_140_, v___x_141_);
v___x_143_ = lean_usize_land(v___x_139_, v___x_142_);
v___x_144_ = lean_array_uget_borrowed(v_buckets_130_, v___x_143_);
v___x_145_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_a_129_, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg___boxed(lean_object* v_m_146_, lean_object* v_a_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_m_146_, v_a_147_);
lean_dec_ref(v_a_147_);
lean_dec_ref(v_m_146_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(lean_object* v___x_149_, lean_object* v___x_150_, lean_object* v_i_151_, lean_object* v_j_152_, lean_object* v_bs_153_){
_start:
{
lean_object* v_zero_154_; uint8_t v_isZero_155_; 
v_zero_154_ = lean_unsigned_to_nat(0u);
v_isZero_155_ = lean_nat_dec_eq(v_i_151_, v_zero_154_);
if (v_isZero_155_ == 1)
{
lean_dec(v_j_152_);
lean_dec(v_i_151_);
return v_bs_153_;
}
else
{
lean_object* v_entries_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v_snd_159_; lean_object* v_one_160_; lean_object* v_n_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_entries_156_ = lean_ctor_get(v___x_149_, 0);
v___x_157_ = lean_array_fget_borrowed(v___x_150_, v_j_152_);
v___x_158_ = lean_array_fget_borrowed(v_entries_156_, v___x_157_);
v_snd_159_ = lean_ctor_get(v___x_158_, 1);
v_one_160_ = lean_unsigned_to_nat(1u);
v_n_161_ = lean_nat_sub(v_i_151_, v_one_160_);
lean_dec(v_i_151_);
v___x_162_ = lean_nat_add(v_j_152_, v_one_160_);
lean_dec(v_j_152_);
lean_inc(v_snd_159_);
v___x_163_ = lean_array_push(v_bs_153_, v_snd_159_);
v_i_151_ = v_n_161_;
v_j_152_ = v___x_162_;
v_bs_153_ = v___x_163_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg___boxed(lean_object* v___x_165_, lean_object* v___x_166_, lean_object* v_i_167_, lean_object* v_j_168_, lean_object* v_bs_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_165_, v___x_166_, v_i_167_, v_j_168_, v_bs_169_);
lean_dec_ref(v___x_166_);
lean_dec_ref(v___x_165_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize(uint8_t v_dir_179_, lean_object* v_message_180_, uint8_t v_allowEOFBody_181_){
_start:
{
lean_object* v___x_182_; lean_object* v___y_184_; lean_object* v___x_237_; lean_object* v___f_238_; lean_object* v___f_239_; uint8_t v___x_240_; 
v___x_182_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_179_, v_message_180_);
v___x_237_ = l_Std_Http_Header_Name_contentLength;
v___f_238_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0));
v___f_239_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1));
v___x_240_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_238_, v___f_239_, v___x_237_, v___x_182_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; 
v___x_241_ = lean_box(0);
v___y_184_ = v___x_241_;
goto v___jp_183_;
}
else
{
lean_object* v_indexes_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v_entries_247_; lean_object* v___x_248_; 
v_indexes_242_ = lean_ctor_get(v___x_182_, 1);
lean_inc_ref(v_indexes_242_);
v___x_243_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_242_, v___x_237_);
lean_dec_ref(v_indexes_242_);
v___x_244_ = lean_array_get_size(v___x_243_);
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = lean_mk_empty_array_with_capacity(v___x_244_);
v_entries_247_ = l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_182_, v___x_243_, v___x_244_, v___x_245_, v___x_246_);
lean_dec(v___x_243_);
v___x_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_248_, 0, v_entries_247_);
v___y_184_ = v___x_248_;
goto v___jp_183_;
}
v___jp_183_:
{
lean_object* v___x_185_; lean_object* v___f_186_; lean_object* v___f_187_; uint8_t v___x_188_; 
v___x_185_ = l_Std_Http_Header_Name_transferEncoding;
v___f_186_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0));
v___f_187_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1));
v___x_188_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_186_, v___f_187_, v___x_185_, v___x_182_);
if (v___x_188_ == 0)
{
lean_dec_ref(v___x_182_);
if (lean_obj_tag(v___y_184_) == 0)
{
if (v_allowEOFBody_181_ == 0)
{
lean_object* v___x_189_; 
v___x_189_ = lean_box(0);
return v___x_189_;
}
else
{
lean_object* v___x_190_; 
v___x_190_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__3));
return v___x_190_;
}
}
else
{
lean_object* v_val_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_214_; 
v_val_191_ = lean_ctor_get(v___y_184_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___y_184_);
if (v_isSharedCheck_214_ == 0)
{
v___x_193_ = v___y_184_;
v_isShared_194_ = v_isSharedCheck_214_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_val_191_);
lean_dec(v___y_184_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_214_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_195_ = lean_array_get_size(v_val_191_);
v___x_196_ = lean_unsigned_to_nat(1u);
v___x_197_ = lean_nat_dec_eq(v___x_195_, v___x_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; 
lean_del_object(v___x_193_);
lean_dec(v_val_191_);
v___x_198_ = lean_box(0);
return v___x_198_;
}
else
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = lean_unsigned_to_nat(0u);
v___x_200_ = lean_array_fget(v_val_191_, v___x_199_);
lean_dec(v_val_191_);
v___x_201_ = l_Std_Http_Header_ContentLength_parse(v___x_200_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v___x_202_; 
lean_del_object(v___x_193_);
v___x_202_ = lean_box(0);
return v___x_202_;
}
else
{
lean_object* v_val_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_213_; 
v_val_203_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_213_ == 0)
{
v___x_205_ = v___x_201_;
v_isShared_206_ = v_isSharedCheck_213_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_val_203_);
lean_dec(v___x_201_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_213_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 0, v_val_203_);
v___x_208_ = v___x_193_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_val_203_);
v___x_208_ = v_reuseFailAlloc_212_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_210_; 
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 0, v___x_208_);
v___x_210_ = v___x_205_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
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
lean_object* v_indexes_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v_entries_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v_indexes_215_ = lean_ctor_get(v___x_182_, 1);
lean_inc_ref(v_indexes_215_);
v___x_216_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_215_, v___x_185_);
lean_dec_ref(v_indexes_215_);
v___x_217_ = lean_array_get_size(v___x_216_);
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_mk_empty_array_with_capacity(v___x_217_);
v_entries_220_ = l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_182_, v___x_216_, v___x_217_, v___x_218_, v___x_219_);
lean_dec(v___x_216_);
lean_dec_ref(v___x_182_);
v___x_221_ = lean_array_get_size(v_entries_220_);
v___x_222_ = lean_unsigned_to_nat(1u);
v___x_223_ = lean_nat_dec_eq(v___x_221_, v___x_222_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; 
lean_dec_ref(v_entries_220_);
lean_dec(v___y_184_);
v___x_224_ = lean_box(0);
return v___x_224_;
}
else
{
lean_object* v___x_225_; lean_object* v_te_226_; 
v___x_225_ = lean_array_fget(v_entries_220_, v___x_218_);
lean_dec_ref(v_entries_220_);
v_te_226_ = l_Std_Http_Header_TransferEncoding_parse(v___x_225_);
if (lean_obj_tag(v_te_226_) == 0)
{
lean_object* v___x_227_; 
lean_dec(v___y_184_);
v___x_227_ = lean_box(0);
return v___x_227_;
}
else
{
lean_object* v_val_228_; uint8_t v___x_229_; 
v_val_228_ = lean_ctor_get(v_te_226_, 0);
lean_inc(v_val_228_);
lean_dec_ref(v_te_226_);
v___x_229_ = l_Std_Http_Header_TransferEncoding_isChunked(v_val_228_);
lean_dec(v_val_228_);
if (v___x_229_ == 1)
{
if (lean_obj_tag(v___y_184_) == 0)
{
uint8_t v___x_230_; uint8_t v___x_231_; uint8_t v___x_232_; 
v___x_230_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_179_, v_message_180_);
v___x_231_ = 0;
v___x_232_ = l_Std_Http_instBEqVersion_beq(v___x_230_, v___x_231_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; 
v___x_233_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__4));
return v___x_233_;
}
else
{
lean_object* v___x_234_; 
v___x_234_ = lean_box(0);
return v___x_234_;
}
}
else
{
lean_object* v___x_235_; 
lean_dec(v___y_184_);
v___x_235_ = lean_box(0);
return v___x_235_;
}
}
else
{
lean_object* v___x_236_; 
lean_dec(v___y_184_);
v___x_236_ = lean_box(0);
return v___x_236_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize___boxed(lean_object* v_dir_249_, lean_object* v_message_250_, lean_object* v_allowEOFBody_251_){
_start:
{
uint8_t v_dir_boxed_252_; uint8_t v_allowEOFBody_boxed_253_; lean_object* v_res_254_; 
v_dir_boxed_252_ = lean_unbox(v_dir_249_);
v_allowEOFBody_boxed_253_ = lean_unbox(v_allowEOFBody_251_);
v_res_254_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v_dir_boxed_252_, v_message_250_, v_allowEOFBody_boxed_253_);
lean_dec(v_message_250_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(lean_object* v_00_u03b2_255_, lean_object* v_m_256_, lean_object* v_a_257_, lean_object* v_hma_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_m_256_, v_a_257_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___boxed(lean_object* v_00_u03b2_260_, lean_object* v_m_261_, lean_object* v_a_262_, lean_object* v_hma_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(v_00_u03b2_260_, v_m_261_, v_a_262_, v_hma_263_);
lean_dec_ref(v_a_262_);
lean_dec_ref(v_m_261_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(lean_object* v___x_265_, lean_object* v___x_266_, lean_object* v_as_267_, lean_object* v_i_268_, lean_object* v_j_269_, lean_object* v_inv_270_, lean_object* v_bs_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_265_, v___x_266_, v_i_268_, v_j_269_, v_bs_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___boxed(lean_object* v___x_273_, lean_object* v___x_274_, lean_object* v_as_275_, lean_object* v_i_276_, lean_object* v_j_277_, lean_object* v_inv_278_, lean_object* v_bs_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(v___x_273_, v___x_274_, v_as_275_, v_i_276_, v_j_277_, v_inv_278_, v_bs_279_);
lean_dec_ref(v_as_275_);
lean_dec_ref(v___x_274_);
lean_dec_ref(v___x_273_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0(lean_object* v_00_u03b2_281_, lean_object* v_a_282_, lean_object* v_x_283_, lean_object* v_x_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_a_282_, v_x_283_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_286_, lean_object* v_a_287_, lean_object* v_x_288_, lean_object* v_x_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0(v_00_u03b2_286_, v_a_287_, v_x_288_, v_x_289_);
lean_dec(v_x_288_);
lean_dec_ref(v_a_287_);
return v_res_290_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(lean_object* v_as_292_, size_t v_i_293_, size_t v_stop_294_){
_start:
{
uint8_t v___x_295_; 
v___x_295_ = lean_usize_dec_eq(v_i_293_, v_stop_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_296_ = lean_array_uget_borrowed(v_as_292_, v_i_293_);
v___x_297_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___closed__0));
v___x_298_ = lean_string_dec_eq(v___x_296_, v___x_297_);
if (v___x_298_ == 0)
{
size_t v___x_299_; size_t v___x_300_; 
v___x_299_ = ((size_t)1ULL);
v___x_300_ = lean_usize_add(v_i_293_, v___x_299_);
v_i_293_ = v___x_300_;
goto _start;
}
else
{
return v___x_298_;
}
}
else
{
uint8_t v___x_302_; 
v___x_302_ = 0;
return v___x_302_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___boxed(lean_object* v_as_303_, lean_object* v_i_304_, lean_object* v_stop_305_){
_start:
{
size_t v_i_boxed_306_; size_t v_stop_boxed_307_; uint8_t v_res_308_; lean_object* v_r_309_; 
v_i_boxed_306_ = lean_unbox_usize(v_i_304_);
lean_dec(v_i_304_);
v_stop_boxed_307_ = lean_unbox_usize(v_stop_305_);
lean_dec(v_stop_305_);
v_res_308_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(v_as_303_, v_i_boxed_306_, v_stop_boxed_307_);
lean_dec_ref(v_as_303_);
v_r_309_ = lean_box(v_res_308_);
return v_r_309_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(lean_object* v_as_311_, size_t v_i_312_, size_t v_stop_313_){
_start:
{
uint8_t v___x_314_; 
v___x_314_ = lean_usize_dec_eq(v_i_312_, v_stop_313_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_315_ = lean_array_uget_borrowed(v_as_311_, v_i_312_);
v___x_316_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___closed__0));
v___x_317_ = lean_string_dec_eq(v___x_315_, v___x_316_);
if (v___x_317_ == 0)
{
size_t v___x_318_; size_t v___x_319_; 
v___x_318_ = ((size_t)1ULL);
v___x_319_ = lean_usize_add(v_i_312_, v___x_318_);
v_i_312_ = v___x_319_;
goto _start;
}
else
{
return v___x_317_;
}
}
else
{
uint8_t v___x_321_; 
v___x_321_ = 0;
return v___x_321_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___boxed(lean_object* v_as_322_, lean_object* v_i_323_, lean_object* v_stop_324_){
_start:
{
size_t v_i_boxed_325_; size_t v_stop_boxed_326_; uint8_t v_res_327_; lean_object* v_r_328_; 
v_i_boxed_325_ = lean_unbox_usize(v_i_323_);
lean_dec(v_i_323_);
v_stop_boxed_326_ = lean_unbox_usize(v_stop_324_);
lean_dec(v_stop_324_);
v_res_327_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(v_as_322_, v_i_boxed_325_, v_stop_boxed_326_);
lean_dec_ref(v_as_322_);
v_r_328_ = lean_box(v_res_327_);
return v_r_328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(lean_object* v_as_329_, size_t v_i_330_, size_t v_stop_331_, lean_object* v_b_332_){
_start:
{
lean_object* v___y_334_; uint8_t v___x_338_; 
v___x_338_ = lean_usize_dec_eq(v_i_330_, v_stop_331_);
if (v___x_338_ == 0)
{
if (lean_obj_tag(v_b_332_) == 0)
{
v___y_334_ = v_b_332_;
goto v___jp_333_;
}
else
{
lean_object* v_val_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_val_339_ = lean_ctor_get(v_b_332_, 0);
lean_inc(v_val_339_);
lean_dec_ref(v_b_332_);
v___x_340_ = lean_array_uget_borrowed(v_as_329_, v_i_330_);
lean_inc(v___x_340_);
v___x_341_ = l_Std_Http_Header_Connection_parse(v___x_340_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v___x_342_; 
lean_dec(v_val_339_);
v___x_342_ = lean_box(0);
v___y_334_ = v___x_342_;
goto v___jp_333_;
}
else
{
lean_object* v_val_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_351_; 
v_val_343_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_351_ == 0)
{
v___x_345_ = v___x_341_;
v_isShared_346_ = v_isSharedCheck_351_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_val_343_);
lean_dec(v___x_341_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_351_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; lean_object* v___x_349_; 
v___x_347_ = l_Array_append___redArg(v_val_339_, v_val_343_);
lean_dec(v_val_343_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v___x_347_);
v___x_349_ = v___x_345_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_347_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
v___y_334_ = v___x_349_;
goto v___jp_333_;
}
}
}
}
}
else
{
return v_b_332_;
}
v___jp_333_:
{
size_t v___x_335_; size_t v___x_336_; 
v___x_335_ = ((size_t)1ULL);
v___x_336_ = lean_usize_add(v_i_330_, v___x_335_);
v_i_330_ = v___x_336_;
v_b_332_ = v___y_334_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2___boxed(lean_object* v_as_352_, lean_object* v_i_353_, lean_object* v_stop_354_, lean_object* v_b_355_){
_start:
{
size_t v_i_boxed_356_; size_t v_stop_boxed_357_; lean_object* v_res_358_; 
v_i_boxed_356_ = lean_unbox_usize(v_i_353_);
lean_dec(v_i_353_);
v_stop_boxed_357_ = lean_unbox_usize(v_stop_354_);
lean_dec(v_stop_354_);
v_res_358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_as_352_, v_i_boxed_356_, v_stop_boxed_357_, v_b_355_);
lean_dec_ref(v_as_352_);
return v_res_358_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(uint8_t v_dir_363_, lean_object* v_message_364_){
_start:
{
lean_object* v_val_366_; lean_object* v___y_384_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___f_389_; lean_object* v___f_390_; uint8_t v___x_391_; 
v___x_387_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_363_, v_message_364_);
v___x_388_ = l_Std_Http_Header_Name_connection;
v___f_389_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0));
v___f_390_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1));
v___x_391_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_389_, v___f_390_, v___x_388_, v___x_387_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; 
lean_dec_ref(v___x_387_);
v___x_392_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0));
v_val_366_ = v___x_392_;
goto v___jp_365_;
}
else
{
lean_object* v_indexes_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v_entries_398_; lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v_indexes_393_ = lean_ctor_get(v___x_387_, 1);
lean_inc_ref(v_indexes_393_);
v___x_394_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_393_, v___x_388_);
lean_dec_ref(v_indexes_393_);
v___x_395_ = lean_array_get_size(v___x_394_);
v___x_396_ = lean_unsigned_to_nat(0u);
v___x_397_ = lean_mk_empty_array_with_capacity(v___x_395_);
v_entries_398_ = l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_387_, v___x_394_, v___x_395_, v___x_396_, v___x_397_);
lean_dec(v___x_394_);
lean_dec_ref(v___x_387_);
v___x_399_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0));
v___x_400_ = lean_array_get_size(v_entries_398_);
v___x_401_ = lean_nat_dec_lt(v___x_396_, v___x_400_);
if (v___x_401_ == 0)
{
lean_dec_ref(v_entries_398_);
v_val_366_ = v___x_399_;
goto v___jp_365_;
}
else
{
lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_402_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__1));
v___x_403_ = lean_nat_dec_le(v___x_400_, v___x_400_);
if (v___x_403_ == 0)
{
if (v___x_401_ == 0)
{
lean_dec_ref(v_entries_398_);
v_val_366_ = v___x_399_;
goto v___jp_365_;
}
else
{
size_t v___x_404_; size_t v___x_405_; lean_object* v___x_406_; 
v___x_404_ = ((size_t)0ULL);
v___x_405_ = lean_usize_of_nat(v___x_400_);
v___x_406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_entries_398_, v___x_404_, v___x_405_, v___x_402_);
lean_dec_ref(v_entries_398_);
v___y_384_ = v___x_406_;
goto v___jp_383_;
}
}
else
{
size_t v___x_407_; size_t v___x_408_; lean_object* v___x_409_; 
v___x_407_ = ((size_t)0ULL);
v___x_408_ = lean_usize_of_nat(v___x_400_);
v___x_409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_entries_398_, v___x_407_, v___x_408_, v___x_402_);
lean_dec_ref(v_entries_398_);
v___y_384_ = v___x_409_;
goto v___jp_383_;
}
}
}
v___jp_365_:
{
uint8_t v___x_367_; uint8_t v___x_368_; uint8_t v___x_369_; 
v___x_367_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_363_, v_message_364_);
v___x_368_ = 1;
v___x_369_ = l_Std_Http_instBEqVersion_beq(v___x_367_, v___x_368_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_370_ = lean_unsigned_to_nat(0u);
v___x_371_ = lean_array_get_size(v_val_366_);
v___x_372_ = lean_nat_dec_lt(v___x_370_, v___x_371_);
if (v___x_372_ == 0)
{
lean_dec_ref(v_val_366_);
return v___x_369_;
}
else
{
if (v___x_372_ == 0)
{
lean_dec_ref(v_val_366_);
return v___x_369_;
}
else
{
size_t v___x_373_; size_t v___x_374_; uint8_t v___x_375_; 
v___x_373_ = ((size_t)0ULL);
v___x_374_ = lean_usize_of_nat(v___x_371_);
v___x_375_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(v_val_366_, v___x_373_, v___x_374_);
lean_dec_ref(v_val_366_);
return v___x_375_;
}
}
}
else
{
lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_376_ = lean_unsigned_to_nat(0u);
v___x_377_ = lean_array_get_size(v_val_366_);
v___x_378_ = lean_nat_dec_lt(v___x_376_, v___x_377_);
if (v___x_378_ == 0)
{
lean_dec_ref(v_val_366_);
return v___x_369_;
}
else
{
if (v___x_378_ == 0)
{
lean_dec_ref(v_val_366_);
return v___x_369_;
}
else
{
size_t v___x_379_; size_t v___x_380_; uint8_t v___x_381_; 
v___x_379_ = ((size_t)0ULL);
v___x_380_ = lean_usize_of_nat(v___x_377_);
v___x_381_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(v_val_366_, v___x_379_, v___x_380_);
lean_dec_ref(v_val_366_);
if (v___x_381_ == 0)
{
return v___x_369_;
}
else
{
uint8_t v___x_382_; 
v___x_382_ = 0;
return v___x_382_;
}
}
}
}
}
v___jp_383_:
{
if (lean_obj_tag(v___y_384_) == 0)
{
uint8_t v___x_385_; 
v___x_385_ = 0;
return v___x_385_;
}
else
{
lean_object* v_val_386_; 
v_val_386_ = lean_ctor_get(v___y_384_, 0);
lean_inc(v_val_386_);
lean_dec_ref(v___y_384_);
v_val_366_ = v_val_386_;
goto v___jp_365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___boxed(lean_object* v_dir_410_, lean_object* v_message_411_){
_start:
{
uint8_t v_dir_boxed_412_; uint8_t v_res_413_; lean_object* v_r_414_; 
v_dir_boxed_412_ = lean_unbox(v_dir_410_);
v_res_413_ = l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(v_dir_boxed_412_, v_message_411_);
lean_dec(v_message_411_);
v_r_414_ = lean_box(v_res_413_);
return v_r_414_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1___redArg(lean_object* v_x_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Std_Http_Request_instReprHead_repr___redArg(v_x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1(lean_object* v_x_417_, lean_object* v_prec_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Std_Http_Request_instReprHead_repr___redArg(v_x_417_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1___boxed(lean_object* v_x_420_, lean_object* v_prec_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Std_Http_Protocol_H1_instReprHead___aux__1(v_x_420_, v_prec_421_);
lean_dec(v_prec_421_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3___redArg(lean_object* v_x_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Std_Http_Response_instReprHead_repr___redArg(v_x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3(lean_object* v_x_425_, lean_object* v_prec_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Std_Http_Response_instReprHead_repr___redArg(v_x_425_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3___boxed(lean_object* v_x_428_, lean_object* v_prec_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Std_Http_Protocol_H1_instReprHead___aux__3(v_x_428_, v_prec_429_);
lean_dec(v_prec_429_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead(uint8_t v_dir_433_){
_start:
{
if (v_dir_433_ == 0)
{
lean_object* v___x_434_; 
v___x_434_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprHead___closed__0));
return v___x_434_;
}
else
{
lean_object* v___x_435_; 
v___x_435_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprHead___closed__1));
return v___x_435_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___boxed(lean_object* v_dir_436_){
_start:
{
uint8_t v_dir_boxed_437_; lean_object* v_res_438_; 
v_dir_boxed_437_ = lean_unbox(v_dir_436_);
v_res_438_ = l_Std_Http_Protocol_H1_instReprHead(v_dir_boxed_437_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__0(lean_object* v_x_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = lean_string_from_utf8_unchecked(v_x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1(lean_object* v_x_441_){
_start:
{
lean_object* v_fst_442_; lean_object* v_snd_443_; lean_object* v___x_444_; 
v_fst_442_ = lean_ctor_get(v_x_441_, 0);
lean_inc(v_fst_442_);
v_snd_443_ = lean_ctor_get(v_x_441_, 1);
lean_inc(v_snd_443_);
lean_dec_ref(v_x_441_);
v___x_444_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_442_, v_snd_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2(lean_object* v___x_445_, lean_object* v___x_446_, lean_object* v___x_447_, lean_object* v_name_448_, lean_object* v___x_449_, uint32_t v___x_450_, lean_object* v___x_451_, lean_object* v_it_452_, lean_object* v_acc_453_, lean_object* v_hP_454_, lean_object* v_recur_455_){
_start:
{
lean_object* v_it_457_; lean_object* v_out_458_; lean_object* v_it_474_; lean_object* v_startInclusive_475_; lean_object* v_endExclusive_476_; 
if (lean_obj_tag(v_it_452_) == 0)
{
lean_object* v_currPos_488_; lean_object* v_searcher_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_511_; 
v_currPos_488_ = lean_ctor_get(v_it_452_, 0);
v_searcher_489_ = lean_ctor_get(v_it_452_, 1);
v_isSharedCheck_511_ = !lean_is_exclusive(v_it_452_);
if (v_isSharedCheck_511_ == 0)
{
v___x_491_ = v_it_452_;
v_isShared_492_ = v_isSharedCheck_511_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_searcher_489_);
lean_inc(v_currPos_488_);
lean_dec(v_it_452_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_511_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
uint8_t v___x_493_; 
v___x_493_ = lean_nat_dec_eq(v_searcher_489_, v___x_449_);
if (v___x_493_ == 0)
{
uint32_t v___x_494_; uint8_t v___x_495_; 
lean_dec(v___x_449_);
v___x_494_ = lean_string_utf8_get_fast(v_name_448_, v_searcher_489_);
v___x_495_ = lean_uint32_dec_eq(v___x_494_, v___x_450_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_496_ = lean_string_utf8_next_fast(v_name_448_, v_searcher_489_);
lean_dec(v_searcher_489_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 1, v___x_496_);
v___x_498_ = v___x_491_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_currPos_488_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v___x_496_);
v___x_498_ = v_reuseFailAlloc_500_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_499_; 
v___x_499_ = lean_apply_4(v_recur_455_, v___x_498_, v_acc_453_, lean_box(0), lean_box(0));
return v___x_499_;
}
}
else
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v_slice_504_; lean_object* v_nextIt_506_; 
v___x_501_ = lean_string_utf8_next_fast(v_name_448_, v_searcher_489_);
v___x_502_ = lean_nat_sub(v___x_501_, v_searcher_489_);
v___x_503_ = lean_nat_add(v_searcher_489_, v___x_502_);
lean_dec(v___x_502_);
v_slice_504_ = l_String_Slice_subslice_x21(v___x_451_, v_currPos_488_, v_searcher_489_);
lean_inc(v___x_503_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 1, v___x_503_);
lean_ctor_set(v___x_491_, 0, v___x_503_);
v_nextIt_506_ = v___x_491_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v___x_503_);
v_nextIt_506_ = v_reuseFailAlloc_509_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v_startInclusive_507_; lean_object* v_endExclusive_508_; 
v_startInclusive_507_ = lean_ctor_get(v_slice_504_, 0);
lean_inc(v_startInclusive_507_);
v_endExclusive_508_ = lean_ctor_get(v_slice_504_, 1);
lean_inc(v_endExclusive_508_);
lean_dec_ref(v_slice_504_);
v_it_474_ = v_nextIt_506_;
v_startInclusive_475_ = v_startInclusive_507_;
v_endExclusive_476_ = v_endExclusive_508_;
goto v___jp_473_;
}
}
}
else
{
lean_object* v___x_510_; 
lean_del_object(v___x_491_);
lean_dec(v_searcher_489_);
v___x_510_ = lean_box(1);
v_it_474_ = v___x_510_;
v_startInclusive_475_ = v_currPos_488_;
v_endExclusive_476_ = v___x_449_;
goto v___jp_473_;
}
}
}
else
{
lean_dec_ref(v_recur_455_);
lean_dec(v___x_449_);
return v_acc_453_;
}
v___jp_456_:
{
if (lean_obj_tag(v_acc_453_) == 0)
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_459_, 0, v_out_458_);
v___x_460_ = lean_apply_4(v_recur_455_, v_it_457_, v___x_459_, lean_box(0), lean_box(0));
return v___x_460_;
}
else
{
lean_object* v_val_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_472_; 
v_val_461_ = lean_ctor_get(v_acc_453_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v_acc_453_);
if (v_isSharedCheck_472_ == 0)
{
v___x_463_ = v_acc_453_;
v_isShared_464_ = v_isSharedCheck_472_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_val_461_);
lean_dec(v_acc_453_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_472_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_465_ = lean_string_utf8_extract(v___x_445_, v___x_446_, v___x_447_);
v___x_466_ = lean_string_append(v_val_461_, v___x_465_);
lean_dec_ref(v___x_465_);
v___x_467_ = lean_string_append(v___x_466_, v_out_458_);
lean_dec_ref(v_out_458_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v___x_467_);
v___x_469_ = v___x_463_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_471_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; 
v___x_470_ = lean_apply_4(v_recur_455_, v_it_457_, v___x_469_, lean_box(0), lean_box(0));
return v___x_470_;
}
}
}
}
v___jp_473_:
{
lean_object* v___x_477_; uint32_t v___x_478_; uint32_t v___x_479_; uint8_t v___x_480_; 
v___x_477_ = lean_string_utf8_extract(v_name_448_, v_startInclusive_475_, v_endExclusive_476_);
lean_dec(v_endExclusive_476_);
lean_dec(v_startInclusive_475_);
v___x_478_ = lean_string_utf8_get(v___x_477_, v___x_446_);
v___x_479_ = 97;
v___x_480_ = lean_uint32_dec_le(v___x_479_, v___x_478_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; 
v___x_481_ = lean_string_utf8_set(v___x_477_, v___x_446_, v___x_478_);
v_it_457_ = v_it_474_;
v_out_458_ = v___x_481_;
goto v___jp_456_;
}
else
{
uint32_t v___x_482_; uint8_t v___x_483_; 
v___x_482_ = 122;
v___x_483_ = lean_uint32_dec_le(v___x_478_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; 
v___x_484_ = lean_string_utf8_set(v___x_477_, v___x_446_, v___x_478_);
v_it_457_ = v_it_474_;
v_out_458_ = v___x_484_;
goto v___jp_456_;
}
else
{
uint32_t v___x_485_; uint32_t v___x_486_; lean_object* v___x_487_; 
v___x_485_ = 4294967264;
v___x_486_ = lean_uint32_add(v___x_478_, v___x_485_);
v___x_487_ = lean_string_utf8_set(v___x_477_, v___x_446_, v___x_486_);
v_it_457_ = v_it_474_;
v_out_458_ = v___x_487_;
goto v___jp_456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed(lean_object* v___x_512_, lean_object* v___x_513_, lean_object* v___x_514_, lean_object* v_name_515_, lean_object* v___x_516_, lean_object* v___x_517_, lean_object* v___x_518_, lean_object* v_it_519_, lean_object* v_acc_520_, lean_object* v_hP_521_, lean_object* v_recur_522_){
_start:
{
uint32_t v___x_2817__boxed_523_; lean_object* v_res_524_; 
v___x_2817__boxed_523_ = lean_unbox_uint32(v___x_517_);
lean_dec(v___x_517_);
v_res_524_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2(v___x_512_, v___x_513_, v___x_514_, v_name_515_, v___x_516_, v___x_2817__boxed_523_, v___x_518_, v_it_519_, v_acc_520_, v_hP_521_, v_recur_522_);
lean_dec_ref(v___x_518_);
lean_dec_ref(v_name_515_);
lean_dec(v___x_514_);
lean_dec(v___x_513_);
lean_dec_ref(v___x_512_);
return v_res_524_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__4(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__3));
v___x_530_ = lean_string_utf8_byte_size(v___x_529_);
return v___x_530_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___boxed__const__1(void){
_start:
{
uint32_t v___x_532_; lean_object* v___x_533_; 
v___x_532_ = 45;
v___x_533_ = lean_box_uint32(v___x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3(lean_object* v_buf_534_, lean_object* v_name_535_, lean_object* v_value_536_){
_start:
{
lean_object* v___y_538_; lean_object* v___f_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v_it_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___f_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___f_557_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__2));
v___x_558_ = lean_unsigned_to_nat(0u);
v___x_559_ = lean_string_utf8_byte_size(v_name_535_);
lean_inc_ref(v_name_535_);
v___x_560_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_560_, 0, v_name_535_);
lean_ctor_set(v___x_560_, 1, v___x_558_);
lean_ctor_set(v___x_560_, 2, v___x_559_);
lean_inc_ref(v___x_560_);
v_it_561_ = l_String_Slice_splitToSubslice___redArg(v___x_560_, v___f_557_);
v___x_562_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__3));
v___x_563_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__4, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__4_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__4);
v___x_564_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___boxed__const__1;
v___f_565_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed), 11, 7);
lean_closure_set(v___f_565_, 0, v___x_562_);
lean_closure_set(v___f_565_, 1, v___x_558_);
lean_closure_set(v___f_565_, 2, v___x_563_);
lean_closure_set(v___f_565_, 3, v_name_535_);
lean_closure_set(v___f_565_, 4, v___x_559_);
lean_closure_set(v___f_565_, 5, v___x_564_);
lean_closure_set(v___f_565_, 6, v___x_560_);
v___x_566_ = lean_box(0);
v___x_567_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_565_, v_it_561_, v___x_566_, lean_box(0));
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v___x_568_; 
v___x_568_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5));
v___y_538_ = v___x_568_;
goto v___jp_537_;
}
else
{
lean_object* v_val_569_; 
v_val_569_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_val_569_);
lean_dec_ref(v___x_567_);
v___y_538_ = v_val_569_;
goto v___jp_537_;
}
v___jp_537_:
{
lean_object* v_data_539_; lean_object* v_size_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_556_; 
v_data_539_ = lean_ctor_get(v_buf_534_, 0);
v_size_540_ = lean_ctor_get(v_buf_534_, 1);
v_isSharedCheck_556_ = !lean_is_exclusive(v_buf_534_);
if (v_isSharedCheck_556_ == 0)
{
v___x_542_ = v_buf_534_;
v_isShared_543_ = v_isSharedCheck_556_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_size_540_);
lean_inc(v_data_539_);
lean_dec(v_buf_534_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_556_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_544_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__0));
v___x_545_ = lean_string_append(v___y_538_, v___x_544_);
v___x_546_ = lean_string_append(v___x_545_, v_value_536_);
v___x_547_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__1));
v___x_548_ = lean_string_append(v___x_546_, v___x_547_);
v___x_549_ = lean_string_to_utf8(v___x_548_);
lean_dec_ref(v___x_548_);
lean_inc_ref(v___x_549_);
v___x_550_ = lean_array_push(v_data_539_, v___x_549_);
v___x_551_ = lean_byte_array_size(v___x_549_);
lean_dec_ref(v___x_549_);
v___x_552_ = lean_nat_add(v_size_540_, v___x_551_);
lean_dec(v_size_540_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 1, v___x_552_);
lean_ctor_set(v___x_542_, 0, v___x_550_);
v___x_554_ = v___x_542_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v___x_552_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___boxed(lean_object* v_buf_570_, lean_object* v_name_571_, lean_object* v_value_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3(v_buf_570_, v_name_571_, v_value_572_);
lean_dec_ref(v_value_572_);
return v_res_573_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__1));
v___x_578_ = lean_string_to_utf8(v___x_577_);
return v___x_578_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3);
v___x_580_ = lean_byte_array_size(v___x_579_);
return v___x_580_;
}
}
static uint8_t _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26(void){
_start:
{
uint32_t v___x_611_; uint8_t v___x_612_; 
v___x_611_ = 32;
v___x_612_ = lean_uint32_to_uint8(v___x_611_);
return v___x_612_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27(void){
_start:
{
uint8_t v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_613_ = lean_uint8_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26);
v___x_614_ = lean_unsigned_to_nat(1u);
v___x_615_ = lean_mk_empty_array_with_capacity(v___x_614_);
v___x_616_ = lean_box(v___x_613_);
v___x_617_ = lean_array_push(v___x_615_, v___x_616_);
v___x_618_ = lean_byte_array_mk(v___x_617_);
return v___x_618_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27);
v___x_620_ = lean_byte_array_size(v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1(lean_object* v_buffer_664_, lean_object* v_req_665_){
_start:
{
uint8_t v_method_666_; uint8_t v_version_667_; lean_object* v_uri_668_; lean_object* v_headers_669_; lean_object* v___f_670_; lean_object* v___f_671_; lean_object* v___f_672_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v_port_781_; lean_object* v___y_782_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v_host_795_; lean_object* v_port_796_; lean_object* v___y_797_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v_port_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v_host_891_; lean_object* v_port_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_907_; 
v_method_666_ = lean_ctor_get_uint8(v_req_665_, sizeof(void*)*2);
v_version_667_ = lean_ctor_get_uint8(v_req_665_, sizeof(void*)*2 + 1);
v_uri_668_ = lean_ctor_get(v_req_665_, 0);
lean_inc(v_uri_668_);
v_headers_669_ = lean_ctor_get(v_req_665_, 1);
lean_inc_ref(v_headers_669_);
lean_dec_ref(v_req_665_);
v___f_670_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__0));
v___f_671_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1));
v___f_672_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2));
switch(v_method_666_)
{
case 0:
{
lean_object* v___x_987_; 
v___x_987_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32));
v___y_907_ = v___x_987_;
goto v___jp_906_;
}
case 1:
{
lean_object* v___x_988_; 
v___x_988_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33));
v___y_907_ = v___x_988_;
goto v___jp_906_;
}
case 2:
{
lean_object* v___x_989_; 
v___x_989_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34));
v___y_907_ = v___x_989_;
goto v___jp_906_;
}
case 3:
{
lean_object* v___x_990_; 
v___x_990_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35));
v___y_907_ = v___x_990_;
goto v___jp_906_;
}
case 4:
{
lean_object* v___x_991_; 
v___x_991_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36));
v___y_907_ = v___x_991_;
goto v___jp_906_;
}
case 5:
{
lean_object* v___x_992_; 
v___x_992_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37));
v___y_907_ = v___x_992_;
goto v___jp_906_;
}
case 6:
{
lean_object* v___x_993_; 
v___x_993_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38));
v___y_907_ = v___x_993_;
goto v___jp_906_;
}
case 7:
{
lean_object* v___x_994_; 
v___x_994_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39));
v___y_907_ = v___x_994_;
goto v___jp_906_;
}
case 8:
{
lean_object* v___x_995_; 
v___x_995_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40));
v___y_907_ = v___x_995_;
goto v___jp_906_;
}
case 9:
{
lean_object* v___x_996_; 
v___x_996_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41));
v___y_907_ = v___x_996_;
goto v___jp_906_;
}
case 10:
{
lean_object* v___x_997_; 
v___x_997_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42));
v___y_907_ = v___x_997_;
goto v___jp_906_;
}
case 11:
{
lean_object* v___x_998_; 
v___x_998_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43));
v___y_907_ = v___x_998_;
goto v___jp_906_;
}
case 12:
{
lean_object* v___x_999_; 
v___x_999_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44));
v___y_907_ = v___x_999_;
goto v___jp_906_;
}
case 13:
{
lean_object* v___x_1000_; 
v___x_1000_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45));
v___y_907_ = v___x_1000_;
goto v___jp_906_;
}
case 14:
{
lean_object* v___x_1001_; 
v___x_1001_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46));
v___y_907_ = v___x_1001_;
goto v___jp_906_;
}
case 15:
{
lean_object* v___x_1002_; 
v___x_1002_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47));
v___y_907_ = v___x_1002_;
goto v___jp_906_;
}
case 16:
{
lean_object* v___x_1003_; 
v___x_1003_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48));
v___y_907_ = v___x_1003_;
goto v___jp_906_;
}
case 17:
{
lean_object* v___x_1004_; 
v___x_1004_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49));
v___y_907_ = v___x_1004_;
goto v___jp_906_;
}
case 18:
{
lean_object* v___x_1005_; 
v___x_1005_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50));
v___y_907_ = v___x_1005_;
goto v___jp_906_;
}
case 19:
{
lean_object* v___x_1006_; 
v___x_1006_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51));
v___y_907_ = v___x_1006_;
goto v___jp_906_;
}
case 20:
{
lean_object* v___x_1007_; 
v___x_1007_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52));
v___y_907_ = v___x_1007_;
goto v___jp_906_;
}
case 21:
{
lean_object* v___x_1008_; 
v___x_1008_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53));
v___y_907_ = v___x_1008_;
goto v___jp_906_;
}
case 22:
{
lean_object* v___x_1009_; 
v___x_1009_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54));
v___y_907_ = v___x_1009_;
goto v___jp_906_;
}
case 23:
{
lean_object* v___x_1010_; 
v___x_1010_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55));
v___y_907_ = v___x_1010_;
goto v___jp_906_;
}
case 24:
{
lean_object* v___x_1011_; 
v___x_1011_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56));
v___y_907_ = v___x_1011_;
goto v___jp_906_;
}
case 25:
{
lean_object* v___x_1012_; 
v___x_1012_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57));
v___y_907_ = v___x_1012_;
goto v___jp_906_;
}
case 26:
{
lean_object* v___x_1013_; 
v___x_1013_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58));
v___y_907_ = v___x_1013_;
goto v___jp_906_;
}
case 27:
{
lean_object* v___x_1014_; 
v___x_1014_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59));
v___y_907_ = v___x_1014_;
goto v___jp_906_;
}
case 28:
{
lean_object* v___x_1015_; 
v___x_1015_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60));
v___y_907_ = v___x_1015_;
goto v___jp_906_;
}
case 29:
{
lean_object* v___x_1016_; 
v___x_1016_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61));
v___y_907_ = v___x_1016_;
goto v___jp_906_;
}
case 30:
{
lean_object* v___x_1017_; 
v___x_1017_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62));
v___y_907_ = v___x_1017_;
goto v___jp_906_;
}
case 31:
{
lean_object* v___x_1018_; 
v___x_1018_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63));
v___y_907_ = v___x_1018_;
goto v___jp_906_;
}
case 32:
{
lean_object* v___x_1019_; 
v___x_1019_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64));
v___y_907_ = v___x_1019_;
goto v___jp_906_;
}
case 33:
{
lean_object* v___x_1020_; 
v___x_1020_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65));
v___y_907_ = v___x_1020_;
goto v___jp_906_;
}
case 34:
{
lean_object* v___x_1021_; 
v___x_1021_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66));
v___y_907_ = v___x_1021_;
goto v___jp_906_;
}
case 35:
{
lean_object* v___x_1022_; 
v___x_1022_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67));
v___y_907_ = v___x_1022_;
goto v___jp_906_;
}
case 36:
{
lean_object* v___x_1023_; 
v___x_1023_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__68));
v___y_907_ = v___x_1023_;
goto v___jp_906_;
}
case 37:
{
lean_object* v___x_1024_; 
v___x_1024_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__69));
v___y_907_ = v___x_1024_;
goto v___jp_906_;
}
case 38:
{
lean_object* v___x_1025_; 
v___x_1025_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__70));
v___y_907_ = v___x_1025_;
goto v___jp_906_;
}
default: 
{
lean_object* v___x_1026_; 
v___x_1026_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__71));
v___y_907_ = v___x_1026_;
goto v___jp_906_;
}
}
v___jp_673_:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v_buffer_685_; lean_object* v_buffer_686_; lean_object* v_data_687_; lean_object* v_size_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_697_; 
v___x_677_ = lean_string_to_utf8(v___y_676_);
lean_inc_ref(v___x_677_);
v___x_678_ = lean_array_push(v___y_675_, v___x_677_);
v___x_679_ = lean_byte_array_size(v___x_677_);
lean_dec_ref(v___x_677_);
v___x_680_ = lean_nat_add(v___y_674_, v___x_679_);
lean_dec(v___y_674_);
v___x_681_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3);
v___x_682_ = lean_array_push(v___x_678_, v___x_681_);
v___x_683_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4);
v___x_684_ = lean_nat_add(v___x_680_, v___x_683_);
lean_dec(v___x_680_);
v_buffer_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_buffer_685_, 0, v___x_682_);
lean_ctor_set(v_buffer_685_, 1, v___x_684_);
v_buffer_686_ = l_Std_Http_Headers_fold___redArg(v_headers_669_, v_buffer_685_, v___f_672_);
lean_dec_ref(v_headers_669_);
v_data_687_ = lean_ctor_get(v_buffer_686_, 0);
v_size_688_ = lean_ctor_get(v_buffer_686_, 1);
v_isSharedCheck_697_ = !lean_is_exclusive(v_buffer_686_);
if (v_isSharedCheck_697_ == 0)
{
v___x_690_ = v_buffer_686_;
v_isShared_691_ = v_isSharedCheck_697_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_size_688_);
lean_inc(v_data_687_);
lean_dec(v_buffer_686_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_697_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_695_; 
v___x_692_ = lean_array_push(v_data_687_, v___x_681_);
v___x_693_ = lean_nat_add(v_size_688_, v___x_683_);
lean_dec(v_size_688_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v___x_693_);
lean_ctor_set(v___x_690_, 0, v___x_692_);
v___x_695_ = v___x_690_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v___x_693_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
v___jp_698_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_704_ = lean_string_to_utf8(v___y_703_);
lean_dec_ref(v___y_703_);
lean_inc_ref(v___x_704_);
v___x_705_ = lean_array_push(v___y_702_, v___x_704_);
v___x_706_ = lean_byte_array_size(v___x_704_);
lean_dec_ref(v___x_704_);
v___x_707_ = lean_nat_add(v___y_701_, v___x_706_);
lean_dec(v___y_701_);
v___x_708_ = lean_array_push(v___x_705_, v___y_699_);
v___x_709_ = lean_nat_add(v___x_707_, v___y_700_);
lean_dec(v___x_707_);
switch(v_version_667_)
{
case 0:
{
lean_object* v___x_710_; 
v___x_710_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5));
v___y_674_ = v___x_709_;
v___y_675_ = v___x_708_;
v___y_676_ = v___x_710_;
goto v___jp_673_;
}
case 1:
{
lean_object* v___x_711_; 
v___x_711_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6));
v___y_674_ = v___x_709_;
v___y_675_ = v___x_708_;
v___y_676_ = v___x_711_;
goto v___jp_673_;
}
case 2:
{
lean_object* v___x_712_; 
v___x_712_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7));
v___y_674_ = v___x_709_;
v___y_675_ = v___x_708_;
v___y_676_ = v___x_712_;
goto v___jp_673_;
}
default: 
{
lean_object* v___x_713_; 
v___x_713_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___y_674_ = v___x_709_;
v___y_675_ = v___x_708_;
v___y_676_ = v___x_713_;
goto v___jp_673_;
}
}
}
v___jp_714_:
{
if (lean_obj_tag(v___y_716_) == 0)
{
v___y_699_ = v___y_715_;
v___y_700_ = v___y_718_;
v___y_701_ = v___y_717_;
v___y_702_ = v___y_719_;
v___y_703_ = v___y_720_;
goto v___jp_698_;
}
else
{
lean_object* v_val_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v_val_721_ = lean_ctor_get(v___y_716_, 0);
lean_inc(v_val_721_);
lean_dec_ref(v___y_716_);
v___x_722_ = lean_array_get_size(v_val_721_);
v___x_723_ = lean_unsigned_to_nat(0u);
v___x_724_ = lean_nat_dec_eq(v___x_722_, v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v_encodedParams_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_725_ = lean_array_to_list(v_val_721_);
v___x_726_ = lean_box(0);
v_encodedParams_727_ = l_List_mapTR_loop___redArg(v___f_671_, v___x_725_, v___x_726_);
v___x_728_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9));
v___x_729_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10));
v___x_730_ = l_String_intercalate(v___x_729_, v_encodedParams_727_);
v___x_731_ = lean_string_append(v___x_728_, v___x_730_);
lean_dec_ref(v___x_730_);
v___x_732_ = lean_string_append(v___y_720_, v___x_731_);
lean_dec_ref(v___x_731_);
v___y_699_ = v___y_715_;
v___y_700_ = v___y_718_;
v___y_701_ = v___y_717_;
v___y_702_ = v___y_719_;
v___y_703_ = v___x_732_;
goto v___jp_698_;
}
else
{
lean_dec(v_val_721_);
v___y_699_ = v___y_715_;
v___y_700_ = v___y_718_;
v___y_701_ = v___y_717_;
v___y_702_ = v___y_719_;
v___y_703_ = v___y_720_;
goto v___jp_698_;
}
}
}
v___jp_733_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_743_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11));
v___x_744_ = lean_string_append(v___y_741_, v___x_743_);
v___x_745_ = lean_string_append(v___x_744_, v___y_734_);
lean_dec_ref(v___y_734_);
v___x_746_ = lean_string_append(v___x_745_, v___y_740_);
lean_dec_ref(v___y_740_);
v___x_747_ = lean_string_append(v___x_746_, v___y_739_);
lean_dec_ref(v___y_739_);
v___x_748_ = lean_string_append(v___x_747_, v___y_742_);
lean_dec_ref(v___y_742_);
v___y_699_ = v___y_735_;
v___y_700_ = v___y_737_;
v___y_701_ = v___y_736_;
v___y_702_ = v___y_738_;
v___y_703_ = v___x_748_;
goto v___jp_698_;
}
v___jp_749_:
{
if (lean_obj_tag(v___y_751_) == 0)
{
lean_object* v___x_759_; 
v___x_759_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5));
v___y_734_ = v___y_750_;
v___y_735_ = v___y_752_;
v___y_736_ = v___y_754_;
v___y_737_ = v___y_753_;
v___y_738_ = v___y_755_;
v___y_739_ = v___y_758_;
v___y_740_ = v___y_757_;
v___y_741_ = v___y_756_;
v___y_742_ = v___x_759_;
goto v___jp_733_;
}
else
{
lean_object* v_val_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v_val_760_ = lean_ctor_get(v___y_751_, 0);
lean_inc(v_val_760_);
lean_dec_ref(v___y_751_);
v___x_761_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12));
v___x_762_ = l_Std_Http_URI_EncodedFragment_encode(v_val_760_);
lean_dec(v_val_760_);
v___x_763_ = lean_string_from_utf8_unchecked(v___x_762_);
v___x_764_ = lean_string_append(v___x_761_, v___x_763_);
lean_dec_ref(v___x_763_);
v___y_734_ = v___y_750_;
v___y_735_ = v___y_752_;
v___y_736_ = v___y_754_;
v___y_737_ = v___y_753_;
v___y_738_ = v___y_755_;
v___y_739_ = v___y_758_;
v___y_740_ = v___y_757_;
v___y_741_ = v___y_756_;
v___y_742_ = v___x_764_;
goto v___jp_733_;
}
}
v___jp_765_:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_string_append(v___y_768_, v___y_766_);
lean_dec_ref(v___y_766_);
v___x_774_ = lean_string_append(v___x_773_, v___y_772_);
lean_dec_ref(v___y_772_);
v___y_699_ = v___y_767_;
v___y_700_ = v___y_770_;
v___y_701_ = v___y_769_;
v___y_702_ = v___y_771_;
v___y_703_ = v___x_774_;
goto v___jp_698_;
}
v___jp_775_:
{
switch(lean_obj_tag(v_port_781_))
{
case 0:
{
lean_object* v___x_783_; 
v___x_783_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5));
v___y_766_ = v___y_782_;
v___y_767_ = v___y_776_;
v___y_768_ = v___y_777_;
v___y_769_ = v___y_779_;
v___y_770_ = v___y_778_;
v___y_771_ = v___y_780_;
v___y_772_ = v___x_783_;
goto v___jp_765_;
}
case 1:
{
lean_object* v___x_784_; 
v___x_784_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11));
v___y_766_ = v___y_782_;
v___y_767_ = v___y_776_;
v___y_768_ = v___y_777_;
v___y_769_ = v___y_779_;
v___y_770_ = v___y_778_;
v___y_771_ = v___y_780_;
v___y_772_ = v___x_784_;
goto v___jp_765_;
}
default: 
{
uint16_t v_port_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v_port_785_ = lean_ctor_get_uint16(v_port_781_, 0);
lean_dec_ref(v_port_781_);
v___x_786_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11));
v___x_787_ = lean_uint16_to_nat(v_port_785_);
v___x_788_ = l_Nat_reprFast(v___x_787_);
v___x_789_ = lean_string_append(v___x_786_, v___x_788_);
lean_dec_ref(v___x_788_);
v___y_766_ = v___y_782_;
v___y_767_ = v___y_776_;
v___y_768_ = v___y_777_;
v___y_769_ = v___y_779_;
v___y_770_ = v___y_778_;
v___y_771_ = v___y_780_;
v___y_772_ = v___x_789_;
goto v___jp_765_;
}
}
}
v___jp_790_:
{
switch(lean_obj_tag(v_host_795_))
{
case 0:
{
lean_object* v_name_798_; 
v_name_798_ = lean_ctor_get(v_host_795_, 0);
lean_inc_ref(v_name_798_);
lean_dec_ref(v_host_795_);
v___y_776_ = v___y_791_;
v___y_777_ = v___y_797_;
v___y_778_ = v___y_793_;
v___y_779_ = v___y_792_;
v___y_780_ = v___y_794_;
v_port_781_ = v_port_796_;
v___y_782_ = v_name_798_;
goto v___jp_775_;
}
case 1:
{
lean_object* v_ipv4_799_; lean_object* v___x_800_; 
v_ipv4_799_ = lean_ctor_get(v_host_795_, 0);
lean_inc_ref(v_ipv4_799_);
lean_dec_ref(v_host_795_);
v___x_800_ = lean_uv_ntop_v4(v_ipv4_799_);
lean_dec_ref(v_ipv4_799_);
v___y_776_ = v___y_791_;
v___y_777_ = v___y_797_;
v___y_778_ = v___y_793_;
v___y_779_ = v___y_792_;
v___y_780_ = v___y_794_;
v_port_781_ = v_port_796_;
v___y_782_ = v___x_800_;
goto v___jp_775_;
}
default: 
{
lean_object* v_ipv6_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v_ipv6_801_ = lean_ctor_get(v_host_795_, 0);
lean_inc_ref(v_ipv6_801_);
lean_dec_ref(v_host_795_);
v___x_802_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__13));
v___x_803_ = lean_uv_ntop_v6(v_ipv6_801_);
lean_dec_ref(v_ipv6_801_);
v___x_804_ = lean_string_append(v___x_802_, v___x_803_);
lean_dec_ref(v___x_803_);
v___x_805_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14));
v___x_806_ = lean_string_append(v___x_804_, v___x_805_);
v___y_776_ = v___y_791_;
v___y_777_ = v___y_797_;
v___y_778_ = v___y_793_;
v___y_779_ = v___y_792_;
v___y_780_ = v___y_794_;
v_port_781_ = v_port_796_;
v___y_782_ = v___x_806_;
goto v___jp_775_;
}
}
}
v___jp_807_:
{
lean_object* v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_817_ = lean_array_get_size(v___y_810_);
v___x_818_ = lean_unsigned_to_nat(0u);
v___x_819_ = lean_nat_dec_eq(v___x_817_, v___x_818_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v_encodedParams_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_820_ = lean_array_to_list(v___y_810_);
v___x_821_ = lean_box(0);
v_encodedParams_822_ = l_List_mapTR_loop___redArg(v___f_671_, v___x_820_, v___x_821_);
v___x_823_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9));
v___x_824_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10));
v___x_825_ = l_String_intercalate(v___x_824_, v_encodedParams_822_);
v___x_826_ = lean_string_append(v___x_823_, v___x_825_);
lean_dec_ref(v___x_825_);
v___y_750_ = v___y_808_;
v___y_751_ = v___y_809_;
v___y_752_ = v___y_811_;
v___y_753_ = v___y_813_;
v___y_754_ = v___y_812_;
v___y_755_ = v___y_814_;
v___y_756_ = v___y_815_;
v___y_757_ = v___y_816_;
v___y_758_ = v___x_826_;
goto v___jp_749_;
}
else
{
lean_object* v___x_827_; 
lean_dec_ref(v___y_810_);
v___x_827_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5));
v___y_750_ = v___y_808_;
v___y_751_ = v___y_809_;
v___y_752_ = v___y_811_;
v___y_753_ = v___y_813_;
v___y_754_ = v___y_812_;
v___y_755_ = v___y_814_;
v___y_756_ = v___y_815_;
v___y_757_ = v___y_816_;
v___y_758_ = v___x_827_;
goto v___jp_749_;
}
}
v___jp_828_:
{
lean_object* v_segments_838_; uint8_t v_absolute_839_; lean_object* v___x_840_; lean_object* v___x_841_; size_t v_sz_842_; size_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v_result_846_; 
v_segments_838_ = lean_ctor_get(v___y_834_, 0);
lean_inc_ref(v_segments_838_);
v_absolute_839_ = lean_ctor_get_uint8(v___y_834_, sizeof(void*)*1);
lean_dec_ref(v___y_834_);
v___x_840_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15));
v___x_841_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25));
v_sz_842_ = lean_array_size(v_segments_838_);
v___x_843_ = ((size_t)0ULL);
v___x_844_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_841_, v___f_670_, v_sz_842_, v___x_843_, v_segments_838_);
v___x_845_ = lean_array_to_list(v___x_844_);
v_result_846_ = l_String_intercalate(v___x_840_, v___x_845_);
if (v_absolute_839_ == 0)
{
v___y_808_ = v___y_837_;
v___y_809_ = v___y_829_;
v___y_810_ = v___y_830_;
v___y_811_ = v___y_831_;
v___y_812_ = v___y_833_;
v___y_813_ = v___y_832_;
v___y_814_ = v___y_835_;
v___y_815_ = v___y_836_;
v___y_816_ = v_result_846_;
goto v___jp_807_;
}
else
{
lean_object* v___x_847_; 
v___x_847_ = lean_string_append(v___x_840_, v_result_846_);
lean_dec_ref(v_result_846_);
v___y_808_ = v___y_837_;
v___y_809_ = v___y_829_;
v___y_810_ = v___y_830_;
v___y_811_ = v___y_831_;
v___y_812_ = v___y_833_;
v___y_813_ = v___y_832_;
v___y_814_ = v___y_835_;
v___y_815_ = v___y_836_;
v___y_816_ = v___x_847_;
goto v___jp_807_;
}
}
v___jp_848_:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_861_ = lean_string_append(v___y_859_, v___y_858_);
lean_dec_ref(v___y_858_);
v___x_862_ = lean_string_append(v___x_861_, v___y_860_);
lean_dec_ref(v___y_860_);
lean_inc_ref(v___y_852_);
v___x_863_ = lean_string_append(v___y_852_, v___x_862_);
lean_dec_ref(v___x_862_);
v___y_829_ = v___y_849_;
v___y_830_ = v___y_850_;
v___y_831_ = v___y_851_;
v___y_832_ = v___y_854_;
v___y_833_ = v___y_853_;
v___y_834_ = v___y_856_;
v___y_835_ = v___y_855_;
v___y_836_ = v___y_857_;
v___y_837_ = v___x_863_;
goto v___jp_828_;
}
v___jp_864_:
{
switch(lean_obj_tag(v_port_869_))
{
case 0:
{
lean_object* v___x_877_; 
v___x_877_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5));
v___y_849_ = v___y_865_;
v___y_850_ = v___y_866_;
v___y_851_ = v___y_867_;
v___y_852_ = v___y_868_;
v___y_853_ = v___y_871_;
v___y_854_ = v___y_870_;
v___y_855_ = v___y_873_;
v___y_856_ = v___y_872_;
v___y_857_ = v___y_875_;
v___y_858_ = v___y_876_;
v___y_859_ = v___y_874_;
v___y_860_ = v___x_877_;
goto v___jp_848_;
}
case 1:
{
lean_object* v___x_878_; 
v___x_878_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11));
v___y_849_ = v___y_865_;
v___y_850_ = v___y_866_;
v___y_851_ = v___y_867_;
v___y_852_ = v___y_868_;
v___y_853_ = v___y_871_;
v___y_854_ = v___y_870_;
v___y_855_ = v___y_873_;
v___y_856_ = v___y_872_;
v___y_857_ = v___y_875_;
v___y_858_ = v___y_876_;
v___y_859_ = v___y_874_;
v___y_860_ = v___x_878_;
goto v___jp_848_;
}
default: 
{
uint16_t v_port_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v_port_879_ = lean_ctor_get_uint16(v_port_869_, 0);
lean_dec_ref(v_port_869_);
v___x_880_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11));
v___x_881_ = lean_uint16_to_nat(v_port_879_);
v___x_882_ = l_Nat_reprFast(v___x_881_);
v___x_883_ = lean_string_append(v___x_880_, v___x_882_);
lean_dec_ref(v___x_882_);
v___y_849_ = v___y_865_;
v___y_850_ = v___y_866_;
v___y_851_ = v___y_867_;
v___y_852_ = v___y_868_;
v___y_853_ = v___y_871_;
v___y_854_ = v___y_870_;
v___y_855_ = v___y_873_;
v___y_856_ = v___y_872_;
v___y_857_ = v___y_875_;
v___y_858_ = v___y_876_;
v___y_859_ = v___y_874_;
v___y_860_ = v___x_883_;
goto v___jp_848_;
}
}
}
v___jp_884_:
{
switch(lean_obj_tag(v_host_891_))
{
case 0:
{
lean_object* v_name_897_; 
v_name_897_ = lean_ctor_get(v_host_891_, 0);
lean_inc_ref(v_name_897_);
lean_dec_ref(v_host_891_);
v___y_865_ = v___y_885_;
v___y_866_ = v___y_886_;
v___y_867_ = v___y_887_;
v___y_868_ = v___y_888_;
v_port_869_ = v_port_892_;
v___y_870_ = v___y_890_;
v___y_871_ = v___y_889_;
v___y_872_ = v___y_894_;
v___y_873_ = v___y_893_;
v___y_874_ = v___y_896_;
v___y_875_ = v___y_895_;
v___y_876_ = v_name_897_;
goto v___jp_864_;
}
case 1:
{
lean_object* v_ipv4_898_; lean_object* v___x_899_; 
v_ipv4_898_ = lean_ctor_get(v_host_891_, 0);
lean_inc_ref(v_ipv4_898_);
lean_dec_ref(v_host_891_);
v___x_899_ = lean_uv_ntop_v4(v_ipv4_898_);
lean_dec_ref(v_ipv4_898_);
v___y_865_ = v___y_885_;
v___y_866_ = v___y_886_;
v___y_867_ = v___y_887_;
v___y_868_ = v___y_888_;
v_port_869_ = v_port_892_;
v___y_870_ = v___y_890_;
v___y_871_ = v___y_889_;
v___y_872_ = v___y_894_;
v___y_873_ = v___y_893_;
v___y_874_ = v___y_896_;
v___y_875_ = v___y_895_;
v___y_876_ = v___x_899_;
goto v___jp_864_;
}
default: 
{
lean_object* v_ipv6_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v_ipv6_900_ = lean_ctor_get(v_host_891_, 0);
lean_inc_ref(v_ipv6_900_);
lean_dec_ref(v_host_891_);
v___x_901_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__13));
v___x_902_ = lean_uv_ntop_v6(v_ipv6_900_);
lean_dec_ref(v_ipv6_900_);
v___x_903_ = lean_string_append(v___x_901_, v___x_902_);
lean_dec_ref(v___x_902_);
v___x_904_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14));
v___x_905_ = lean_string_append(v___x_903_, v___x_904_);
v___y_865_ = v___y_885_;
v___y_866_ = v___y_886_;
v___y_867_ = v___y_887_;
v___y_868_ = v___y_888_;
v_port_869_ = v_port_892_;
v___y_870_ = v___y_890_;
v___y_871_ = v___y_889_;
v___y_872_ = v___y_894_;
v___y_873_ = v___y_893_;
v___y_874_ = v___y_896_;
v___y_875_ = v___y_895_;
v___y_876_ = v___x_905_;
goto v___jp_864_;
}
}
}
v___jp_906_:
{
lean_object* v_data_908_; lean_object* v_size_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v_data_908_ = lean_ctor_get(v_buffer_664_, 0);
lean_inc_ref(v_data_908_);
v_size_909_ = lean_ctor_get(v_buffer_664_, 1);
lean_inc(v_size_909_);
lean_dec_ref(v_buffer_664_);
v___x_910_ = lean_string_to_utf8(v___y_907_);
lean_inc_ref(v___x_910_);
v___x_911_ = lean_array_push(v_data_908_, v___x_910_);
v___x_912_ = lean_byte_array_size(v___x_910_);
lean_dec_ref(v___x_910_);
v___x_913_ = lean_nat_add(v_size_909_, v___x_912_);
lean_dec(v_size_909_);
v___x_914_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27);
v___x_915_ = lean_array_push(v___x_911_, v___x_914_);
v___x_916_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28);
v___x_917_ = lean_nat_add(v___x_913_, v___x_916_);
lean_dec(v___x_913_);
switch(lean_obj_tag(v_uri_668_))
{
case 0:
{
lean_object* v_path_918_; lean_object* v_query_919_; lean_object* v_segments_920_; uint8_t v_absolute_921_; lean_object* v___x_922_; lean_object* v___x_923_; size_t v_sz_924_; size_t v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v_result_928_; 
v_path_918_ = lean_ctor_get(v_uri_668_, 0);
lean_inc_ref(v_path_918_);
v_query_919_ = lean_ctor_get(v_uri_668_, 1);
lean_inc(v_query_919_);
lean_dec_ref(v_uri_668_);
v_segments_920_ = lean_ctor_get(v_path_918_, 0);
lean_inc_ref(v_segments_920_);
v_absolute_921_ = lean_ctor_get_uint8(v_path_918_, sizeof(void*)*1);
lean_dec_ref(v_path_918_);
v___x_922_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15));
v___x_923_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25));
v_sz_924_ = lean_array_size(v_segments_920_);
v___x_925_ = ((size_t)0ULL);
v___x_926_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_923_, v___f_670_, v_sz_924_, v___x_925_, v_segments_920_);
v___x_927_ = lean_array_to_list(v___x_926_);
v_result_928_ = l_String_intercalate(v___x_922_, v___x_927_);
if (v_absolute_921_ == 0)
{
v___y_715_ = v___x_914_;
v___y_716_ = v_query_919_;
v___y_717_ = v___x_917_;
v___y_718_ = v___x_916_;
v___y_719_ = v___x_915_;
v___y_720_ = v_result_928_;
goto v___jp_714_;
}
else
{
lean_object* v___x_929_; 
v___x_929_ = lean_string_append(v___x_922_, v_result_928_);
lean_dec_ref(v_result_928_);
v___y_715_ = v___x_914_;
v___y_716_ = v_query_919_;
v___y_717_ = v___x_917_;
v___y_718_ = v___x_916_;
v___y_719_ = v___x_915_;
v___y_720_ = v___x_929_;
goto v___jp_714_;
}
}
case 1:
{
lean_object* v_uri_930_; lean_object* v_authority_931_; 
v_uri_930_ = lean_ctor_get(v_uri_668_, 0);
lean_inc_ref(v_uri_930_);
lean_dec_ref(v_uri_668_);
v_authority_931_ = lean_ctor_get(v_uri_930_, 1);
if (lean_obj_tag(v_authority_931_) == 0)
{
lean_object* v_scheme_932_; lean_object* v_path_933_; lean_object* v_query_934_; lean_object* v_fragment_935_; lean_object* v___x_936_; 
v_scheme_932_ = lean_ctor_get(v_uri_930_, 0);
lean_inc_ref(v_scheme_932_);
v_path_933_ = lean_ctor_get(v_uri_930_, 2);
lean_inc_ref(v_path_933_);
v_query_934_ = lean_ctor_get(v_uri_930_, 3);
lean_inc_ref(v_query_934_);
v_fragment_935_ = lean_ctor_get(v_uri_930_, 4);
lean_inc(v_fragment_935_);
lean_dec_ref(v_uri_930_);
v___x_936_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5));
v___y_829_ = v_fragment_935_;
v___y_830_ = v_query_934_;
v___y_831_ = v___x_914_;
v___y_832_ = v___x_916_;
v___y_833_ = v___x_917_;
v___y_834_ = v_path_933_;
v___y_835_ = v___x_915_;
v___y_836_ = v_scheme_932_;
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
lean_inc_ref(v_query_940_);
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
v___x_945_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29));
if (lean_obj_tag(v_userInfo_942_) == 0)
{
lean_object* v___x_946_; 
v___x_946_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5));
v___y_885_ = v_fragment_941_;
v___y_886_ = v_query_940_;
v___y_887_ = v___x_914_;
v___y_888_ = v___x_945_;
v___y_889_ = v___x_917_;
v___y_890_ = v___x_916_;
v_host_891_ = v_host_943_;
v_port_892_ = v_port_944_;
v___y_893_ = v___x_915_;
v___y_894_ = v_path_939_;
v___y_895_ = v_scheme_938_;
v___y_896_ = v___x_946_;
goto v___jp_884_;
}
else
{
lean_object* v_val_947_; lean_object* v_password_948_; 
v_val_947_ = lean_ctor_get(v_userInfo_942_, 0);
lean_inc(v_val_947_);
lean_dec_ref(v_userInfo_942_);
v_password_948_ = lean_ctor_get(v_val_947_, 1);
if (lean_obj_tag(v_password_948_) == 0)
{
lean_object* v_username_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v_username_949_ = lean_ctor_get(v_val_947_, 0);
lean_inc_ref(v_username_949_);
lean_dec(v_val_947_);
v___x_950_ = lean_string_from_utf8_unchecked(v_username_949_);
v___x_951_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30));
v___x_952_ = lean_string_append(v___x_950_, v___x_951_);
v___y_885_ = v_fragment_941_;
v___y_886_ = v_query_940_;
v___y_887_ = v___x_914_;
v___y_888_ = v___x_945_;
v___y_889_ = v___x_917_;
v___y_890_ = v___x_916_;
v_host_891_ = v_host_943_;
v_port_892_ = v_port_944_;
v___y_893_ = v___x_915_;
v___y_894_ = v_path_939_;
v___y_895_ = v_scheme_938_;
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
lean_dec_ref(v_password_948_);
v___x_955_ = lean_string_from_utf8_unchecked(v_username_953_);
v___x_956_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11));
v___x_957_ = lean_string_append(v___x_955_, v___x_956_);
v___x_958_ = lean_string_from_utf8_unchecked(v_val_954_);
v___x_959_ = lean_string_append(v___x_957_, v___x_958_);
lean_dec_ref(v___x_958_);
v___x_960_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30));
v___x_961_ = lean_string_append(v___x_959_, v___x_960_);
v___y_885_ = v_fragment_941_;
v___y_886_ = v_query_940_;
v___y_887_ = v___x_914_;
v___y_888_ = v___x_945_;
v___y_889_ = v___x_917_;
v___y_890_ = v___x_916_;
v_host_891_ = v_host_943_;
v_port_892_ = v_port_944_;
v___y_893_ = v___x_915_;
v___y_894_ = v_path_939_;
v___y_895_ = v_scheme_938_;
v___y_896_ = v___x_961_;
goto v___jp_884_;
}
}
}
}
case 2:
{
lean_object* v_authority_962_; lean_object* v_userInfo_963_; 
v_authority_962_ = lean_ctor_get(v_uri_668_, 0);
lean_inc_ref(v_authority_962_);
lean_dec_ref(v_uri_668_);
v_userInfo_963_ = lean_ctor_get(v_authority_962_, 0);
if (lean_obj_tag(v_userInfo_963_) == 0)
{
lean_object* v_host_964_; lean_object* v_port_965_; lean_object* v___x_966_; 
v_host_964_ = lean_ctor_get(v_authority_962_, 1);
lean_inc_ref(v_host_964_);
v_port_965_ = lean_ctor_get(v_authority_962_, 2);
lean_inc(v_port_965_);
lean_dec_ref(v_authority_962_);
v___x_966_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5));
v___y_791_ = v___x_914_;
v___y_792_ = v___x_917_;
v___y_793_ = v___x_916_;
v___y_794_ = v___x_915_;
v_host_795_ = v_host_964_;
v_port_796_ = v_port_965_;
v___y_797_ = v___x_966_;
goto v___jp_790_;
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
v___x_973_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30));
v___x_974_ = lean_string_append(v___x_972_, v___x_973_);
v___y_791_ = v___x_914_;
v___y_792_ = v___x_917_;
v___y_793_ = v___x_916_;
v___y_794_ = v___x_915_;
v_host_795_ = v_host_969_;
v_port_796_ = v_port_970_;
v___y_797_ = v___x_974_;
goto v___jp_790_;
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
lean_dec_ref(v_password_968_);
v___x_979_ = lean_string_from_utf8_unchecked(v_username_977_);
v___x_980_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11));
v___x_981_ = lean_string_append(v___x_979_, v___x_980_);
v___x_982_ = lean_string_from_utf8_unchecked(v_val_978_);
v___x_983_ = lean_string_append(v___x_981_, v___x_982_);
lean_dec_ref(v___x_982_);
v___x_984_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30));
v___x_985_ = lean_string_append(v___x_983_, v___x_984_);
v___y_791_ = v___x_914_;
v___y_792_ = v___x_917_;
v___y_793_ = v___x_916_;
v___y_794_ = v___x_915_;
v_host_795_ = v_host_975_;
v_port_796_ = v_port_976_;
v___y_797_ = v___x_985_;
goto v___jp_790_;
}
}
}
default: 
{
lean_object* v___x_986_; 
v___x_986_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31));
v___y_699_ = v___x_914_;
v___y_700_ = v___x_916_;
v___y_701_ = v___x_917_;
v___y_702_ = v___x_915_;
v___y_703_ = v___x_986_;
goto v___jp_698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(lean_object* v_buffer_1027_, lean_object* v_r_1028_){
_start:
{
lean_object* v_status_1029_; uint8_t v_version_1030_; lean_object* v_headers_1031_; lean_object* v___f_1032_; lean_object* v___y_1034_; 
v_status_1029_ = lean_ctor_get(v_r_1028_, 0);
v_version_1030_ = lean_ctor_get_uint8(v_r_1028_, sizeof(void*)*2);
v_headers_1031_ = lean_ctor_get(v_r_1028_, 1);
v___f_1032_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2));
switch(v_version_1030_)
{
case 0:
{
lean_object* v___x_1084_; 
v___x_1084_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5));
v___y_1034_ = v___x_1084_;
goto v___jp_1033_;
}
case 1:
{
lean_object* v___x_1085_; 
v___x_1085_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6));
v___y_1034_ = v___x_1085_;
goto v___jp_1033_;
}
case 2:
{
lean_object* v___x_1086_; 
v___x_1086_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7));
v___y_1034_ = v___x_1086_;
goto v___jp_1033_;
}
default: 
{
lean_object* v___x_1087_; 
v___x_1087_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___y_1034_ = v___x_1087_;
goto v___jp_1033_;
}
}
v___jp_1033_:
{
lean_object* v_data_1035_; lean_object* v_size_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1083_; 
v_data_1035_ = lean_ctor_get(v_buffer_1027_, 0);
v_size_1036_ = lean_ctor_get(v_buffer_1027_, 1);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_buffer_1027_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1038_ = v_buffer_1027_;
v_isShared_1039_ = v_isSharedCheck_1083_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_size_1036_);
lean_inc(v_data_1035_);
lean_dec(v_buffer_1027_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1083_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; uint16_t v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v_buffer_1069_; 
v___x_1040_ = lean_string_to_utf8(v___y_1034_);
lean_inc_ref(v___x_1040_);
v___x_1041_ = lean_array_push(v_data_1035_, v___x_1040_);
v___x_1042_ = lean_byte_array_size(v___x_1040_);
lean_dec_ref(v___x_1040_);
v___x_1043_ = lean_nat_add(v_size_1036_, v___x_1042_);
lean_dec(v_size_1036_);
v___x_1044_ = lean_unsigned_to_nat(1u);
v___x_1045_ = lean_mk_empty_array_with_capacity(v___x_1044_);
lean_dec_ref(v___x_1045_);
v___x_1046_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27);
v___x_1047_ = lean_array_push(v___x_1041_, v___x_1046_);
v___x_1048_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28);
v___x_1049_ = lean_nat_add(v___x_1043_, v___x_1048_);
lean_dec(v___x_1043_);
v___x_1050_ = l_Std_Http_Status_toCode(v_status_1029_);
v___x_1051_ = lean_uint16_to_nat(v___x_1050_);
v___x_1052_ = l_Nat_reprFast(v___x_1051_);
v___x_1053_ = lean_string_to_utf8(v___x_1052_);
lean_dec_ref(v___x_1052_);
lean_inc_ref(v___x_1053_);
v___x_1054_ = lean_array_push(v___x_1047_, v___x_1053_);
v___x_1055_ = lean_byte_array_size(v___x_1053_);
lean_dec_ref(v___x_1053_);
v___x_1056_ = lean_nat_add(v___x_1049_, v___x_1055_);
lean_dec(v___x_1049_);
v___x_1057_ = lean_array_push(v___x_1054_, v___x_1046_);
v___x_1058_ = lean_nat_add(v___x_1056_, v___x_1048_);
lean_dec(v___x_1056_);
v___x_1059_ = l_Std_Http_Status_reasonPhrase(v_status_1029_);
v___x_1060_ = lean_string_to_utf8(v___x_1059_);
lean_dec_ref(v___x_1059_);
lean_inc_ref(v___x_1060_);
v___x_1061_ = lean_array_push(v___x_1057_, v___x_1060_);
v___x_1062_ = lean_byte_array_size(v___x_1060_);
lean_dec_ref(v___x_1060_);
v___x_1063_ = lean_nat_add(v___x_1058_, v___x_1062_);
lean_dec(v___x_1058_);
v___x_1064_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3);
v___x_1065_ = lean_array_push(v___x_1061_, v___x_1064_);
v___x_1066_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4);
v___x_1067_ = lean_nat_add(v___x_1063_, v___x_1066_);
lean_dec(v___x_1063_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 1, v___x_1067_);
lean_ctor_set(v___x_1038_, 0, v___x_1065_);
v_buffer_1069_ = v___x_1038_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v___x_1067_);
v_buffer_1069_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
lean_object* v_buffer_1070_; lean_object* v_data_1071_; lean_object* v_size_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1081_; 
v_buffer_1070_ = l_Std_Http_Headers_fold___redArg(v_headers_1031_, v_buffer_1069_, v___f_1032_);
v_data_1071_ = lean_ctor_get(v_buffer_1070_, 0);
v_size_1072_ = lean_ctor_get(v_buffer_1070_, 1);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_buffer_1070_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1074_ = v_buffer_1070_;
v_isShared_1075_ = v_isSharedCheck_1081_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_size_1072_);
lean_inc(v_data_1071_);
lean_dec(v_buffer_1070_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1081_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1079_; 
v___x_1076_ = lean_array_push(v_data_1071_, v___x_1064_);
v___x_1077_ = lean_nat_add(v_size_1072_, v___x_1066_);
lean_dec(v_size_1072_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 1, v___x_1077_);
lean_ctor_set(v___x_1074_, 0, v___x_1076_);
v___x_1079_ = v___x_1074_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___boxed(lean_object* v_buffer_1088_, lean_object* v_r_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(v_buffer_1088_, v_r_1089_);
lean_dec_ref(v_r_1089_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head(uint8_t v_dir_1093_){
_start:
{
if (v_dir_1093_ == 0)
{
lean_object* v___x_1094_; 
v___x_1094_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___closed__0));
return v___x_1094_;
}
else
{
lean_object* v___x_1095_; 
v___x_1095_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___closed__1));
return v___x_1095_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___boxed(lean_object* v_dir_1096_){
_start:
{
uint8_t v_dir_boxed_1097_; lean_object* v_res_1098_; 
v_dir_boxed_1097_ = lean_unbox(v_dir_1096_);
v_res_1098_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v_dir_boxed_1097_);
return v_res_1098_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; uint8_t v___x_1102_; lean_object* v___x_1103_; 
v___x_1099_ = l_Std_Http_Headers_empty;
v___x_1100_ = lean_box(3);
v___x_1101_ = 1;
v___x_1102_ = 8;
v___x_1103_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1103_, 0, v___x_1100_);
lean_ctor_set(v___x_1103_, 1, v___x_1099_);
lean_ctor_set_uint8(v___x_1103_, sizeof(void*)*2, v___x_1102_);
lean_ctor_set_uint8(v___x_1103_, sizeof(void*)*2 + 1, v___x_1101_);
return v___x_1103_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1(void){
_start:
{
lean_object* v___x_1104_; uint8_t v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1104_ = l_Std_Http_Headers_empty;
v___x_1105_ = 1;
v___x_1106_ = lean_box(4);
v___x_1107_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
lean_ctor_set(v___x_1107_, 1, v___x_1104_);
lean_ctor_set_uint8(v___x_1107_, sizeof(void*)*2, v___x_1105_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead(uint8_t v_dir_1108_){
_start:
{
if (v_dir_1108_ == 0)
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0, &l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0_once, _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0);
return v___x_1109_;
}
else
{
lean_object* v___x_1110_; 
v___x_1110_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1, &l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1_once, _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1);
return v___x_1110_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead___boxed(lean_object* v_dir_1111_){
_start:
{
uint8_t v_dir_boxed_1112_; lean_object* v_res_1113_; 
v_dir_boxed_1112_ = lean_unbox(v_dir_1111_);
v_res_1113_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v_dir_boxed_1112_);
return v_res_1113_;
}
}
lean_object* runtime_initialize_Init_Data_Array(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Protocol_H1_Message(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___boxed__const__1 = _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___boxed__const__1();
lean_mark_persistent(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___boxed__const__1);
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
