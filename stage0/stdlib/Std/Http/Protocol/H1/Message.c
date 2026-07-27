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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(lean_object* v___x_149_, lean_object* v___x_150_, size_t v_sz_151_, size_t v_i_152_, lean_object* v_bs_153_){
_start:
{
uint8_t v___x_154_; 
v___x_154_ = lean_usize_dec_lt(v_i_152_, v_sz_151_);
if (v___x_154_ == 0)
{
return v_bs_153_;
}
else
{
lean_object* v_entries_155_; lean_object* v___x_156_; lean_object* v_bs_x27_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v_snd_161_; size_t v___x_162_; size_t v___x_163_; lean_object* v___x_164_; 
v_entries_155_ = lean_ctor_get(v___x_149_, 0);
v___x_156_ = lean_unsigned_to_nat(0u);
v_bs_x27_157_ = lean_array_uset(v_bs_153_, v_i_152_, v___x_156_);
v___x_158_ = lean_usize_to_nat(v_i_152_);
v___x_159_ = lean_array_fget_borrowed(v___x_150_, v___x_158_);
lean_dec(v___x_158_);
v___x_160_ = lean_array_fget_borrowed(v_entries_155_, v___x_159_);
v_snd_161_ = lean_ctor_get(v___x_160_, 1);
v___x_162_ = ((size_t)1ULL);
v___x_163_ = lean_usize_add(v_i_152_, v___x_162_);
lean_inc(v_snd_161_);
v___x_164_ = lean_array_uset(v_bs_x27_157_, v_i_152_, v_snd_161_);
v_i_152_ = v___x_163_;
v_bs_153_ = v___x_164_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg___boxed(lean_object* v___x_166_, lean_object* v___x_167_, lean_object* v_sz_168_, lean_object* v_i_169_, lean_object* v_bs_170_){
_start:
{
size_t v_sz_boxed_171_; size_t v_i_boxed_172_; lean_object* v_res_173_; 
v_sz_boxed_171_ = lean_unbox_usize(v_sz_168_);
lean_dec(v_sz_168_);
v_i_boxed_172_ = lean_unbox_usize(v_i_169_);
lean_dec(v_i_169_);
v_res_173_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_166_, v___x_167_, v_sz_boxed_171_, v_i_boxed_172_, v_bs_170_);
lean_dec_ref(v___x_167_);
lean_dec_ref(v___x_166_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize(uint8_t v_dir_182_, lean_object* v_message_183_, uint8_t v_allowEOFBody_184_){
_start:
{
lean_object* v___x_185_; lean_object* v___y_187_; lean_object* v___x_240_; lean_object* v___f_241_; lean_object* v___f_242_; uint8_t v___x_243_; 
v___x_185_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_182_, v_message_183_);
v___x_240_ = l_Std_Http_Header_Name_contentLength;
v___f_241_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0));
v___f_242_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1));
v___x_243_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_241_, v___f_242_, v___x_240_, v___x_185_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; 
v___x_244_ = lean_box(0);
v___y_187_ = v___x_244_;
goto v___jp_186_;
}
else
{
lean_object* v_indexes_245_; lean_object* v___x_246_; size_t v_sz_247_; size_t v___x_248_; lean_object* v_entries_249_; lean_object* v___x_250_; 
v_indexes_245_ = lean_ctor_get(v___x_185_, 1);
lean_inc_ref(v_indexes_245_);
v___x_246_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_245_, v___x_240_);
lean_dec_ref(v_indexes_245_);
v_sz_247_ = lean_array_size(v___x_246_);
v___x_248_ = ((size_t)0ULL);
lean_inc(v___x_246_);
v_entries_249_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_185_, v___x_246_, v_sz_247_, v___x_248_, v___x_246_);
lean_dec(v___x_246_);
v___x_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_250_, 0, v_entries_249_);
v___y_187_ = v___x_250_;
goto v___jp_186_;
}
v___jp_186_:
{
lean_object* v___x_188_; lean_object* v___f_189_; lean_object* v___f_190_; uint8_t v___x_191_; 
v___x_188_ = l_Std_Http_Header_Name_transferEncoding;
v___f_189_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0));
v___f_190_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1));
v___x_191_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_189_, v___f_190_, v___x_188_, v___x_185_);
if (v___x_191_ == 0)
{
lean_dec_ref(v___x_185_);
if (lean_obj_tag(v___y_187_) == 0)
{
if (v_allowEOFBody_184_ == 0)
{
lean_object* v___x_192_; 
v___x_192_ = lean_box(0);
return v___x_192_;
}
else
{
lean_object* v___x_193_; 
v___x_193_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__3));
return v___x_193_;
}
}
else
{
lean_object* v_val_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_217_; 
v_val_194_ = lean_ctor_get(v___y_187_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___y_187_);
if (v_isSharedCheck_217_ == 0)
{
v___x_196_ = v___y_187_;
v_isShared_197_ = v_isSharedCheck_217_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_val_194_);
lean_dec(v___y_187_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_217_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_198_ = lean_array_get_size(v_val_194_);
v___x_199_ = lean_unsigned_to_nat(1u);
v___x_200_ = lean_nat_dec_eq(v___x_198_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; 
lean_del_object(v___x_196_);
lean_dec(v_val_194_);
v___x_201_ = lean_box(0);
return v___x_201_;
}
else
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_202_ = lean_unsigned_to_nat(0u);
v___x_203_ = lean_array_fget(v_val_194_, v___x_202_);
lean_dec(v_val_194_);
v___x_204_ = l_Std_Http_Header_ContentLength_parse(v___x_203_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v___x_205_; 
lean_del_object(v___x_196_);
v___x_205_ = lean_box(0);
return v___x_205_;
}
else
{
lean_object* v_val_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_216_; 
v_val_206_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_216_ == 0)
{
v___x_208_ = v___x_204_;
v_isShared_209_ = v_isSharedCheck_216_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_val_206_);
lean_dec(v___x_204_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_216_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v_val_206_);
v___x_211_ = v___x_196_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_val_206_);
v___x_211_ = v_reuseFailAlloc_215_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_213_; 
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v___x_211_);
v___x_213_ = v___x_208_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
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
lean_object* v_indexes_218_; lean_object* v___x_219_; size_t v_sz_220_; size_t v___x_221_; lean_object* v_entries_222_; lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v_indexes_218_ = lean_ctor_get(v___x_185_, 1);
lean_inc_ref(v_indexes_218_);
v___x_219_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_218_, v___x_188_);
lean_dec_ref(v_indexes_218_);
v_sz_220_ = lean_array_size(v___x_219_);
v___x_221_ = ((size_t)0ULL);
lean_inc(v___x_219_);
v_entries_222_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_185_, v___x_219_, v_sz_220_, v___x_221_, v___x_219_);
lean_dec(v___x_219_);
lean_dec_ref(v___x_185_);
v___x_223_ = lean_array_get_size(v_entries_222_);
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = lean_nat_dec_eq(v___x_223_, v___x_224_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; 
lean_dec_ref(v_entries_222_);
lean_dec(v___y_187_);
v___x_226_ = lean_box(0);
return v___x_226_;
}
else
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v_te_229_; 
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = lean_array_fget(v_entries_222_, v___x_227_);
lean_dec_ref(v_entries_222_);
v_te_229_ = l_Std_Http_Header_TransferEncoding_parse(v___x_228_);
if (lean_obj_tag(v_te_229_) == 0)
{
lean_object* v___x_230_; 
lean_dec(v___y_187_);
v___x_230_ = lean_box(0);
return v___x_230_;
}
else
{
lean_object* v_val_231_; uint8_t v___x_232_; 
v_val_231_ = lean_ctor_get(v_te_229_, 0);
lean_inc(v_val_231_);
lean_dec_ref_known(v_te_229_, 1);
v___x_232_ = l_Std_Http_Header_TransferEncoding_isChunked(v_val_231_);
lean_dec(v_val_231_);
if (v___x_232_ == 1)
{
if (lean_obj_tag(v___y_187_) == 0)
{
uint8_t v___x_233_; uint8_t v___x_234_; uint8_t v___x_235_; 
v___x_233_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_182_, v_message_183_);
v___x_234_ = 0;
v___x_235_ = l_Std_Http_instBEqVersion_beq(v___x_233_, v___x_234_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; 
v___x_236_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__4));
return v___x_236_;
}
else
{
lean_object* v___x_237_; 
v___x_237_ = lean_box(0);
return v___x_237_;
}
}
else
{
lean_object* v___x_238_; 
lean_dec(v___y_187_);
v___x_238_ = lean_box(0);
return v___x_238_;
}
}
else
{
lean_object* v___x_239_; 
lean_dec(v___y_187_);
v___x_239_ = lean_box(0);
return v___x_239_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize___boxed(lean_object* v_dir_251_, lean_object* v_message_252_, lean_object* v_allowEOFBody_253_){
_start:
{
uint8_t v_dir_boxed_254_; uint8_t v_allowEOFBody_boxed_255_; lean_object* v_res_256_; 
v_dir_boxed_254_ = lean_unbox(v_dir_251_);
v_allowEOFBody_boxed_255_ = lean_unbox(v_allowEOFBody_253_);
v_res_256_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v_dir_boxed_254_, v_message_252_, v_allowEOFBody_boxed_255_);
lean_dec(v_message_252_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(lean_object* v_00_u03b2_257_, lean_object* v_m_258_, lean_object* v_a_259_, lean_object* v_hma_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_m_258_, v_a_259_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___boxed(lean_object* v_00_u03b2_262_, lean_object* v_m_263_, lean_object* v_a_264_, lean_object* v_hma_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(v_00_u03b2_262_, v_m_263_, v_a_264_, v_hma_265_);
lean_dec_ref(v_a_264_);
lean_dec_ref(v_m_263_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(lean_object* v___x_267_, lean_object* v___x_268_, lean_object* v_as_269_, size_t v_sz_270_, size_t v_i_271_, lean_object* v_bs_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_267_, v___x_268_, v_sz_270_, v_i_271_, v_bs_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___boxed(lean_object* v___x_274_, lean_object* v___x_275_, lean_object* v_as_276_, lean_object* v_sz_277_, lean_object* v_i_278_, lean_object* v_bs_279_){
_start:
{
size_t v_sz_boxed_280_; size_t v_i_boxed_281_; lean_object* v_res_282_; 
v_sz_boxed_280_ = lean_unbox_usize(v_sz_277_);
lean_dec(v_sz_277_);
v_i_boxed_281_ = lean_unbox_usize(v_i_278_);
lean_dec(v_i_278_);
v_res_282_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(v___x_274_, v___x_275_, v_as_276_, v_sz_boxed_280_, v_i_boxed_281_, v_bs_279_);
lean_dec_ref(v_as_276_);
lean_dec_ref(v___x_275_);
lean_dec_ref(v___x_274_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0(lean_object* v_00_u03b2_283_, lean_object* v_a_284_, lean_object* v_x_285_, lean_object* v_x_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_a_284_, v_x_285_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_288_, lean_object* v_a_289_, lean_object* v_x_290_, lean_object* v_x_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0(v_00_u03b2_288_, v_a_289_, v_x_290_, v_x_291_);
lean_dec(v_x_290_);
lean_dec_ref(v_a_289_);
return v_res_292_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(lean_object* v_as_294_, size_t v_i_295_, size_t v_stop_296_){
_start:
{
uint8_t v___x_297_; 
v___x_297_ = lean_usize_dec_eq(v_i_295_, v_stop_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_298_ = lean_array_uget_borrowed(v_as_294_, v_i_295_);
v___x_299_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___closed__0));
v___x_300_ = lean_string_dec_eq(v___x_298_, v___x_299_);
if (v___x_300_ == 0)
{
size_t v___x_301_; size_t v___x_302_; 
v___x_301_ = ((size_t)1ULL);
v___x_302_ = lean_usize_add(v_i_295_, v___x_301_);
v_i_295_ = v___x_302_;
goto _start;
}
else
{
return v___x_300_;
}
}
else
{
uint8_t v___x_304_; 
v___x_304_ = 0;
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___boxed(lean_object* v_as_305_, lean_object* v_i_306_, lean_object* v_stop_307_){
_start:
{
size_t v_i_boxed_308_; size_t v_stop_boxed_309_; uint8_t v_res_310_; lean_object* v_r_311_; 
v_i_boxed_308_ = lean_unbox_usize(v_i_306_);
lean_dec(v_i_306_);
v_stop_boxed_309_ = lean_unbox_usize(v_stop_307_);
lean_dec(v_stop_307_);
v_res_310_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(v_as_305_, v_i_boxed_308_, v_stop_boxed_309_);
lean_dec_ref(v_as_305_);
v_r_311_ = lean_box(v_res_310_);
return v_r_311_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(lean_object* v_as_313_, size_t v_i_314_, size_t v_stop_315_){
_start:
{
uint8_t v___x_316_; 
v___x_316_ = lean_usize_dec_eq(v_i_314_, v_stop_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_317_ = lean_array_uget_borrowed(v_as_313_, v_i_314_);
v___x_318_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___closed__0));
v___x_319_ = lean_string_dec_eq(v___x_317_, v___x_318_);
if (v___x_319_ == 0)
{
size_t v___x_320_; size_t v___x_321_; 
v___x_320_ = ((size_t)1ULL);
v___x_321_ = lean_usize_add(v_i_314_, v___x_320_);
v_i_314_ = v___x_321_;
goto _start;
}
else
{
return v___x_319_;
}
}
else
{
uint8_t v___x_323_; 
v___x_323_ = 0;
return v___x_323_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___boxed(lean_object* v_as_324_, lean_object* v_i_325_, lean_object* v_stop_326_){
_start:
{
size_t v_i_boxed_327_; size_t v_stop_boxed_328_; uint8_t v_res_329_; lean_object* v_r_330_; 
v_i_boxed_327_ = lean_unbox_usize(v_i_325_);
lean_dec(v_i_325_);
v_stop_boxed_328_ = lean_unbox_usize(v_stop_326_);
lean_dec(v_stop_326_);
v_res_329_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(v_as_324_, v_i_boxed_327_, v_stop_boxed_328_);
lean_dec_ref(v_as_324_);
v_r_330_ = lean_box(v_res_329_);
return v_r_330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(lean_object* v_as_331_, size_t v_i_332_, size_t v_stop_333_, lean_object* v_b_334_){
_start:
{
lean_object* v___y_336_; uint8_t v___x_340_; 
v___x_340_ = lean_usize_dec_eq(v_i_332_, v_stop_333_);
if (v___x_340_ == 0)
{
if (lean_obj_tag(v_b_334_) == 0)
{
v___y_336_ = v_b_334_;
goto v___jp_335_;
}
else
{
lean_object* v_val_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v_val_341_ = lean_ctor_get(v_b_334_, 0);
lean_inc(v_val_341_);
lean_dec_ref_known(v_b_334_, 1);
v___x_342_ = lean_array_uget_borrowed(v_as_331_, v_i_332_);
lean_inc(v___x_342_);
v___x_343_ = l_Std_Http_Header_Connection_parse(v___x_342_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v___x_344_; 
lean_dec(v_val_341_);
v___x_344_ = lean_box(0);
v___y_336_ = v___x_344_;
goto v___jp_335_;
}
else
{
lean_object* v_val_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_353_; 
v_val_345_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_353_ == 0)
{
v___x_347_ = v___x_343_;
v_isShared_348_ = v_isSharedCheck_353_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_val_345_);
lean_dec(v___x_343_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_353_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v___x_351_; 
v___x_349_ = l_Array_append___redArg(v_val_341_, v_val_345_);
lean_dec(v_val_345_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 0, v___x_349_);
v___x_351_ = v___x_347_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_349_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
v___y_336_ = v___x_351_;
goto v___jp_335_;
}
}
}
}
}
else
{
return v_b_334_;
}
v___jp_335_:
{
size_t v___x_337_; size_t v___x_338_; 
v___x_337_ = ((size_t)1ULL);
v___x_338_ = lean_usize_add(v_i_332_, v___x_337_);
v_i_332_ = v___x_338_;
v_b_334_ = v___y_336_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2___boxed(lean_object* v_as_354_, lean_object* v_i_355_, lean_object* v_stop_356_, lean_object* v_b_357_){
_start:
{
size_t v_i_boxed_358_; size_t v_stop_boxed_359_; lean_object* v_res_360_; 
v_i_boxed_358_ = lean_unbox_usize(v_i_355_);
lean_dec(v_i_355_);
v_stop_boxed_359_ = lean_unbox_usize(v_stop_356_);
lean_dec(v_stop_356_);
v_res_360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_as_354_, v_i_boxed_358_, v_stop_boxed_359_, v_b_357_);
lean_dec_ref(v_as_354_);
return v_res_360_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(uint8_t v_dir_365_, lean_object* v_message_366_){
_start:
{
lean_object* v_val_368_; lean_object* v___y_386_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___f_391_; lean_object* v___f_392_; uint8_t v___x_393_; 
v___x_389_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_365_, v_message_366_);
v___x_390_ = l_Std_Http_Header_Name_connection;
v___f_391_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0));
v___f_392_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1));
v___x_393_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_391_, v___f_392_, v___x_390_, v___x_389_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; 
lean_dec_ref(v___x_389_);
v___x_394_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0));
v_val_368_ = v___x_394_;
goto v___jp_367_;
}
else
{
lean_object* v_indexes_395_; lean_object* v___x_396_; size_t v_sz_397_; size_t v___x_398_; lean_object* v_entries_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; uint8_t v___x_403_; 
v_indexes_395_ = lean_ctor_get(v___x_389_, 1);
lean_inc_ref(v_indexes_395_);
v___x_396_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_395_, v___x_390_);
lean_dec_ref(v_indexes_395_);
v_sz_397_ = lean_array_size(v___x_396_);
v___x_398_ = ((size_t)0ULL);
lean_inc(v___x_396_);
v_entries_399_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_389_, v___x_396_, v_sz_397_, v___x_398_, v___x_396_);
lean_dec(v___x_396_);
lean_dec_ref(v___x_389_);
v___x_400_ = lean_unsigned_to_nat(0u);
v___x_401_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0));
v___x_402_ = lean_array_get_size(v_entries_399_);
v___x_403_ = lean_nat_dec_lt(v___x_400_, v___x_402_);
if (v___x_403_ == 0)
{
lean_dec_ref(v_entries_399_);
v_val_368_ = v___x_401_;
goto v___jp_367_;
}
else
{
lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_404_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__1));
v___x_405_ = lean_nat_dec_le(v___x_402_, v___x_402_);
if (v___x_405_ == 0)
{
if (v___x_403_ == 0)
{
lean_dec_ref(v_entries_399_);
v_val_368_ = v___x_401_;
goto v___jp_367_;
}
else
{
size_t v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_usize_of_nat(v___x_402_);
v___x_407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_entries_399_, v___x_398_, v___x_406_, v___x_404_);
lean_dec_ref(v_entries_399_);
v___y_386_ = v___x_407_;
goto v___jp_385_;
}
}
else
{
size_t v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_usize_of_nat(v___x_402_);
v___x_409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_entries_399_, v___x_398_, v___x_408_, v___x_404_);
lean_dec_ref(v_entries_399_);
v___y_386_ = v___x_409_;
goto v___jp_385_;
}
}
}
v___jp_367_:
{
uint8_t v___x_369_; uint8_t v___x_370_; uint8_t v___x_371_; 
v___x_369_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_365_, v_message_366_);
v___x_370_ = 1;
v___x_371_ = l_Std_Http_instBEqVersion_beq(v___x_369_, v___x_370_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_372_ = lean_unsigned_to_nat(0u);
v___x_373_ = lean_array_get_size(v_val_368_);
v___x_374_ = lean_nat_dec_lt(v___x_372_, v___x_373_);
if (v___x_374_ == 0)
{
lean_dec_ref(v_val_368_);
return v___x_371_;
}
else
{
if (v___x_374_ == 0)
{
lean_dec_ref(v_val_368_);
return v___x_371_;
}
else
{
size_t v___x_375_; size_t v___x_376_; uint8_t v___x_377_; 
v___x_375_ = ((size_t)0ULL);
v___x_376_ = lean_usize_of_nat(v___x_373_);
v___x_377_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(v_val_368_, v___x_375_, v___x_376_);
lean_dec_ref(v_val_368_);
return v___x_377_;
}
}
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_378_ = lean_unsigned_to_nat(0u);
v___x_379_ = lean_array_get_size(v_val_368_);
v___x_380_ = lean_nat_dec_lt(v___x_378_, v___x_379_);
if (v___x_380_ == 0)
{
lean_dec_ref(v_val_368_);
return v___x_371_;
}
else
{
if (v___x_380_ == 0)
{
lean_dec_ref(v_val_368_);
return v___x_371_;
}
else
{
size_t v___x_381_; size_t v___x_382_; uint8_t v___x_383_; 
v___x_381_ = ((size_t)0ULL);
v___x_382_ = lean_usize_of_nat(v___x_379_);
v___x_383_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(v_val_368_, v___x_381_, v___x_382_);
lean_dec_ref(v_val_368_);
if (v___x_383_ == 0)
{
return v___x_371_;
}
else
{
uint8_t v___x_384_; 
v___x_384_ = 0;
return v___x_384_;
}
}
}
}
}
v___jp_385_:
{
if (lean_obj_tag(v___y_386_) == 0)
{
uint8_t v___x_387_; 
v___x_387_ = 0;
return v___x_387_;
}
else
{
lean_object* v_val_388_; 
v_val_388_ = lean_ctor_get(v___y_386_, 0);
lean_inc(v_val_388_);
lean_dec_ref_known(v___y_386_, 1);
v_val_368_ = v_val_388_;
goto v___jp_367_;
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1(lean_object* v___x_441_, lean_object* v___x_442_, lean_object* v___x_443_, lean_object* v_name_444_, lean_object* v___x_445_, uint32_t v___x_446_, lean_object* v___x_447_, lean_object* v_it_448_, lean_object* v_acc_449_, lean_object* v_hP_450_, lean_object* v_recur_451_){
_start:
{
lean_object* v_it_453_; lean_object* v_out_454_; lean_object* v_it_470_; lean_object* v_startInclusive_471_; lean_object* v_endExclusive_472_; 
if (lean_obj_tag(v_it_448_) == 0)
{
lean_object* v_currPos_484_; lean_object* v_searcher_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_507_; 
v_currPos_484_ = lean_ctor_get(v_it_448_, 0);
v_searcher_485_ = lean_ctor_get(v_it_448_, 1);
v_isSharedCheck_507_ = !lean_is_exclusive(v_it_448_);
if (v_isSharedCheck_507_ == 0)
{
v___x_487_ = v_it_448_;
v_isShared_488_ = v_isSharedCheck_507_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_searcher_485_);
lean_inc(v_currPos_484_);
lean_dec(v_it_448_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_507_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
uint8_t v___x_489_; 
v___x_489_ = lean_nat_dec_eq(v_searcher_485_, v___x_445_);
if (v___x_489_ == 0)
{
uint32_t v___x_490_; uint8_t v___x_491_; 
lean_dec(v___x_445_);
v___x_490_ = lean_string_utf8_get_fast(v_name_444_, v_searcher_485_);
v___x_491_ = lean_uint32_dec_eq(v___x_490_, v___x_446_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_494_; 
v___x_492_ = lean_string_utf8_next_fast(v_name_444_, v_searcher_485_);
lean_dec(v_searcher_485_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 1, v___x_492_);
v___x_494_ = v___x_487_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_currPos_484_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v___x_492_);
v___x_494_ = v_reuseFailAlloc_496_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
lean_object* v___x_495_; 
v___x_495_ = lean_apply_4(v_recur_451_, v___x_494_, v_acc_449_, lean_box(0), lean_box(0));
return v___x_495_;
}
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v_slice_500_; lean_object* v_nextIt_502_; 
v___x_497_ = lean_string_utf8_next_fast(v_name_444_, v_searcher_485_);
v___x_498_ = lean_nat_sub(v___x_497_, v_searcher_485_);
v___x_499_ = lean_nat_add(v_searcher_485_, v___x_498_);
lean_dec(v___x_498_);
v_slice_500_ = l_String_Slice_subslice_x21(v___x_447_, v_currPos_484_, v_searcher_485_);
lean_inc(v___x_499_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 1, v___x_499_);
lean_ctor_set(v___x_487_, 0, v___x_499_);
v_nextIt_502_ = v___x_487_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_499_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v___x_499_);
v_nextIt_502_ = v_reuseFailAlloc_505_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v_startInclusive_503_; lean_object* v_endExclusive_504_; 
v_startInclusive_503_ = lean_ctor_get(v_slice_500_, 0);
lean_inc(v_startInclusive_503_);
v_endExclusive_504_ = lean_ctor_get(v_slice_500_, 1);
lean_inc(v_endExclusive_504_);
lean_dec_ref(v_slice_500_);
v_it_470_ = v_nextIt_502_;
v_startInclusive_471_ = v_startInclusive_503_;
v_endExclusive_472_ = v_endExclusive_504_;
goto v___jp_469_;
}
}
}
else
{
lean_object* v___x_506_; 
lean_del_object(v___x_487_);
lean_dec(v_searcher_485_);
v___x_506_ = lean_box(1);
v_it_470_ = v___x_506_;
v_startInclusive_471_ = v_currPos_484_;
v_endExclusive_472_ = v___x_445_;
goto v___jp_469_;
}
}
}
else
{
lean_dec_ref(v_recur_451_);
lean_dec(v___x_445_);
return v_acc_449_;
}
v___jp_452_:
{
if (lean_obj_tag(v_acc_449_) == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_455_, 0, v_out_454_);
v___x_456_ = lean_apply_4(v_recur_451_, v_it_453_, v___x_455_, lean_box(0), lean_box(0));
return v___x_456_;
}
else
{
lean_object* v_val_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_468_; 
v_val_457_ = lean_ctor_get(v_acc_449_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v_acc_449_);
if (v_isSharedCheck_468_ == 0)
{
v___x_459_ = v_acc_449_;
v_isShared_460_ = v_isSharedCheck_468_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_val_457_);
lean_dec(v_acc_449_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_468_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_461_ = lean_string_utf8_extract(v___x_441_, v___x_442_, v___x_443_);
v___x_462_ = lean_string_append(v_val_457_, v___x_461_);
lean_dec_ref(v___x_461_);
v___x_463_ = lean_string_append(v___x_462_, v_out_454_);
lean_dec_ref(v_out_454_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v___x_463_);
v___x_465_ = v___x_459_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_463_);
v___x_465_ = v_reuseFailAlloc_467_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_466_; 
v___x_466_ = lean_apply_4(v_recur_451_, v_it_453_, v___x_465_, lean_box(0), lean_box(0));
return v___x_466_;
}
}
}
}
v___jp_469_:
{
lean_object* v___x_473_; uint32_t v___x_474_; uint32_t v___x_475_; uint8_t v___x_476_; 
v___x_473_ = lean_string_utf8_extract(v_name_444_, v_startInclusive_471_, v_endExclusive_472_);
lean_dec(v_endExclusive_472_);
lean_dec(v_startInclusive_471_);
v___x_474_ = lean_string_utf8_get(v___x_473_, v___x_442_);
v___x_475_ = 97;
v___x_476_ = lean_uint32_dec_le(v___x_475_, v___x_474_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; 
v___x_477_ = lean_string_utf8_set(v___x_473_, v___x_442_, v___x_474_);
v_it_453_ = v_it_470_;
v_out_454_ = v___x_477_;
goto v___jp_452_;
}
else
{
uint32_t v___x_478_; uint8_t v___x_479_; 
v___x_478_ = 122;
v___x_479_ = lean_uint32_dec_le(v___x_474_, v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; 
v___x_480_ = lean_string_utf8_set(v___x_473_, v___x_442_, v___x_474_);
v_it_453_ = v_it_470_;
v_out_454_ = v___x_480_;
goto v___jp_452_;
}
else
{
uint32_t v___x_481_; uint32_t v___x_482_; lean_object* v___x_483_; 
v___x_481_ = 4294967264;
v___x_482_ = lean_uint32_add(v___x_474_, v___x_481_);
v___x_483_ = lean_string_utf8_set(v___x_473_, v___x_442_, v___x_482_);
v_it_453_ = v_it_470_;
v_out_454_ = v___x_483_;
goto v___jp_452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1___boxed(lean_object* v___x_508_, lean_object* v___x_509_, lean_object* v___x_510_, lean_object* v_name_511_, lean_object* v___x_512_, lean_object* v___x_513_, lean_object* v___x_514_, lean_object* v_it_515_, lean_object* v_acc_516_, lean_object* v_hP_517_, lean_object* v_recur_518_){
_start:
{
uint32_t v___x_2699__boxed_519_; lean_object* v_res_520_; 
v___x_2699__boxed_519_ = lean_unbox_uint32(v___x_513_);
lean_dec(v___x_513_);
v_res_520_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1(v___x_508_, v___x_509_, v___x_510_, v_name_511_, v___x_512_, v___x_2699__boxed_519_, v___x_514_, v_it_515_, v_acc_516_, v_hP_517_, v_recur_518_);
lean_dec_ref(v___x_514_);
lean_dec_ref(v_name_511_);
lean_dec(v___x_510_);
lean_dec(v___x_509_);
lean_dec_ref(v___x_508_);
return v_res_520_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4(void){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__3));
v___x_526_ = lean_string_utf8_byte_size(v___x_525_);
return v___x_526_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed__const__1(void){
_start:
{
uint32_t v___x_528_; lean_object* v___x_529_; 
v___x_528_ = 45;
v___x_529_ = lean_box_uint32(v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2(lean_object* v_buf_530_, lean_object* v_name_531_, lean_object* v_value_532_){
_start:
{
lean_object* v___y_534_; lean_object* v___f_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v_it_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___f_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___f_553_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__2));
v___x_554_ = lean_unsigned_to_nat(0u);
v___x_555_ = lean_string_utf8_byte_size(v_name_531_);
lean_inc_ref(v_name_531_);
v___x_556_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_556_, 0, v_name_531_);
lean_ctor_set(v___x_556_, 1, v___x_554_);
lean_ctor_set(v___x_556_, 2, v___x_555_);
lean_inc_ref(v___x_556_);
v_it_557_ = l_String_Slice_splitToSubslice___redArg(v___x_556_, v___f_553_);
v___x_558_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__3));
v___x_559_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__4);
v___x_560_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed__const__1;
v___f_561_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1___boxed), 11, 7);
lean_closure_set(v___f_561_, 0, v___x_558_);
lean_closure_set(v___f_561_, 1, v___x_554_);
lean_closure_set(v___f_561_, 2, v___x_559_);
lean_closure_set(v___f_561_, 3, v_name_531_);
lean_closure_set(v___f_561_, 4, v___x_555_);
lean_closure_set(v___f_561_, 5, v___x_560_);
lean_closure_set(v___f_561_, 6, v___x_556_);
v___x_562_ = lean_box(0);
v___x_563_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_561_, v_it_557_, v___x_562_, lean_box(0));
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v___x_564_; 
v___x_564_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_534_ = v___x_564_;
goto v___jp_533_;
}
else
{
lean_object* v_val_565_; 
v_val_565_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_val_565_);
lean_dec_ref_known(v___x_563_, 1);
v___y_534_ = v_val_565_;
goto v___jp_533_;
}
v___jp_533_:
{
lean_object* v_data_535_; lean_object* v_size_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_552_; 
v_data_535_ = lean_ctor_get(v_buf_530_, 0);
v_size_536_ = lean_ctor_get(v_buf_530_, 1);
v_isSharedCheck_552_ = !lean_is_exclusive(v_buf_530_);
if (v_isSharedCheck_552_ == 0)
{
v___x_538_ = v_buf_530_;
v_isShared_539_ = v_isSharedCheck_552_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_size_536_);
lean_inc(v_data_535_);
lean_dec(v_buf_530_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_552_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_540_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__0));
v___x_541_ = lean_string_append(v___y_534_, v___x_540_);
v___x_542_ = lean_string_append(v___x_541_, v_value_532_);
v___x_543_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__1));
v___x_544_ = lean_string_append(v___x_542_, v___x_543_);
v___x_545_ = lean_string_to_utf8(v___x_544_);
lean_dec_ref(v___x_544_);
lean_inc_ref(v___x_545_);
v___x_546_ = lean_array_push(v_data_535_, v___x_545_);
v___x_547_ = lean_byte_array_size(v___x_545_);
lean_dec_ref(v___x_545_);
v___x_548_ = lean_nat_add(v_size_536_, v___x_547_);
lean_dec(v_size_536_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 1, v___x_548_);
lean_ctor_set(v___x_538_, 0, v___x_546_);
v___x_550_ = v___x_538_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed(lean_object* v_buf_566_, lean_object* v_name_567_, lean_object* v_value_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2(v_buf_566_, v_name_567_, v_value_568_);
lean_dec_ref(v_value_568_);
return v_res_569_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__1));
v___x_573_ = lean_string_to_utf8(v___x_572_);
return v___x_573_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_575_ = lean_byte_array_size(v___x_574_);
return v___x_575_;
}
}
static uint8_t _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23(void){
_start:
{
uint32_t v___x_604_; uint8_t v___x_605_; 
v___x_604_ = 32;
v___x_605_ = lean_uint32_to_uint8(v___x_604_);
return v___x_605_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24(void){
_start:
{
uint8_t v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_606_ = lean_uint8_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23);
v___x_607_ = lean_unsigned_to_nat(1u);
v___x_608_ = lean_mk_empty_array_with_capacity(v___x_607_);
v___x_609_ = lean_box(v___x_606_);
v___x_610_ = lean_array_push(v___x_608_, v___x_609_);
v___x_611_ = lean_byte_array_mk(v___x_610_);
return v___x_611_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24);
v___x_613_ = lean_byte_array_size(v___x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1(lean_object* v_buffer_657_, lean_object* v_req_658_){
_start:
{
uint8_t v_method_659_; uint8_t v_version_660_; lean_object* v_uri_661_; lean_object* v_headers_662_; lean_object* v___f_663_; lean_object* v___f_664_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v_port_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v_host_735_; lean_object* v_port_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v_port_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v_host_856_; lean_object* v_port_857_; lean_object* v___y_858_; lean_object* v___y_869_; 
v_method_659_ = lean_ctor_get_uint8(v_req_658_, sizeof(void*)*2);
v_version_660_ = lean_ctor_get_uint8(v_req_658_, sizeof(void*)*2 + 1);
v_uri_661_ = lean_ctor_get(v_req_658_, 0);
lean_inc(v_uri_661_);
v_headers_662_ = lean_ctor_get(v_req_658_, 1);
lean_inc_ref(v_headers_662_);
lean_dec_ref(v_req_658_);
v___f_663_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__0));
v___f_664_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1));
switch(v_method_659_)
{
case 0:
{
lean_object* v___x_949_; 
v___x_949_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29));
v___y_869_ = v___x_949_;
goto v___jp_868_;
}
case 1:
{
lean_object* v___x_950_; 
v___x_950_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30));
v___y_869_ = v___x_950_;
goto v___jp_868_;
}
case 2:
{
lean_object* v___x_951_; 
v___x_951_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31));
v___y_869_ = v___x_951_;
goto v___jp_868_;
}
case 3:
{
lean_object* v___x_952_; 
v___x_952_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32));
v___y_869_ = v___x_952_;
goto v___jp_868_;
}
case 4:
{
lean_object* v___x_953_; 
v___x_953_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33));
v___y_869_ = v___x_953_;
goto v___jp_868_;
}
case 5:
{
lean_object* v___x_954_; 
v___x_954_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34));
v___y_869_ = v___x_954_;
goto v___jp_868_;
}
case 6:
{
lean_object* v___x_955_; 
v___x_955_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35));
v___y_869_ = v___x_955_;
goto v___jp_868_;
}
case 7:
{
lean_object* v___x_956_; 
v___x_956_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36));
v___y_869_ = v___x_956_;
goto v___jp_868_;
}
case 8:
{
lean_object* v___x_957_; 
v___x_957_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37));
v___y_869_ = v___x_957_;
goto v___jp_868_;
}
case 9:
{
lean_object* v___x_958_; 
v___x_958_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38));
v___y_869_ = v___x_958_;
goto v___jp_868_;
}
case 10:
{
lean_object* v___x_959_; 
v___x_959_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39));
v___y_869_ = v___x_959_;
goto v___jp_868_;
}
case 11:
{
lean_object* v___x_960_; 
v___x_960_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40));
v___y_869_ = v___x_960_;
goto v___jp_868_;
}
case 12:
{
lean_object* v___x_961_; 
v___x_961_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41));
v___y_869_ = v___x_961_;
goto v___jp_868_;
}
case 13:
{
lean_object* v___x_962_; 
v___x_962_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42));
v___y_869_ = v___x_962_;
goto v___jp_868_;
}
case 14:
{
lean_object* v___x_963_; 
v___x_963_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43));
v___y_869_ = v___x_963_;
goto v___jp_868_;
}
case 15:
{
lean_object* v___x_964_; 
v___x_964_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44));
v___y_869_ = v___x_964_;
goto v___jp_868_;
}
case 16:
{
lean_object* v___x_965_; 
v___x_965_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45));
v___y_869_ = v___x_965_;
goto v___jp_868_;
}
case 17:
{
lean_object* v___x_966_; 
v___x_966_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46));
v___y_869_ = v___x_966_;
goto v___jp_868_;
}
case 18:
{
lean_object* v___x_967_; 
v___x_967_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47));
v___y_869_ = v___x_967_;
goto v___jp_868_;
}
case 19:
{
lean_object* v___x_968_; 
v___x_968_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48));
v___y_869_ = v___x_968_;
goto v___jp_868_;
}
case 20:
{
lean_object* v___x_969_; 
v___x_969_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49));
v___y_869_ = v___x_969_;
goto v___jp_868_;
}
case 21:
{
lean_object* v___x_970_; 
v___x_970_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50));
v___y_869_ = v___x_970_;
goto v___jp_868_;
}
case 22:
{
lean_object* v___x_971_; 
v___x_971_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51));
v___y_869_ = v___x_971_;
goto v___jp_868_;
}
case 23:
{
lean_object* v___x_972_; 
v___x_972_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52));
v___y_869_ = v___x_972_;
goto v___jp_868_;
}
case 24:
{
lean_object* v___x_973_; 
v___x_973_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53));
v___y_869_ = v___x_973_;
goto v___jp_868_;
}
case 25:
{
lean_object* v___x_974_; 
v___x_974_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54));
v___y_869_ = v___x_974_;
goto v___jp_868_;
}
case 26:
{
lean_object* v___x_975_; 
v___x_975_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55));
v___y_869_ = v___x_975_;
goto v___jp_868_;
}
case 27:
{
lean_object* v___x_976_; 
v___x_976_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56));
v___y_869_ = v___x_976_;
goto v___jp_868_;
}
case 28:
{
lean_object* v___x_977_; 
v___x_977_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57));
v___y_869_ = v___x_977_;
goto v___jp_868_;
}
case 29:
{
lean_object* v___x_978_; 
v___x_978_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58));
v___y_869_ = v___x_978_;
goto v___jp_868_;
}
case 30:
{
lean_object* v___x_979_; 
v___x_979_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59));
v___y_869_ = v___x_979_;
goto v___jp_868_;
}
case 31:
{
lean_object* v___x_980_; 
v___x_980_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60));
v___y_869_ = v___x_980_;
goto v___jp_868_;
}
case 32:
{
lean_object* v___x_981_; 
v___x_981_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61));
v___y_869_ = v___x_981_;
goto v___jp_868_;
}
case 33:
{
lean_object* v___x_982_; 
v___x_982_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62));
v___y_869_ = v___x_982_;
goto v___jp_868_;
}
case 34:
{
lean_object* v___x_983_; 
v___x_983_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63));
v___y_869_ = v___x_983_;
goto v___jp_868_;
}
case 35:
{
lean_object* v___x_984_; 
v___x_984_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64));
v___y_869_ = v___x_984_;
goto v___jp_868_;
}
case 36:
{
lean_object* v___x_985_; 
v___x_985_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65));
v___y_869_ = v___x_985_;
goto v___jp_868_;
}
case 37:
{
lean_object* v___x_986_; 
v___x_986_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66));
v___y_869_ = v___x_986_;
goto v___jp_868_;
}
case 38:
{
lean_object* v___x_987_; 
v___x_987_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67));
v___y_869_ = v___x_987_;
goto v___jp_868_;
}
default: 
{
lean_object* v___x_988_; 
v___x_988_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__68));
v___y_869_ = v___x_988_;
goto v___jp_868_;
}
}
v___jp_665_:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v_buffer_677_; lean_object* v_buffer_678_; lean_object* v_data_679_; lean_object* v_size_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_689_; 
v___x_669_ = lean_string_to_utf8(v___y_668_);
lean_inc_ref(v___x_669_);
v___x_670_ = lean_array_push(v___y_667_, v___x_669_);
v___x_671_ = lean_byte_array_size(v___x_669_);
lean_dec_ref(v___x_669_);
v___x_672_ = lean_nat_add(v___y_666_, v___x_671_);
lean_dec(v___y_666_);
v___x_673_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_674_ = lean_array_push(v___x_670_, v___x_673_);
v___x_675_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3);
v___x_676_ = lean_nat_add(v___x_672_, v___x_675_);
lean_dec(v___x_672_);
v_buffer_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_buffer_677_, 0, v___x_674_);
lean_ctor_set(v_buffer_677_, 1, v___x_676_);
v_buffer_678_ = l_Std_Http_Headers_fold___redArg(v_headers_662_, v_buffer_677_, v___f_664_);
lean_dec_ref(v_headers_662_);
v_data_679_ = lean_ctor_get(v_buffer_678_, 0);
v_size_680_ = lean_ctor_get(v_buffer_678_, 1);
v_isSharedCheck_689_ = !lean_is_exclusive(v_buffer_678_);
if (v_isSharedCheck_689_ == 0)
{
v___x_682_ = v_buffer_678_;
v_isShared_683_ = v_isSharedCheck_689_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_size_680_);
lean_inc(v_data_679_);
lean_dec(v_buffer_678_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_689_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_684_ = lean_array_push(v_data_679_, v___x_673_);
v___x_685_ = lean_nat_add(v_size_680_, v___x_675_);
lean_dec(v_size_680_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v___x_685_);
lean_ctor_set(v___x_682_, 0, v___x_684_);
v___x_687_ = v___x_682_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
v___jp_690_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_696_ = lean_string_to_utf8(v___y_695_);
lean_dec_ref(v___y_695_);
lean_inc_ref(v___x_696_);
v___x_697_ = lean_array_push(v___y_692_, v___x_696_);
v___x_698_ = lean_byte_array_size(v___x_696_);
lean_dec_ref(v___x_696_);
v___x_699_ = lean_nat_add(v___y_693_, v___x_698_);
lean_dec(v___y_693_);
v___x_700_ = lean_array_push(v___x_697_, v___y_694_);
v___x_701_ = lean_nat_add(v___x_699_, v___y_691_);
lean_dec(v___x_699_);
switch(v_version_660_)
{
case 0:
{
lean_object* v___x_702_; 
v___x_702_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4));
v___y_666_ = v___x_701_;
v___y_667_ = v___x_700_;
v___y_668_ = v___x_702_;
goto v___jp_665_;
}
case 1:
{
lean_object* v___x_703_; 
v___x_703_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5));
v___y_666_ = v___x_701_;
v___y_667_ = v___x_700_;
v___y_668_ = v___x_703_;
goto v___jp_665_;
}
case 2:
{
lean_object* v___x_704_; 
v___x_704_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6));
v___y_666_ = v___x_701_;
v___y_667_ = v___x_700_;
v___y_668_ = v___x_704_;
goto v___jp_665_;
}
default: 
{
lean_object* v___x_705_; 
v___x_705_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7));
v___y_666_ = v___x_701_;
v___y_667_ = v___x_700_;
v___y_668_ = v___x_705_;
goto v___jp_665_;
}
}
}
v___jp_706_:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_string_append(v___y_707_, v___y_712_);
lean_dec_ref(v___y_712_);
v___x_715_ = lean_string_append(v___x_714_, v___y_713_);
lean_dec_ref(v___y_713_);
v___y_691_ = v___y_708_;
v___y_692_ = v___y_709_;
v___y_693_ = v___y_710_;
v___y_694_ = v___y_711_;
v___y_695_ = v___x_715_;
goto v___jp_690_;
}
v___jp_716_:
{
switch(lean_obj_tag(v_port_721_))
{
case 0:
{
lean_object* v___x_724_; 
v___x_724_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_707_ = v___y_717_;
v___y_708_ = v___y_718_;
v___y_709_ = v___y_719_;
v___y_710_ = v___y_720_;
v___y_711_ = v___y_722_;
v___y_712_ = v___y_723_;
v___y_713_ = v___x_724_;
goto v___jp_706_;
}
case 1:
{
lean_object* v___x_725_; 
v___x_725_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___y_707_ = v___y_717_;
v___y_708_ = v___y_718_;
v___y_709_ = v___y_719_;
v___y_710_ = v___y_720_;
v___y_711_ = v___y_722_;
v___y_712_ = v___y_723_;
v___y_713_ = v___x_725_;
goto v___jp_706_;
}
default: 
{
uint16_t v_port_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v_port_726_ = lean_ctor_get_uint16(v_port_721_, 0);
lean_dec_ref_known(v_port_721_, 0);
v___x_727_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_728_ = lean_uint16_to_nat(v_port_726_);
v___x_729_ = l_Nat_reprFast(v___x_728_);
v___x_730_ = lean_string_append(v___x_727_, v___x_729_);
lean_dec_ref(v___x_729_);
v___y_707_ = v___y_717_;
v___y_708_ = v___y_718_;
v___y_709_ = v___y_719_;
v___y_710_ = v___y_720_;
v___y_711_ = v___y_722_;
v___y_712_ = v___y_723_;
v___y_713_ = v___x_730_;
goto v___jp_706_;
}
}
}
v___jp_731_:
{
switch(lean_obj_tag(v_host_735_))
{
case 0:
{
lean_object* v_name_739_; 
v_name_739_ = lean_ctor_get(v_host_735_, 0);
lean_inc_ref(v_name_739_);
lean_dec_ref_known(v_host_735_, 1);
v___y_717_ = v___y_738_;
v___y_718_ = v___y_732_;
v___y_719_ = v___y_733_;
v___y_720_ = v___y_734_;
v_port_721_ = v_port_736_;
v___y_722_ = v___y_737_;
v___y_723_ = v_name_739_;
goto v___jp_716_;
}
case 1:
{
lean_object* v_ipv4_740_; lean_object* v___x_741_; 
v_ipv4_740_ = lean_ctor_get(v_host_735_, 0);
lean_inc_ref(v_ipv4_740_);
lean_dec_ref_known(v_host_735_, 1);
v___x_741_ = lean_uv_ntop_v4(v_ipv4_740_);
lean_dec_ref(v_ipv4_740_);
v___y_717_ = v___y_738_;
v___y_718_ = v___y_732_;
v___y_719_ = v___y_733_;
v___y_720_ = v___y_734_;
v_port_721_ = v_port_736_;
v___y_722_ = v___y_737_;
v___y_723_ = v___x_741_;
goto v___jp_716_;
}
default: 
{
lean_object* v_ipv6_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v_ipv6_742_ = lean_ctor_get(v_host_735_, 0);
lean_inc_ref(v_ipv6_742_);
lean_dec_ref_known(v_host_735_, 1);
v___x_743_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9));
v___x_744_ = lean_uv_ntop_v6(v_ipv6_742_);
lean_dec_ref(v_ipv6_742_);
v___x_745_ = lean_string_append(v___x_743_, v___x_744_);
lean_dec_ref(v___x_744_);
v___x_746_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10));
v___x_747_ = lean_string_append(v___x_745_, v___x_746_);
v___y_717_ = v___y_738_;
v___y_718_ = v___y_732_;
v___y_719_ = v___y_733_;
v___y_720_ = v___y_734_;
v_port_721_ = v_port_736_;
v___y_722_ = v___y_737_;
v___y_723_ = v___x_747_;
goto v___jp_716_;
}
}
}
v___jp_748_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_758_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_759_ = lean_string_append(v___y_754_, v___x_758_);
v___x_760_ = lean_string_append(v___x_759_, v___y_753_);
lean_dec_ref(v___y_753_);
v___x_761_ = lean_string_append(v___x_760_, v___y_752_);
lean_dec_ref(v___y_752_);
v___x_762_ = lean_string_append(v___x_761_, v___y_751_);
lean_dec_ref(v___y_751_);
v___x_763_ = lean_string_append(v___x_762_, v___y_757_);
lean_dec_ref(v___y_757_);
v___y_691_ = v___y_749_;
v___y_692_ = v___y_750_;
v___y_693_ = v___y_755_;
v___y_694_ = v___y_756_;
v___y_695_ = v___x_763_;
goto v___jp_690_;
}
v___jp_764_:
{
lean_object* v_queryPart_774_; 
v_queryPart_774_ = l_Std_Http_URI_Query_formatOption(v___y_770_);
if (lean_obj_tag(v___y_771_) == 0)
{
lean_object* v___x_775_; 
v___x_775_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_749_ = v___y_765_;
v___y_750_ = v___y_766_;
v___y_751_ = v_queryPart_774_;
v___y_752_ = v___y_773_;
v___y_753_ = v___y_768_;
v___y_754_ = v___y_767_;
v___y_755_ = v___y_769_;
v___y_756_ = v___y_772_;
v___y_757_ = v___x_775_;
goto v___jp_748_;
}
else
{
lean_object* v_val_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v_val_776_ = lean_ctor_get(v___y_771_, 0);
lean_inc(v_val_776_);
lean_dec_ref_known(v___y_771_, 1);
v___x_777_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11));
v___x_778_ = l_Std_Http_URI_EncodedFragment_encode(v_val_776_);
lean_dec(v_val_776_);
v___x_779_ = lean_string_from_utf8_unchecked(v___x_778_);
v___x_780_ = lean_string_append(v___x_777_, v___x_779_);
lean_dec_ref(v___x_779_);
v___y_749_ = v___y_765_;
v___y_750_ = v___y_766_;
v___y_751_ = v_queryPart_774_;
v___y_752_ = v___y_773_;
v___y_753_ = v___y_768_;
v___y_754_ = v___y_767_;
v___y_755_ = v___y_769_;
v___y_756_ = v___y_772_;
v___y_757_ = v___x_780_;
goto v___jp_748_;
}
}
v___jp_781_:
{
lean_object* v_queryStr_788_; lean_object* v___x_789_; 
v_queryStr_788_ = l_Std_Http_URI_Query_formatOption(v___y_785_);
v___x_789_ = lean_string_append(v___y_787_, v_queryStr_788_);
lean_dec_ref(v_queryStr_788_);
v___y_691_ = v___y_782_;
v___y_692_ = v___y_783_;
v___y_693_ = v___y_784_;
v___y_694_ = v___y_786_;
v___y_695_ = v___x_789_;
goto v___jp_690_;
}
v___jp_790_:
{
lean_object* v_segments_800_; uint8_t v_absolute_801_; lean_object* v___x_802_; lean_object* v___x_803_; size_t v_sz_804_; size_t v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v_result_808_; 
v_segments_800_ = lean_ctor_get(v___y_792_, 0);
lean_inc_ref(v_segments_800_);
v_absolute_801_ = lean_ctor_get_uint8(v___y_792_, sizeof(void*)*1);
lean_dec_ref(v___y_792_);
v___x_802_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12));
v___x_803_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22));
v_sz_804_ = lean_array_size(v_segments_800_);
v___x_805_ = ((size_t)0ULL);
v___x_806_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_803_, v___f_663_, v_sz_804_, v___x_805_, v_segments_800_);
v___x_807_ = lean_array_to_list(v___x_806_);
v_result_808_ = l_String_intercalate(v___x_802_, v___x_807_);
if (v_absolute_801_ == 0)
{
v___y_765_ = v___y_791_;
v___y_766_ = v___y_793_;
v___y_767_ = v___y_794_;
v___y_768_ = v___y_799_;
v___y_769_ = v___y_796_;
v___y_770_ = v___y_795_;
v___y_771_ = v___y_797_;
v___y_772_ = v___y_798_;
v___y_773_ = v_result_808_;
goto v___jp_764_;
}
else
{
lean_object* v___x_809_; 
v___x_809_ = lean_string_append(v___x_802_, v_result_808_);
lean_dec_ref(v_result_808_);
v___y_765_ = v___y_791_;
v___y_766_ = v___y_793_;
v___y_767_ = v___y_794_;
v___y_768_ = v___y_799_;
v___y_769_ = v___y_796_;
v___y_770_ = v___y_795_;
v___y_771_ = v___y_797_;
v___y_772_ = v___y_798_;
v___y_773_ = v___x_809_;
goto v___jp_764_;
}
}
v___jp_810_:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_823_ = lean_string_append(v___y_815_, v___y_813_);
lean_dec_ref(v___y_813_);
v___x_824_ = lean_string_append(v___x_823_, v___y_822_);
lean_dec_ref(v___y_822_);
lean_inc_ref(v___y_819_);
v___x_825_ = lean_string_append(v___y_819_, v___x_824_);
lean_dec_ref(v___x_824_);
v___y_791_ = v___y_811_;
v___y_792_ = v___y_812_;
v___y_793_ = v___y_814_;
v___y_794_ = v___y_816_;
v___y_795_ = v___y_818_;
v___y_796_ = v___y_817_;
v___y_797_ = v___y_820_;
v___y_798_ = v___y_821_;
v___y_799_ = v___x_825_;
goto v___jp_790_;
}
v___jp_826_:
{
switch(lean_obj_tag(v_port_836_))
{
case 0:
{
lean_object* v___x_839_; 
v___x_839_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_811_ = v___y_827_;
v___y_812_ = v___y_828_;
v___y_813_ = v___y_838_;
v___y_814_ = v___y_830_;
v___y_815_ = v___y_829_;
v___y_816_ = v___y_831_;
v___y_817_ = v___y_833_;
v___y_818_ = v___y_832_;
v___y_819_ = v___y_834_;
v___y_820_ = v___y_835_;
v___y_821_ = v___y_837_;
v___y_822_ = v___x_839_;
goto v___jp_810_;
}
case 1:
{
lean_object* v___x_840_; 
v___x_840_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___y_811_ = v___y_827_;
v___y_812_ = v___y_828_;
v___y_813_ = v___y_838_;
v___y_814_ = v___y_830_;
v___y_815_ = v___y_829_;
v___y_816_ = v___y_831_;
v___y_817_ = v___y_833_;
v___y_818_ = v___y_832_;
v___y_819_ = v___y_834_;
v___y_820_ = v___y_835_;
v___y_821_ = v___y_837_;
v___y_822_ = v___x_840_;
goto v___jp_810_;
}
default: 
{
uint16_t v_port_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v_port_841_ = lean_ctor_get_uint16(v_port_836_, 0);
lean_dec_ref_known(v_port_836_, 0);
v___x_842_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_843_ = lean_uint16_to_nat(v_port_841_);
v___x_844_ = l_Nat_reprFast(v___x_843_);
v___x_845_ = lean_string_append(v___x_842_, v___x_844_);
lean_dec_ref(v___x_844_);
v___y_811_ = v___y_827_;
v___y_812_ = v___y_828_;
v___y_813_ = v___y_838_;
v___y_814_ = v___y_830_;
v___y_815_ = v___y_829_;
v___y_816_ = v___y_831_;
v___y_817_ = v___y_833_;
v___y_818_ = v___y_832_;
v___y_819_ = v___y_834_;
v___y_820_ = v___y_835_;
v___y_821_ = v___y_837_;
v___y_822_ = v___x_845_;
goto v___jp_810_;
}
}
}
v___jp_846_:
{
switch(lean_obj_tag(v_host_856_))
{
case 0:
{
lean_object* v_name_859_; 
v_name_859_ = lean_ctor_get(v_host_856_, 0);
lean_inc_ref(v_name_859_);
lean_dec_ref_known(v_host_856_, 1);
v___y_827_ = v___y_847_;
v___y_828_ = v___y_848_;
v___y_829_ = v___y_858_;
v___y_830_ = v___y_849_;
v___y_831_ = v___y_850_;
v___y_832_ = v___y_852_;
v___y_833_ = v___y_851_;
v___y_834_ = v___y_853_;
v___y_835_ = v___y_854_;
v_port_836_ = v_port_857_;
v___y_837_ = v___y_855_;
v___y_838_ = v_name_859_;
goto v___jp_826_;
}
case 1:
{
lean_object* v_ipv4_860_; lean_object* v___x_861_; 
v_ipv4_860_ = lean_ctor_get(v_host_856_, 0);
lean_inc_ref(v_ipv4_860_);
lean_dec_ref_known(v_host_856_, 1);
v___x_861_ = lean_uv_ntop_v4(v_ipv4_860_);
lean_dec_ref(v_ipv4_860_);
v___y_827_ = v___y_847_;
v___y_828_ = v___y_848_;
v___y_829_ = v___y_858_;
v___y_830_ = v___y_849_;
v___y_831_ = v___y_850_;
v___y_832_ = v___y_852_;
v___y_833_ = v___y_851_;
v___y_834_ = v___y_853_;
v___y_835_ = v___y_854_;
v_port_836_ = v_port_857_;
v___y_837_ = v___y_855_;
v___y_838_ = v___x_861_;
goto v___jp_826_;
}
default: 
{
lean_object* v_ipv6_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_ipv6_862_ = lean_ctor_get(v_host_856_, 0);
lean_inc_ref(v_ipv6_862_);
lean_dec_ref_known(v_host_856_, 1);
v___x_863_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9));
v___x_864_ = lean_uv_ntop_v6(v_ipv6_862_);
lean_dec_ref(v_ipv6_862_);
v___x_865_ = lean_string_append(v___x_863_, v___x_864_);
lean_dec_ref(v___x_864_);
v___x_866_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10));
v___x_867_ = lean_string_append(v___x_865_, v___x_866_);
v___y_827_ = v___y_847_;
v___y_828_ = v___y_848_;
v___y_829_ = v___y_858_;
v___y_830_ = v___y_849_;
v___y_831_ = v___y_850_;
v___y_832_ = v___y_852_;
v___y_833_ = v___y_851_;
v___y_834_ = v___y_853_;
v___y_835_ = v___y_854_;
v_port_836_ = v_port_857_;
v___y_837_ = v___y_855_;
v___y_838_ = v___x_867_;
goto v___jp_826_;
}
}
}
v___jp_868_:
{
lean_object* v_data_870_; lean_object* v_size_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v_data_870_ = lean_ctor_get(v_buffer_657_, 0);
lean_inc_ref(v_data_870_);
v_size_871_ = lean_ctor_get(v_buffer_657_, 1);
lean_inc(v_size_871_);
lean_dec_ref(v_buffer_657_);
v___x_872_ = lean_string_to_utf8(v___y_869_);
lean_inc_ref(v___x_872_);
v___x_873_ = lean_array_push(v_data_870_, v___x_872_);
v___x_874_ = lean_byte_array_size(v___x_872_);
lean_dec_ref(v___x_872_);
v___x_875_ = lean_nat_add(v_size_871_, v___x_874_);
lean_dec(v_size_871_);
v___x_876_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24);
v___x_877_ = lean_array_push(v___x_873_, v___x_876_);
v___x_878_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25);
v___x_879_ = lean_nat_add(v___x_875_, v___x_878_);
lean_dec(v___x_875_);
switch(lean_obj_tag(v_uri_661_))
{
case 0:
{
lean_object* v_path_880_; lean_object* v_query_881_; lean_object* v_segments_882_; uint8_t v_absolute_883_; lean_object* v___x_884_; lean_object* v___x_885_; size_t v_sz_886_; size_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v_result_890_; 
v_path_880_ = lean_ctor_get(v_uri_661_, 0);
lean_inc_ref(v_path_880_);
v_query_881_ = lean_ctor_get(v_uri_661_, 1);
lean_inc(v_query_881_);
lean_dec_ref_known(v_uri_661_, 2);
v_segments_882_ = lean_ctor_get(v_path_880_, 0);
lean_inc_ref(v_segments_882_);
v_absolute_883_ = lean_ctor_get_uint8(v_path_880_, sizeof(void*)*1);
lean_dec_ref(v_path_880_);
v___x_884_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12));
v___x_885_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22));
v_sz_886_ = lean_array_size(v_segments_882_);
v___x_887_ = ((size_t)0ULL);
v___x_888_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_885_, v___f_663_, v_sz_886_, v___x_887_, v_segments_882_);
v___x_889_ = lean_array_to_list(v___x_888_);
v_result_890_ = l_String_intercalate(v___x_884_, v___x_889_);
if (v_absolute_883_ == 0)
{
v___y_782_ = v___x_878_;
v___y_783_ = v___x_877_;
v___y_784_ = v___x_879_;
v___y_785_ = v_query_881_;
v___y_786_ = v___x_876_;
v___y_787_ = v_result_890_;
goto v___jp_781_;
}
else
{
lean_object* v___x_891_; 
v___x_891_ = lean_string_append(v___x_884_, v_result_890_);
lean_dec_ref(v_result_890_);
v___y_782_ = v___x_878_;
v___y_783_ = v___x_877_;
v___y_784_ = v___x_879_;
v___y_785_ = v_query_881_;
v___y_786_ = v___x_876_;
v___y_787_ = v___x_891_;
goto v___jp_781_;
}
}
case 1:
{
lean_object* v_uri_892_; lean_object* v_authority_893_; 
v_uri_892_ = lean_ctor_get(v_uri_661_, 0);
lean_inc_ref(v_uri_892_);
lean_dec_ref_known(v_uri_661_, 1);
v_authority_893_ = lean_ctor_get(v_uri_892_, 1);
if (lean_obj_tag(v_authority_893_) == 0)
{
lean_object* v_scheme_894_; lean_object* v_path_895_; lean_object* v_query_896_; lean_object* v_fragment_897_; lean_object* v___x_898_; 
v_scheme_894_ = lean_ctor_get(v_uri_892_, 0);
lean_inc_ref(v_scheme_894_);
v_path_895_ = lean_ctor_get(v_uri_892_, 2);
lean_inc_ref(v_path_895_);
v_query_896_ = lean_ctor_get(v_uri_892_, 3);
lean_inc(v_query_896_);
v_fragment_897_ = lean_ctor_get(v_uri_892_, 4);
lean_inc(v_fragment_897_);
lean_dec_ref(v_uri_892_);
v___x_898_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_791_ = v___x_878_;
v___y_792_ = v_path_895_;
v___y_793_ = v___x_877_;
v___y_794_ = v_scheme_894_;
v___y_795_ = v_query_896_;
v___y_796_ = v___x_879_;
v___y_797_ = v_fragment_897_;
v___y_798_ = v___x_876_;
v___y_799_ = v___x_898_;
goto v___jp_790_;
}
else
{
lean_object* v_val_899_; lean_object* v_scheme_900_; lean_object* v_path_901_; lean_object* v_query_902_; lean_object* v_fragment_903_; lean_object* v_userInfo_904_; lean_object* v_host_905_; lean_object* v_port_906_; lean_object* v___x_907_; 
v_val_899_ = lean_ctor_get(v_authority_893_, 0);
lean_inc(v_val_899_);
v_scheme_900_ = lean_ctor_get(v_uri_892_, 0);
lean_inc_ref(v_scheme_900_);
v_path_901_ = lean_ctor_get(v_uri_892_, 2);
lean_inc_ref(v_path_901_);
v_query_902_ = lean_ctor_get(v_uri_892_, 3);
lean_inc(v_query_902_);
v_fragment_903_ = lean_ctor_get(v_uri_892_, 4);
lean_inc(v_fragment_903_);
lean_dec_ref(v_uri_892_);
v_userInfo_904_ = lean_ctor_get(v_val_899_, 0);
lean_inc(v_userInfo_904_);
v_host_905_ = lean_ctor_get(v_val_899_, 1);
lean_inc_ref(v_host_905_);
v_port_906_ = lean_ctor_get(v_val_899_, 2);
lean_inc(v_port_906_);
lean_dec(v_val_899_);
v___x_907_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26));
if (lean_obj_tag(v_userInfo_904_) == 0)
{
lean_object* v___x_908_; 
v___x_908_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_847_ = v___x_878_;
v___y_848_ = v_path_901_;
v___y_849_ = v___x_877_;
v___y_850_ = v_scheme_900_;
v___y_851_ = v___x_879_;
v___y_852_ = v_query_902_;
v___y_853_ = v___x_907_;
v___y_854_ = v_fragment_903_;
v___y_855_ = v___x_876_;
v_host_856_ = v_host_905_;
v_port_857_ = v_port_906_;
v___y_858_ = v___x_908_;
goto v___jp_846_;
}
else
{
lean_object* v_val_909_; lean_object* v_password_910_; 
v_val_909_ = lean_ctor_get(v_userInfo_904_, 0);
lean_inc(v_val_909_);
lean_dec_ref_known(v_userInfo_904_, 1);
v_password_910_ = lean_ctor_get(v_val_909_, 1);
if (lean_obj_tag(v_password_910_) == 0)
{
lean_object* v_username_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v_username_911_ = lean_ctor_get(v_val_909_, 0);
lean_inc_ref(v_username_911_);
lean_dec(v_val_909_);
v___x_912_ = lean_string_from_utf8_unchecked(v_username_911_);
v___x_913_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27));
v___x_914_ = lean_string_append(v___x_912_, v___x_913_);
v___y_847_ = v___x_878_;
v___y_848_ = v_path_901_;
v___y_849_ = v___x_877_;
v___y_850_ = v_scheme_900_;
v___y_851_ = v___x_879_;
v___y_852_ = v_query_902_;
v___y_853_ = v___x_907_;
v___y_854_ = v_fragment_903_;
v___y_855_ = v___x_876_;
v_host_856_ = v_host_905_;
v_port_857_ = v_port_906_;
v___y_858_ = v___x_914_;
goto v___jp_846_;
}
else
{
lean_object* v_username_915_; lean_object* v_val_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
lean_inc_ref(v_password_910_);
v_username_915_ = lean_ctor_get(v_val_909_, 0);
lean_inc_ref(v_username_915_);
lean_dec(v_val_909_);
v_val_916_ = lean_ctor_get(v_password_910_, 0);
lean_inc(v_val_916_);
lean_dec_ref_known(v_password_910_, 1);
v___x_917_ = lean_string_from_utf8_unchecked(v_username_915_);
v___x_918_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_919_ = lean_string_append(v___x_917_, v___x_918_);
v___x_920_ = lean_string_from_utf8_unchecked(v_val_916_);
v___x_921_ = lean_string_append(v___x_919_, v___x_920_);
lean_dec_ref(v___x_920_);
v___x_922_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27));
v___x_923_ = lean_string_append(v___x_921_, v___x_922_);
v___y_847_ = v___x_878_;
v___y_848_ = v_path_901_;
v___y_849_ = v___x_877_;
v___y_850_ = v_scheme_900_;
v___y_851_ = v___x_879_;
v___y_852_ = v_query_902_;
v___y_853_ = v___x_907_;
v___y_854_ = v_fragment_903_;
v___y_855_ = v___x_876_;
v_host_856_ = v_host_905_;
v_port_857_ = v_port_906_;
v___y_858_ = v___x_923_;
goto v___jp_846_;
}
}
}
}
case 2:
{
lean_object* v_authority_924_; lean_object* v_userInfo_925_; 
v_authority_924_ = lean_ctor_get(v_uri_661_, 0);
lean_inc_ref(v_authority_924_);
lean_dec_ref_known(v_uri_661_, 1);
v_userInfo_925_ = lean_ctor_get(v_authority_924_, 0);
if (lean_obj_tag(v_userInfo_925_) == 0)
{
lean_object* v_host_926_; lean_object* v_port_927_; lean_object* v___x_928_; 
v_host_926_ = lean_ctor_get(v_authority_924_, 1);
lean_inc_ref(v_host_926_);
v_port_927_ = lean_ctor_get(v_authority_924_, 2);
lean_inc(v_port_927_);
lean_dec_ref(v_authority_924_);
v___x_928_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___closed__5));
v___y_732_ = v___x_878_;
v___y_733_ = v___x_877_;
v___y_734_ = v___x_879_;
v_host_735_ = v_host_926_;
v_port_736_ = v_port_927_;
v___y_737_ = v___x_876_;
v___y_738_ = v___x_928_;
goto v___jp_731_;
}
else
{
lean_object* v_val_929_; lean_object* v_password_930_; 
v_val_929_ = lean_ctor_get(v_userInfo_925_, 0);
lean_inc(v_val_929_);
v_password_930_ = lean_ctor_get(v_val_929_, 1);
if (lean_obj_tag(v_password_930_) == 0)
{
lean_object* v_host_931_; lean_object* v_port_932_; lean_object* v_username_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v_host_931_ = lean_ctor_get(v_authority_924_, 1);
lean_inc_ref(v_host_931_);
v_port_932_ = lean_ctor_get(v_authority_924_, 2);
lean_inc(v_port_932_);
lean_dec_ref(v_authority_924_);
v_username_933_ = lean_ctor_get(v_val_929_, 0);
lean_inc_ref(v_username_933_);
lean_dec(v_val_929_);
v___x_934_ = lean_string_from_utf8_unchecked(v_username_933_);
v___x_935_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27));
v___x_936_ = lean_string_append(v___x_934_, v___x_935_);
v___y_732_ = v___x_878_;
v___y_733_ = v___x_877_;
v___y_734_ = v___x_879_;
v_host_735_ = v_host_931_;
v_port_736_ = v_port_932_;
v___y_737_ = v___x_876_;
v___y_738_ = v___x_936_;
goto v___jp_731_;
}
else
{
lean_object* v_host_937_; lean_object* v_port_938_; lean_object* v_username_939_; lean_object* v_val_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
lean_inc_ref(v_password_930_);
v_host_937_ = lean_ctor_get(v_authority_924_, 1);
lean_inc_ref(v_host_937_);
v_port_938_ = lean_ctor_get(v_authority_924_, 2);
lean_inc(v_port_938_);
lean_dec_ref(v_authority_924_);
v_username_939_ = lean_ctor_get(v_val_929_, 0);
lean_inc_ref(v_username_939_);
lean_dec(v_val_929_);
v_val_940_ = lean_ctor_get(v_password_930_, 0);
lean_inc(v_val_940_);
lean_dec_ref_known(v_password_930_, 1);
v___x_941_ = lean_string_from_utf8_unchecked(v_username_939_);
v___x_942_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___x_943_ = lean_string_append(v___x_941_, v___x_942_);
v___x_944_ = lean_string_from_utf8_unchecked(v_val_940_);
v___x_945_ = lean_string_append(v___x_943_, v___x_944_);
lean_dec_ref(v___x_944_);
v___x_946_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27));
v___x_947_ = lean_string_append(v___x_945_, v___x_946_);
v___y_732_ = v___x_878_;
v___y_733_ = v___x_877_;
v___y_734_ = v___x_879_;
v_host_735_ = v_host_937_;
v_port_736_ = v_port_938_;
v___y_737_ = v___x_876_;
v___y_738_ = v___x_947_;
goto v___jp_731_;
}
}
}
default: 
{
lean_object* v___x_948_; 
v___x_948_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28));
v___y_691_ = v___x_878_;
v___y_692_ = v___x_877_;
v___y_693_ = v___x_879_;
v___y_694_ = v___x_876_;
v___y_695_ = v___x_948_;
goto v___jp_690_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(lean_object* v_buffer_989_, lean_object* v_r_990_){
_start:
{
lean_object* v_status_991_; uint8_t v_version_992_; lean_object* v_headers_993_; lean_object* v___f_994_; lean_object* v___y_996_; 
v_status_991_ = lean_ctor_get(v_r_990_, 0);
v_version_992_ = lean_ctor_get_uint8(v_r_990_, sizeof(void*)*2);
v_headers_993_ = lean_ctor_get(v_r_990_, 1);
v___f_994_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1));
switch(v_version_992_)
{
case 0:
{
lean_object* v___x_1046_; 
v___x_1046_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4));
v___y_996_ = v___x_1046_;
goto v___jp_995_;
}
case 1:
{
lean_object* v___x_1047_; 
v___x_1047_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5));
v___y_996_ = v___x_1047_;
goto v___jp_995_;
}
case 2:
{
lean_object* v___x_1048_; 
v___x_1048_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6));
v___y_996_ = v___x_1048_;
goto v___jp_995_;
}
default: 
{
lean_object* v___x_1049_; 
v___x_1049_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7));
v___y_996_ = v___x_1049_;
goto v___jp_995_;
}
}
v___jp_995_:
{
lean_object* v_data_997_; lean_object* v_size_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1045_; 
v_data_997_ = lean_ctor_get(v_buffer_989_, 0);
v_size_998_ = lean_ctor_get(v_buffer_989_, 1);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_buffer_989_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1000_ = v_buffer_989_;
v_isShared_1001_ = v_isSharedCheck_1045_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_size_998_);
lean_inc(v_data_997_);
lean_dec(v_buffer_989_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1045_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; uint16_t v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v_buffer_1031_; 
v___x_1002_ = lean_string_to_utf8(v___y_996_);
lean_inc_ref(v___x_1002_);
v___x_1003_ = lean_array_push(v_data_997_, v___x_1002_);
v___x_1004_ = lean_byte_array_size(v___x_1002_);
lean_dec_ref(v___x_1002_);
v___x_1005_ = lean_nat_add(v_size_998_, v___x_1004_);
lean_dec(v_size_998_);
v___x_1006_ = lean_unsigned_to_nat(1u);
v___x_1007_ = lean_mk_empty_array_with_capacity(v___x_1006_);
lean_dec_ref(v___x_1007_);
v___x_1008_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24);
v___x_1009_ = lean_array_push(v___x_1003_, v___x_1008_);
v___x_1010_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25);
v___x_1011_ = lean_nat_add(v___x_1005_, v___x_1010_);
lean_dec(v___x_1005_);
v___x_1012_ = l_Std_Http_Status_toCode(v_status_991_);
v___x_1013_ = lean_uint16_to_nat(v___x_1012_);
v___x_1014_ = l_Nat_reprFast(v___x_1013_);
v___x_1015_ = lean_string_to_utf8(v___x_1014_);
lean_dec_ref(v___x_1014_);
lean_inc_ref(v___x_1015_);
v___x_1016_ = lean_array_push(v___x_1009_, v___x_1015_);
v___x_1017_ = lean_byte_array_size(v___x_1015_);
lean_dec_ref(v___x_1015_);
v___x_1018_ = lean_nat_add(v___x_1011_, v___x_1017_);
lean_dec(v___x_1011_);
v___x_1019_ = lean_array_push(v___x_1016_, v___x_1008_);
v___x_1020_ = lean_nat_add(v___x_1018_, v___x_1010_);
lean_dec(v___x_1018_);
v___x_1021_ = l_Std_Http_Status_reasonPhrase(v_status_991_);
v___x_1022_ = lean_string_to_utf8(v___x_1021_);
lean_dec_ref(v___x_1021_);
lean_inc_ref(v___x_1022_);
v___x_1023_ = lean_array_push(v___x_1019_, v___x_1022_);
v___x_1024_ = lean_byte_array_size(v___x_1022_);
lean_dec_ref(v___x_1022_);
v___x_1025_ = lean_nat_add(v___x_1020_, v___x_1024_);
lean_dec(v___x_1020_);
v___x_1026_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_1027_ = lean_array_push(v___x_1023_, v___x_1026_);
v___x_1028_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3);
v___x_1029_ = lean_nat_add(v___x_1025_, v___x_1028_);
lean_dec(v___x_1025_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 1, v___x_1029_);
lean_ctor_set(v___x_1000_, 0, v___x_1027_);
v_buffer_1031_ = v___x_1000_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1027_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v___x_1029_);
v_buffer_1031_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v_buffer_1032_; lean_object* v_data_1033_; lean_object* v_size_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1043_; 
v_buffer_1032_ = l_Std_Http_Headers_fold___redArg(v_headers_993_, v_buffer_1031_, v___f_994_);
v_data_1033_ = lean_ctor_get(v_buffer_1032_, 0);
v_size_1034_ = lean_ctor_get(v_buffer_1032_, 1);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_buffer_1032_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1036_ = v_buffer_1032_;
v_isShared_1037_ = v_isSharedCheck_1043_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_size_1034_);
lean_inc(v_data_1033_);
lean_dec(v_buffer_1032_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1043_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1038_ = lean_array_push(v_data_1033_, v___x_1026_);
v___x_1039_ = lean_nat_add(v_size_1034_, v___x_1028_);
lean_dec(v_size_1034_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 1, v___x_1039_);
lean_ctor_set(v___x_1036_, 0, v___x_1038_);
v___x_1041_ = v___x_1036_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___boxed(lean_object* v_buffer_1050_, lean_object* v_r_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(v_buffer_1050_, v_r_1051_);
lean_dec_ref(v_r_1051_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head(uint8_t v_dir_1055_){
_start:
{
if (v_dir_1055_ == 0)
{
lean_object* v___x_1056_; 
v___x_1056_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___closed__0));
return v___x_1056_;
}
else
{
lean_object* v___x_1057_; 
v___x_1057_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___closed__1));
return v___x_1057_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___boxed(lean_object* v_dir_1058_){
_start:
{
uint8_t v_dir_boxed_1059_; lean_object* v_res_1060_; 
v_dir_boxed_1059_ = lean_unbox(v_dir_1058_);
v_res_1060_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v_dir_boxed_1059_);
return v_res_1060_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; uint8_t v___x_1064_; lean_object* v___x_1065_; 
v___x_1061_ = l_Std_Http_Headers_empty;
v___x_1062_ = lean_box(3);
v___x_1063_ = 1;
v___x_1064_ = 8;
v___x_1065_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1065_, 0, v___x_1062_);
lean_ctor_set(v___x_1065_, 1, v___x_1061_);
lean_ctor_set_uint8(v___x_1065_, sizeof(void*)*2, v___x_1064_);
lean_ctor_set_uint8(v___x_1065_, sizeof(void*)*2 + 1, v___x_1063_);
return v___x_1065_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1(void){
_start:
{
lean_object* v___x_1066_; uint8_t v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1066_ = l_Std_Http_Headers_empty;
v___x_1067_ = 1;
v___x_1068_ = lean_box(4);
v___x_1069_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v___x_1066_);
lean_ctor_set_uint8(v___x_1069_, sizeof(void*)*2, v___x_1067_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead(uint8_t v_dir_1070_){
_start:
{
if (v_dir_1070_ == 0)
{
lean_object* v___x_1071_; 
v___x_1071_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0, &l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0_once, _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0);
return v___x_1071_;
}
else
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1, &l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1_once, _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1);
return v___x_1072_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead___boxed(lean_object* v_dir_1073_){
_start:
{
uint8_t v_dir_boxed_1074_; lean_object* v_res_1075_; 
v_dir_boxed_1074_ = lean_unbox(v_dir_1073_);
v_res_1075_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v_dir_boxed_1074_);
return v_res_1075_;
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
