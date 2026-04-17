// Lean compiler output
// Module: Std.Internal.Http.Protocol.H1.Message
// Imports: import Init.Data.Array public import Std.Internal.Http.Data
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
lean_object* l_String_Slice_toNat_x3f(lean_object*);
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
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Message_Head_version(uint8_t v_dir_80_, lean_object* v_m_81_){
_start:
{
if (v_dir_80_ == 0)
{
uint8_t v_version_82_; 
v_version_82_ = lean_ctor_get_uint8(v_m_81_, sizeof(void*)*2 + 1);
return v_version_82_;
}
else
{
uint8_t v_version_83_; 
v_version_83_ = lean_ctor_get_uint8(v_m_81_, sizeof(void*)*2);
return v_version_83_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_version___boxed(lean_object* v_dir_84_, lean_object* v_m_85_){
_start:
{
uint8_t v_dir_boxed_86_; uint8_t v_res_87_; lean_object* v_r_88_; 
v_dir_boxed_86_ = lean_unbox(v_dir_84_);
v_res_87_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_boxed_86_, v_m_85_);
lean_dec(v_m_85_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(lean_object* v_a_89_, lean_object* v_x_90_){
_start:
{
lean_object* v_key_91_; lean_object* v_value_92_; lean_object* v_tail_93_; uint8_t v___x_94_; 
v_key_91_ = lean_ctor_get(v_x_90_, 0);
v_value_92_ = lean_ctor_get(v_x_90_, 1);
v_tail_93_ = lean_ctor_get(v_x_90_, 2);
v___x_94_ = lean_string_dec_eq(v_key_91_, v_a_89_);
if (v___x_94_ == 0)
{
v_x_90_ = v_tail_93_;
goto _start;
}
else
{
lean_inc(v_value_92_);
return v_value_92_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg___boxed(lean_object* v_a_96_, lean_object* v_x_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_a_96_, v_x_97_);
lean_dec(v_x_97_);
lean_dec_ref(v_a_96_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(lean_object* v_m_99_, lean_object* v_a_100_){
_start:
{
lean_object* v_buckets_101_; lean_object* v___x_102_; uint64_t v___x_103_; uint64_t v___x_104_; uint64_t v___x_105_; uint64_t v_fold_106_; uint64_t v___x_107_; uint64_t v___x_108_; uint64_t v___x_109_; size_t v___x_110_; size_t v___x_111_; size_t v___x_112_; size_t v___x_113_; size_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v_buckets_101_ = lean_ctor_get(v_m_99_, 1);
v___x_102_ = lean_array_get_size(v_buckets_101_);
v___x_103_ = lean_string_hash(v_a_100_);
v___x_104_ = 32ULL;
v___x_105_ = lean_uint64_shift_right(v___x_103_, v___x_104_);
v_fold_106_ = lean_uint64_xor(v___x_103_, v___x_105_);
v___x_107_ = 16ULL;
v___x_108_ = lean_uint64_shift_right(v_fold_106_, v___x_107_);
v___x_109_ = lean_uint64_xor(v_fold_106_, v___x_108_);
v___x_110_ = lean_uint64_to_usize(v___x_109_);
v___x_111_ = lean_usize_of_nat(v___x_102_);
v___x_112_ = ((size_t)1ULL);
v___x_113_ = lean_usize_sub(v___x_111_, v___x_112_);
v___x_114_ = lean_usize_land(v___x_110_, v___x_113_);
v___x_115_ = lean_array_uget_borrowed(v_buckets_101_, v___x_114_);
v___x_116_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_a_100_, v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg___boxed(lean_object* v_m_117_, lean_object* v_a_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_m_117_, v_a_118_);
lean_dec_ref(v_a_118_);
lean_dec_ref(v_m_117_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(lean_object* v___x_120_, lean_object* v___x_121_, lean_object* v_i_122_, lean_object* v_j_123_, lean_object* v_bs_124_){
_start:
{
lean_object* v_zero_125_; uint8_t v_isZero_126_; 
v_zero_125_ = lean_unsigned_to_nat(0u);
v_isZero_126_ = lean_nat_dec_eq(v_i_122_, v_zero_125_);
if (v_isZero_126_ == 1)
{
lean_dec(v_j_123_);
lean_dec(v_i_122_);
return v_bs_124_;
}
else
{
lean_object* v_entries_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v_snd_130_; lean_object* v_one_131_; lean_object* v_n_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_entries_127_ = lean_ctor_get(v___x_120_, 0);
v___x_128_ = lean_array_fget_borrowed(v___x_121_, v_j_123_);
v___x_129_ = lean_array_fget_borrowed(v_entries_127_, v___x_128_);
v_snd_130_ = lean_ctor_get(v___x_129_, 1);
v_one_131_ = lean_unsigned_to_nat(1u);
v_n_132_ = lean_nat_sub(v_i_122_, v_one_131_);
lean_dec(v_i_122_);
v___x_133_ = lean_nat_add(v_j_123_, v_one_131_);
lean_dec(v_j_123_);
lean_inc(v_snd_130_);
v___x_134_ = lean_array_push(v_bs_124_, v_snd_130_);
v_i_122_ = v_n_132_;
v_j_123_ = v___x_133_;
v_bs_124_ = v___x_134_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg___boxed(lean_object* v___x_136_, lean_object* v___x_137_, lean_object* v_i_138_, lean_object* v_j_139_, lean_object* v_bs_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_136_, v___x_137_, v_i_138_, v_j_139_, v_bs_140_);
lean_dec_ref(v___x_137_);
lean_dec_ref(v___x_136_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize(uint8_t v_dir_150_, lean_object* v_message_151_, uint8_t v_allowEOFBody_152_){
_start:
{
lean_object* v___x_153_; lean_object* v___y_155_; lean_object* v___x_210_; lean_object* v___f_211_; lean_object* v___f_212_; uint8_t v___x_213_; 
v___x_153_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_150_, v_message_151_);
v___x_210_ = l_Std_Http_Header_Name_contentLength;
v___f_211_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0));
v___f_212_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1));
v___x_213_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_211_, v___f_212_, v___x_210_, v___x_153_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; 
v___x_214_ = lean_box(0);
v___y_155_ = v___x_214_;
goto v___jp_154_;
}
else
{
lean_object* v_indexes_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v_entries_220_; lean_object* v___x_221_; 
v_indexes_215_ = lean_ctor_get(v___x_153_, 1);
lean_inc_ref(v_indexes_215_);
v___x_216_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_215_, v___x_210_);
lean_dec_ref(v_indexes_215_);
v___x_217_ = lean_array_get_size(v___x_216_);
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_mk_empty_array_with_capacity(v___x_217_);
v_entries_220_ = l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_153_, v___x_216_, v___x_217_, v___x_218_, v___x_219_);
lean_dec(v___x_216_);
v___x_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_221_, 0, v_entries_220_);
v___y_155_ = v___x_221_;
goto v___jp_154_;
}
v___jp_154_:
{
lean_object* v___x_156_; lean_object* v___f_157_; lean_object* v___f_158_; uint8_t v___x_159_; 
v___x_156_ = l_Std_Http_Header_Name_transferEncoding;
v___f_157_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0));
v___f_158_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1));
v___x_159_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_157_, v___f_158_, v___x_156_, v___x_153_);
if (v___x_159_ == 0)
{
lean_dec_ref(v___x_153_);
if (lean_obj_tag(v___y_155_) == 0)
{
if (v_allowEOFBody_152_ == 0)
{
lean_object* v___x_160_; 
v___x_160_ = lean_box(0);
return v___x_160_;
}
else
{
lean_object* v___x_161_; 
v___x_161_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__3));
return v___x_161_;
}
}
else
{
lean_object* v_val_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_187_; 
v_val_162_ = lean_ctor_get(v___y_155_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___y_155_);
if (v_isSharedCheck_187_ == 0)
{
v___x_164_ = v___y_155_;
v_isShared_165_ = v_isSharedCheck_187_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_val_162_);
lean_dec(v___y_155_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_187_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_166_ = lean_array_get_size(v_val_162_);
v___x_167_ = lean_unsigned_to_nat(1u);
v___x_168_ = lean_nat_dec_eq(v___x_166_, v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; 
lean_del_object(v___x_164_);
lean_dec(v_val_162_);
v___x_169_ = lean_box(0);
return v___x_169_;
}
else
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = lean_array_fget(v_val_162_, v___x_170_);
lean_dec(v_val_162_);
v___x_172_ = lean_string_utf8_byte_size(v___x_171_);
v___x_173_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_173_, 0, v___x_171_);
lean_ctor_set(v___x_173_, 1, v___x_170_);
lean_ctor_set(v___x_173_, 2, v___x_172_);
v___x_174_ = l_String_Slice_toNat_x3f(v___x_173_);
lean_dec_ref(v___x_173_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v___x_175_; 
lean_del_object(v___x_164_);
v___x_175_ = lean_box(0);
return v___x_175_;
}
else
{
lean_object* v_val_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_186_; 
v_val_176_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_186_ == 0)
{
v___x_178_ = v___x_174_;
v_isShared_179_ = v_isSharedCheck_186_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_val_176_);
lean_dec(v___x_174_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_186_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v_val_176_);
v___x_181_ = v___x_164_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_val_176_);
v___x_181_ = v_reuseFailAlloc_185_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_183_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_181_);
v___x_183_ = v___x_178_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_181_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
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
lean_object* v_indexes_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v_entries_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v_indexes_188_ = lean_ctor_get(v___x_153_, 1);
lean_inc_ref(v_indexes_188_);
v___x_189_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_188_, v___x_156_);
lean_dec_ref(v_indexes_188_);
v___x_190_ = lean_array_get_size(v___x_189_);
v___x_191_ = lean_unsigned_to_nat(0u);
v___x_192_ = lean_mk_empty_array_with_capacity(v___x_190_);
v_entries_193_ = l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_153_, v___x_189_, v___x_190_, v___x_191_, v___x_192_);
lean_dec(v___x_189_);
lean_dec_ref(v___x_153_);
v___x_194_ = lean_array_get_size(v_entries_193_);
v___x_195_ = lean_unsigned_to_nat(1u);
v___x_196_ = lean_nat_dec_eq(v___x_194_, v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; 
lean_dec_ref(v_entries_193_);
lean_dec(v___y_155_);
v___x_197_ = lean_box(0);
return v___x_197_;
}
else
{
lean_object* v___x_198_; lean_object* v_te_199_; 
v___x_198_ = lean_array_fget(v_entries_193_, v___x_191_);
lean_dec_ref(v_entries_193_);
v_te_199_ = l_Std_Http_Header_TransferEncoding_parse(v___x_198_);
if (lean_obj_tag(v_te_199_) == 0)
{
lean_object* v___x_200_; 
lean_dec(v___y_155_);
v___x_200_ = lean_box(0);
return v___x_200_;
}
else
{
lean_object* v_val_201_; uint8_t v___x_202_; 
v_val_201_ = lean_ctor_get(v_te_199_, 0);
lean_inc(v_val_201_);
lean_dec_ref(v_te_199_);
v___x_202_ = l_Std_Http_Header_TransferEncoding_isChunked(v_val_201_);
lean_dec(v_val_201_);
if (v___x_202_ == 1)
{
if (lean_obj_tag(v___y_155_) == 0)
{
uint8_t v___x_203_; uint8_t v___x_204_; uint8_t v___x_205_; 
v___x_203_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_150_, v_message_151_);
v___x_204_ = 0;
v___x_205_ = l_Std_Http_instBEqVersion_beq(v___x_203_, v___x_204_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; 
v___x_206_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__4));
return v___x_206_;
}
else
{
lean_object* v___x_207_; 
v___x_207_ = lean_box(0);
return v___x_207_;
}
}
else
{
lean_object* v___x_208_; 
lean_dec(v___y_155_);
v___x_208_ = lean_box(0);
return v___x_208_;
}
}
else
{
lean_object* v___x_209_; 
lean_dec(v___y_155_);
v___x_209_ = lean_box(0);
return v___x_209_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize___boxed(lean_object* v_dir_222_, lean_object* v_message_223_, lean_object* v_allowEOFBody_224_){
_start:
{
uint8_t v_dir_boxed_225_; uint8_t v_allowEOFBody_boxed_226_; lean_object* v_res_227_; 
v_dir_boxed_225_ = lean_unbox(v_dir_222_);
v_allowEOFBody_boxed_226_ = lean_unbox(v_allowEOFBody_224_);
v_res_227_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v_dir_boxed_225_, v_message_223_, v_allowEOFBody_boxed_226_);
lean_dec(v_message_223_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(lean_object* v_00_u03b2_228_, lean_object* v_m_229_, lean_object* v_a_230_, lean_object* v_hma_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_m_229_, v_a_230_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___boxed(lean_object* v_00_u03b2_233_, lean_object* v_m_234_, lean_object* v_a_235_, lean_object* v_hma_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(v_00_u03b2_233_, v_m_234_, v_a_235_, v_hma_236_);
lean_dec_ref(v_a_235_);
lean_dec_ref(v_m_234_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(lean_object* v___x_238_, lean_object* v___x_239_, lean_object* v_as_240_, lean_object* v_i_241_, lean_object* v_j_242_, lean_object* v_inv_243_, lean_object* v_bs_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_238_, v___x_239_, v_i_241_, v_j_242_, v_bs_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___boxed(lean_object* v___x_246_, lean_object* v___x_247_, lean_object* v_as_248_, lean_object* v_i_249_, lean_object* v_j_250_, lean_object* v_inv_251_, lean_object* v_bs_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(v___x_246_, v___x_247_, v_as_248_, v_i_249_, v_j_250_, v_inv_251_, v_bs_252_);
lean_dec_ref(v_as_248_);
lean_dec_ref(v___x_247_);
lean_dec_ref(v___x_246_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0(lean_object* v_00_u03b2_254_, lean_object* v_a_255_, lean_object* v_x_256_, lean_object* v_x_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___redArg(v_a_255_, v_x_256_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_259_, lean_object* v_a_260_, lean_object* v_x_261_, lean_object* v_x_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0_spec__0(v_00_u03b2_259_, v_a_260_, v_x_261_, v_x_262_);
lean_dec(v_x_261_);
lean_dec_ref(v_a_260_);
return v_res_263_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(lean_object* v_as_265_, size_t v_i_266_, size_t v_stop_267_){
_start:
{
uint8_t v___x_268_; 
v___x_268_ = lean_usize_dec_eq(v_i_266_, v_stop_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_269_ = lean_array_uget_borrowed(v_as_265_, v_i_266_);
v___x_270_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___closed__0));
v___x_271_ = lean_string_dec_eq(v___x_269_, v___x_270_);
if (v___x_271_ == 0)
{
size_t v___x_272_; size_t v___x_273_; 
v___x_272_ = ((size_t)1ULL);
v___x_273_ = lean_usize_add(v_i_266_, v___x_272_);
v_i_266_ = v___x_273_;
goto _start;
}
else
{
return v___x_271_;
}
}
else
{
uint8_t v___x_275_; 
v___x_275_ = 0;
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___boxed(lean_object* v_as_276_, lean_object* v_i_277_, lean_object* v_stop_278_){
_start:
{
size_t v_i_boxed_279_; size_t v_stop_boxed_280_; uint8_t v_res_281_; lean_object* v_r_282_; 
v_i_boxed_279_ = lean_unbox_usize(v_i_277_);
lean_dec(v_i_277_);
v_stop_boxed_280_ = lean_unbox_usize(v_stop_278_);
lean_dec(v_stop_278_);
v_res_281_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(v_as_276_, v_i_boxed_279_, v_stop_boxed_280_);
lean_dec_ref(v_as_276_);
v_r_282_ = lean_box(v_res_281_);
return v_r_282_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(lean_object* v_as_284_, size_t v_i_285_, size_t v_stop_286_){
_start:
{
uint8_t v___x_287_; 
v___x_287_ = lean_usize_dec_eq(v_i_285_, v_stop_286_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_288_ = lean_array_uget_borrowed(v_as_284_, v_i_285_);
v___x_289_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___closed__0));
v___x_290_ = lean_string_dec_eq(v___x_288_, v___x_289_);
if (v___x_290_ == 0)
{
size_t v___x_291_; size_t v___x_292_; 
v___x_291_ = ((size_t)1ULL);
v___x_292_ = lean_usize_add(v_i_285_, v___x_291_);
v_i_285_ = v___x_292_;
goto _start;
}
else
{
return v___x_290_;
}
}
else
{
uint8_t v___x_294_; 
v___x_294_ = 0;
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___boxed(lean_object* v_as_295_, lean_object* v_i_296_, lean_object* v_stop_297_){
_start:
{
size_t v_i_boxed_298_; size_t v_stop_boxed_299_; uint8_t v_res_300_; lean_object* v_r_301_; 
v_i_boxed_298_ = lean_unbox_usize(v_i_296_);
lean_dec(v_i_296_);
v_stop_boxed_299_ = lean_unbox_usize(v_stop_297_);
lean_dec(v_stop_297_);
v_res_300_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(v_as_295_, v_i_boxed_298_, v_stop_boxed_299_);
lean_dec_ref(v_as_295_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(lean_object* v_as_302_, size_t v_i_303_, size_t v_stop_304_, lean_object* v_b_305_){
_start:
{
lean_object* v___y_307_; uint8_t v___x_311_; 
v___x_311_ = lean_usize_dec_eq(v_i_303_, v_stop_304_);
if (v___x_311_ == 0)
{
if (lean_obj_tag(v_b_305_) == 0)
{
v___y_307_ = v_b_305_;
goto v___jp_306_;
}
else
{
lean_object* v_val_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v_val_312_ = lean_ctor_get(v_b_305_, 0);
lean_inc(v_val_312_);
lean_dec_ref(v_b_305_);
v___x_313_ = lean_array_uget_borrowed(v_as_302_, v_i_303_);
lean_inc(v___x_313_);
v___x_314_ = l_Std_Http_Header_Connection_parse(v___x_313_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v___x_315_; 
lean_dec(v_val_312_);
v___x_315_ = lean_box(0);
v___y_307_ = v___x_315_;
goto v___jp_306_;
}
else
{
lean_object* v_val_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_324_; 
v_val_316_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_324_ == 0)
{
v___x_318_ = v___x_314_;
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_val_316_);
lean_dec(v___x_314_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_320_ = l_Array_append___redArg(v_val_312_, v_val_316_);
lean_dec(v_val_316_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_320_);
v___x_322_ = v___x_318_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
v___y_307_ = v___x_322_;
goto v___jp_306_;
}
}
}
}
}
else
{
return v_b_305_;
}
v___jp_306_:
{
size_t v___x_308_; size_t v___x_309_; 
v___x_308_ = ((size_t)1ULL);
v___x_309_ = lean_usize_add(v_i_303_, v___x_308_);
v_i_303_ = v___x_309_;
v_b_305_ = v___y_307_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2___boxed(lean_object* v_as_325_, lean_object* v_i_326_, lean_object* v_stop_327_, lean_object* v_b_328_){
_start:
{
size_t v_i_boxed_329_; size_t v_stop_boxed_330_; lean_object* v_res_331_; 
v_i_boxed_329_ = lean_unbox_usize(v_i_326_);
lean_dec(v_i_326_);
v_stop_boxed_330_ = lean_unbox_usize(v_stop_327_);
lean_dec(v_stop_327_);
v_res_331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_as_325_, v_i_boxed_329_, v_stop_boxed_330_, v_b_328_);
lean_dec_ref(v_as_325_);
return v_res_331_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(uint8_t v_dir_336_, lean_object* v_message_337_){
_start:
{
lean_object* v_val_339_; lean_object* v___y_357_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___f_362_; lean_object* v___f_363_; uint8_t v___x_364_; 
v___x_360_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_336_, v_message_337_);
v___x_361_ = l_Std_Http_Header_Name_connection;
v___f_362_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0));
v___f_363_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1));
v___x_364_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_362_, v___f_363_, v___x_361_, v___x_360_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; 
lean_dec_ref(v___x_360_);
v___x_365_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0));
v_val_339_ = v___x_365_;
goto v___jp_338_;
}
else
{
lean_object* v_indexes_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v_entries_371_; lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v_indexes_366_ = lean_ctor_get(v___x_360_, 1);
lean_inc_ref(v_indexes_366_);
v___x_367_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___redArg(v_indexes_366_, v___x_361_);
lean_dec_ref(v_indexes_366_);
v___x_368_ = lean_array_get_size(v___x_367_);
v___x_369_ = lean_unsigned_to_nat(0u);
v___x_370_ = lean_mk_empty_array_with_capacity(v___x_368_);
v_entries_371_ = l_Array_mapFinIdxM_map___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___redArg(v___x_360_, v___x_367_, v___x_368_, v___x_369_, v___x_370_);
lean_dec(v___x_367_);
lean_dec_ref(v___x_360_);
v___x_372_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0));
v___x_373_ = lean_array_get_size(v_entries_371_);
v___x_374_ = lean_nat_dec_lt(v___x_369_, v___x_373_);
if (v___x_374_ == 0)
{
lean_dec_ref(v_entries_371_);
v_val_339_ = v___x_372_;
goto v___jp_338_;
}
else
{
lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_375_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__1));
v___x_376_ = lean_nat_dec_le(v___x_373_, v___x_373_);
if (v___x_376_ == 0)
{
if (v___x_374_ == 0)
{
lean_dec_ref(v_entries_371_);
v_val_339_ = v___x_372_;
goto v___jp_338_;
}
else
{
size_t v___x_377_; size_t v___x_378_; lean_object* v___x_379_; 
v___x_377_ = ((size_t)0ULL);
v___x_378_ = lean_usize_of_nat(v___x_373_);
v___x_379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_entries_371_, v___x_377_, v___x_378_, v___x_375_);
lean_dec_ref(v_entries_371_);
v___y_357_ = v___x_379_;
goto v___jp_356_;
}
}
else
{
size_t v___x_380_; size_t v___x_381_; lean_object* v___x_382_; 
v___x_380_ = ((size_t)0ULL);
v___x_381_ = lean_usize_of_nat(v___x_373_);
v___x_382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_entries_371_, v___x_380_, v___x_381_, v___x_375_);
lean_dec_ref(v_entries_371_);
v___y_357_ = v___x_382_;
goto v___jp_356_;
}
}
}
v___jp_338_:
{
uint8_t v___x_340_; uint8_t v___x_341_; uint8_t v___x_342_; 
v___x_340_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_336_, v_message_337_);
v___x_341_ = 1;
v___x_342_ = l_Std_Http_instBEqVersion_beq(v___x_340_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = lean_array_get_size(v_val_339_);
v___x_345_ = lean_nat_dec_lt(v___x_343_, v___x_344_);
if (v___x_345_ == 0)
{
lean_dec_ref(v_val_339_);
return v___x_342_;
}
else
{
if (v___x_345_ == 0)
{
lean_dec_ref(v_val_339_);
return v___x_342_;
}
else
{
size_t v___x_346_; size_t v___x_347_; uint8_t v___x_348_; 
v___x_346_ = ((size_t)0ULL);
v___x_347_ = lean_usize_of_nat(v___x_344_);
v___x_348_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(v_val_339_, v___x_346_, v___x_347_);
lean_dec_ref(v_val_339_);
return v___x_348_;
}
}
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_349_ = lean_unsigned_to_nat(0u);
v___x_350_ = lean_array_get_size(v_val_339_);
v___x_351_ = lean_nat_dec_lt(v___x_349_, v___x_350_);
if (v___x_351_ == 0)
{
lean_dec_ref(v_val_339_);
return v___x_342_;
}
else
{
if (v___x_351_ == 0)
{
lean_dec_ref(v_val_339_);
return v___x_342_;
}
else
{
size_t v___x_352_; size_t v___x_353_; uint8_t v___x_354_; 
v___x_352_ = ((size_t)0ULL);
v___x_353_ = lean_usize_of_nat(v___x_350_);
v___x_354_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(v_val_339_, v___x_352_, v___x_353_);
lean_dec_ref(v_val_339_);
if (v___x_354_ == 0)
{
return v___x_342_;
}
else
{
uint8_t v___x_355_; 
v___x_355_ = 0;
return v___x_355_;
}
}
}
}
}
v___jp_356_:
{
if (lean_obj_tag(v___y_357_) == 0)
{
uint8_t v___x_358_; 
v___x_358_ = 0;
return v___x_358_;
}
else
{
lean_object* v_val_359_; 
v_val_359_ = lean_ctor_get(v___y_357_, 0);
lean_inc(v_val_359_);
lean_dec_ref(v___y_357_);
v_val_339_ = v_val_359_;
goto v___jp_338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___boxed(lean_object* v_dir_383_, lean_object* v_message_384_){
_start:
{
uint8_t v_dir_boxed_385_; uint8_t v_res_386_; lean_object* v_r_387_; 
v_dir_boxed_385_ = lean_unbox(v_dir_383_);
v_res_386_ = l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(v_dir_boxed_385_, v_message_384_);
lean_dec(v_message_384_);
v_r_387_ = lean_box(v_res_386_);
return v_r_387_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1___redArg(lean_object* v_x_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Std_Http_Request_instReprHead_repr___redArg(v_x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1(lean_object* v_x_390_, lean_object* v_prec_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Std_Http_Request_instReprHead_repr___redArg(v_x_390_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1___boxed(lean_object* v_x_393_, lean_object* v_prec_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Std_Http_Protocol_H1_instReprHead___aux__1(v_x_393_, v_prec_394_);
lean_dec(v_prec_394_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3___redArg(lean_object* v_x_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Std_Http_Response_instReprHead_repr___redArg(v_x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3(lean_object* v_x_398_, lean_object* v_prec_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Std_Http_Response_instReprHead_repr___redArg(v_x_398_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3___boxed(lean_object* v_x_401_, lean_object* v_prec_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Std_Http_Protocol_H1_instReprHead___aux__3(v_x_401_, v_prec_402_);
lean_dec(v_prec_402_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead(uint8_t v_dir_406_){
_start:
{
if (v_dir_406_ == 0)
{
lean_object* v___x_407_; 
v___x_407_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprHead___closed__0));
return v___x_407_;
}
else
{
lean_object* v___x_408_; 
v___x_408_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprHead___closed__1));
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___boxed(lean_object* v_dir_409_){
_start:
{
uint8_t v_dir_boxed_410_; lean_object* v_res_411_; 
v_dir_boxed_410_ = lean_unbox(v_dir_409_);
v_res_411_ = l_Std_Http_Protocol_H1_instReprHead(v_dir_boxed_410_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__0(lean_object* v_x_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = lean_string_from_utf8_unchecked(v_x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__1(lean_object* v_x_414_){
_start:
{
lean_object* v_fst_415_; lean_object* v_snd_416_; lean_object* v___x_417_; 
v_fst_415_ = lean_ctor_get(v_x_414_, 0);
lean_inc(v_fst_415_);
v_snd_416_ = lean_ctor_get(v_x_414_, 1);
lean_inc(v_snd_416_);
lean_dec_ref(v_x_414_);
v___x_417_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_415_, v_snd_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2(lean_object* v___x_418_, lean_object* v___x_419_, lean_object* v___x_420_, lean_object* v_name_421_, lean_object* v___x_422_, uint32_t v___x_423_, lean_object* v___x_424_, lean_object* v_it_425_, lean_object* v_acc_426_, lean_object* v_hP_427_, lean_object* v_recur_428_){
_start:
{
lean_object* v_it_430_; lean_object* v_out_431_; lean_object* v_it_447_; lean_object* v_startInclusive_448_; lean_object* v_endExclusive_449_; 
if (lean_obj_tag(v_it_425_) == 0)
{
lean_object* v_currPos_461_; lean_object* v_searcher_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_484_; 
v_currPos_461_ = lean_ctor_get(v_it_425_, 0);
v_searcher_462_ = lean_ctor_get(v_it_425_, 1);
v_isSharedCheck_484_ = !lean_is_exclusive(v_it_425_);
if (v_isSharedCheck_484_ == 0)
{
v___x_464_ = v_it_425_;
v_isShared_465_ = v_isSharedCheck_484_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_searcher_462_);
lean_inc(v_currPos_461_);
lean_dec(v_it_425_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_484_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
uint8_t v___x_466_; 
v___x_466_ = lean_nat_dec_eq(v_searcher_462_, v___x_422_);
if (v___x_466_ == 0)
{
uint32_t v___x_467_; uint8_t v___x_468_; 
lean_dec(v___x_422_);
v___x_467_ = lean_string_utf8_get_fast(v_name_421_, v_searcher_462_);
v___x_468_ = lean_uint32_dec_eq(v___x_467_, v___x_423_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_469_ = lean_string_utf8_next_fast(v_name_421_, v_searcher_462_);
lean_dec(v_searcher_462_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 1, v___x_469_);
v___x_471_ = v___x_464_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_currPos_461_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v___x_469_);
v___x_471_ = v_reuseFailAlloc_473_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; 
v___x_472_ = lean_apply_4(v_recur_428_, v___x_471_, v_acc_426_, lean_box(0), lean_box(0));
return v___x_472_;
}
}
else
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v_slice_477_; lean_object* v_nextIt_479_; 
v___x_474_ = lean_string_utf8_next_fast(v_name_421_, v_searcher_462_);
v___x_475_ = lean_nat_sub(v___x_474_, v_searcher_462_);
v___x_476_ = lean_nat_add(v_searcher_462_, v___x_475_);
lean_dec(v___x_475_);
v_slice_477_ = l_String_Slice_subslice_x21(v___x_424_, v_currPos_461_, v_searcher_462_);
lean_inc(v___x_476_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 1, v___x_476_);
lean_ctor_set(v___x_464_, 0, v___x_476_);
v_nextIt_479_ = v___x_464_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v___x_476_);
v_nextIt_479_ = v_reuseFailAlloc_482_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
lean_object* v_startInclusive_480_; lean_object* v_endExclusive_481_; 
v_startInclusive_480_ = lean_ctor_get(v_slice_477_, 0);
lean_inc(v_startInclusive_480_);
v_endExclusive_481_ = lean_ctor_get(v_slice_477_, 1);
lean_inc(v_endExclusive_481_);
lean_dec_ref(v_slice_477_);
v_it_447_ = v_nextIt_479_;
v_startInclusive_448_ = v_startInclusive_480_;
v_endExclusive_449_ = v_endExclusive_481_;
goto v___jp_446_;
}
}
}
else
{
lean_object* v___x_483_; 
lean_del_object(v___x_464_);
lean_dec(v_searcher_462_);
v___x_483_ = lean_box(1);
v_it_447_ = v___x_483_;
v_startInclusive_448_ = v_currPos_461_;
v_endExclusive_449_ = v___x_422_;
goto v___jp_446_;
}
}
}
else
{
lean_dec_ref(v_recur_428_);
lean_dec(v___x_422_);
return v_acc_426_;
}
v___jp_429_:
{
if (lean_obj_tag(v_acc_426_) == 0)
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_432_, 0, v_out_431_);
v___x_433_ = lean_apply_4(v_recur_428_, v_it_430_, v___x_432_, lean_box(0), lean_box(0));
return v___x_433_;
}
else
{
lean_object* v_val_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_445_; 
v_val_434_ = lean_ctor_get(v_acc_426_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v_acc_426_);
if (v_isSharedCheck_445_ == 0)
{
v___x_436_ = v_acc_426_;
v_isShared_437_ = v_isSharedCheck_445_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_val_434_);
lean_dec(v_acc_426_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_445_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_438_ = lean_string_utf8_extract(v___x_418_, v___x_419_, v___x_420_);
v___x_439_ = lean_string_append(v_val_434_, v___x_438_);
lean_dec_ref(v___x_438_);
v___x_440_ = lean_string_append(v___x_439_, v_out_431_);
lean_dec_ref(v_out_431_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_440_);
v___x_442_ = v___x_436_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_440_);
v___x_442_ = v_reuseFailAlloc_444_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
lean_object* v___x_443_; 
v___x_443_ = lean_apply_4(v_recur_428_, v_it_430_, v___x_442_, lean_box(0), lean_box(0));
return v___x_443_;
}
}
}
}
v___jp_446_:
{
lean_object* v___x_450_; uint32_t v___x_451_; uint32_t v___x_452_; uint8_t v___x_453_; 
v___x_450_ = lean_string_utf8_extract(v_name_421_, v_startInclusive_448_, v_endExclusive_449_);
lean_dec(v_endExclusive_449_);
lean_dec(v_startInclusive_448_);
v___x_451_ = lean_string_utf8_get(v___x_450_, v___x_419_);
v___x_452_ = 97;
v___x_453_ = lean_uint32_dec_le(v___x_452_, v___x_451_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; 
v___x_454_ = lean_string_utf8_set(v___x_450_, v___x_419_, v___x_451_);
v_it_430_ = v_it_447_;
v_out_431_ = v___x_454_;
goto v___jp_429_;
}
else
{
uint32_t v___x_455_; uint8_t v___x_456_; 
v___x_455_ = 122;
v___x_456_ = lean_uint32_dec_le(v___x_451_, v___x_455_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; 
v___x_457_ = lean_string_utf8_set(v___x_450_, v___x_419_, v___x_451_);
v_it_430_ = v_it_447_;
v_out_431_ = v___x_457_;
goto v___jp_429_;
}
else
{
uint32_t v___x_458_; uint32_t v___x_459_; lean_object* v___x_460_; 
v___x_458_ = 4294967264;
v___x_459_ = lean_uint32_add(v___x_451_, v___x_458_);
v___x_460_ = lean_string_utf8_set(v___x_450_, v___x_419_, v___x_459_);
v_it_430_ = v_it_447_;
v_out_431_ = v___x_460_;
goto v___jp_429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed(lean_object* v___x_485_, lean_object* v___x_486_, lean_object* v___x_487_, lean_object* v_name_488_, lean_object* v___x_489_, lean_object* v___x_490_, lean_object* v___x_491_, lean_object* v_it_492_, lean_object* v_acc_493_, lean_object* v_hP_494_, lean_object* v_recur_495_){
_start:
{
uint32_t v___x_2817__boxed_496_; lean_object* v_res_497_; 
v___x_2817__boxed_496_ = lean_unbox_uint32(v___x_490_);
lean_dec(v___x_490_);
v_res_497_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2(v___x_485_, v___x_486_, v___x_487_, v_name_488_, v___x_489_, v___x_2817__boxed_496_, v___x_491_, v_it_492_, v_acc_493_, v_hP_494_, v_recur_495_);
lean_dec_ref(v___x_491_);
lean_dec_ref(v_name_488_);
lean_dec(v___x_487_);
lean_dec(v___x_486_);
lean_dec_ref(v___x_485_);
return v_res_497_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__4(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__3));
v___x_503_ = lean_string_utf8_byte_size(v___x_502_);
return v___x_503_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___boxed__const__1(void){
_start:
{
uint32_t v___x_505_; lean_object* v___x_506_; 
v___x_505_ = 45;
v___x_506_ = lean_box_uint32(v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3(lean_object* v_buf_507_, lean_object* v_name_508_, lean_object* v_value_509_){
_start:
{
lean_object* v___y_511_; lean_object* v___f_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v_it_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___f_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___f_530_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__2));
v___x_531_ = lean_unsigned_to_nat(0u);
v___x_532_ = lean_string_utf8_byte_size(v_name_508_);
lean_inc_ref(v_name_508_);
v___x_533_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_533_, 0, v_name_508_);
lean_ctor_set(v___x_533_, 1, v___x_531_);
lean_ctor_set(v___x_533_, 2, v___x_532_);
lean_inc_ref(v___x_533_);
v_it_534_ = l_String_Slice_splitToSubslice___redArg(v___x_533_, v___f_530_);
v___x_535_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__3));
v___x_536_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__4, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__4_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__4);
v___x_537_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___boxed__const__1;
v___f_538_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__2___boxed), 11, 7);
lean_closure_set(v___f_538_, 0, v___x_535_);
lean_closure_set(v___f_538_, 1, v___x_531_);
lean_closure_set(v___f_538_, 2, v___x_536_);
lean_closure_set(v___f_538_, 3, v_name_508_);
lean_closure_set(v___f_538_, 4, v___x_532_);
lean_closure_set(v___f_538_, 5, v___x_537_);
lean_closure_set(v___f_538_, 6, v___x_533_);
v___x_539_ = lean_box(0);
v___x_540_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_538_, v_it_534_, v___x_539_, lean_box(0));
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v___x_541_; 
v___x_541_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5));
v___y_511_ = v___x_541_;
goto v___jp_510_;
}
else
{
lean_object* v_val_542_; 
v_val_542_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_val_542_);
lean_dec_ref(v___x_540_);
v___y_511_ = v_val_542_;
goto v___jp_510_;
}
v___jp_510_:
{
lean_object* v_data_512_; lean_object* v_size_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_529_; 
v_data_512_ = lean_ctor_get(v_buf_507_, 0);
v_size_513_ = lean_ctor_get(v_buf_507_, 1);
v_isSharedCheck_529_ = !lean_is_exclusive(v_buf_507_);
if (v_isSharedCheck_529_ == 0)
{
v___x_515_ = v_buf_507_;
v_isShared_516_ = v_isSharedCheck_529_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_size_513_);
lean_inc(v_data_512_);
lean_dec(v_buf_507_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_529_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_517_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__0));
v___x_518_ = lean_string_append(v___y_511_, v___x_517_);
v___x_519_ = lean_string_append(v___x_518_, v_value_509_);
v___x_520_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__1));
v___x_521_ = lean_string_append(v___x_519_, v___x_520_);
v___x_522_ = lean_string_to_utf8(v___x_521_);
lean_dec_ref(v___x_521_);
lean_inc_ref(v___x_522_);
v___x_523_ = lean_array_push(v_data_512_, v___x_522_);
v___x_524_ = lean_byte_array_size(v___x_522_);
lean_dec_ref(v___x_522_);
v___x_525_ = lean_nat_add(v_size_513_, v___x_524_);
lean_dec(v_size_513_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 1, v___x_525_);
lean_ctor_set(v___x_515_, 0, v___x_523_);
v___x_527_ = v___x_515_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v___x_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___boxed(lean_object* v_buf_543_, lean_object* v_name_544_, lean_object* v_value_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3(v_buf_543_, v_name_544_, v_value_545_);
lean_dec_ref(v_value_545_);
return v_res_546_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__1));
v___x_551_ = lean_string_to_utf8(v___x_550_);
return v___x_551_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4(void){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3);
v___x_553_ = lean_byte_array_size(v___x_552_);
return v___x_553_;
}
}
static uint8_t _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26(void){
_start:
{
uint32_t v___x_584_; uint8_t v___x_585_; 
v___x_584_ = 32;
v___x_585_ = lean_uint32_to_uint8(v___x_584_);
return v___x_585_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27(void){
_start:
{
uint8_t v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_586_ = lean_uint8_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26);
v___x_587_ = lean_unsigned_to_nat(1u);
v___x_588_ = lean_mk_empty_array_with_capacity(v___x_587_);
v___x_589_ = lean_box(v___x_586_);
v___x_590_ = lean_array_push(v___x_588_, v___x_589_);
v___x_591_ = lean_byte_array_mk(v___x_590_);
return v___x_591_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27);
v___x_593_ = lean_byte_array_size(v___x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1(lean_object* v_buffer_637_, lean_object* v_req_638_){
_start:
{
uint8_t v_method_639_; uint8_t v_version_640_; lean_object* v_uri_641_; lean_object* v_headers_642_; lean_object* v___f_643_; lean_object* v___f_644_; lean_object* v___f_645_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v_port_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v_host_768_; lean_object* v_port_769_; lean_object* v___y_770_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v_port_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v_host_858_; lean_object* v_port_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_880_; 
v_method_639_ = lean_ctor_get_uint8(v_req_638_, sizeof(void*)*2);
v_version_640_ = lean_ctor_get_uint8(v_req_638_, sizeof(void*)*2 + 1);
v_uri_641_ = lean_ctor_get(v_req_638_, 0);
lean_inc(v_uri_641_);
v_headers_642_ = lean_ctor_get(v_req_638_, 1);
lean_inc_ref(v_headers_642_);
lean_dec_ref(v_req_638_);
v___f_643_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__0));
v___f_644_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1));
v___f_645_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2));
switch(v_method_639_)
{
case 0:
{
lean_object* v___x_960_; 
v___x_960_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32));
v___y_880_ = v___x_960_;
goto v___jp_879_;
}
case 1:
{
lean_object* v___x_961_; 
v___x_961_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33));
v___y_880_ = v___x_961_;
goto v___jp_879_;
}
case 2:
{
lean_object* v___x_962_; 
v___x_962_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34));
v___y_880_ = v___x_962_;
goto v___jp_879_;
}
case 3:
{
lean_object* v___x_963_; 
v___x_963_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35));
v___y_880_ = v___x_963_;
goto v___jp_879_;
}
case 4:
{
lean_object* v___x_964_; 
v___x_964_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36));
v___y_880_ = v___x_964_;
goto v___jp_879_;
}
case 5:
{
lean_object* v___x_965_; 
v___x_965_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37));
v___y_880_ = v___x_965_;
goto v___jp_879_;
}
case 6:
{
lean_object* v___x_966_; 
v___x_966_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38));
v___y_880_ = v___x_966_;
goto v___jp_879_;
}
case 7:
{
lean_object* v___x_967_; 
v___x_967_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39));
v___y_880_ = v___x_967_;
goto v___jp_879_;
}
case 8:
{
lean_object* v___x_968_; 
v___x_968_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40));
v___y_880_ = v___x_968_;
goto v___jp_879_;
}
case 9:
{
lean_object* v___x_969_; 
v___x_969_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41));
v___y_880_ = v___x_969_;
goto v___jp_879_;
}
case 10:
{
lean_object* v___x_970_; 
v___x_970_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42));
v___y_880_ = v___x_970_;
goto v___jp_879_;
}
case 11:
{
lean_object* v___x_971_; 
v___x_971_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43));
v___y_880_ = v___x_971_;
goto v___jp_879_;
}
case 12:
{
lean_object* v___x_972_; 
v___x_972_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44));
v___y_880_ = v___x_972_;
goto v___jp_879_;
}
case 13:
{
lean_object* v___x_973_; 
v___x_973_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45));
v___y_880_ = v___x_973_;
goto v___jp_879_;
}
case 14:
{
lean_object* v___x_974_; 
v___x_974_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46));
v___y_880_ = v___x_974_;
goto v___jp_879_;
}
case 15:
{
lean_object* v___x_975_; 
v___x_975_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47));
v___y_880_ = v___x_975_;
goto v___jp_879_;
}
case 16:
{
lean_object* v___x_976_; 
v___x_976_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48));
v___y_880_ = v___x_976_;
goto v___jp_879_;
}
case 17:
{
lean_object* v___x_977_; 
v___x_977_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49));
v___y_880_ = v___x_977_;
goto v___jp_879_;
}
case 18:
{
lean_object* v___x_978_; 
v___x_978_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50));
v___y_880_ = v___x_978_;
goto v___jp_879_;
}
case 19:
{
lean_object* v___x_979_; 
v___x_979_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51));
v___y_880_ = v___x_979_;
goto v___jp_879_;
}
case 20:
{
lean_object* v___x_980_; 
v___x_980_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52));
v___y_880_ = v___x_980_;
goto v___jp_879_;
}
case 21:
{
lean_object* v___x_981_; 
v___x_981_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53));
v___y_880_ = v___x_981_;
goto v___jp_879_;
}
case 22:
{
lean_object* v___x_982_; 
v___x_982_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54));
v___y_880_ = v___x_982_;
goto v___jp_879_;
}
case 23:
{
lean_object* v___x_983_; 
v___x_983_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55));
v___y_880_ = v___x_983_;
goto v___jp_879_;
}
case 24:
{
lean_object* v___x_984_; 
v___x_984_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56));
v___y_880_ = v___x_984_;
goto v___jp_879_;
}
case 25:
{
lean_object* v___x_985_; 
v___x_985_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57));
v___y_880_ = v___x_985_;
goto v___jp_879_;
}
case 26:
{
lean_object* v___x_986_; 
v___x_986_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58));
v___y_880_ = v___x_986_;
goto v___jp_879_;
}
case 27:
{
lean_object* v___x_987_; 
v___x_987_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59));
v___y_880_ = v___x_987_;
goto v___jp_879_;
}
case 28:
{
lean_object* v___x_988_; 
v___x_988_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60));
v___y_880_ = v___x_988_;
goto v___jp_879_;
}
case 29:
{
lean_object* v___x_989_; 
v___x_989_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61));
v___y_880_ = v___x_989_;
goto v___jp_879_;
}
case 30:
{
lean_object* v___x_990_; 
v___x_990_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62));
v___y_880_ = v___x_990_;
goto v___jp_879_;
}
case 31:
{
lean_object* v___x_991_; 
v___x_991_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63));
v___y_880_ = v___x_991_;
goto v___jp_879_;
}
case 32:
{
lean_object* v___x_992_; 
v___x_992_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64));
v___y_880_ = v___x_992_;
goto v___jp_879_;
}
case 33:
{
lean_object* v___x_993_; 
v___x_993_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65));
v___y_880_ = v___x_993_;
goto v___jp_879_;
}
case 34:
{
lean_object* v___x_994_; 
v___x_994_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66));
v___y_880_ = v___x_994_;
goto v___jp_879_;
}
case 35:
{
lean_object* v___x_995_; 
v___x_995_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67));
v___y_880_ = v___x_995_;
goto v___jp_879_;
}
case 36:
{
lean_object* v___x_996_; 
v___x_996_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__68));
v___y_880_ = v___x_996_;
goto v___jp_879_;
}
case 37:
{
lean_object* v___x_997_; 
v___x_997_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__69));
v___y_880_ = v___x_997_;
goto v___jp_879_;
}
case 38:
{
lean_object* v___x_998_; 
v___x_998_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__70));
v___y_880_ = v___x_998_;
goto v___jp_879_;
}
default: 
{
lean_object* v___x_999_; 
v___x_999_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__71));
v___y_880_ = v___x_999_;
goto v___jp_879_;
}
}
v___jp_646_:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v_buffer_658_; lean_object* v_buffer_659_; lean_object* v_data_660_; lean_object* v_size_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_670_; 
v___x_650_ = lean_string_to_utf8(v___y_649_);
lean_inc_ref(v___x_650_);
v___x_651_ = lean_array_push(v___y_648_, v___x_650_);
v___x_652_ = lean_byte_array_size(v___x_650_);
lean_dec_ref(v___x_650_);
v___x_653_ = lean_nat_add(v___y_647_, v___x_652_);
lean_dec(v___y_647_);
v___x_654_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3);
v___x_655_ = lean_array_push(v___x_651_, v___x_654_);
v___x_656_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4);
v___x_657_ = lean_nat_add(v___x_653_, v___x_656_);
lean_dec(v___x_653_);
v_buffer_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_buffer_658_, 0, v___x_655_);
lean_ctor_set(v_buffer_658_, 1, v___x_657_);
v_buffer_659_ = l_Std_Http_Headers_fold___redArg(v_headers_642_, v_buffer_658_, v___f_645_);
lean_dec_ref(v_headers_642_);
v_data_660_ = lean_ctor_get(v_buffer_659_, 0);
v_size_661_ = lean_ctor_get(v_buffer_659_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v_buffer_659_);
if (v_isSharedCheck_670_ == 0)
{
v___x_663_ = v_buffer_659_;
v_isShared_664_ = v_isSharedCheck_670_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_size_661_);
lean_inc(v_data_660_);
lean_dec(v_buffer_659_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_670_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_665_ = lean_array_push(v_data_660_, v___x_654_);
v___x_666_ = lean_nat_add(v_size_661_, v___x_656_);
lean_dec(v_size_661_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 1, v___x_666_);
lean_ctor_set(v___x_663_, 0, v___x_665_);
v___x_668_ = v___x_663_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
v___jp_671_:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_677_ = lean_string_to_utf8(v___y_676_);
lean_dec_ref(v___y_676_);
lean_inc_ref(v___x_677_);
v___x_678_ = lean_array_push(v___y_672_, v___x_677_);
v___x_679_ = lean_byte_array_size(v___x_677_);
lean_dec_ref(v___x_677_);
v___x_680_ = lean_nat_add(v___y_673_, v___x_679_);
lean_dec(v___y_673_);
v___x_681_ = lean_array_push(v___x_678_, v___y_674_);
v___x_682_ = lean_nat_add(v___x_680_, v___y_675_);
lean_dec(v___x_680_);
switch(v_version_640_)
{
case 0:
{
lean_object* v___x_683_; 
v___x_683_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5));
v___y_647_ = v___x_682_;
v___y_648_ = v___x_681_;
v___y_649_ = v___x_683_;
goto v___jp_646_;
}
case 1:
{
lean_object* v___x_684_; 
v___x_684_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6));
v___y_647_ = v___x_682_;
v___y_648_ = v___x_681_;
v___y_649_ = v___x_684_;
goto v___jp_646_;
}
case 2:
{
lean_object* v___x_685_; 
v___x_685_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7));
v___y_647_ = v___x_682_;
v___y_648_ = v___x_681_;
v___y_649_ = v___x_685_;
goto v___jp_646_;
}
default: 
{
lean_object* v___x_686_; 
v___x_686_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___y_647_ = v___x_682_;
v___y_648_ = v___x_681_;
v___y_649_ = v___x_686_;
goto v___jp_646_;
}
}
}
v___jp_687_:
{
if (lean_obj_tag(v___y_690_) == 0)
{
v___y_672_ = v___y_688_;
v___y_673_ = v___y_689_;
v___y_674_ = v___y_691_;
v___y_675_ = v___y_692_;
v___y_676_ = v___y_693_;
goto v___jp_671_;
}
else
{
lean_object* v_val_694_; lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v_val_694_ = lean_ctor_get(v___y_690_, 0);
lean_inc(v_val_694_);
lean_dec_ref(v___y_690_);
v___x_695_ = lean_array_get_size(v_val_694_);
v___x_696_ = lean_unsigned_to_nat(0u);
v___x_697_ = lean_nat_dec_eq(v___x_695_, v___x_696_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v_encodedParams_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_698_ = lean_array_to_list(v_val_694_);
v___x_699_ = lean_box(0);
v_encodedParams_700_ = l_List_mapTR_loop___redArg(v___f_644_, v___x_698_, v___x_699_);
v___x_701_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9));
v___x_702_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10));
v___x_703_ = l_String_intercalate(v___x_702_, v_encodedParams_700_);
v___x_704_ = lean_string_append(v___x_701_, v___x_703_);
lean_dec_ref(v___x_703_);
v___x_705_ = lean_string_append(v___y_693_, v___x_704_);
lean_dec_ref(v___x_704_);
v___y_672_ = v___y_688_;
v___y_673_ = v___y_689_;
v___y_674_ = v___y_691_;
v___y_675_ = v___y_692_;
v___y_676_ = v___x_705_;
goto v___jp_671_;
}
else
{
lean_dec(v_val_694_);
v___y_672_ = v___y_688_;
v___y_673_ = v___y_689_;
v___y_674_ = v___y_691_;
v___y_675_ = v___y_692_;
v___y_676_ = v___y_693_;
goto v___jp_671_;
}
}
}
v___jp_706_:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_716_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11));
v___x_717_ = lean_string_append(v___y_710_, v___x_716_);
v___x_718_ = lean_string_append(v___x_717_, v___y_709_);
lean_dec_ref(v___y_709_);
v___x_719_ = lean_string_append(v___x_718_, v___y_708_);
lean_dec_ref(v___y_708_);
v___x_720_ = lean_string_append(v___x_719_, v___y_707_);
lean_dec_ref(v___y_707_);
v___x_721_ = lean_string_append(v___x_720_, v___y_715_);
lean_dec_ref(v___y_715_);
v___y_672_ = v___y_711_;
v___y_673_ = v___y_712_;
v___y_674_ = v___y_713_;
v___y_675_ = v___y_714_;
v___y_676_ = v___x_721_;
goto v___jp_671_;
}
v___jp_722_:
{
if (lean_obj_tag(v___y_726_) == 0)
{
lean_object* v___x_732_; 
v___x_732_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5));
v___y_707_ = v___y_731_;
v___y_708_ = v___y_724_;
v___y_709_ = v___y_723_;
v___y_710_ = v___y_725_;
v___y_711_ = v___y_727_;
v___y_712_ = v___y_728_;
v___y_713_ = v___y_729_;
v___y_714_ = v___y_730_;
v___y_715_ = v___x_732_;
goto v___jp_706_;
}
else
{
lean_object* v_val_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v_val_733_ = lean_ctor_get(v___y_726_, 0);
lean_inc(v_val_733_);
lean_dec_ref(v___y_726_);
v___x_734_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12));
v___x_735_ = l_Std_Http_URI_EncodedFragment_encode(v_val_733_);
lean_dec(v_val_733_);
v___x_736_ = lean_string_from_utf8_unchecked(v___x_735_);
v___x_737_ = lean_string_append(v___x_734_, v___x_736_);
lean_dec_ref(v___x_736_);
v___y_707_ = v___y_731_;
v___y_708_ = v___y_724_;
v___y_709_ = v___y_723_;
v___y_710_ = v___y_725_;
v___y_711_ = v___y_727_;
v___y_712_ = v___y_728_;
v___y_713_ = v___y_729_;
v___y_714_ = v___y_730_;
v___y_715_ = v___x_737_;
goto v___jp_706_;
}
}
v___jp_738_:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = lean_string_append(v___y_742_, v___y_740_);
lean_dec_ref(v___y_740_);
v___x_747_ = lean_string_append(v___x_746_, v___y_745_);
lean_dec_ref(v___y_745_);
v___y_672_ = v___y_739_;
v___y_673_ = v___y_741_;
v___y_674_ = v___y_743_;
v___y_675_ = v___y_744_;
v___y_676_ = v___x_747_;
goto v___jp_671_;
}
v___jp_748_:
{
switch(lean_obj_tag(v_port_753_))
{
case 0:
{
lean_object* v___x_756_; 
v___x_756_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5));
v___y_739_ = v___y_749_;
v___y_740_ = v___y_755_;
v___y_741_ = v___y_751_;
v___y_742_ = v___y_750_;
v___y_743_ = v___y_752_;
v___y_744_ = v___y_754_;
v___y_745_ = v___x_756_;
goto v___jp_738_;
}
case 1:
{
lean_object* v___x_757_; 
v___x_757_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11));
v___y_739_ = v___y_749_;
v___y_740_ = v___y_755_;
v___y_741_ = v___y_751_;
v___y_742_ = v___y_750_;
v___y_743_ = v___y_752_;
v___y_744_ = v___y_754_;
v___y_745_ = v___x_757_;
goto v___jp_738_;
}
default: 
{
uint16_t v_port_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v_port_758_ = lean_ctor_get_uint16(v_port_753_, 0);
lean_dec_ref(v_port_753_);
v___x_759_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11));
v___x_760_ = lean_uint16_to_nat(v_port_758_);
v___x_761_ = l_Nat_reprFast(v___x_760_);
v___x_762_ = lean_string_append(v___x_759_, v___x_761_);
lean_dec_ref(v___x_761_);
v___y_739_ = v___y_749_;
v___y_740_ = v___y_755_;
v___y_741_ = v___y_751_;
v___y_742_ = v___y_750_;
v___y_743_ = v___y_752_;
v___y_744_ = v___y_754_;
v___y_745_ = v___x_762_;
goto v___jp_738_;
}
}
}
v___jp_763_:
{
switch(lean_obj_tag(v_host_768_))
{
case 0:
{
lean_object* v_name_771_; 
v_name_771_ = lean_ctor_get(v_host_768_, 0);
lean_inc_ref(v_name_771_);
lean_dec_ref(v_host_768_);
v___y_749_ = v___y_764_;
v___y_750_ = v___y_770_;
v___y_751_ = v___y_765_;
v___y_752_ = v___y_766_;
v_port_753_ = v_port_769_;
v___y_754_ = v___y_767_;
v___y_755_ = v_name_771_;
goto v___jp_748_;
}
case 1:
{
lean_object* v_ipv4_772_; lean_object* v___x_773_; 
v_ipv4_772_ = lean_ctor_get(v_host_768_, 0);
lean_inc_ref(v_ipv4_772_);
lean_dec_ref(v_host_768_);
v___x_773_ = lean_uv_ntop_v4(v_ipv4_772_);
lean_dec_ref(v_ipv4_772_);
v___y_749_ = v___y_764_;
v___y_750_ = v___y_770_;
v___y_751_ = v___y_765_;
v___y_752_ = v___y_766_;
v_port_753_ = v_port_769_;
v___y_754_ = v___y_767_;
v___y_755_ = v___x_773_;
goto v___jp_748_;
}
default: 
{
lean_object* v_ipv6_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v_ipv6_774_ = lean_ctor_get(v_host_768_, 0);
lean_inc_ref(v_ipv6_774_);
lean_dec_ref(v_host_768_);
v___x_775_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__13));
v___x_776_ = lean_uv_ntop_v6(v_ipv6_774_);
lean_dec_ref(v_ipv6_774_);
v___x_777_ = lean_string_append(v___x_775_, v___x_776_);
lean_dec_ref(v___x_776_);
v___x_778_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14));
v___x_779_ = lean_string_append(v___x_777_, v___x_778_);
v___y_749_ = v___y_764_;
v___y_750_ = v___y_770_;
v___y_751_ = v___y_765_;
v___y_752_ = v___y_766_;
v_port_753_ = v_port_769_;
v___y_754_ = v___y_767_;
v___y_755_ = v___x_779_;
goto v___jp_748_;
}
}
}
v___jp_780_:
{
lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
v___x_790_ = lean_array_get_size(v___y_785_);
v___x_791_ = lean_unsigned_to_nat(0u);
v___x_792_ = lean_nat_dec_eq(v___x_790_, v___x_791_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v_encodedParams_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_793_ = lean_array_to_list(v___y_785_);
v___x_794_ = lean_box(0);
v_encodedParams_795_ = l_List_mapTR_loop___redArg(v___f_644_, v___x_793_, v___x_794_);
v___x_796_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9));
v___x_797_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10));
v___x_798_ = l_String_intercalate(v___x_797_, v_encodedParams_795_);
v___x_799_ = lean_string_append(v___x_796_, v___x_798_);
lean_dec_ref(v___x_798_);
v___y_723_ = v___y_781_;
v___y_724_ = v___y_789_;
v___y_725_ = v___y_782_;
v___y_726_ = v___y_783_;
v___y_727_ = v___y_784_;
v___y_728_ = v___y_786_;
v___y_729_ = v___y_787_;
v___y_730_ = v___y_788_;
v___y_731_ = v___x_799_;
goto v___jp_722_;
}
else
{
lean_object* v___x_800_; 
lean_dec_ref(v___y_785_);
v___x_800_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5));
v___y_723_ = v___y_781_;
v___y_724_ = v___y_789_;
v___y_725_ = v___y_782_;
v___y_726_ = v___y_783_;
v___y_727_ = v___y_784_;
v___y_728_ = v___y_786_;
v___y_729_ = v___y_787_;
v___y_730_ = v___y_788_;
v___y_731_ = v___x_800_;
goto v___jp_722_;
}
}
v___jp_801_:
{
lean_object* v_segments_811_; uint8_t v_absolute_812_; lean_object* v___x_813_; lean_object* v___x_814_; size_t v_sz_815_; size_t v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v_result_819_; 
v_segments_811_ = lean_ctor_get(v___y_808_, 0);
lean_inc_ref(v_segments_811_);
v_absolute_812_ = lean_ctor_get_uint8(v___y_808_, sizeof(void*)*1);
lean_dec_ref(v___y_808_);
v___x_813_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15));
v___x_814_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25));
v_sz_815_ = lean_array_size(v_segments_811_);
v___x_816_ = ((size_t)0ULL);
v___x_817_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_814_, v___f_643_, v_sz_815_, v___x_816_, v_segments_811_);
v___x_818_ = lean_array_to_list(v___x_817_);
v_result_819_ = l_String_intercalate(v___x_813_, v___x_818_);
if (v_absolute_812_ == 0)
{
v___y_781_ = v___y_810_;
v___y_782_ = v___y_802_;
v___y_783_ = v___y_803_;
v___y_784_ = v___y_804_;
v___y_785_ = v___y_805_;
v___y_786_ = v___y_806_;
v___y_787_ = v___y_807_;
v___y_788_ = v___y_809_;
v___y_789_ = v_result_819_;
goto v___jp_780_;
}
else
{
lean_object* v___x_820_; 
v___x_820_ = lean_string_append(v___x_813_, v_result_819_);
lean_dec_ref(v_result_819_);
v___y_781_ = v___y_810_;
v___y_782_ = v___y_802_;
v___y_783_ = v___y_803_;
v___y_784_ = v___y_804_;
v___y_785_ = v___y_805_;
v___y_786_ = v___y_806_;
v___y_787_ = v___y_807_;
v___y_788_ = v___y_809_;
v___y_789_ = v___x_820_;
goto v___jp_780_;
}
}
v___jp_821_:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_834_ = lean_string_append(v___y_823_, v___y_822_);
lean_dec_ref(v___y_822_);
v___x_835_ = lean_string_append(v___x_834_, v___y_833_);
lean_dec_ref(v___y_833_);
lean_inc_ref(v___y_829_);
v___x_836_ = lean_string_append(v___y_829_, v___x_835_);
lean_dec_ref(v___x_835_);
v___y_802_ = v___y_824_;
v___y_803_ = v___y_825_;
v___y_804_ = v___y_826_;
v___y_805_ = v___y_827_;
v___y_806_ = v___y_828_;
v___y_807_ = v___y_830_;
v___y_808_ = v___y_832_;
v___y_809_ = v___y_831_;
v___y_810_ = v___x_836_;
goto v___jp_801_;
}
v___jp_837_:
{
switch(lean_obj_tag(v_port_838_))
{
case 0:
{
lean_object* v___x_850_; 
v___x_850_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5));
v___y_822_ = v___y_849_;
v___y_823_ = v___y_839_;
v___y_824_ = v___y_840_;
v___y_825_ = v___y_841_;
v___y_826_ = v___y_842_;
v___y_827_ = v___y_843_;
v___y_828_ = v___y_844_;
v___y_829_ = v___y_845_;
v___y_830_ = v___y_846_;
v___y_831_ = v___y_848_;
v___y_832_ = v___y_847_;
v___y_833_ = v___x_850_;
goto v___jp_821_;
}
case 1:
{
lean_object* v___x_851_; 
v___x_851_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11));
v___y_822_ = v___y_849_;
v___y_823_ = v___y_839_;
v___y_824_ = v___y_840_;
v___y_825_ = v___y_841_;
v___y_826_ = v___y_842_;
v___y_827_ = v___y_843_;
v___y_828_ = v___y_844_;
v___y_829_ = v___y_845_;
v___y_830_ = v___y_846_;
v___y_831_ = v___y_848_;
v___y_832_ = v___y_847_;
v___y_833_ = v___x_851_;
goto v___jp_821_;
}
default: 
{
uint16_t v_port_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v_port_852_ = lean_ctor_get_uint16(v_port_838_, 0);
lean_dec_ref(v_port_838_);
v___x_853_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11));
v___x_854_ = lean_uint16_to_nat(v_port_852_);
v___x_855_ = l_Nat_reprFast(v___x_854_);
v___x_856_ = lean_string_append(v___x_853_, v___x_855_);
lean_dec_ref(v___x_855_);
v___y_822_ = v___y_849_;
v___y_823_ = v___y_839_;
v___y_824_ = v___y_840_;
v___y_825_ = v___y_841_;
v___y_826_ = v___y_842_;
v___y_827_ = v___y_843_;
v___y_828_ = v___y_844_;
v___y_829_ = v___y_845_;
v___y_830_ = v___y_846_;
v___y_831_ = v___y_848_;
v___y_832_ = v___y_847_;
v___y_833_ = v___x_856_;
goto v___jp_821_;
}
}
}
v___jp_857_:
{
switch(lean_obj_tag(v_host_858_))
{
case 0:
{
lean_object* v_name_870_; 
v_name_870_ = lean_ctor_get(v_host_858_, 0);
lean_inc_ref(v_name_870_);
lean_dec_ref(v_host_858_);
v_port_838_ = v_port_859_;
v___y_839_ = v___y_869_;
v___y_840_ = v___y_860_;
v___y_841_ = v___y_861_;
v___y_842_ = v___y_862_;
v___y_843_ = v___y_863_;
v___y_844_ = v___y_864_;
v___y_845_ = v___y_865_;
v___y_846_ = v___y_866_;
v___y_847_ = v___y_868_;
v___y_848_ = v___y_867_;
v___y_849_ = v_name_870_;
goto v___jp_837_;
}
case 1:
{
lean_object* v_ipv4_871_; lean_object* v___x_872_; 
v_ipv4_871_ = lean_ctor_get(v_host_858_, 0);
lean_inc_ref(v_ipv4_871_);
lean_dec_ref(v_host_858_);
v___x_872_ = lean_uv_ntop_v4(v_ipv4_871_);
lean_dec_ref(v_ipv4_871_);
v_port_838_ = v_port_859_;
v___y_839_ = v___y_869_;
v___y_840_ = v___y_860_;
v___y_841_ = v___y_861_;
v___y_842_ = v___y_862_;
v___y_843_ = v___y_863_;
v___y_844_ = v___y_864_;
v___y_845_ = v___y_865_;
v___y_846_ = v___y_866_;
v___y_847_ = v___y_868_;
v___y_848_ = v___y_867_;
v___y_849_ = v___x_872_;
goto v___jp_837_;
}
default: 
{
lean_object* v_ipv6_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v_ipv6_873_ = lean_ctor_get(v_host_858_, 0);
lean_inc_ref(v_ipv6_873_);
lean_dec_ref(v_host_858_);
v___x_874_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__13));
v___x_875_ = lean_uv_ntop_v6(v_ipv6_873_);
lean_dec_ref(v_ipv6_873_);
v___x_876_ = lean_string_append(v___x_874_, v___x_875_);
lean_dec_ref(v___x_875_);
v___x_877_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14));
v___x_878_ = lean_string_append(v___x_876_, v___x_877_);
v_port_838_ = v_port_859_;
v___y_839_ = v___y_869_;
v___y_840_ = v___y_860_;
v___y_841_ = v___y_861_;
v___y_842_ = v___y_862_;
v___y_843_ = v___y_863_;
v___y_844_ = v___y_864_;
v___y_845_ = v___y_865_;
v___y_846_ = v___y_866_;
v___y_847_ = v___y_868_;
v___y_848_ = v___y_867_;
v___y_849_ = v___x_878_;
goto v___jp_837_;
}
}
}
v___jp_879_:
{
lean_object* v_data_881_; lean_object* v_size_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v_data_881_ = lean_ctor_get(v_buffer_637_, 0);
lean_inc_ref(v_data_881_);
v_size_882_ = lean_ctor_get(v_buffer_637_, 1);
lean_inc(v_size_882_);
lean_dec_ref(v_buffer_637_);
v___x_883_ = lean_string_to_utf8(v___y_880_);
lean_inc_ref(v___x_883_);
v___x_884_ = lean_array_push(v_data_881_, v___x_883_);
v___x_885_ = lean_byte_array_size(v___x_883_);
lean_dec_ref(v___x_883_);
v___x_886_ = lean_nat_add(v_size_882_, v___x_885_);
lean_dec(v_size_882_);
v___x_887_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27);
v___x_888_ = lean_array_push(v___x_884_, v___x_887_);
v___x_889_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28);
v___x_890_ = lean_nat_add(v___x_886_, v___x_889_);
lean_dec(v___x_886_);
switch(lean_obj_tag(v_uri_641_))
{
case 0:
{
lean_object* v_path_891_; lean_object* v_query_892_; lean_object* v_segments_893_; uint8_t v_absolute_894_; lean_object* v___x_895_; lean_object* v___x_896_; size_t v_sz_897_; size_t v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v_result_901_; 
v_path_891_ = lean_ctor_get(v_uri_641_, 0);
lean_inc_ref(v_path_891_);
v_query_892_ = lean_ctor_get(v_uri_641_, 1);
lean_inc(v_query_892_);
lean_dec_ref(v_uri_641_);
v_segments_893_ = lean_ctor_get(v_path_891_, 0);
lean_inc_ref(v_segments_893_);
v_absolute_894_ = lean_ctor_get_uint8(v_path_891_, sizeof(void*)*1);
lean_dec_ref(v_path_891_);
v___x_895_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15));
v___x_896_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25));
v_sz_897_ = lean_array_size(v_segments_893_);
v___x_898_ = ((size_t)0ULL);
v___x_899_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_896_, v___f_643_, v_sz_897_, v___x_898_, v_segments_893_);
v___x_900_ = lean_array_to_list(v___x_899_);
v_result_901_ = l_String_intercalate(v___x_895_, v___x_900_);
if (v_absolute_894_ == 0)
{
v___y_688_ = v___x_888_;
v___y_689_ = v___x_890_;
v___y_690_ = v_query_892_;
v___y_691_ = v___x_887_;
v___y_692_ = v___x_889_;
v___y_693_ = v_result_901_;
goto v___jp_687_;
}
else
{
lean_object* v___x_902_; 
v___x_902_ = lean_string_append(v___x_895_, v_result_901_);
lean_dec_ref(v_result_901_);
v___y_688_ = v___x_888_;
v___y_689_ = v___x_890_;
v___y_690_ = v_query_892_;
v___y_691_ = v___x_887_;
v___y_692_ = v___x_889_;
v___y_693_ = v___x_902_;
goto v___jp_687_;
}
}
case 1:
{
lean_object* v_uri_903_; lean_object* v_authority_904_; 
v_uri_903_ = lean_ctor_get(v_uri_641_, 0);
lean_inc_ref(v_uri_903_);
lean_dec_ref(v_uri_641_);
v_authority_904_ = lean_ctor_get(v_uri_903_, 1);
if (lean_obj_tag(v_authority_904_) == 0)
{
lean_object* v_scheme_905_; lean_object* v_path_906_; lean_object* v_query_907_; lean_object* v_fragment_908_; lean_object* v___x_909_; 
v_scheme_905_ = lean_ctor_get(v_uri_903_, 0);
lean_inc_ref(v_scheme_905_);
v_path_906_ = lean_ctor_get(v_uri_903_, 2);
lean_inc_ref(v_path_906_);
v_query_907_ = lean_ctor_get(v_uri_903_, 3);
lean_inc_ref(v_query_907_);
v_fragment_908_ = lean_ctor_get(v_uri_903_, 4);
lean_inc(v_fragment_908_);
lean_dec_ref(v_uri_903_);
v___x_909_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5));
v___y_802_ = v_scheme_905_;
v___y_803_ = v_fragment_908_;
v___y_804_ = v___x_888_;
v___y_805_ = v_query_907_;
v___y_806_ = v___x_890_;
v___y_807_ = v___x_887_;
v___y_808_ = v_path_906_;
v___y_809_ = v___x_889_;
v___y_810_ = v___x_909_;
goto v___jp_801_;
}
else
{
lean_object* v_val_910_; lean_object* v_scheme_911_; lean_object* v_path_912_; lean_object* v_query_913_; lean_object* v_fragment_914_; lean_object* v_userInfo_915_; lean_object* v_host_916_; lean_object* v_port_917_; lean_object* v___x_918_; 
v_val_910_ = lean_ctor_get(v_authority_904_, 0);
lean_inc(v_val_910_);
v_scheme_911_ = lean_ctor_get(v_uri_903_, 0);
lean_inc_ref(v_scheme_911_);
v_path_912_ = lean_ctor_get(v_uri_903_, 2);
lean_inc_ref(v_path_912_);
v_query_913_ = lean_ctor_get(v_uri_903_, 3);
lean_inc_ref(v_query_913_);
v_fragment_914_ = lean_ctor_get(v_uri_903_, 4);
lean_inc(v_fragment_914_);
lean_dec_ref(v_uri_903_);
v_userInfo_915_ = lean_ctor_get(v_val_910_, 0);
lean_inc(v_userInfo_915_);
v_host_916_ = lean_ctor_get(v_val_910_, 1);
lean_inc_ref(v_host_916_);
v_port_917_ = lean_ctor_get(v_val_910_, 2);
lean_inc(v_port_917_);
lean_dec(v_val_910_);
v___x_918_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29));
if (lean_obj_tag(v_userInfo_915_) == 0)
{
lean_object* v___x_919_; 
v___x_919_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5));
v_host_858_ = v_host_916_;
v_port_859_ = v_port_917_;
v___y_860_ = v_scheme_911_;
v___y_861_ = v_fragment_914_;
v___y_862_ = v___x_888_;
v___y_863_ = v_query_913_;
v___y_864_ = v___x_890_;
v___y_865_ = v___x_918_;
v___y_866_ = v___x_887_;
v___y_867_ = v___x_889_;
v___y_868_ = v_path_912_;
v___y_869_ = v___x_919_;
goto v___jp_857_;
}
else
{
lean_object* v_val_920_; lean_object* v_password_921_; 
v_val_920_ = lean_ctor_get(v_userInfo_915_, 0);
lean_inc(v_val_920_);
lean_dec_ref(v_userInfo_915_);
v_password_921_ = lean_ctor_get(v_val_920_, 1);
if (lean_obj_tag(v_password_921_) == 0)
{
lean_object* v_username_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v_username_922_ = lean_ctor_get(v_val_920_, 0);
lean_inc_ref(v_username_922_);
lean_dec(v_val_920_);
v___x_923_ = lean_string_from_utf8_unchecked(v_username_922_);
v___x_924_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30));
v___x_925_ = lean_string_append(v___x_923_, v___x_924_);
v_host_858_ = v_host_916_;
v_port_859_ = v_port_917_;
v___y_860_ = v_scheme_911_;
v___y_861_ = v_fragment_914_;
v___y_862_ = v___x_888_;
v___y_863_ = v_query_913_;
v___y_864_ = v___x_890_;
v___y_865_ = v___x_918_;
v___y_866_ = v___x_887_;
v___y_867_ = v___x_889_;
v___y_868_ = v_path_912_;
v___y_869_ = v___x_925_;
goto v___jp_857_;
}
else
{
lean_object* v_username_926_; lean_object* v_val_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
lean_inc_ref(v_password_921_);
v_username_926_ = lean_ctor_get(v_val_920_, 0);
lean_inc_ref(v_username_926_);
lean_dec(v_val_920_);
v_val_927_ = lean_ctor_get(v_password_921_, 0);
lean_inc(v_val_927_);
lean_dec_ref(v_password_921_);
v___x_928_ = lean_string_from_utf8_unchecked(v_username_926_);
v___x_929_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11));
v___x_930_ = lean_string_append(v___x_928_, v___x_929_);
v___x_931_ = lean_string_from_utf8_unchecked(v_val_927_);
v___x_932_ = lean_string_append(v___x_930_, v___x_931_);
lean_dec_ref(v___x_931_);
v___x_933_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30));
v___x_934_ = lean_string_append(v___x_932_, v___x_933_);
v_host_858_ = v_host_916_;
v_port_859_ = v_port_917_;
v___y_860_ = v_scheme_911_;
v___y_861_ = v_fragment_914_;
v___y_862_ = v___x_888_;
v___y_863_ = v_query_913_;
v___y_864_ = v___x_890_;
v___y_865_ = v___x_918_;
v___y_866_ = v___x_887_;
v___y_867_ = v___x_889_;
v___y_868_ = v_path_912_;
v___y_869_ = v___x_934_;
goto v___jp_857_;
}
}
}
}
case 2:
{
lean_object* v_authority_935_; lean_object* v_userInfo_936_; 
v_authority_935_ = lean_ctor_get(v_uri_641_, 0);
lean_inc_ref(v_authority_935_);
lean_dec_ref(v_uri_641_);
v_userInfo_936_ = lean_ctor_get(v_authority_935_, 0);
if (lean_obj_tag(v_userInfo_936_) == 0)
{
lean_object* v_host_937_; lean_object* v_port_938_; lean_object* v___x_939_; 
v_host_937_ = lean_ctor_get(v_authority_935_, 1);
lean_inc_ref(v_host_937_);
v_port_938_ = lean_ctor_get(v_authority_935_, 2);
lean_inc(v_port_938_);
lean_dec_ref(v_authority_935_);
v___x_939_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___closed__5));
v___y_764_ = v___x_888_;
v___y_765_ = v___x_890_;
v___y_766_ = v___x_887_;
v___y_767_ = v___x_889_;
v_host_768_ = v_host_937_;
v_port_769_ = v_port_938_;
v___y_770_ = v___x_939_;
goto v___jp_763_;
}
else
{
lean_object* v_val_940_; lean_object* v_password_941_; 
v_val_940_ = lean_ctor_get(v_userInfo_936_, 0);
lean_inc(v_val_940_);
v_password_941_ = lean_ctor_get(v_val_940_, 1);
if (lean_obj_tag(v_password_941_) == 0)
{
lean_object* v_host_942_; lean_object* v_port_943_; lean_object* v_username_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v_host_942_ = lean_ctor_get(v_authority_935_, 1);
lean_inc_ref(v_host_942_);
v_port_943_ = lean_ctor_get(v_authority_935_, 2);
lean_inc(v_port_943_);
lean_dec_ref(v_authority_935_);
v_username_944_ = lean_ctor_get(v_val_940_, 0);
lean_inc_ref(v_username_944_);
lean_dec(v_val_940_);
v___x_945_ = lean_string_from_utf8_unchecked(v_username_944_);
v___x_946_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30));
v___x_947_ = lean_string_append(v___x_945_, v___x_946_);
v___y_764_ = v___x_888_;
v___y_765_ = v___x_890_;
v___y_766_ = v___x_887_;
v___y_767_ = v___x_889_;
v_host_768_ = v_host_942_;
v_port_769_ = v_port_943_;
v___y_770_ = v___x_947_;
goto v___jp_763_;
}
else
{
lean_object* v_host_948_; lean_object* v_port_949_; lean_object* v_username_950_; lean_object* v_val_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
lean_inc_ref(v_password_941_);
v_host_948_ = lean_ctor_get(v_authority_935_, 1);
lean_inc_ref(v_host_948_);
v_port_949_ = lean_ctor_get(v_authority_935_, 2);
lean_inc(v_port_949_);
lean_dec_ref(v_authority_935_);
v_username_950_ = lean_ctor_get(v_val_940_, 0);
lean_inc_ref(v_username_950_);
lean_dec(v_val_940_);
v_val_951_ = lean_ctor_get(v_password_941_, 0);
lean_inc(v_val_951_);
lean_dec_ref(v_password_941_);
v___x_952_ = lean_string_from_utf8_unchecked(v_username_950_);
v___x_953_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11));
v___x_954_ = lean_string_append(v___x_952_, v___x_953_);
v___x_955_ = lean_string_from_utf8_unchecked(v_val_951_);
v___x_956_ = lean_string_append(v___x_954_, v___x_955_);
lean_dec_ref(v___x_955_);
v___x_957_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30));
v___x_958_ = lean_string_append(v___x_956_, v___x_957_);
v___y_764_ = v___x_888_;
v___y_765_ = v___x_890_;
v___y_766_ = v___x_887_;
v___y_767_ = v___x_889_;
v_host_768_ = v_host_948_;
v_port_769_ = v_port_949_;
v___y_770_ = v___x_958_;
goto v___jp_763_;
}
}
}
default: 
{
lean_object* v___x_959_; 
v___x_959_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31));
v___y_672_ = v___x_888_;
v___y_673_ = v___x_890_;
v___y_674_ = v___x_887_;
v___y_675_ = v___x_889_;
v___y_676_ = v___x_959_;
goto v___jp_671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(lean_object* v_buffer_1000_, lean_object* v_r_1001_){
_start:
{
lean_object* v_status_1002_; uint8_t v_version_1003_; lean_object* v_headers_1004_; lean_object* v___f_1005_; lean_object* v___y_1007_; 
v_status_1002_ = lean_ctor_get(v_r_1001_, 0);
v_version_1003_ = lean_ctor_get_uint8(v_r_1001_, sizeof(void*)*2);
v_headers_1004_ = lean_ctor_get(v_r_1001_, 1);
v___f_1005_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2));
switch(v_version_1003_)
{
case 0:
{
lean_object* v___x_1057_; 
v___x_1057_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5));
v___y_1007_ = v___x_1057_;
goto v___jp_1006_;
}
case 1:
{
lean_object* v___x_1058_; 
v___x_1058_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6));
v___y_1007_ = v___x_1058_;
goto v___jp_1006_;
}
case 2:
{
lean_object* v___x_1059_; 
v___x_1059_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7));
v___y_1007_ = v___x_1059_;
goto v___jp_1006_;
}
default: 
{
lean_object* v___x_1060_; 
v___x_1060_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8));
v___y_1007_ = v___x_1060_;
goto v___jp_1006_;
}
}
v___jp_1006_:
{
lean_object* v_data_1008_; lean_object* v_size_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1056_; 
v_data_1008_ = lean_ctor_get(v_buffer_1000_, 0);
v_size_1009_ = lean_ctor_get(v_buffer_1000_, 1);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_buffer_1000_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1011_ = v_buffer_1000_;
v_isShared_1012_ = v_isSharedCheck_1056_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_size_1009_);
lean_inc(v_data_1008_);
lean_dec(v_buffer_1000_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1056_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; uint16_t v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v_buffer_1042_; 
v___x_1013_ = lean_string_to_utf8(v___y_1007_);
lean_inc_ref(v___x_1013_);
v___x_1014_ = lean_array_push(v_data_1008_, v___x_1013_);
v___x_1015_ = lean_byte_array_size(v___x_1013_);
lean_dec_ref(v___x_1013_);
v___x_1016_ = lean_nat_add(v_size_1009_, v___x_1015_);
lean_dec(v_size_1009_);
v___x_1017_ = lean_unsigned_to_nat(1u);
v___x_1018_ = lean_mk_empty_array_with_capacity(v___x_1017_);
lean_dec_ref(v___x_1018_);
v___x_1019_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27);
v___x_1020_ = lean_array_push(v___x_1014_, v___x_1019_);
v___x_1021_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28);
v___x_1022_ = lean_nat_add(v___x_1016_, v___x_1021_);
lean_dec(v___x_1016_);
v___x_1023_ = l_Std_Http_Status_toCode(v_status_1002_);
v___x_1024_ = lean_uint16_to_nat(v___x_1023_);
v___x_1025_ = l_Nat_reprFast(v___x_1024_);
v___x_1026_ = lean_string_to_utf8(v___x_1025_);
lean_dec_ref(v___x_1025_);
lean_inc_ref(v___x_1026_);
v___x_1027_ = lean_array_push(v___x_1020_, v___x_1026_);
v___x_1028_ = lean_byte_array_size(v___x_1026_);
lean_dec_ref(v___x_1026_);
v___x_1029_ = lean_nat_add(v___x_1022_, v___x_1028_);
lean_dec(v___x_1022_);
v___x_1030_ = lean_array_push(v___x_1027_, v___x_1019_);
v___x_1031_ = lean_nat_add(v___x_1029_, v___x_1021_);
lean_dec(v___x_1029_);
v___x_1032_ = l_Std_Http_Status_reasonPhrase(v_status_1002_);
v___x_1033_ = lean_string_to_utf8(v___x_1032_);
lean_dec_ref(v___x_1032_);
lean_inc_ref(v___x_1033_);
v___x_1034_ = lean_array_push(v___x_1030_, v___x_1033_);
v___x_1035_ = lean_byte_array_size(v___x_1033_);
lean_dec_ref(v___x_1033_);
v___x_1036_ = lean_nat_add(v___x_1031_, v___x_1035_);
lean_dec(v___x_1031_);
v___x_1037_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3);
v___x_1038_ = lean_array_push(v___x_1034_, v___x_1037_);
v___x_1039_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4);
v___x_1040_ = lean_nat_add(v___x_1036_, v___x_1039_);
lean_dec(v___x_1036_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 1, v___x_1040_);
lean_ctor_set(v___x_1011_, 0, v___x_1038_);
v_buffer_1042_ = v___x_1011_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v___x_1040_);
v_buffer_1042_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v_buffer_1043_; lean_object* v_data_1044_; lean_object* v_size_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1054_; 
v_buffer_1043_ = l_Std_Http_Headers_fold___redArg(v_headers_1004_, v_buffer_1042_, v___f_1005_);
v_data_1044_ = lean_ctor_get(v_buffer_1043_, 0);
v_size_1045_ = lean_ctor_get(v_buffer_1043_, 1);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_buffer_1043_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1047_ = v_buffer_1043_;
v_isShared_1048_ = v_isSharedCheck_1054_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_size_1045_);
lean_inc(v_data_1044_);
lean_dec(v_buffer_1043_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1054_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1049_ = lean_array_push(v_data_1044_, v___x_1037_);
v___x_1050_ = lean_nat_add(v_size_1045_, v___x_1039_);
lean_dec(v_size_1045_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 1, v___x_1050_);
lean_ctor_set(v___x_1047_, 0, v___x_1049_);
v___x_1052_ = v___x_1047_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___boxed(lean_object* v_buffer_1061_, lean_object* v_r_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(v_buffer_1061_, v_r_1062_);
lean_dec_ref(v_r_1062_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head(uint8_t v_dir_1066_){
_start:
{
if (v_dir_1066_ == 0)
{
lean_object* v___x_1067_; 
v___x_1067_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___closed__0));
return v___x_1067_;
}
else
{
lean_object* v___x_1068_; 
v___x_1068_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___closed__1));
return v___x_1068_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___boxed(lean_object* v_dir_1069_){
_start:
{
uint8_t v_dir_boxed_1070_; lean_object* v_res_1071_; 
v_dir_boxed_1070_ = lean_unbox(v_dir_1069_);
v_res_1071_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v_dir_boxed_1070_);
return v_res_1071_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; uint8_t v___x_1075_; lean_object* v___x_1076_; 
v___x_1072_ = l_Std_Http_Headers_empty;
v___x_1073_ = lean_box(3);
v___x_1074_ = 1;
v___x_1075_ = 8;
v___x_1076_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1076_, 0, v___x_1073_);
lean_ctor_set(v___x_1076_, 1, v___x_1072_);
lean_ctor_set_uint8(v___x_1076_, sizeof(void*)*2, v___x_1075_);
lean_ctor_set_uint8(v___x_1076_, sizeof(void*)*2 + 1, v___x_1074_);
return v___x_1076_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1(void){
_start:
{
lean_object* v___x_1077_; uint8_t v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1077_ = l_Std_Http_Headers_empty;
v___x_1078_ = 1;
v___x_1079_ = lean_box(4);
v___x_1080_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
lean_ctor_set(v___x_1080_, 1, v___x_1077_);
lean_ctor_set_uint8(v___x_1080_, sizeof(void*)*2, v___x_1078_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead(uint8_t v_dir_1081_){
_start:
{
if (v_dir_1081_ == 0)
{
lean_object* v___x_1082_; 
v___x_1082_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0, &l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0_once, _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0);
return v___x_1082_;
}
else
{
lean_object* v___x_1083_; 
v___x_1083_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1, &l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1_once, _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1);
return v___x_1083_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead___boxed(lean_object* v_dir_1084_){
_start:
{
uint8_t v_dir_boxed_1085_; lean_object* v_res_1086_; 
v_dir_boxed_1085_ = lean_unbox(v_dir_1084_);
v_res_1086_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v_dir_boxed_1085_);
return v_res_1086_;
}
}
lean_object* runtime_initialize_Init_Data_Array(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Http_Protocol_H1_Message(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___boxed__const__1 = _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___boxed__const__1();
lean_mark_persistent(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__3___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Http_Protocol_H1_Message(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Http_Protocol_H1_Message(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Protocol_H1_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Http_Protocol_H1_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Http_Protocol_H1_Message(builtin);
}
#ifdef __cplusplus
}
#endif
