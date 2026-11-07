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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Std_Http_Header_Connection_parse(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_contentLength;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Http_Response_instReprHead_repr___redArg(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Http_Request_instReprHead_repr___redArg(lean_object*);
extern lean_object* l_Std_Http_Headers_empty;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Http_Internal_appendFieldLine___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Headers_fold___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
uint16_t l_Std_Http_Status_toCode(lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* l_Std_Http_Internal_appendNat(lean_object*, lean_object*);
lean_object* l_Std_Http_Status_reasonPhrase(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_URI_Query_formatOption(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_Http_URI_EncodedFragment_encode(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_uv_ntop_v4(lean_object*);
lean_object* lean_uv_ntop_v6(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_connection;
extern lean_object* l_Std_Http_Header_Name_transferEncoding;
uint8_t l_Std_Http_instBEqVersion_beq(uint8_t, uint8_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Std_Http_Header_TransferEncoding_parse(lean_object*);
uint8_t l_Std_Http_Header_TransferEncoding_isChunked(lean_object*);
lean_object* l_Std_Http_Header_ContentLength_parse(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Message_Head_getSize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Message_Head_getSize___closed__1_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize___closed__2 = (const lean_object*)&l_Std_Http_Protocol_H1_Message_Head_getSize___closed__2_value;
static const lean_array_object l_Std_Http_Protocol_H1_Message_Head_getSize___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize___closed__3 = (const lean_object*)&l_Std_Http_Protocol_H1_Message_Head_getSize___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize(uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "close"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2___closed__0_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "keep-alive"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___closed__0_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Message_Head_getSize___closed__3_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0_value;
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
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__0_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1;
static lean_once_cell_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_appendFieldLine___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.0"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5;
static lean_once_cell_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.1"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8;
static lean_once_cell_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/2.0"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11;
static lean_once_cell_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/3.0"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__13 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__13_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14;
static lean_once_cell_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__17 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__17_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__18 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__18_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__19 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__19_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__20 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__20_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__21 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__21_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28_value;
static const lean_closure_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23_value),((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30_value),((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25_value),((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26_value),((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27_value),((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31_value),((lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "//"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ACL"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "BASELINE-CONTROL"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "BIND"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CHECKIN"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CHECKOUT"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CONNECT"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "COPY"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "DELETE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "GET"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "LABEL"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LINK"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LOCK"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MERGE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKACTIVITY"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKCALENDAR"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MKCOL"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "MKREDIRECTREF"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MKWORKSPACE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "MOVE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "OPTIONS"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ORDERPATCH"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PATCH"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "POST"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PRI"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "PROPFIND"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PROPPATCH"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PUT"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "QUERY"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REBIND"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REPORT"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "SEARCH"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "TRACE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__68 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__68_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNBIND"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__69 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__69_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "UNCHECKOUT"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__70 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__70_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLINK"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__71 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__71_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLOCK"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__72 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__72_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UPDATE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__73 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__73_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "UPDATEREDIRECTREF"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__74 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__74_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "VERSION-CONTROL"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__75 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__75_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "200 OK"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__0_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__1;
static lean_once_cell_t l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__2;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(lean_object* v_as_115_, size_t v_i_116_, size_t v_stop_117_, lean_object* v_b_118_){
_start:
{
lean_object* v___y_120_; uint8_t v___x_124_; 
v___x_124_ = lean_usize_dec_eq(v_i_116_, v_stop_117_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; lean_object* v_fst_126_; lean_object* v_snd_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_125_ = lean_array_uget_borrowed(v_as_115_, v_i_116_);
v_fst_126_ = lean_ctor_get(v___x_125_, 0);
v_snd_127_ = lean_ctor_get(v___x_125_, 1);
v___x_128_ = l_Std_Http_Header_Name_transferEncoding;
v___x_129_ = lean_string_dec_eq(v_fst_126_, v___x_128_);
if (v___x_129_ == 0)
{
v___y_120_ = v_b_118_;
goto v___jp_119_;
}
else
{
lean_object* v___x_130_; 
lean_inc(v_snd_127_);
v___x_130_ = lean_array_push(v_b_118_, v_snd_127_);
v___y_120_ = v___x_130_;
goto v___jp_119_;
}
}
else
{
return v_b_118_;
}
v___jp_119_:
{
size_t v___x_121_; size_t v___x_122_; 
v___x_121_ = ((size_t)1ULL);
v___x_122_ = lean_usize_add(v_i_116_, v___x_121_);
v_i_116_ = v___x_122_;
v_b_118_ = v___y_120_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0___boxed(lean_object* v_as_131_, lean_object* v_i_132_, lean_object* v_stop_133_, lean_object* v_b_134_){
_start:
{
size_t v_i_boxed_135_; size_t v_stop_boxed_136_; lean_object* v_res_137_; 
v_i_boxed_135_ = lean_unbox_usize(v_i_132_);
lean_dec(v_i_132_);
v_stop_boxed_136_ = lean_unbox_usize(v_stop_133_);
lean_dec(v_stop_133_);
v_res_137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(v_as_131_, v_i_boxed_135_, v_stop_boxed_136_, v_b_134_);
lean_dec_ref(v_as_131_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(lean_object* v_as_138_, size_t v_i_139_, size_t v_stop_140_, lean_object* v_b_141_){
_start:
{
lean_object* v___y_143_; uint8_t v___x_147_; 
v___x_147_ = lean_usize_dec_eq(v_i_139_, v_stop_140_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; lean_object* v_fst_149_; lean_object* v_snd_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_148_ = lean_array_uget_borrowed(v_as_138_, v_i_139_);
v_fst_149_ = lean_ctor_get(v___x_148_, 0);
v_snd_150_ = lean_ctor_get(v___x_148_, 1);
v___x_151_ = l_Std_Http_Header_Name_contentLength;
v___x_152_ = lean_string_dec_eq(v_fst_149_, v___x_151_);
if (v___x_152_ == 0)
{
v___y_143_ = v_b_141_;
goto v___jp_142_;
}
else
{
lean_object* v___x_153_; 
lean_inc(v_snd_150_);
v___x_153_ = lean_array_push(v_b_141_, v_snd_150_);
v___y_143_ = v___x_153_;
goto v___jp_142_;
}
}
else
{
return v_b_141_;
}
v___jp_142_:
{
size_t v___x_144_; size_t v___x_145_; 
v___x_144_ = ((size_t)1ULL);
v___x_145_ = lean_usize_add(v_i_139_, v___x_144_);
v_i_139_ = v___x_145_;
v_b_141_ = v___y_143_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1___boxed(lean_object* v_as_154_, lean_object* v_i_155_, lean_object* v_stop_156_, lean_object* v_b_157_){
_start:
{
size_t v_i_boxed_158_; size_t v_stop_boxed_159_; lean_object* v_res_160_; 
v_i_boxed_158_ = lean_unbox_usize(v_i_155_);
lean_dec(v_i_155_);
v_stop_boxed_159_ = lean_unbox_usize(v_stop_156_);
lean_dec(v_stop_156_);
v_res_160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(v_as_154_, v_i_boxed_158_, v_stop_boxed_159_, v_b_157_);
lean_dec_ref(v_as_154_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize(uint8_t v_dir_169_, lean_object* v_message_170_, uint8_t v_allowEOFBody_171_){
_start:
{
lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___x_218_; lean_object* v___y_220_; lean_object* v___y_229_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_218_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_169_, v_message_170_);
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__3));
v___x_237_ = lean_array_get_size(v___x_218_);
v___x_238_ = lean_nat_dec_lt(v___x_235_, v___x_237_);
if (v___x_238_ == 0)
{
v___y_229_ = v___x_236_;
goto v___jp_228_;
}
else
{
size_t v___x_239_; size_t v___x_240_; lean_object* v___x_241_; 
v___x_239_ = ((size_t)0ULL);
v___x_240_ = lean_usize_of_nat(v___x_237_);
v___x_241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(v___x_218_, v___x_239_, v___x_240_, v___x_236_);
v___y_229_ = v___x_241_;
goto v___jp_228_;
}
v___jp_172_:
{
lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_175_ = lean_array_get_size(v___y_174_);
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_177_ = lean_nat_dec_eq(v___x_175_, v___x_176_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_178_ = lean_unsigned_to_nat(1u);
v___x_179_ = lean_nat_dec_eq(v___x_175_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; 
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
v___x_180_ = lean_box(0);
return v___x_180_;
}
else
{
lean_object* v___x_181_; lean_object* v_te_182_; 
v___x_181_ = lean_array_fget(v___y_174_, v___x_176_);
lean_dec_ref(v___y_174_);
v_te_182_ = l_Std_Http_Header_TransferEncoding_parse(v___x_181_);
if (lean_obj_tag(v_te_182_) == 0)
{
lean_object* v___x_183_; 
lean_dec(v___y_173_);
v___x_183_ = lean_box(0);
return v___x_183_;
}
else
{
lean_object* v_val_184_; uint8_t v___x_185_; 
v_val_184_ = lean_ctor_get(v_te_182_, 0);
lean_inc(v_val_184_);
lean_dec_ref_known(v_te_182_, 1);
v___x_185_ = l_Std_Http_Header_TransferEncoding_isChunked(v_val_184_);
lean_dec(v_val_184_);
if (v___x_185_ == 1)
{
if (lean_obj_tag(v___y_173_) == 0)
{
uint8_t v___x_186_; uint8_t v___x_187_; uint8_t v___x_188_; 
v___x_186_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_169_, v_message_170_);
v___x_187_ = 0;
v___x_188_ = l_Std_Http_instBEqVersion_beq(v___x_186_, v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; 
v___x_189_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0));
return v___x_189_;
}
else
{
lean_object* v___x_190_; 
v___x_190_ = lean_box(0);
return v___x_190_;
}
}
else
{
lean_object* v___x_191_; 
lean_dec(v___y_173_);
v___x_191_ = lean_box(0);
return v___x_191_;
}
}
else
{
lean_object* v___x_192_; 
lean_dec(v___y_173_);
v___x_192_ = lean_box(0);
return v___x_192_;
}
}
}
}
else
{
lean_dec_ref(v___y_174_);
if (lean_obj_tag(v___y_173_) == 0)
{
if (v_allowEOFBody_171_ == 0)
{
lean_object* v___x_193_; 
v___x_193_ = lean_box(0);
return v___x_193_;
}
else
{
lean_object* v___x_194_; 
v___x_194_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__2));
return v___x_194_;
}
}
else
{
lean_object* v_val_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_217_; 
v_val_195_ = lean_ctor_get(v___y_173_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___y_173_);
if (v_isSharedCheck_217_ == 0)
{
v___x_197_ = v___y_173_;
v_isShared_198_ = v_isSharedCheck_217_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_val_195_);
lean_dec(v___y_173_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_217_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_199_ = lean_array_get_size(v_val_195_);
v___x_200_ = lean_unsigned_to_nat(1u);
v___x_201_ = lean_nat_dec_eq(v___x_199_, v___x_200_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; 
lean_del_object(v___x_197_);
lean_dec(v_val_195_);
v___x_202_ = lean_box(0);
return v___x_202_;
}
else
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_array_fget(v_val_195_, v___x_176_);
lean_dec(v_val_195_);
v___x_204_ = l_Std_Http_Header_ContentLength_parse(v___x_203_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v___x_205_; 
lean_del_object(v___x_197_);
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
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v_val_206_);
v___x_211_ = v___x_197_;
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
}
v___jp_219_:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__3));
v___x_223_ = lean_array_get_size(v___x_218_);
v___x_224_ = lean_nat_dec_lt(v___x_221_, v___x_223_);
if (v___x_224_ == 0)
{
lean_dec_ref(v___x_218_);
v___y_173_ = v___y_220_;
v___y_174_ = v___x_222_;
goto v___jp_172_;
}
else
{
size_t v___x_225_; size_t v___x_226_; lean_object* v___x_227_; 
v___x_225_ = ((size_t)0ULL);
v___x_226_ = lean_usize_of_nat(v___x_223_);
v___x_227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(v___x_218_, v___x_225_, v___x_226_, v___x_222_);
lean_dec_ref(v___x_218_);
v___y_173_ = v___y_220_;
v___y_174_ = v___x_227_;
goto v___jp_172_;
}
}
v___jp_228_:
{
lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_230_ = lean_array_get_size(v___y_229_);
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = lean_nat_dec_eq(v___x_230_, v___x_231_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_233_, 0, v___y_229_);
v___y_220_ = v___x_233_;
goto v___jp_219_;
}
else
{
lean_object* v___x_234_; 
lean_dec_ref(v___y_229_);
v___x_234_ = lean_box(0);
v___y_220_ = v___x_234_;
goto v___jp_219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize___boxed(lean_object* v_dir_242_, lean_object* v_message_243_, lean_object* v_allowEOFBody_244_){
_start:
{
uint8_t v_dir_boxed_245_; uint8_t v_allowEOFBody_boxed_246_; lean_object* v_res_247_; 
v_dir_boxed_245_ = lean_unbox(v_dir_242_);
v_allowEOFBody_boxed_246_ = lean_unbox(v_allowEOFBody_244_);
v_res_247_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v_dir_boxed_245_, v_message_243_, v_allowEOFBody_boxed_246_);
lean_dec(v_message_243_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__4(lean_object* v_as_248_, size_t v_i_249_, size_t v_stop_250_, lean_object* v_b_251_){
_start:
{
lean_object* v___y_253_; uint8_t v___x_257_; 
v___x_257_ = lean_usize_dec_eq(v_i_249_, v_stop_250_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; lean_object* v_fst_259_; lean_object* v_snd_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_258_ = lean_array_uget_borrowed(v_as_248_, v_i_249_);
v_fst_259_ = lean_ctor_get(v___x_258_, 0);
v_snd_260_ = lean_ctor_get(v___x_258_, 1);
v___x_261_ = l_Std_Http_Header_Name_connection;
v___x_262_ = lean_string_dec_eq(v_fst_259_, v___x_261_);
if (v___x_262_ == 0)
{
v___y_253_ = v_b_251_;
goto v___jp_252_;
}
else
{
lean_object* v___x_263_; 
lean_inc(v_snd_260_);
v___x_263_ = lean_array_push(v_b_251_, v_snd_260_);
v___y_253_ = v___x_263_;
goto v___jp_252_;
}
}
else
{
return v_b_251_;
}
v___jp_252_:
{
size_t v___x_254_; size_t v___x_255_; 
v___x_254_ = ((size_t)1ULL);
v___x_255_ = lean_usize_add(v_i_249_, v___x_254_);
v_i_249_ = v___x_255_;
v_b_251_ = v___y_253_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__4___boxed(lean_object* v_as_264_, lean_object* v_i_265_, lean_object* v_stop_266_, lean_object* v_b_267_){
_start:
{
size_t v_i_boxed_268_; size_t v_stop_boxed_269_; lean_object* v_res_270_; 
v_i_boxed_268_ = lean_unbox_usize(v_i_265_);
lean_dec(v_i_265_);
v_stop_boxed_269_ = lean_unbox_usize(v_stop_266_);
lean_dec(v_stop_266_);
v_res_270_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__4(v_as_264_, v_i_boxed_268_, v_stop_boxed_269_, v_b_267_);
lean_dec_ref(v_as_264_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__3(lean_object* v_as_271_, size_t v_i_272_, size_t v_stop_273_, lean_object* v_b_274_){
_start:
{
lean_object* v___y_276_; uint8_t v___x_280_; 
v___x_280_ = lean_usize_dec_eq(v_i_272_, v_stop_273_);
if (v___x_280_ == 0)
{
if (lean_obj_tag(v_b_274_) == 0)
{
v___y_276_ = v_b_274_;
goto v___jp_275_;
}
else
{
lean_object* v_val_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v_val_281_ = lean_ctor_get(v_b_274_, 0);
lean_inc(v_val_281_);
lean_dec_ref_known(v_b_274_, 1);
v___x_282_ = lean_array_uget_borrowed(v_as_271_, v_i_272_);
lean_inc(v___x_282_);
v___x_283_ = l_Std_Http_Header_Connection_parse(v___x_282_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v___x_284_; 
lean_dec(v_val_281_);
v___x_284_ = lean_box(0);
v___y_276_ = v___x_284_;
goto v___jp_275_;
}
else
{
lean_object* v_val_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_293_; 
v_val_285_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_293_ == 0)
{
v___x_287_ = v___x_283_;
v_isShared_288_ = v_isSharedCheck_293_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_val_285_);
lean_dec(v___x_283_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_293_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_289_ = l_Array_append___redArg(v_val_281_, v_val_285_);
lean_dec(v_val_285_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_289_);
v___x_291_ = v___x_287_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_289_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
v___y_276_ = v___x_291_;
goto v___jp_275_;
}
}
}
}
}
else
{
return v_b_274_;
}
v___jp_275_:
{
size_t v___x_277_; size_t v___x_278_; 
v___x_277_ = ((size_t)1ULL);
v___x_278_ = lean_usize_add(v_i_272_, v___x_277_);
v_i_272_ = v___x_278_;
v_b_274_ = v___y_276_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__3___boxed(lean_object* v_as_294_, lean_object* v_i_295_, lean_object* v_stop_296_, lean_object* v_b_297_){
_start:
{
size_t v_i_boxed_298_; size_t v_stop_boxed_299_; lean_object* v_res_300_; 
v_i_boxed_298_ = lean_unbox_usize(v_i_295_);
lean_dec(v_i_295_);
v_stop_boxed_299_ = lean_unbox_usize(v_stop_296_);
lean_dec(v_stop_296_);
v_res_300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__3(v_as_294_, v_i_boxed_298_, v_stop_boxed_299_, v_b_297_);
lean_dec_ref(v_as_294_);
return v_res_300_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(lean_object* v_as_302_, size_t v_i_303_, size_t v_stop_304_){
_start:
{
uint8_t v___x_305_; 
v___x_305_ = lean_usize_dec_eq(v_i_303_, v_stop_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_306_ = lean_array_uget_borrowed(v_as_302_, v_i_303_);
v___x_307_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2___closed__0));
v___x_308_ = lean_string_dec_eq(v___x_306_, v___x_307_);
if (v___x_308_ == 0)
{
size_t v___x_309_; size_t v___x_310_; 
v___x_309_ = ((size_t)1ULL);
v___x_310_ = lean_usize_add(v_i_303_, v___x_309_);
v_i_303_ = v___x_310_;
goto _start;
}
else
{
return v___x_308_;
}
}
else
{
uint8_t v___x_312_; 
v___x_312_ = 0;
return v___x_312_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2___boxed(lean_object* v_as_313_, lean_object* v_i_314_, lean_object* v_stop_315_){
_start:
{
size_t v_i_boxed_316_; size_t v_stop_boxed_317_; uint8_t v_res_318_; lean_object* v_r_319_; 
v_i_boxed_316_ = lean_unbox_usize(v_i_314_);
lean_dec(v_i_314_);
v_stop_boxed_317_ = lean_unbox_usize(v_stop_315_);
lean_dec(v_stop_315_);
v_res_318_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_as_313_, v_i_boxed_316_, v_stop_boxed_317_);
lean_dec_ref(v_as_313_);
v_r_319_ = lean_box(v_res_318_);
return v_r_319_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(lean_object* v_as_321_, size_t v_i_322_, size_t v_stop_323_){
_start:
{
uint8_t v___x_324_; 
v___x_324_ = lean_usize_dec_eq(v_i_322_, v_stop_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_325_ = lean_array_uget_borrowed(v_as_321_, v_i_322_);
v___x_326_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___closed__0));
v___x_327_ = lean_string_dec_eq(v___x_325_, v___x_326_);
if (v___x_327_ == 0)
{
size_t v___x_328_; size_t v___x_329_; 
v___x_328_ = ((size_t)1ULL);
v___x_329_ = lean_usize_add(v_i_322_, v___x_328_);
v_i_322_ = v___x_329_;
goto _start;
}
else
{
return v___x_327_;
}
}
else
{
uint8_t v___x_331_; 
v___x_331_ = 0;
return v___x_331_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___boxed(lean_object* v_as_332_, lean_object* v_i_333_, lean_object* v_stop_334_){
_start:
{
size_t v_i_boxed_335_; size_t v_stop_boxed_336_; uint8_t v_res_337_; lean_object* v_r_338_; 
v_i_boxed_335_ = lean_unbox_usize(v_i_333_);
lean_dec(v_i_333_);
v_stop_boxed_336_ = lean_unbox_usize(v_stop_334_);
lean_dec(v_stop_334_);
v_res_337_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(v_as_332_, v_i_boxed_335_, v_stop_boxed_336_);
lean_dec_ref(v_as_332_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(lean_object* v_as_339_, size_t v_i_340_, size_t v_stop_341_){
_start:
{
uint8_t v___x_342_; 
v___x_342_ = lean_usize_dec_eq(v_i_340_, v_stop_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v_fst_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_343_ = lean_array_uget_borrowed(v_as_339_, v_i_340_);
v_fst_344_ = lean_ctor_get(v___x_343_, 0);
v___x_345_ = l_Std_Http_Header_Name_connection;
v___x_346_ = lean_string_dec_eq(v_fst_344_, v___x_345_);
if (v___x_346_ == 0)
{
size_t v___x_347_; size_t v___x_348_; 
v___x_347_ = ((size_t)1ULL);
v___x_348_ = lean_usize_add(v_i_340_, v___x_347_);
v_i_340_ = v___x_348_;
goto _start;
}
else
{
return v___x_346_;
}
}
else
{
uint8_t v___x_350_; 
v___x_350_ = 0;
return v___x_350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___boxed(lean_object* v_as_351_, lean_object* v_i_352_, lean_object* v_stop_353_){
_start:
{
size_t v_i_boxed_354_; size_t v_stop_boxed_355_; uint8_t v_res_356_; lean_object* v_r_357_; 
v_i_boxed_354_ = lean_unbox_usize(v_i_352_);
lean_dec(v_i_352_);
v_stop_boxed_355_ = lean_unbox_usize(v_stop_353_);
lean_dec(v_stop_353_);
v_res_356_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(v_as_351_, v_i_boxed_354_, v_stop_boxed_355_);
lean_dec_ref(v_as_351_);
v_r_357_ = lean_box(v_res_356_);
return v_r_357_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(uint8_t v_dir_360_, lean_object* v_message_361_){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_366_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_360_, v_message_361_);
v___x_367_ = lean_unsigned_to_nat(0u);
v___x_368_ = lean_array_get_size(v___x_366_);
v___x_369_ = lean_nat_dec_lt(v___x_367_, v___x_368_);
if (v___x_369_ == 0)
{
lean_dec_ref(v___x_366_);
goto v___jp_362_;
}
else
{
if (v___x_369_ == 0)
{
lean_dec_ref(v___x_366_);
goto v___jp_362_;
}
else
{
size_t v___x_370_; size_t v___x_371_; uint8_t v___x_372_; 
v___x_370_ = ((size_t)0ULL);
v___x_371_ = lean_usize_of_nat(v___x_368_);
v___x_372_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(v___x_366_, v___x_370_, v___x_371_);
if (v___x_372_ == 0)
{
lean_dec_ref(v___x_366_);
goto v___jp_362_;
}
else
{
uint8_t v___x_373_; lean_object* v_val_375_; lean_object* v___y_388_; lean_object* v___x_398_; 
v___x_373_ = 0;
v___x_398_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__3));
if (v___x_369_ == 0)
{
lean_dec_ref(v___x_366_);
v___y_388_ = v___x_398_;
goto v___jp_387_;
}
else
{
lean_object* v___x_399_; 
v___x_399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__4(v___x_366_, v___x_370_, v___x_371_, v___x_398_);
lean_dec_ref(v___x_366_);
v___y_388_ = v___x_399_;
goto v___jp_387_;
}
v___jp_374_:
{
uint8_t v___x_376_; uint8_t v___x_377_; uint8_t v___x_378_; 
v___x_376_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_360_, v_message_361_);
v___x_377_ = 1;
v___x_378_ = l_Std_Http_instBEqVersion_beq(v___x_376_, v___x_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_379_ = lean_array_get_size(v_val_375_);
v___x_380_ = lean_nat_dec_lt(v___x_367_, v___x_379_);
if (v___x_380_ == 0)
{
lean_dec_ref(v_val_375_);
return v___x_380_;
}
else
{
if (v___x_380_ == 0)
{
lean_dec_ref(v_val_375_);
return v___x_380_;
}
else
{
size_t v___x_381_; uint8_t v___x_382_; 
v___x_381_ = lean_usize_of_nat(v___x_379_);
v___x_382_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(v_val_375_, v___x_370_, v___x_381_);
lean_dec_ref(v_val_375_);
return v___x_382_;
}
}
}
else
{
lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_383_ = lean_array_get_size(v_val_375_);
v___x_384_ = lean_nat_dec_lt(v___x_367_, v___x_383_);
if (v___x_384_ == 0)
{
lean_dec_ref(v_val_375_);
return v___x_378_;
}
else
{
if (v___x_384_ == 0)
{
lean_dec_ref(v_val_375_);
return v___x_378_;
}
else
{
size_t v___x_385_; uint8_t v___x_386_; 
v___x_385_ = lean_usize_of_nat(v___x_383_);
v___x_386_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_val_375_, v___x_370_, v___x_385_);
lean_dec_ref(v_val_375_);
if (v___x_386_ == 0)
{
return v___x_378_;
}
else
{
return v___x_373_;
}
}
}
}
}
v___jp_387_:
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = lean_array_get_size(v___y_388_);
v___x_390_ = lean_nat_dec_eq(v___x_389_, v___x_367_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_391_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__3));
v___x_392_ = lean_nat_dec_lt(v___x_367_, v___x_389_);
if (v___x_392_ == 0)
{
lean_dec_ref(v___y_388_);
v_val_375_ = v___x_391_;
goto v___jp_374_;
}
else
{
lean_object* v___x_393_; size_t v___x_394_; lean_object* v___x_395_; 
v___x_393_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0));
v___x_394_ = lean_usize_of_nat(v___x_389_);
v___x_395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__3(v___y_388_, v___x_370_, v___x_394_, v___x_393_);
lean_dec_ref(v___y_388_);
if (lean_obj_tag(v___x_395_) == 0)
{
return v___x_373_;
}
else
{
lean_object* v_val_396_; 
v_val_396_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_val_396_);
lean_dec_ref_known(v___x_395_, 1);
v_val_375_ = v_val_396_;
goto v___jp_374_;
}
}
}
else
{
lean_object* v___x_397_; 
lean_dec_ref(v___y_388_);
v___x_397_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__3));
v_val_375_ = v___x_397_;
goto v___jp_374_;
}
}
}
}
}
v___jp_362_:
{
uint8_t v___x_363_; uint8_t v___x_364_; uint8_t v___x_365_; 
v___x_363_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_360_, v_message_361_);
v___x_364_ = 1;
v___x_365_ = l_Std_Http_instBEqVersion_beq(v___x_363_, v___x_364_);
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___boxed(lean_object* v_dir_400_, lean_object* v_message_401_){
_start:
{
uint8_t v_dir_boxed_402_; uint8_t v_res_403_; lean_object* v_r_404_; 
v_dir_boxed_402_ = lean_unbox(v_dir_400_);
v_res_403_ = l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(v_dir_boxed_402_, v_message_401_);
lean_dec(v_message_401_);
v_r_404_ = lean_box(v_res_403_);
return v_r_404_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1___redArg(lean_object* v_x_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Std_Http_Request_instReprHead_repr___redArg(v_x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1(lean_object* v_x_407_, lean_object* v_prec_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Std_Http_Request_instReprHead_repr___redArg(v_x_407_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1___boxed(lean_object* v_x_410_, lean_object* v_prec_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Std_Http_Protocol_H1_instReprHead___aux__1(v_x_410_, v_prec_411_);
lean_dec(v_prec_411_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3___redArg(lean_object* v_x_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Std_Http_Response_instReprHead_repr___redArg(v_x_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3(lean_object* v_x_415_, lean_object* v_prec_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Std_Http_Response_instReprHead_repr___redArg(v_x_415_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3___boxed(lean_object* v_x_418_, lean_object* v_prec_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Std_Http_Protocol_H1_instReprHead___aux__3(v_x_418_, v_prec_419_);
lean_dec(v_prec_419_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead(uint8_t v_dir_423_){
_start:
{
if (v_dir_423_ == 0)
{
lean_object* v___x_424_; 
v___x_424_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprHead___closed__0));
return v___x_424_;
}
else
{
lean_object* v___x_425_; 
v___x_425_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprHead___closed__1));
return v___x_425_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___boxed(lean_object* v_dir_426_){
_start:
{
uint8_t v_dir_boxed_427_; lean_object* v_res_428_; 
v_dir_boxed_427_ = lean_unbox(v_dir_426_);
v_res_428_ = l_Std_Http_Protocol_H1_instReprHead(v_dir_boxed_427_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___lam__0(lean_object* v_x_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = lean_string_from_utf8_unchecked(v_x_429_);
return v___x_430_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__0));
v___x_433_ = lean_string_to_utf8(v___x_432_);
return v___x_433_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1);
v___x_435_ = lean_byte_array_size(v___x_434_);
return v___x_435_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4));
v___x_439_ = lean_string_to_utf8(v___x_438_);
return v___x_439_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5);
v___x_441_ = lean_byte_array_size(v___x_440_);
return v___x_441_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7));
v___x_444_ = lean_string_to_utf8(v___x_443_);
return v___x_444_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8);
v___x_446_ = lean_byte_array_size(v___x_445_);
return v___x_446_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10));
v___x_449_ = lean_string_to_utf8(v___x_448_);
return v___x_449_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11);
v___x_451_ = lean_byte_array_size(v___x_450_);
return v___x_451_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__13));
v___x_454_ = lean_string_to_utf8(v___x_453_);
return v___x_454_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14);
v___x_456_ = lean_byte_array_size(v___x_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1(lean_object* v_out_526_, lean_object* v_req_527_){
_start:
{
uint8_t v_method_528_; uint8_t v_version_529_; lean_object* v_uri_530_; lean_object* v_headers_531_; lean_object* v___y_533_; lean_object* v___y_545_; lean_object* v___y_546_; uint8_t v___y_547_; lean_object* v___y_548_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; uint8_t v___y_583_; lean_object* v___y_584_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; uint8_t v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; uint8_t v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; uint8_t v___y_623_; lean_object* v___y_624_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v_port_631_; uint8_t v___y_632_; lean_object* v___y_633_; lean_object* v___y_642_; lean_object* v___y_643_; uint8_t v___y_644_; lean_object* v_host_645_; lean_object* v_port_646_; lean_object* v___y_647_; lean_object* v___f_657_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; uint8_t v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; uint8_t v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; uint8_t v___y_697_; lean_object* v___y_698_; lean_object* v_port_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; uint8_t v___y_716_; lean_object* v___y_717_; lean_object* v_host_718_; lean_object* v_port_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_733_; 
v_method_528_ = lean_ctor_get_uint8(v_req_527_, sizeof(void*)*2);
v_version_529_ = lean_ctor_get_uint8(v_req_527_, sizeof(void*)*2 + 1);
v_uri_530_ = lean_ctor_get(v_req_527_, 0);
lean_inc(v_uri_530_);
v_headers_531_ = lean_ctor_get(v_req_527_, 1);
lean_inc_ref(v_headers_531_);
lean_dec_ref(v_req_527_);
v___f_657_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__21));
switch(v_method_528_)
{
case 0:
{
lean_object* v___x_811_; 
v___x_811_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36));
v___y_733_ = v___x_811_;
goto v___jp_732_;
}
case 1:
{
lean_object* v___x_812_; 
v___x_812_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37));
v___y_733_ = v___x_812_;
goto v___jp_732_;
}
case 2:
{
lean_object* v___x_813_; 
v___x_813_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38));
v___y_733_ = v___x_813_;
goto v___jp_732_;
}
case 3:
{
lean_object* v___x_814_; 
v___x_814_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39));
v___y_733_ = v___x_814_;
goto v___jp_732_;
}
case 4:
{
lean_object* v___x_815_; 
v___x_815_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40));
v___y_733_ = v___x_815_;
goto v___jp_732_;
}
case 5:
{
lean_object* v___x_816_; 
v___x_816_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41));
v___y_733_ = v___x_816_;
goto v___jp_732_;
}
case 6:
{
lean_object* v___x_817_; 
v___x_817_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42));
v___y_733_ = v___x_817_;
goto v___jp_732_;
}
case 7:
{
lean_object* v___x_818_; 
v___x_818_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43));
v___y_733_ = v___x_818_;
goto v___jp_732_;
}
case 8:
{
lean_object* v___x_819_; 
v___x_819_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44));
v___y_733_ = v___x_819_;
goto v___jp_732_;
}
case 9:
{
lean_object* v___x_820_; 
v___x_820_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45));
v___y_733_ = v___x_820_;
goto v___jp_732_;
}
case 10:
{
lean_object* v___x_821_; 
v___x_821_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46));
v___y_733_ = v___x_821_;
goto v___jp_732_;
}
case 11:
{
lean_object* v___x_822_; 
v___x_822_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47));
v___y_733_ = v___x_822_;
goto v___jp_732_;
}
case 12:
{
lean_object* v___x_823_; 
v___x_823_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48));
v___y_733_ = v___x_823_;
goto v___jp_732_;
}
case 13:
{
lean_object* v___x_824_; 
v___x_824_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49));
v___y_733_ = v___x_824_;
goto v___jp_732_;
}
case 14:
{
lean_object* v___x_825_; 
v___x_825_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50));
v___y_733_ = v___x_825_;
goto v___jp_732_;
}
case 15:
{
lean_object* v___x_826_; 
v___x_826_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51));
v___y_733_ = v___x_826_;
goto v___jp_732_;
}
case 16:
{
lean_object* v___x_827_; 
v___x_827_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52));
v___y_733_ = v___x_827_;
goto v___jp_732_;
}
case 17:
{
lean_object* v___x_828_; 
v___x_828_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53));
v___y_733_ = v___x_828_;
goto v___jp_732_;
}
case 18:
{
lean_object* v___x_829_; 
v___x_829_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54));
v___y_733_ = v___x_829_;
goto v___jp_732_;
}
case 19:
{
lean_object* v___x_830_; 
v___x_830_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55));
v___y_733_ = v___x_830_;
goto v___jp_732_;
}
case 20:
{
lean_object* v___x_831_; 
v___x_831_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56));
v___y_733_ = v___x_831_;
goto v___jp_732_;
}
case 21:
{
lean_object* v___x_832_; 
v___x_832_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57));
v___y_733_ = v___x_832_;
goto v___jp_732_;
}
case 22:
{
lean_object* v___x_833_; 
v___x_833_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58));
v___y_733_ = v___x_833_;
goto v___jp_732_;
}
case 23:
{
lean_object* v___x_834_; 
v___x_834_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59));
v___y_733_ = v___x_834_;
goto v___jp_732_;
}
case 24:
{
lean_object* v___x_835_; 
v___x_835_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60));
v___y_733_ = v___x_835_;
goto v___jp_732_;
}
case 25:
{
lean_object* v___x_836_; 
v___x_836_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61));
v___y_733_ = v___x_836_;
goto v___jp_732_;
}
case 26:
{
lean_object* v___x_837_; 
v___x_837_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62));
v___y_733_ = v___x_837_;
goto v___jp_732_;
}
case 27:
{
lean_object* v___x_838_; 
v___x_838_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__63));
v___y_733_ = v___x_838_;
goto v___jp_732_;
}
case 28:
{
lean_object* v___x_839_; 
v___x_839_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__64));
v___y_733_ = v___x_839_;
goto v___jp_732_;
}
case 29:
{
lean_object* v___x_840_; 
v___x_840_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__65));
v___y_733_ = v___x_840_;
goto v___jp_732_;
}
case 30:
{
lean_object* v___x_841_; 
v___x_841_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__66));
v___y_733_ = v___x_841_;
goto v___jp_732_;
}
case 31:
{
lean_object* v___x_842_; 
v___x_842_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__67));
v___y_733_ = v___x_842_;
goto v___jp_732_;
}
case 32:
{
lean_object* v___x_843_; 
v___x_843_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__68));
v___y_733_ = v___x_843_;
goto v___jp_732_;
}
case 33:
{
lean_object* v___x_844_; 
v___x_844_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__69));
v___y_733_ = v___x_844_;
goto v___jp_732_;
}
case 34:
{
lean_object* v___x_845_; 
v___x_845_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__70));
v___y_733_ = v___x_845_;
goto v___jp_732_;
}
case 35:
{
lean_object* v___x_846_; 
v___x_846_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__71));
v___y_733_ = v___x_846_;
goto v___jp_732_;
}
case 36:
{
lean_object* v___x_847_; 
v___x_847_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__72));
v___y_733_ = v___x_847_;
goto v___jp_732_;
}
case 37:
{
lean_object* v___x_848_; 
v___x_848_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__73));
v___y_733_ = v___x_848_;
goto v___jp_732_;
}
case 38:
{
lean_object* v___x_849_; 
v___x_849_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__74));
v___y_733_ = v___x_849_;
goto v___jp_732_;
}
default: 
{
lean_object* v___x_850_; 
v___x_850_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__75));
v___y_733_ = v___x_850_;
goto v___jp_732_;
}
}
v___jp_532_:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_534_ = lean_byte_array_size(v___y_533_);
v___x_535_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1);
v___x_536_ = lean_unsigned_to_nat(0u);
v___x_537_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_538_ = 0;
v___x_539_ = lean_byte_array_copy_slice(v___x_535_, v___x_536_, v___y_533_, v___x_534_, v___x_537_, v___x_538_);
v___x_540_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3));
v___x_541_ = l_Std_Http_Headers_fold___redArg(v_headers_531_, v___x_539_, v___x_540_);
lean_dec_ref(v_headers_531_);
v___x_542_ = lean_byte_array_size(v___x_541_);
v___x_543_ = lean_byte_array_copy_slice(v___x_535_, v___x_536_, v___x_541_, v___x_542_, v___x_537_, v___x_538_);
return v___x_543_;
}
v___jp_544_:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; lean_object* v___x_554_; 
v___x_549_ = lean_byte_array_size(v___y_546_);
v___x_550_ = lean_string_to_utf8(v___y_548_);
v___x_551_ = lean_byte_array_size(v___x_550_);
v___x_552_ = lean_byte_array_copy_slice(v___x_550_, v___y_545_, v___y_546_, v___x_549_, v___x_551_, v___y_547_);
lean_dec_ref(v___x_550_);
v___x_553_ = 32;
v___x_554_ = lean_byte_array_push(v___x_552_, v___x_553_);
switch(v_version_529_)
{
case 0:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; lean_object* v___x_560_; 
v___x_555_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5);
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = lean_byte_array_size(v___x_554_);
v___x_558_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6);
v___x_559_ = 0;
v___x_560_ = lean_byte_array_copy_slice(v___x_555_, v___x_556_, v___x_554_, v___x_557_, v___x_558_, v___x_559_);
v___y_533_ = v___x_560_;
goto v___jp_532_;
}
case 1:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; lean_object* v___x_566_; 
v___x_561_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8);
v___x_562_ = lean_unsigned_to_nat(0u);
v___x_563_ = lean_byte_array_size(v___x_554_);
v___x_564_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9);
v___x_565_ = 0;
v___x_566_ = lean_byte_array_copy_slice(v___x_561_, v___x_562_, v___x_554_, v___x_563_, v___x_564_, v___x_565_);
v___y_533_ = v___x_566_;
goto v___jp_532_;
}
case 2:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; lean_object* v___x_572_; 
v___x_567_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11);
v___x_568_ = lean_unsigned_to_nat(0u);
v___x_569_ = lean_byte_array_size(v___x_554_);
v___x_570_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12);
v___x_571_ = 0;
v___x_572_ = lean_byte_array_copy_slice(v___x_567_, v___x_568_, v___x_554_, v___x_569_, v___x_570_, v___x_571_);
v___y_533_ = v___x_572_;
goto v___jp_532_;
}
default: 
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; uint8_t v___x_577_; lean_object* v___x_578_; 
v___x_573_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14);
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = lean_byte_array_size(v___x_554_);
v___x_576_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15);
v___x_577_ = 0;
v___x_578_ = lean_byte_array_copy_slice(v___x_573_, v___x_574_, v___x_554_, v___x_575_, v___x_576_, v___x_577_);
v___y_533_ = v___x_578_;
goto v___jp_532_;
}
}
}
v___jp_579_:
{
lean_object* v_queryStr_585_; lean_object* v___x_586_; 
v_queryStr_585_ = l_Std_Http_URI_Query_formatOption(v___y_581_);
v___x_586_ = lean_string_append(v___y_584_, v_queryStr_585_);
lean_dec_ref(v_queryStr_585_);
v___y_545_ = v___y_580_;
v___y_546_ = v___y_582_;
v___y_547_ = v___y_583_;
v___y_548_ = v___x_586_;
goto v___jp_544_;
}
v___jp_587_:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_596_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16));
v___x_597_ = lean_string_append(v___y_594_, v___x_596_);
v___x_598_ = lean_string_append(v___x_597_, v___y_593_);
lean_dec_ref(v___y_593_);
v___x_599_ = lean_string_append(v___x_598_, v___y_592_);
lean_dec_ref(v___y_592_);
v___x_600_ = lean_string_append(v___x_599_, v___y_590_);
lean_dec_ref(v___y_590_);
v___x_601_ = lean_string_append(v___x_600_, v___y_595_);
lean_dec_ref(v___y_595_);
v___y_545_ = v___y_588_;
v___y_546_ = v___y_589_;
v___y_547_ = v___y_591_;
v___y_548_ = v___x_601_;
goto v___jp_544_;
}
v___jp_602_:
{
lean_object* v_queryPart_611_; 
v_queryPart_611_ = l_Std_Http_URI_Query_formatOption(v___y_604_);
if (lean_obj_tag(v___y_608_) == 0)
{
lean_object* v___x_612_; 
v___x_612_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__17));
v___y_588_ = v___y_603_;
v___y_589_ = v___y_605_;
v___y_590_ = v_queryPart_611_;
v___y_591_ = v___y_606_;
v___y_592_ = v___y_610_;
v___y_593_ = v___y_607_;
v___y_594_ = v___y_609_;
v___y_595_ = v___x_612_;
goto v___jp_587_;
}
else
{
lean_object* v_val_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v_val_613_ = lean_ctor_get(v___y_608_, 0);
lean_inc(v_val_613_);
lean_dec_ref_known(v___y_608_, 1);
v___x_614_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__18));
v___x_615_ = l_Std_Http_URI_EncodedFragment_encode(v_val_613_);
v___x_616_ = lean_string_from_utf8_unchecked(v___x_615_);
v___x_617_ = lean_string_append(v___x_614_, v___x_616_);
lean_dec_ref(v___x_616_);
v___y_588_ = v___y_603_;
v___y_589_ = v___y_605_;
v___y_590_ = v_queryPart_611_;
v___y_591_ = v___y_606_;
v___y_592_ = v___y_610_;
v___y_593_ = v___y_607_;
v___y_594_ = v___y_609_;
v___y_595_ = v___x_617_;
goto v___jp_587_;
}
}
v___jp_618_:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_string_append(v___y_620_, v___y_621_);
lean_dec_ref(v___y_621_);
v___x_626_ = lean_string_append(v___x_625_, v___y_624_);
lean_dec_ref(v___y_624_);
v___y_545_ = v___y_619_;
v___y_546_ = v___y_622_;
v___y_547_ = v___y_623_;
v___y_548_ = v___x_626_;
goto v___jp_544_;
}
v___jp_627_:
{
switch(lean_obj_tag(v_port_631_))
{
case 0:
{
lean_object* v___x_634_; 
v___x_634_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__17));
v___y_619_ = v___y_629_;
v___y_620_ = v___y_628_;
v___y_621_ = v___y_633_;
v___y_622_ = v___y_630_;
v___y_623_ = v___y_632_;
v___y_624_ = v___x_634_;
goto v___jp_618_;
}
case 1:
{
lean_object* v___x_635_; 
v___x_635_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16));
v___y_619_ = v___y_629_;
v___y_620_ = v___y_628_;
v___y_621_ = v___y_633_;
v___y_622_ = v___y_630_;
v___y_623_ = v___y_632_;
v___y_624_ = v___x_635_;
goto v___jp_618_;
}
default: 
{
uint16_t v_port_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v_port_636_ = lean_ctor_get_uint16(v_port_631_, 0);
lean_dec_ref_known(v_port_631_, 0);
v___x_637_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16));
v___x_638_ = lean_uint16_to_nat(v_port_636_);
v___x_639_ = l_Nat_reprFast(v___x_638_);
v___x_640_ = lean_string_append(v___x_637_, v___x_639_);
lean_dec_ref(v___x_639_);
v___y_619_ = v___y_629_;
v___y_620_ = v___y_628_;
v___y_621_ = v___y_633_;
v___y_622_ = v___y_630_;
v___y_623_ = v___y_632_;
v___y_624_ = v___x_640_;
goto v___jp_618_;
}
}
}
v___jp_641_:
{
switch(lean_obj_tag(v_host_645_))
{
case 0:
{
lean_object* v_name_648_; 
v_name_648_ = lean_ctor_get(v_host_645_, 0);
lean_inc_ref(v_name_648_);
lean_dec_ref_known(v_host_645_, 1);
v___y_628_ = v___y_647_;
v___y_629_ = v___y_642_;
v___y_630_ = v___y_643_;
v_port_631_ = v_port_646_;
v___y_632_ = v___y_644_;
v___y_633_ = v_name_648_;
goto v___jp_627_;
}
case 1:
{
lean_object* v_ipv4_649_; lean_object* v___x_650_; 
v_ipv4_649_ = lean_ctor_get(v_host_645_, 0);
lean_inc_ref(v_ipv4_649_);
lean_dec_ref_known(v_host_645_, 1);
v___x_650_ = lean_uv_ntop_v4(v_ipv4_649_);
lean_dec_ref(v_ipv4_649_);
v___y_628_ = v___y_647_;
v___y_629_ = v___y_642_;
v___y_630_ = v___y_643_;
v_port_631_ = v_port_646_;
v___y_632_ = v___y_644_;
v___y_633_ = v___x_650_;
goto v___jp_627_;
}
default: 
{
lean_object* v_ipv6_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v_ipv6_651_ = lean_ctor_get(v_host_645_, 0);
lean_inc_ref(v_ipv6_651_);
lean_dec_ref_known(v_host_645_, 1);
v___x_652_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__19));
v___x_653_ = lean_uv_ntop_v6(v_ipv6_651_);
lean_dec_ref(v_ipv6_651_);
v___x_654_ = lean_string_append(v___x_652_, v___x_653_);
lean_dec_ref(v___x_653_);
v___x_655_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__20));
v___x_656_ = lean_string_append(v___x_654_, v___x_655_);
v___y_628_ = v___y_647_;
v___y_629_ = v___y_642_;
v___y_630_ = v___y_643_;
v_port_631_ = v_port_646_;
v___y_632_ = v___y_644_;
v___y_633_ = v___x_656_;
goto v___jp_627_;
}
}
}
v___jp_658_:
{
lean_object* v_segments_667_; uint8_t v_absolute_668_; lean_object* v___x_669_; lean_object* v___x_670_; size_t v_sz_671_; size_t v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v_result_675_; 
v_segments_667_ = lean_ctor_get(v___y_663_, 0);
lean_inc_ref(v_segments_667_);
v_absolute_668_ = lean_ctor_get_uint8(v___y_663_, sizeof(void*)*1);
lean_dec_ref(v___y_663_);
v___x_669_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22));
v___x_670_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32));
v_sz_671_ = lean_array_size(v_segments_667_);
v___x_672_ = ((size_t)0ULL);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_670_, v___f_657_, v_sz_671_, v___x_672_, v_segments_667_);
v___x_674_ = lean_array_to_list(v___x_673_);
v_result_675_ = l_String_intercalate(v___x_669_, v___x_674_);
if (v_absolute_668_ == 0)
{
v___y_603_ = v___y_659_;
v___y_604_ = v___y_660_;
v___y_605_ = v___y_661_;
v___y_606_ = v___y_662_;
v___y_607_ = v___y_666_;
v___y_608_ = v___y_664_;
v___y_609_ = v___y_665_;
v___y_610_ = v_result_675_;
goto v___jp_602_;
}
else
{
lean_object* v___x_676_; 
v___x_676_ = lean_string_append(v___x_669_, v_result_675_);
lean_dec_ref(v_result_675_);
v___y_603_ = v___y_659_;
v___y_604_ = v___y_660_;
v___y_605_ = v___y_661_;
v___y_606_ = v___y_662_;
v___y_607_ = v___y_666_;
v___y_608_ = v___y_664_;
v___y_609_ = v___y_665_;
v___y_610_ = v___x_676_;
goto v___jp_602_;
}
}
v___jp_677_:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_689_ = lean_string_append(v___y_687_, v___y_681_);
lean_dec_ref(v___y_681_);
v___x_690_ = lean_string_append(v___x_689_, v___y_688_);
lean_dec_ref(v___y_688_);
lean_inc_ref(v___y_679_);
v___x_691_ = lean_string_append(v___y_679_, v___x_690_);
lean_dec_ref(v___x_690_);
v___y_659_ = v___y_678_;
v___y_660_ = v___y_680_;
v___y_661_ = v___y_682_;
v___y_662_ = v___y_683_;
v___y_663_ = v___y_684_;
v___y_664_ = v___y_685_;
v___y_665_ = v___y_686_;
v___y_666_ = v___x_691_;
goto v___jp_658_;
}
v___jp_692_:
{
switch(lean_obj_tag(v_port_699_))
{
case 0:
{
lean_object* v___x_704_; 
v___x_704_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__17));
v___y_678_ = v___y_694_;
v___y_679_ = v___y_693_;
v___y_680_ = v___y_695_;
v___y_681_ = v___y_703_;
v___y_682_ = v___y_696_;
v___y_683_ = v___y_697_;
v___y_684_ = v___y_698_;
v___y_685_ = v___y_700_;
v___y_686_ = v___y_702_;
v___y_687_ = v___y_701_;
v___y_688_ = v___x_704_;
goto v___jp_677_;
}
case 1:
{
lean_object* v___x_705_; 
v___x_705_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16));
v___y_678_ = v___y_694_;
v___y_679_ = v___y_693_;
v___y_680_ = v___y_695_;
v___y_681_ = v___y_703_;
v___y_682_ = v___y_696_;
v___y_683_ = v___y_697_;
v___y_684_ = v___y_698_;
v___y_685_ = v___y_700_;
v___y_686_ = v___y_702_;
v___y_687_ = v___y_701_;
v___y_688_ = v___x_705_;
goto v___jp_677_;
}
default: 
{
uint16_t v_port_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v_port_706_ = lean_ctor_get_uint16(v_port_699_, 0);
lean_dec_ref_known(v_port_699_, 0);
v___x_707_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16));
v___x_708_ = lean_uint16_to_nat(v_port_706_);
v___x_709_ = l_Nat_reprFast(v___x_708_);
v___x_710_ = lean_string_append(v___x_707_, v___x_709_);
lean_dec_ref(v___x_709_);
v___y_678_ = v___y_694_;
v___y_679_ = v___y_693_;
v___y_680_ = v___y_695_;
v___y_681_ = v___y_703_;
v___y_682_ = v___y_696_;
v___y_683_ = v___y_697_;
v___y_684_ = v___y_698_;
v___y_685_ = v___y_700_;
v___y_686_ = v___y_702_;
v___y_687_ = v___y_701_;
v___y_688_ = v___x_710_;
goto v___jp_677_;
}
}
}
v___jp_711_:
{
switch(lean_obj_tag(v_host_718_))
{
case 0:
{
lean_object* v_name_723_; 
v_name_723_ = lean_ctor_get(v_host_718_, 0);
lean_inc_ref(v_name_723_);
lean_dec_ref_known(v_host_718_, 1);
v___y_693_ = v___y_713_;
v___y_694_ = v___y_712_;
v___y_695_ = v___y_714_;
v___y_696_ = v___y_715_;
v___y_697_ = v___y_716_;
v___y_698_ = v___y_717_;
v_port_699_ = v_port_719_;
v___y_700_ = v___y_720_;
v___y_701_ = v___y_722_;
v___y_702_ = v___y_721_;
v___y_703_ = v_name_723_;
goto v___jp_692_;
}
case 1:
{
lean_object* v_ipv4_724_; lean_object* v___x_725_; 
v_ipv4_724_ = lean_ctor_get(v_host_718_, 0);
lean_inc_ref(v_ipv4_724_);
lean_dec_ref_known(v_host_718_, 1);
v___x_725_ = lean_uv_ntop_v4(v_ipv4_724_);
lean_dec_ref(v_ipv4_724_);
v___y_693_ = v___y_713_;
v___y_694_ = v___y_712_;
v___y_695_ = v___y_714_;
v___y_696_ = v___y_715_;
v___y_697_ = v___y_716_;
v___y_698_ = v___y_717_;
v_port_699_ = v_port_719_;
v___y_700_ = v___y_720_;
v___y_701_ = v___y_722_;
v___y_702_ = v___y_721_;
v___y_703_ = v___x_725_;
goto v___jp_692_;
}
default: 
{
lean_object* v_ipv6_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_ipv6_726_ = lean_ctor_get(v_host_718_, 0);
lean_inc_ref(v_ipv6_726_);
lean_dec_ref_known(v_host_718_, 1);
v___x_727_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__19));
v___x_728_ = lean_uv_ntop_v6(v_ipv6_726_);
lean_dec_ref(v_ipv6_726_);
v___x_729_ = lean_string_append(v___x_727_, v___x_728_);
lean_dec_ref(v___x_728_);
v___x_730_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__20));
v___x_731_ = lean_string_append(v___x_729_, v___x_730_);
v___y_693_ = v___y_713_;
v___y_694_ = v___y_712_;
v___y_695_ = v___y_714_;
v___y_696_ = v___y_715_;
v___y_697_ = v___y_716_;
v___y_698_ = v___y_717_;
v_port_699_ = v_port_719_;
v___y_700_ = v___y_720_;
v___y_701_ = v___y_722_;
v___y_702_ = v___y_721_;
v___y_703_ = v___x_731_;
goto v___jp_692_;
}
}
}
v___jp_732_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; lean_object* v___x_741_; 
v___x_734_ = lean_byte_array_size(v_out_526_);
lean_inc_ref(v___y_733_);
v___x_735_ = lean_string_to_utf8(v___y_733_);
v___x_736_ = lean_unsigned_to_nat(0u);
v___x_737_ = lean_byte_array_size(v___x_735_);
v___x_738_ = 0;
v___x_739_ = lean_byte_array_copy_slice(v___x_735_, v___x_736_, v_out_526_, v___x_734_, v___x_737_, v___x_738_);
lean_dec_ref(v___x_735_);
v___x_740_ = 32;
v___x_741_ = lean_byte_array_push(v___x_739_, v___x_740_);
switch(lean_obj_tag(v_uri_530_))
{
case 0:
{
lean_object* v_path_742_; lean_object* v_query_743_; lean_object* v_segments_744_; uint8_t v_absolute_745_; lean_object* v___x_746_; lean_object* v___x_747_; size_t v_sz_748_; size_t v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v_result_752_; 
v_path_742_ = lean_ctor_get(v_uri_530_, 0);
lean_inc_ref(v_path_742_);
v_query_743_ = lean_ctor_get(v_uri_530_, 1);
lean_inc(v_query_743_);
lean_dec_ref_known(v_uri_530_, 2);
v_segments_744_ = lean_ctor_get(v_path_742_, 0);
lean_inc_ref(v_segments_744_);
v_absolute_745_ = lean_ctor_get_uint8(v_path_742_, sizeof(void*)*1);
lean_dec_ref(v_path_742_);
v___x_746_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22));
v___x_747_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32));
v_sz_748_ = lean_array_size(v_segments_744_);
v___x_749_ = ((size_t)0ULL);
v___x_750_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_747_, v___f_657_, v_sz_748_, v___x_749_, v_segments_744_);
v___x_751_ = lean_array_to_list(v___x_750_);
v_result_752_ = l_String_intercalate(v___x_746_, v___x_751_);
if (v_absolute_745_ == 0)
{
v___y_580_ = v___x_736_;
v___y_581_ = v_query_743_;
v___y_582_ = v___x_741_;
v___y_583_ = v___x_738_;
v___y_584_ = v_result_752_;
goto v___jp_579_;
}
else
{
lean_object* v___x_753_; 
v___x_753_ = lean_string_append(v___x_746_, v_result_752_);
lean_dec_ref(v_result_752_);
v___y_580_ = v___x_736_;
v___y_581_ = v_query_743_;
v___y_582_ = v___x_741_;
v___y_583_ = v___x_738_;
v___y_584_ = v___x_753_;
goto v___jp_579_;
}
}
case 1:
{
lean_object* v_uri_754_; lean_object* v_authority_755_; 
v_uri_754_ = lean_ctor_get(v_uri_530_, 0);
lean_inc_ref(v_uri_754_);
lean_dec_ref_known(v_uri_530_, 1);
v_authority_755_ = lean_ctor_get(v_uri_754_, 1);
if (lean_obj_tag(v_authority_755_) == 0)
{
lean_object* v_scheme_756_; lean_object* v_path_757_; lean_object* v_query_758_; lean_object* v_fragment_759_; lean_object* v___x_760_; 
v_scheme_756_ = lean_ctor_get(v_uri_754_, 0);
lean_inc_ref(v_scheme_756_);
v_path_757_ = lean_ctor_get(v_uri_754_, 2);
lean_inc_ref(v_path_757_);
v_query_758_ = lean_ctor_get(v_uri_754_, 3);
lean_inc(v_query_758_);
v_fragment_759_ = lean_ctor_get(v_uri_754_, 4);
lean_inc(v_fragment_759_);
lean_dec_ref(v_uri_754_);
v___x_760_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__17));
v___y_659_ = v___x_736_;
v___y_660_ = v_query_758_;
v___y_661_ = v___x_741_;
v___y_662_ = v___x_738_;
v___y_663_ = v_path_757_;
v___y_664_ = v_fragment_759_;
v___y_665_ = v_scheme_756_;
v___y_666_ = v___x_760_;
goto v___jp_658_;
}
else
{
lean_object* v_val_761_; lean_object* v_scheme_762_; lean_object* v_path_763_; lean_object* v_query_764_; lean_object* v_fragment_765_; lean_object* v_userInfo_766_; lean_object* v_host_767_; lean_object* v_port_768_; lean_object* v___x_769_; 
v_val_761_ = lean_ctor_get(v_authority_755_, 0);
lean_inc(v_val_761_);
v_scheme_762_ = lean_ctor_get(v_uri_754_, 0);
lean_inc_ref(v_scheme_762_);
v_path_763_ = lean_ctor_get(v_uri_754_, 2);
lean_inc_ref(v_path_763_);
v_query_764_ = lean_ctor_get(v_uri_754_, 3);
lean_inc(v_query_764_);
v_fragment_765_ = lean_ctor_get(v_uri_754_, 4);
lean_inc(v_fragment_765_);
lean_dec_ref(v_uri_754_);
v_userInfo_766_ = lean_ctor_get(v_val_761_, 0);
lean_inc(v_userInfo_766_);
v_host_767_ = lean_ctor_get(v_val_761_, 1);
lean_inc_ref(v_host_767_);
v_port_768_ = lean_ctor_get(v_val_761_, 2);
lean_inc(v_port_768_);
lean_dec(v_val_761_);
v___x_769_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33));
if (lean_obj_tag(v_userInfo_766_) == 0)
{
lean_object* v___x_770_; 
v___x_770_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__17));
v___y_712_ = v___x_736_;
v___y_713_ = v___x_769_;
v___y_714_ = v_query_764_;
v___y_715_ = v___x_741_;
v___y_716_ = v___x_738_;
v___y_717_ = v_path_763_;
v_host_718_ = v_host_767_;
v_port_719_ = v_port_768_;
v___y_720_ = v_fragment_765_;
v___y_721_ = v_scheme_762_;
v___y_722_ = v___x_770_;
goto v___jp_711_;
}
else
{
lean_object* v_val_771_; lean_object* v_password_772_; 
v_val_771_ = lean_ctor_get(v_userInfo_766_, 0);
lean_inc(v_val_771_);
lean_dec_ref_known(v_userInfo_766_, 1);
v_password_772_ = lean_ctor_get(v_val_771_, 1);
if (lean_obj_tag(v_password_772_) == 0)
{
lean_object* v_username_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v_username_773_ = lean_ctor_get(v_val_771_, 0);
lean_inc_ref(v_username_773_);
lean_dec(v_val_771_);
v___x_774_ = lean_string_from_utf8_unchecked(v_username_773_);
v___x_775_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34));
v___x_776_ = lean_string_append(v___x_774_, v___x_775_);
v___y_712_ = v___x_736_;
v___y_713_ = v___x_769_;
v___y_714_ = v_query_764_;
v___y_715_ = v___x_741_;
v___y_716_ = v___x_738_;
v___y_717_ = v_path_763_;
v_host_718_ = v_host_767_;
v_port_719_ = v_port_768_;
v___y_720_ = v_fragment_765_;
v___y_721_ = v_scheme_762_;
v___y_722_ = v___x_776_;
goto v___jp_711_;
}
else
{
lean_object* v_username_777_; lean_object* v_val_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
lean_inc_ref(v_password_772_);
v_username_777_ = lean_ctor_get(v_val_771_, 0);
lean_inc_ref(v_username_777_);
lean_dec(v_val_771_);
v_val_778_ = lean_ctor_get(v_password_772_, 0);
lean_inc(v_val_778_);
lean_dec_ref_known(v_password_772_, 1);
v___x_779_ = lean_string_from_utf8_unchecked(v_username_777_);
v___x_780_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16));
v___x_781_ = lean_string_append(v___x_779_, v___x_780_);
v___x_782_ = lean_string_from_utf8_unchecked(v_val_778_);
v___x_783_ = lean_string_append(v___x_781_, v___x_782_);
lean_dec_ref(v___x_782_);
v___x_784_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34));
v___x_785_ = lean_string_append(v___x_783_, v___x_784_);
v___y_712_ = v___x_736_;
v___y_713_ = v___x_769_;
v___y_714_ = v_query_764_;
v___y_715_ = v___x_741_;
v___y_716_ = v___x_738_;
v___y_717_ = v_path_763_;
v_host_718_ = v_host_767_;
v_port_719_ = v_port_768_;
v___y_720_ = v_fragment_765_;
v___y_721_ = v_scheme_762_;
v___y_722_ = v___x_785_;
goto v___jp_711_;
}
}
}
}
case 2:
{
lean_object* v_authority_786_; lean_object* v_userInfo_787_; 
v_authority_786_ = lean_ctor_get(v_uri_530_, 0);
lean_inc_ref(v_authority_786_);
lean_dec_ref_known(v_uri_530_, 1);
v_userInfo_787_ = lean_ctor_get(v_authority_786_, 0);
if (lean_obj_tag(v_userInfo_787_) == 0)
{
lean_object* v_host_788_; lean_object* v_port_789_; lean_object* v___x_790_; 
v_host_788_ = lean_ctor_get(v_authority_786_, 1);
lean_inc_ref(v_host_788_);
v_port_789_ = lean_ctor_get(v_authority_786_, 2);
lean_inc(v_port_789_);
lean_dec_ref(v_authority_786_);
v___x_790_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__17));
v___y_642_ = v___x_736_;
v___y_643_ = v___x_741_;
v___y_644_ = v___x_738_;
v_host_645_ = v_host_788_;
v_port_646_ = v_port_789_;
v___y_647_ = v___x_790_;
goto v___jp_641_;
}
else
{
lean_object* v_val_791_; lean_object* v_password_792_; 
v_val_791_ = lean_ctor_get(v_userInfo_787_, 0);
lean_inc(v_val_791_);
v_password_792_ = lean_ctor_get(v_val_791_, 1);
if (lean_obj_tag(v_password_792_) == 0)
{
lean_object* v_host_793_; lean_object* v_port_794_; lean_object* v_username_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_host_793_ = lean_ctor_get(v_authority_786_, 1);
lean_inc_ref(v_host_793_);
v_port_794_ = lean_ctor_get(v_authority_786_, 2);
lean_inc(v_port_794_);
lean_dec_ref(v_authority_786_);
v_username_795_ = lean_ctor_get(v_val_791_, 0);
lean_inc_ref(v_username_795_);
lean_dec(v_val_791_);
v___x_796_ = lean_string_from_utf8_unchecked(v_username_795_);
v___x_797_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34));
v___x_798_ = lean_string_append(v___x_796_, v___x_797_);
v___y_642_ = v___x_736_;
v___y_643_ = v___x_741_;
v___y_644_ = v___x_738_;
v_host_645_ = v_host_793_;
v_port_646_ = v_port_794_;
v___y_647_ = v___x_798_;
goto v___jp_641_;
}
else
{
lean_object* v_host_799_; lean_object* v_port_800_; lean_object* v_username_801_; lean_object* v_val_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
lean_inc_ref(v_password_792_);
v_host_799_ = lean_ctor_get(v_authority_786_, 1);
lean_inc_ref(v_host_799_);
v_port_800_ = lean_ctor_get(v_authority_786_, 2);
lean_inc(v_port_800_);
lean_dec_ref(v_authority_786_);
v_username_801_ = lean_ctor_get(v_val_791_, 0);
lean_inc_ref(v_username_801_);
lean_dec(v_val_791_);
v_val_802_ = lean_ctor_get(v_password_792_, 0);
lean_inc(v_val_802_);
lean_dec_ref_known(v_password_792_, 1);
v___x_803_ = lean_string_from_utf8_unchecked(v_username_801_);
v___x_804_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16));
v___x_805_ = lean_string_append(v___x_803_, v___x_804_);
v___x_806_ = lean_string_from_utf8_unchecked(v_val_802_);
v___x_807_ = lean_string_append(v___x_805_, v___x_806_);
lean_dec_ref(v___x_806_);
v___x_808_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34));
v___x_809_ = lean_string_append(v___x_807_, v___x_808_);
v___y_642_ = v___x_736_;
v___y_643_ = v___x_741_;
v___y_644_ = v___x_738_;
v_host_645_ = v_host_799_;
v_port_646_ = v_port_800_;
v___y_647_ = v___x_809_;
goto v___jp_641_;
}
}
}
default: 
{
lean_object* v___x_810_; 
v___x_810_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35));
v___y_545_ = v___x_736_;
v___y_546_ = v___x_741_;
v___y_547_ = v___x_738_;
v___y_548_ = v___x_810_;
goto v___jp_544_;
}
}
}
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__1(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__0));
v___x_853_ = lean_string_to_utf8(v___x_852_);
return v___x_853_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__2(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__1, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__1_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__1);
v___x_855_ = lean_byte_array_size(v___x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(lean_object* v_out_856_, lean_object* v_r_857_){
_start:
{
lean_object* v_status_858_; uint8_t v_version_859_; lean_object* v_headers_860_; lean_object* v___y_862_; lean_object* v___y_874_; 
v_status_858_ = lean_ctor_get(v_r_857_, 0);
v_version_859_ = lean_ctor_get_uint8(v_r_857_, sizeof(void*)*2);
v_headers_860_ = lean_ctor_get(v_r_857_, 1);
switch(v_version_859_)
{
case 0:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; lean_object* v___x_899_; 
v___x_894_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5);
v___x_895_ = lean_unsigned_to_nat(0u);
v___x_896_ = lean_byte_array_size(v_out_856_);
v___x_897_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6);
v___x_898_ = 0;
v___x_899_ = lean_byte_array_copy_slice(v___x_894_, v___x_895_, v_out_856_, v___x_896_, v___x_897_, v___x_898_);
v___y_874_ = v___x_899_;
goto v___jp_873_;
}
case 1:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; lean_object* v___x_905_; 
v___x_900_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8);
v___x_901_ = lean_unsigned_to_nat(0u);
v___x_902_ = lean_byte_array_size(v_out_856_);
v___x_903_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9);
v___x_904_ = 0;
v___x_905_ = lean_byte_array_copy_slice(v___x_900_, v___x_901_, v_out_856_, v___x_902_, v___x_903_, v___x_904_);
v___y_874_ = v___x_905_;
goto v___jp_873_;
}
case 2:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; lean_object* v___x_911_; 
v___x_906_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11);
v___x_907_ = lean_unsigned_to_nat(0u);
v___x_908_ = lean_byte_array_size(v_out_856_);
v___x_909_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12);
v___x_910_ = 0;
v___x_911_ = lean_byte_array_copy_slice(v___x_906_, v___x_907_, v_out_856_, v___x_908_, v___x_909_, v___x_910_);
v___y_874_ = v___x_911_;
goto v___jp_873_;
}
default: 
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; lean_object* v___x_917_; 
v___x_912_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14);
v___x_913_ = lean_unsigned_to_nat(0u);
v___x_914_ = lean_byte_array_size(v_out_856_);
v___x_915_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15);
v___x_916_ = 0;
v___x_917_ = lean_byte_array_copy_slice(v___x_912_, v___x_913_, v_out_856_, v___x_914_, v___x_915_, v___x_916_);
v___y_874_ = v___x_917_;
goto v___jp_873_;
}
}
v___jp_861_:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; uint8_t v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_863_ = lean_byte_array_size(v___y_862_);
v___x_864_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1);
v___x_865_ = lean_unsigned_to_nat(0u);
v___x_866_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_867_ = 0;
v___x_868_ = lean_byte_array_copy_slice(v___x_864_, v___x_865_, v___y_862_, v___x_863_, v___x_866_, v___x_867_);
v___x_869_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3));
v___x_870_ = l_Std_Http_Headers_fold___redArg(v_headers_860_, v___x_868_, v___x_869_);
v___x_871_ = lean_byte_array_size(v___x_870_);
v___x_872_ = lean_byte_array_copy_slice(v___x_864_, v___x_865_, v___x_870_, v___x_871_, v___x_866_, v___x_867_);
return v___x_872_;
}
v___jp_873_:
{
uint8_t v___x_875_; lean_object* v___x_876_; 
v___x_875_ = 32;
v___x_876_ = lean_byte_array_push(v___y_874_, v___x_875_);
if (lean_obj_tag(v_status_858_) == 4)
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; uint8_t v___x_881_; lean_object* v___x_882_; 
v___x_877_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__1, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__1_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__1);
v___x_878_ = lean_unsigned_to_nat(0u);
v___x_879_ = lean_byte_array_size(v___x_876_);
v___x_880_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__2);
v___x_881_ = 0;
v___x_882_ = lean_byte_array_copy_slice(v___x_877_, v___x_878_, v___x_876_, v___x_879_, v___x_880_, v___x_881_);
v___y_862_ = v___x_882_;
goto v___jp_861_;
}
else
{
uint16_t v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; lean_object* v___x_893_; 
v___x_883_ = l_Std_Http_Status_toCode(v_status_858_);
v___x_884_ = lean_uint16_to_nat(v___x_883_);
v___x_885_ = l_Std_Http_Internal_appendNat(v___x_876_, v___x_884_);
v___x_886_ = lean_byte_array_push(v___x_885_, v___x_875_);
v___x_887_ = l_Std_Http_Status_reasonPhrase(v_status_858_);
v___x_888_ = lean_string_to_utf8(v___x_887_);
v___x_889_ = lean_unsigned_to_nat(0u);
v___x_890_ = lean_byte_array_size(v___x_886_);
v___x_891_ = lean_byte_array_size(v___x_888_);
v___x_892_ = 0;
v___x_893_ = lean_byte_array_copy_slice(v___x_888_, v___x_889_, v___x_886_, v___x_890_, v___x_891_, v___x_892_);
lean_dec_ref(v___x_888_);
v___y_862_ = v___x_893_;
goto v___jp_861_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___boxed(lean_object* v_out_918_, lean_object* v_r_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(v_out_918_, v_r_919_);
lean_dec_ref(v_r_919_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head(uint8_t v_dir_923_){
_start:
{
if (v_dir_923_ == 0)
{
lean_object* v___x_924_; 
v___x_924_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___closed__0));
return v___x_924_;
}
else
{
lean_object* v___x_925_; 
v___x_925_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___closed__1));
return v___x_925_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___boxed(lean_object* v_dir_926_){
_start:
{
uint8_t v_dir_boxed_927_; lean_object* v_res_928_; 
v_dir_boxed_927_ = lean_unbox(v_dir_926_);
v_res_928_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v_dir_boxed_927_);
return v_res_928_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; uint8_t v___x_931_; uint8_t v___x_932_; lean_object* v___x_933_; 
v___x_929_ = l_Std_Http_Headers_empty;
v___x_930_ = lean_box(3);
v___x_931_ = 1;
v___x_932_ = 8;
v___x_933_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_933_, 0, v___x_930_);
lean_ctor_set(v___x_933_, 1, v___x_929_);
lean_ctor_set_uint8(v___x_933_, sizeof(void*)*2, v___x_932_);
lean_ctor_set_uint8(v___x_933_, sizeof(void*)*2 + 1, v___x_931_);
return v___x_933_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1(void){
_start:
{
lean_object* v___x_934_; uint8_t v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_934_ = l_Std_Http_Headers_empty;
v___x_935_ = 1;
v___x_936_ = lean_box(4);
v___x_937_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_937_, 0, v___x_936_);
lean_ctor_set(v___x_937_, 1, v___x_934_);
lean_ctor_set_uint8(v___x_937_, sizeof(void*)*2, v___x_935_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead(uint8_t v_dir_938_){
_start:
{
if (v_dir_938_ == 0)
{
lean_object* v___x_939_; 
v___x_939_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0, &l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0_once, _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0);
return v___x_939_;
}
else
{
lean_object* v___x_940_; 
v___x_940_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1, &l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1_once, _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1);
return v___x_940_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead___boxed(lean_object* v_dir_941_){
_start:
{
uint8_t v_dir_boxed_942_; lean_object* v_res_943_; 
v_dir_boxed_942_ = lean_unbox(v_dir_941_);
v_res_943_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v_dir_boxed_942_);
return v_res_943_;
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
