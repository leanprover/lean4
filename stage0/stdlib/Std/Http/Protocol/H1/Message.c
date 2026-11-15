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
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Http_Internal_appendFieldLine___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Headers_fold___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
uint16_t l_Std_Http_Status_toCode(lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* l_Std_Http_Internal_appendNat(lean_object*, lean_object*);
lean_object* l_Std_Http_Status_reasonPhrase(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Http_URI_Query_formatOption(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_Http_URI_Path_render(lean_object*, uint8_t, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_uv_ntop_v4(lean_object*);
lean_object* lean_uv_ntop_v6(lean_object*);
extern lean_object* l_Std_Http_Header_Name_connection;
extern lean_object* l_Std_Http_Header_Name_transferEncoding;
uint8_t l_Std_Http_instBEqVersion_beq(uint8_t, uint8_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Std_Http_Header_TransferEncoding_finalCodingIsChunked_x3f(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__18 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__18_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "//"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__19 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__19_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__20 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__20_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__21 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__21_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ACL"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "BASELINE-CONTROL"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "BIND"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CHECKIN"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CHECKOUT"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CONNECT"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "COPY"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "DELETE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "GET"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "LABEL"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LINK"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LOCK"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MERGE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKACTIVITY"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKCALENDAR"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MKCOL"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "MKREDIRECTREF"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MKWORKSPACE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "MOVE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "OPTIONS"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ORDERPATCH"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PATCH"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "POST"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PRI"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "PROPFIND"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PROPPATCH"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PUT"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "QUERY"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REBIND"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REPORT"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "SEARCH"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "TRACE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNBIND"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "UNCHECKOUT"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLINK"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLOCK"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UPDATE"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "UPDATEREDIRECTREF"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61_value;
static const lean_string_object l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "VERSION-CONTROL"};
static const lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62 = (const lean_object*)&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62_value;
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
lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___x_214_; lean_object* v___y_216_; lean_object* v___y_225_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_214_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_169_, v_message_170_);
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__3));
v___x_233_ = lean_array_get_size(v___x_214_);
v___x_234_ = lean_nat_dec_lt(v___x_231_, v___x_233_);
if (v___x_234_ == 0)
{
v___y_225_ = v___x_232_;
goto v___jp_224_;
}
else
{
size_t v___x_235_; size_t v___x_236_; lean_object* v___x_237_; 
v___x_235_ = ((size_t)0ULL);
v___x_236_ = lean_usize_of_nat(v___x_233_);
v___x_237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__1(v___x_214_, v___x_235_, v___x_236_, v___x_232_);
v___y_225_ = v___x_237_;
goto v___jp_224_;
}
v___jp_172_:
{
lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_175_ = lean_array_get_size(v___y_174_);
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_177_ = lean_nat_dec_eq(v___x_175_, v___x_176_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; 
v___x_178_ = l_Std_Http_Header_TransferEncoding_finalCodingIsChunked_x3f(v___y_174_);
lean_dec_ref(v___y_174_);
if (lean_obj_tag(v___x_178_) == 1)
{
lean_object* v_val_179_; uint8_t v___x_180_; 
v_val_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_val_179_);
lean_dec_ref_known(v___x_178_, 1);
v___x_180_ = lean_unbox(v_val_179_);
lean_dec(v_val_179_);
if (v___x_180_ == 1)
{
if (lean_obj_tag(v___y_173_) == 0)
{
uint8_t v___x_181_; uint8_t v___x_182_; uint8_t v___x_183_; 
v___x_181_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_169_, v_message_170_);
v___x_182_ = 0;
v___x_183_ = l_Std_Http_instBEqVersion_beq(v___x_181_, v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; 
v___x_184_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__0));
return v___x_184_;
}
else
{
lean_object* v___x_185_; 
v___x_185_ = lean_box(0);
return v___x_185_;
}
}
else
{
lean_object* v___x_186_; 
lean_dec(v___y_173_);
v___x_186_ = lean_box(0);
return v___x_186_;
}
}
else
{
lean_object* v___x_187_; 
lean_dec(v___y_173_);
v___x_187_ = lean_box(0);
return v___x_187_;
}
}
else
{
lean_object* v___x_188_; 
lean_dec(v___x_178_);
lean_dec(v___y_173_);
v___x_188_ = lean_box(0);
return v___x_188_;
}
}
else
{
lean_dec_ref(v___y_174_);
if (lean_obj_tag(v___y_173_) == 0)
{
if (v_allowEOFBody_171_ == 0)
{
lean_object* v___x_189_; 
v___x_189_ = lean_box(0);
return v___x_189_;
}
else
{
lean_object* v___x_190_; 
v___x_190_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__2));
return v___x_190_;
}
}
else
{
lean_object* v_val_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_213_; 
v_val_191_ = lean_ctor_get(v___y_173_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___y_173_);
if (v_isSharedCheck_213_ == 0)
{
v___x_193_ = v___y_173_;
v_isShared_194_ = v_isSharedCheck_213_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_val_191_);
lean_dec(v___y_173_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_213_;
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
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_array_fget(v_val_191_, v___x_176_);
lean_dec(v_val_191_);
v___x_200_ = l_Std_Http_Header_ContentLength_parse(v___x_199_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v___x_201_; 
lean_del_object(v___x_193_);
v___x_201_ = lean_box(0);
return v___x_201_;
}
else
{
lean_object* v_val_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_212_; 
v_val_202_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_212_ == 0)
{
v___x_204_ = v___x_200_;
v_isShared_205_ = v_isSharedCheck_212_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_val_202_);
lean_dec(v___x_200_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_212_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 0, v_val_202_);
v___x_207_ = v___x_193_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_val_202_);
v___x_207_ = v_reuseFailAlloc_211_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_209_; 
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_207_);
v___x_209_ = v___x_204_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
}
}
}
}
}
v___jp_215_:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__3));
v___x_219_ = lean_array_get_size(v___x_214_);
v___x_220_ = lean_nat_dec_lt(v___x_217_, v___x_219_);
if (v___x_220_ == 0)
{
lean_dec_ref(v___x_214_);
v___y_173_ = v___y_216_;
v___y_174_ = v___x_218_;
goto v___jp_172_;
}
else
{
size_t v___x_221_; size_t v___x_222_; lean_object* v___x_223_; 
v___x_221_ = ((size_t)0ULL);
v___x_222_ = lean_usize_of_nat(v___x_219_);
v___x_223_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_getSize_spec__0(v___x_214_, v___x_221_, v___x_222_, v___x_218_);
lean_dec_ref(v___x_214_);
v___y_173_ = v___y_216_;
v___y_174_ = v___x_223_;
goto v___jp_172_;
}
}
v___jp_224_:
{
lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_226_ = lean_array_get_size(v___y_225_);
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = lean_nat_dec_eq(v___x_226_, v___x_227_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; 
v___x_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_229_, 0, v___y_225_);
v___y_216_ = v___x_229_;
goto v___jp_215_;
}
else
{
lean_object* v___x_230_; 
lean_dec_ref(v___y_225_);
v___x_230_ = lean_box(0);
v___y_216_ = v___x_230_;
goto v___jp_215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize___boxed(lean_object* v_dir_238_, lean_object* v_message_239_, lean_object* v_allowEOFBody_240_){
_start:
{
uint8_t v_dir_boxed_241_; uint8_t v_allowEOFBody_boxed_242_; lean_object* v_res_243_; 
v_dir_boxed_241_ = lean_unbox(v_dir_238_);
v_allowEOFBody_boxed_242_ = lean_unbox(v_allowEOFBody_240_);
v_res_243_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v_dir_boxed_241_, v_message_239_, v_allowEOFBody_boxed_242_);
lean_dec(v_message_239_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__4(lean_object* v_as_244_, size_t v_i_245_, size_t v_stop_246_, lean_object* v_b_247_){
_start:
{
lean_object* v___y_249_; uint8_t v___x_253_; 
v___x_253_ = lean_usize_dec_eq(v_i_245_, v_stop_246_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v_fst_255_; lean_object* v_snd_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_254_ = lean_array_uget_borrowed(v_as_244_, v_i_245_);
v_fst_255_ = lean_ctor_get(v___x_254_, 0);
v_snd_256_ = lean_ctor_get(v___x_254_, 1);
v___x_257_ = l_Std_Http_Header_Name_connection;
v___x_258_ = lean_string_dec_eq(v_fst_255_, v___x_257_);
if (v___x_258_ == 0)
{
v___y_249_ = v_b_247_;
goto v___jp_248_;
}
else
{
lean_object* v___x_259_; 
lean_inc(v_snd_256_);
v___x_259_ = lean_array_push(v_b_247_, v_snd_256_);
v___y_249_ = v___x_259_;
goto v___jp_248_;
}
}
else
{
return v_b_247_;
}
v___jp_248_:
{
size_t v___x_250_; size_t v___x_251_; 
v___x_250_ = ((size_t)1ULL);
v___x_251_ = lean_usize_add(v_i_245_, v___x_250_);
v_i_245_ = v___x_251_;
v_b_247_ = v___y_249_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__4___boxed(lean_object* v_as_260_, lean_object* v_i_261_, lean_object* v_stop_262_, lean_object* v_b_263_){
_start:
{
size_t v_i_boxed_264_; size_t v_stop_boxed_265_; lean_object* v_res_266_; 
v_i_boxed_264_ = lean_unbox_usize(v_i_261_);
lean_dec(v_i_261_);
v_stop_boxed_265_ = lean_unbox_usize(v_stop_262_);
lean_dec(v_stop_262_);
v_res_266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__4(v_as_260_, v_i_boxed_264_, v_stop_boxed_265_, v_b_263_);
lean_dec_ref(v_as_260_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__3(lean_object* v_as_267_, size_t v_i_268_, size_t v_stop_269_, lean_object* v_b_270_){
_start:
{
lean_object* v___y_272_; uint8_t v___x_276_; 
v___x_276_ = lean_usize_dec_eq(v_i_268_, v_stop_269_);
if (v___x_276_ == 0)
{
if (lean_obj_tag(v_b_270_) == 0)
{
v___y_272_ = v_b_270_;
goto v___jp_271_;
}
else
{
lean_object* v_val_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_val_277_ = lean_ctor_get(v_b_270_, 0);
lean_inc(v_val_277_);
lean_dec_ref_known(v_b_270_, 1);
v___x_278_ = lean_array_uget_borrowed(v_as_267_, v_i_268_);
lean_inc(v___x_278_);
v___x_279_ = l_Std_Http_Header_Connection_parse(v___x_278_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v___x_280_; 
lean_dec(v_val_277_);
v___x_280_ = lean_box(0);
v___y_272_ = v___x_280_;
goto v___jp_271_;
}
else
{
lean_object* v_val_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_289_; 
v_val_281_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_289_ == 0)
{
v___x_283_ = v___x_279_;
v_isShared_284_ = v_isSharedCheck_289_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_val_281_);
lean_dec(v___x_279_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_289_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_285_ = l_Array_append___redArg(v_val_277_, v_val_281_);
lean_dec(v_val_281_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v___x_285_);
v___x_287_ = v___x_283_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
v___y_272_ = v___x_287_;
goto v___jp_271_;
}
}
}
}
}
else
{
return v_b_270_;
}
v___jp_271_:
{
size_t v___x_273_; size_t v___x_274_; 
v___x_273_ = ((size_t)1ULL);
v___x_274_ = lean_usize_add(v_i_268_, v___x_273_);
v_i_268_ = v___x_274_;
v_b_270_ = v___y_272_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__3___boxed(lean_object* v_as_290_, lean_object* v_i_291_, lean_object* v_stop_292_, lean_object* v_b_293_){
_start:
{
size_t v_i_boxed_294_; size_t v_stop_boxed_295_; lean_object* v_res_296_; 
v_i_boxed_294_ = lean_unbox_usize(v_i_291_);
lean_dec(v_i_291_);
v_stop_boxed_295_ = lean_unbox_usize(v_stop_292_);
lean_dec(v_stop_292_);
v_res_296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__3(v_as_290_, v_i_boxed_294_, v_stop_boxed_295_, v_b_293_);
lean_dec_ref(v_as_290_);
return v_res_296_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(lean_object* v_as_298_, size_t v_i_299_, size_t v_stop_300_){
_start:
{
uint8_t v___x_301_; 
v___x_301_ = lean_usize_dec_eq(v_i_299_, v_stop_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_302_ = lean_array_uget_borrowed(v_as_298_, v_i_299_);
v___x_303_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2___closed__0));
v___x_304_ = lean_string_dec_eq(v___x_302_, v___x_303_);
if (v___x_304_ == 0)
{
size_t v___x_305_; size_t v___x_306_; 
v___x_305_ = ((size_t)1ULL);
v___x_306_ = lean_usize_add(v_i_299_, v___x_305_);
v_i_299_ = v___x_306_;
goto _start;
}
else
{
return v___x_304_;
}
}
else
{
uint8_t v___x_308_; 
v___x_308_ = 0;
return v___x_308_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2___boxed(lean_object* v_as_309_, lean_object* v_i_310_, lean_object* v_stop_311_){
_start:
{
size_t v_i_boxed_312_; size_t v_stop_boxed_313_; uint8_t v_res_314_; lean_object* v_r_315_; 
v_i_boxed_312_ = lean_unbox_usize(v_i_310_);
lean_dec(v_i_310_);
v_stop_boxed_313_ = lean_unbox_usize(v_stop_311_);
lean_dec(v_stop_311_);
v_res_314_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_as_309_, v_i_boxed_312_, v_stop_boxed_313_);
lean_dec_ref(v_as_309_);
v_r_315_ = lean_box(v_res_314_);
return v_r_315_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(lean_object* v_as_317_, size_t v_i_318_, size_t v_stop_319_){
_start:
{
uint8_t v___x_320_; 
v___x_320_ = lean_usize_dec_eq(v_i_318_, v_stop_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_321_ = lean_array_uget_borrowed(v_as_317_, v_i_318_);
v___x_322_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___closed__0));
v___x_323_ = lean_string_dec_eq(v___x_321_, v___x_322_);
if (v___x_323_ == 0)
{
size_t v___x_324_; size_t v___x_325_; 
v___x_324_ = ((size_t)1ULL);
v___x_325_ = lean_usize_add(v_i_318_, v___x_324_);
v_i_318_ = v___x_325_;
goto _start;
}
else
{
return v___x_323_;
}
}
else
{
uint8_t v___x_327_; 
v___x_327_ = 0;
return v___x_327_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1___boxed(lean_object* v_as_328_, lean_object* v_i_329_, lean_object* v_stop_330_){
_start:
{
size_t v_i_boxed_331_; size_t v_stop_boxed_332_; uint8_t v_res_333_; lean_object* v_r_334_; 
v_i_boxed_331_ = lean_unbox_usize(v_i_329_);
lean_dec(v_i_329_);
v_stop_boxed_332_ = lean_unbox_usize(v_stop_330_);
lean_dec(v_stop_330_);
v_res_333_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(v_as_328_, v_i_boxed_331_, v_stop_boxed_332_);
lean_dec_ref(v_as_328_);
v_r_334_ = lean_box(v_res_333_);
return v_r_334_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(lean_object* v_as_335_, size_t v_i_336_, size_t v_stop_337_){
_start:
{
uint8_t v___x_338_; 
v___x_338_ = lean_usize_dec_eq(v_i_336_, v_stop_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; lean_object* v_fst_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_339_ = lean_array_uget_borrowed(v_as_335_, v_i_336_);
v_fst_340_ = lean_ctor_get(v___x_339_, 0);
v___x_341_ = l_Std_Http_Header_Name_connection;
v___x_342_ = lean_string_dec_eq(v_fst_340_, v___x_341_);
if (v___x_342_ == 0)
{
size_t v___x_343_; size_t v___x_344_; 
v___x_343_ = ((size_t)1ULL);
v___x_344_ = lean_usize_add(v_i_336_, v___x_343_);
v_i_336_ = v___x_344_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0___boxed(lean_object* v_as_347_, lean_object* v_i_348_, lean_object* v_stop_349_){
_start:
{
size_t v_i_boxed_350_; size_t v_stop_boxed_351_; uint8_t v_res_352_; lean_object* v_r_353_; 
v_i_boxed_350_ = lean_unbox_usize(v_i_348_);
lean_dec(v_i_348_);
v_stop_boxed_351_ = lean_unbox_usize(v_stop_349_);
lean_dec(v_stop_349_);
v_res_352_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(v_as_347_, v_i_boxed_350_, v_stop_boxed_351_);
lean_dec_ref(v_as_347_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(uint8_t v_dir_356_, lean_object* v_message_357_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_362_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_356_, v_message_357_);
v___x_363_ = lean_unsigned_to_nat(0u);
v___x_364_ = lean_array_get_size(v___x_362_);
v___x_365_ = lean_nat_dec_lt(v___x_363_, v___x_364_);
if (v___x_365_ == 0)
{
lean_dec_ref(v___x_362_);
goto v___jp_358_;
}
else
{
if (v___x_365_ == 0)
{
lean_dec_ref(v___x_362_);
goto v___jp_358_;
}
else
{
size_t v___x_366_; size_t v___x_367_; uint8_t v___x_368_; lean_object* v___y_370_; lean_object* v___y_371_; 
v___x_366_ = ((size_t)0ULL);
v___x_367_ = lean_usize_of_nat(v___x_364_);
v___x_368_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__0(v___x_362_, v___x_366_, v___x_367_);
if (v___x_368_ == 0)
{
lean_dec_ref(v___x_362_);
goto v___jp_358_;
}
else
{
uint8_t v___x_378_; lean_object* v_val_380_; lean_object* v___y_386_; lean_object* v___x_396_; 
v___x_378_ = 0;
v___x_396_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__3));
if (v___x_365_ == 0)
{
lean_dec_ref(v___x_362_);
v___y_386_ = v___x_396_;
goto v___jp_385_;
}
else
{
lean_object* v___x_397_; 
v___x_397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__4(v___x_362_, v___x_366_, v___x_367_, v___x_396_);
lean_dec_ref(v___x_362_);
v___y_386_ = v___x_397_;
goto v___jp_385_;
}
v___jp_379_:
{
lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_381_ = lean_array_get_size(v_val_380_);
v___x_382_ = lean_nat_dec_lt(v___x_363_, v___x_381_);
if (v___x_382_ == 0)
{
v___y_370_ = v_val_380_;
v___y_371_ = v___x_381_;
goto v___jp_369_;
}
else
{
if (v___x_382_ == 0)
{
v___y_370_ = v_val_380_;
v___y_371_ = v___x_381_;
goto v___jp_369_;
}
else
{
size_t v___x_383_; uint8_t v___x_384_; 
v___x_383_ = lean_usize_of_nat(v___x_381_);
v___x_384_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__2(v_val_380_, v___x_366_, v___x_383_);
if (v___x_384_ == 0)
{
v___y_370_ = v_val_380_;
v___y_371_ = v___x_381_;
goto v___jp_369_;
}
else
{
lean_dec_ref(v_val_380_);
return v___x_378_;
}
}
}
}
v___jp_385_:
{
lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_387_ = lean_array_get_size(v___y_386_);
v___x_388_ = lean_nat_dec_eq(v___x_387_, v___x_363_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__3));
v___x_390_ = lean_nat_dec_lt(v___x_363_, v___x_387_);
if (v___x_390_ == 0)
{
lean_dec_ref(v___y_386_);
v_val_380_ = v___x_389_;
goto v___jp_379_;
}
else
{
lean_object* v___x_391_; size_t v___x_392_; lean_object* v___x_393_; 
v___x_391_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___closed__0));
v___x_392_ = lean_usize_of_nat(v___x_387_);
v___x_393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__3(v___y_386_, v___x_366_, v___x_392_, v___x_391_);
lean_dec_ref(v___y_386_);
if (lean_obj_tag(v___x_393_) == 0)
{
return v___x_378_;
}
else
{
lean_object* v_val_394_; 
v_val_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_val_394_);
lean_dec_ref_known(v___x_393_, 1);
v_val_380_ = v_val_394_;
goto v___jp_379_;
}
}
}
else
{
lean_object* v___x_395_; 
lean_dec_ref(v___y_386_);
v___x_395_ = ((lean_object*)(l_Std_Http_Protocol_H1_Message_Head_getSize___closed__3));
v_val_380_ = v___x_395_;
goto v___jp_379_;
}
}
}
v___jp_369_:
{
uint8_t v___x_372_; uint8_t v___x_373_; uint8_t v___x_374_; 
v___x_372_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_356_, v_message_357_);
v___x_373_ = 1;
v___x_374_ = l_Std_Http_instBEqVersion_beq(v___x_372_, v___x_373_);
if (v___x_374_ == 0)
{
uint8_t v___x_375_; 
v___x_375_ = lean_nat_dec_lt(v___x_363_, v___y_371_);
if (v___x_375_ == 0)
{
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
return v___x_375_;
}
else
{
if (v___x_375_ == 0)
{
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
return v___x_375_;
}
else
{
size_t v___x_376_; uint8_t v___x_377_; 
v___x_376_ = lean_usize_of_nat(v___y_371_);
lean_dec(v___y_371_);
v___x_377_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Protocol_H1_Message_Head_shouldKeepAlive_spec__1(v___y_370_, v___x_366_, v___x_376_);
lean_dec_ref(v___y_370_);
return v___x_377_;
}
}
}
else
{
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
return v___x_368_;
}
}
}
}
v___jp_358_:
{
uint8_t v___x_359_; uint8_t v___x_360_; uint8_t v___x_361_; 
v___x_359_ = l_Std_Http_Protocol_H1_Message_Head_version(v_dir_356_, v_message_357_);
v___x_360_ = 1;
v___x_361_ = l_Std_Http_instBEqVersion_beq(v___x_359_, v___x_360_);
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive___boxed(lean_object* v_dir_398_, lean_object* v_message_399_){
_start:
{
uint8_t v_dir_boxed_400_; uint8_t v_res_401_; lean_object* v_r_402_; 
v_dir_boxed_400_ = lean_unbox(v_dir_398_);
v_res_401_ = l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(v_dir_boxed_400_, v_message_399_);
lean_dec(v_message_399_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1___redArg(lean_object* v_x_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Std_Http_Request_instReprHead_repr___redArg(v_x_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1(lean_object* v_x_405_, lean_object* v_prec_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Std_Http_Request_instReprHead_repr___redArg(v_x_405_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__1___boxed(lean_object* v_x_408_, lean_object* v_prec_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Std_Http_Protocol_H1_instReprHead___aux__1(v_x_408_, v_prec_409_);
lean_dec(v_prec_409_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3___redArg(lean_object* v_x_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Std_Http_Response_instReprHead_repr___redArg(v_x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3(lean_object* v_x_413_, lean_object* v_prec_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Std_Http_Response_instReprHead_repr___redArg(v_x_413_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___aux__3___boxed(lean_object* v_x_416_, lean_object* v_prec_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Std_Http_Protocol_H1_instReprHead___aux__3(v_x_416_, v_prec_417_);
lean_dec(v_prec_417_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead(uint8_t v_dir_421_){
_start:
{
if (v_dir_421_ == 0)
{
lean_object* v___x_422_; 
v___x_422_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprHead___closed__0));
return v___x_422_;
}
else
{
lean_object* v___x_423_; 
v___x_423_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprHead___closed__1));
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprHead___boxed(lean_object* v_dir_424_){
_start:
{
uint8_t v_dir_boxed_425_; lean_object* v_res_426_; 
v_dir_boxed_425_ = lean_unbox(v_dir_424_);
v_res_426_ = l_Std_Http_Protocol_H1_instReprHead(v_dir_boxed_425_);
return v_res_426_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__0));
v___x_429_ = lean_string_to_utf8(v___x_428_);
return v___x_429_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1);
v___x_431_ = lean_byte_array_size(v___x_430_);
return v___x_431_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__4));
v___x_435_ = lean_string_to_utf8(v___x_434_);
return v___x_435_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5);
v___x_437_ = lean_byte_array_size(v___x_436_);
return v___x_437_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__7));
v___x_440_ = lean_string_to_utf8(v___x_439_);
return v___x_440_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8);
v___x_442_ = lean_byte_array_size(v___x_441_);
return v___x_442_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__10));
v___x_445_ = lean_string_to_utf8(v___x_444_);
return v___x_445_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11);
v___x_447_ = lean_byte_array_size(v___x_446_);
return v___x_447_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__13));
v___x_450_ = lean_string_to_utf8(v___x_449_);
return v___x_450_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14);
v___x_452_ = lean_byte_array_size(v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1(lean_object* v_out_500_, lean_object* v_req_501_){
_start:
{
uint8_t v_method_502_; uint8_t v_version_503_; lean_object* v_uri_504_; lean_object* v_headers_505_; lean_object* v___y_507_; lean_object* v___y_519_; lean_object* v___y_520_; uint8_t v___y_521_; lean_object* v___y_522_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; uint8_t v___y_557_; lean_object* v___y_558_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; uint8_t v___y_568_; uint8_t v___y_569_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; uint8_t v___y_587_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v_port_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; uint8_t v___y_604_; lean_object* v___y_605_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; uint8_t v___y_617_; lean_object* v___y_618_; lean_object* v___y_628_; 
v_method_502_ = lean_ctor_get_uint8(v_req_501_, sizeof(void*)*2);
v_version_503_ = lean_ctor_get_uint8(v_req_501_, sizeof(void*)*2 + 1);
v_uri_504_ = lean_ctor_get(v_req_501_, 0);
lean_inc(v_uri_504_);
v_headers_505_ = lean_ctor_get(v_req_501_, 1);
lean_inc_ref(v_headers_505_);
lean_dec_ref(v_req_501_);
switch(v_method_502_)
{
case 0:
{
lean_object* v___x_698_; 
v___x_698_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__23));
v___y_628_ = v___x_698_;
goto v___jp_627_;
}
case 1:
{
lean_object* v___x_699_; 
v___x_699_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__24));
v___y_628_ = v___x_699_;
goto v___jp_627_;
}
case 2:
{
lean_object* v___x_700_; 
v___x_700_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__25));
v___y_628_ = v___x_700_;
goto v___jp_627_;
}
case 3:
{
lean_object* v___x_701_; 
v___x_701_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__26));
v___y_628_ = v___x_701_;
goto v___jp_627_;
}
case 4:
{
lean_object* v___x_702_; 
v___x_702_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__27));
v___y_628_ = v___x_702_;
goto v___jp_627_;
}
case 5:
{
lean_object* v___x_703_; 
v___x_703_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__28));
v___y_628_ = v___x_703_;
goto v___jp_627_;
}
case 6:
{
lean_object* v___x_704_; 
v___x_704_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__29));
v___y_628_ = v___x_704_;
goto v___jp_627_;
}
case 7:
{
lean_object* v___x_705_; 
v___x_705_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__30));
v___y_628_ = v___x_705_;
goto v___jp_627_;
}
case 8:
{
lean_object* v___x_706_; 
v___x_706_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__31));
v___y_628_ = v___x_706_;
goto v___jp_627_;
}
case 9:
{
lean_object* v___x_707_; 
v___x_707_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__32));
v___y_628_ = v___x_707_;
goto v___jp_627_;
}
case 10:
{
lean_object* v___x_708_; 
v___x_708_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__33));
v___y_628_ = v___x_708_;
goto v___jp_627_;
}
case 11:
{
lean_object* v___x_709_; 
v___x_709_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__34));
v___y_628_ = v___x_709_;
goto v___jp_627_;
}
case 12:
{
lean_object* v___x_710_; 
v___x_710_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__35));
v___y_628_ = v___x_710_;
goto v___jp_627_;
}
case 13:
{
lean_object* v___x_711_; 
v___x_711_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__36));
v___y_628_ = v___x_711_;
goto v___jp_627_;
}
case 14:
{
lean_object* v___x_712_; 
v___x_712_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__37));
v___y_628_ = v___x_712_;
goto v___jp_627_;
}
case 15:
{
lean_object* v___x_713_; 
v___x_713_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__38));
v___y_628_ = v___x_713_;
goto v___jp_627_;
}
case 16:
{
lean_object* v___x_714_; 
v___x_714_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__39));
v___y_628_ = v___x_714_;
goto v___jp_627_;
}
case 17:
{
lean_object* v___x_715_; 
v___x_715_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__40));
v___y_628_ = v___x_715_;
goto v___jp_627_;
}
case 18:
{
lean_object* v___x_716_; 
v___x_716_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__41));
v___y_628_ = v___x_716_;
goto v___jp_627_;
}
case 19:
{
lean_object* v___x_717_; 
v___x_717_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__42));
v___y_628_ = v___x_717_;
goto v___jp_627_;
}
case 20:
{
lean_object* v___x_718_; 
v___x_718_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__43));
v___y_628_ = v___x_718_;
goto v___jp_627_;
}
case 21:
{
lean_object* v___x_719_; 
v___x_719_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__44));
v___y_628_ = v___x_719_;
goto v___jp_627_;
}
case 22:
{
lean_object* v___x_720_; 
v___x_720_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__45));
v___y_628_ = v___x_720_;
goto v___jp_627_;
}
case 23:
{
lean_object* v___x_721_; 
v___x_721_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__46));
v___y_628_ = v___x_721_;
goto v___jp_627_;
}
case 24:
{
lean_object* v___x_722_; 
v___x_722_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__47));
v___y_628_ = v___x_722_;
goto v___jp_627_;
}
case 25:
{
lean_object* v___x_723_; 
v___x_723_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__48));
v___y_628_ = v___x_723_;
goto v___jp_627_;
}
case 26:
{
lean_object* v___x_724_; 
v___x_724_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__49));
v___y_628_ = v___x_724_;
goto v___jp_627_;
}
case 27:
{
lean_object* v___x_725_; 
v___x_725_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__50));
v___y_628_ = v___x_725_;
goto v___jp_627_;
}
case 28:
{
lean_object* v___x_726_; 
v___x_726_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__51));
v___y_628_ = v___x_726_;
goto v___jp_627_;
}
case 29:
{
lean_object* v___x_727_; 
v___x_727_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__52));
v___y_628_ = v___x_727_;
goto v___jp_627_;
}
case 30:
{
lean_object* v___x_728_; 
v___x_728_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__53));
v___y_628_ = v___x_728_;
goto v___jp_627_;
}
case 31:
{
lean_object* v___x_729_; 
v___x_729_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__54));
v___y_628_ = v___x_729_;
goto v___jp_627_;
}
case 32:
{
lean_object* v___x_730_; 
v___x_730_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__55));
v___y_628_ = v___x_730_;
goto v___jp_627_;
}
case 33:
{
lean_object* v___x_731_; 
v___x_731_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__56));
v___y_628_ = v___x_731_;
goto v___jp_627_;
}
case 34:
{
lean_object* v___x_732_; 
v___x_732_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__57));
v___y_628_ = v___x_732_;
goto v___jp_627_;
}
case 35:
{
lean_object* v___x_733_; 
v___x_733_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__58));
v___y_628_ = v___x_733_;
goto v___jp_627_;
}
case 36:
{
lean_object* v___x_734_; 
v___x_734_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__59));
v___y_628_ = v___x_734_;
goto v___jp_627_;
}
case 37:
{
lean_object* v___x_735_; 
v___x_735_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__60));
v___y_628_ = v___x_735_;
goto v___jp_627_;
}
case 38:
{
lean_object* v___x_736_; 
v___x_736_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__61));
v___y_628_ = v___x_736_;
goto v___jp_627_;
}
default: 
{
lean_object* v___x_737_; 
v___x_737_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__62));
v___y_628_ = v___x_737_;
goto v___jp_627_;
}
}
v___jp_506_:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_508_ = lean_byte_array_size(v___y_507_);
v___x_509_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1);
v___x_510_ = lean_unsigned_to_nat(0u);
v___x_511_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_512_ = 0;
v___x_513_ = lean_byte_array_copy_slice(v___x_509_, v___x_510_, v___y_507_, v___x_508_, v___x_511_, v___x_512_);
v___x_514_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3));
v___x_515_ = l_Std_Http_Headers_fold___redArg(v_headers_505_, v___x_513_, v___x_514_);
lean_dec_ref(v_headers_505_);
v___x_516_ = lean_byte_array_size(v___x_515_);
v___x_517_ = lean_byte_array_copy_slice(v___x_509_, v___x_510_, v___x_515_, v___x_516_, v___x_511_, v___x_512_);
return v___x_517_;
}
v___jp_518_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; lean_object* v___x_528_; 
v___x_523_ = lean_byte_array_size(v___y_520_);
v___x_524_ = lean_string_to_utf8(v___y_522_);
v___x_525_ = lean_byte_array_size(v___x_524_);
v___x_526_ = lean_byte_array_copy_slice(v___x_524_, v___y_519_, v___y_520_, v___x_523_, v___x_525_, v___y_521_);
lean_dec_ref(v___x_524_);
v___x_527_ = 32;
v___x_528_ = lean_byte_array_push(v___x_526_, v___x_527_);
switch(v_version_503_)
{
case 0:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; lean_object* v___x_534_; 
v___x_529_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5);
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = lean_byte_array_size(v___x_528_);
v___x_532_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6);
v___x_533_ = 0;
v___x_534_ = lean_byte_array_copy_slice(v___x_529_, v___x_530_, v___x_528_, v___x_531_, v___x_532_, v___x_533_);
v___y_507_ = v___x_534_;
goto v___jp_506_;
}
case 1:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; lean_object* v___x_540_; 
v___x_535_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8);
v___x_536_ = lean_unsigned_to_nat(0u);
v___x_537_ = lean_byte_array_size(v___x_528_);
v___x_538_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9);
v___x_539_ = 0;
v___x_540_ = lean_byte_array_copy_slice(v___x_535_, v___x_536_, v___x_528_, v___x_537_, v___x_538_, v___x_539_);
v___y_507_ = v___x_540_;
goto v___jp_506_;
}
case 2:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; lean_object* v___x_546_; 
v___x_541_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11);
v___x_542_ = lean_unsigned_to_nat(0u);
v___x_543_ = lean_byte_array_size(v___x_528_);
v___x_544_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12);
v___x_545_ = 0;
v___x_546_ = lean_byte_array_copy_slice(v___x_541_, v___x_542_, v___x_528_, v___x_543_, v___x_544_, v___x_545_);
v___y_507_ = v___x_546_;
goto v___jp_506_;
}
default: 
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; lean_object* v___x_552_; 
v___x_547_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14);
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_549_ = lean_byte_array_size(v___x_528_);
v___x_550_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15);
v___x_551_ = 0;
v___x_552_ = lean_byte_array_copy_slice(v___x_547_, v___x_548_, v___x_528_, v___x_549_, v___x_550_, v___x_551_);
v___y_507_ = v___x_552_;
goto v___jp_506_;
}
}
}
v___jp_553_:
{
lean_object* v_queryStr_559_; lean_object* v___x_560_; 
v_queryStr_559_ = l_Std_Http_URI_Query_formatOption(v___y_556_);
v___x_560_ = lean_string_append(v___y_558_, v_queryStr_559_);
lean_dec_ref(v_queryStr_559_);
v___y_519_ = v___y_554_;
v___y_520_ = v___y_555_;
v___y_521_ = v___y_557_;
v___y_522_ = v___x_560_;
goto v___jp_518_;
}
v___jp_561_:
{
uint8_t v___x_570_; lean_object* v_pathPart_571_; lean_object* v_queryPart_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_570_ = 1;
v_pathPart_571_ = l_Std_Http_URI_Path_render(v___y_564_, v___y_569_, v___x_570_);
v_queryPart_572_ = l_Std_Http_URI_Query_formatOption(v___y_563_);
v___x_573_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16));
v___x_574_ = lean_string_append(v___y_566_, v___x_573_);
v___x_575_ = lean_string_append(v___x_574_, v___y_567_);
lean_dec_ref(v___y_567_);
v___x_576_ = lean_string_append(v___x_575_, v_pathPart_571_);
lean_dec_ref(v_pathPart_571_);
v___x_577_ = lean_string_append(v___x_576_, v_queryPart_572_);
lean_dec_ref(v_queryPart_572_);
v___y_519_ = v___y_562_;
v___y_520_ = v___y_565_;
v___y_521_ = v___y_568_;
v___y_522_ = v___x_577_;
goto v___jp_518_;
}
v___jp_578_:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
lean_dec(v___y_581_);
lean_inc_ref(v___y_586_);
v___x_590_ = lean_string_append(v___y_586_, v___y_588_);
lean_dec_ref(v___y_588_);
v___x_591_ = lean_string_append(v___x_590_, v___y_589_);
lean_dec_ref(v___y_589_);
lean_inc_ref(v___y_583_);
v___x_592_ = lean_string_append(v___y_583_, v___x_591_);
lean_dec_ref(v___x_591_);
v___x_593_ = 1;
v___y_562_ = v___y_579_;
v___y_563_ = v___y_580_;
v___y_564_ = v___y_582_;
v___y_565_ = v___y_584_;
v___y_566_ = v___y_585_;
v___y_567_ = v___x_592_;
v___y_568_ = v___y_587_;
v___y_569_ = v___x_593_;
goto v___jp_561_;
}
v___jp_594_:
{
switch(lean_obj_tag(v_port_600_))
{
case 0:
{
lean_object* v___x_606_; 
v___x_606_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__17));
v___y_579_ = v___y_597_;
v___y_580_ = v___y_596_;
v___y_581_ = v___y_595_;
v___y_582_ = v___y_598_;
v___y_583_ = v___y_599_;
v___y_584_ = v___y_602_;
v___y_585_ = v___y_601_;
v___y_586_ = v___y_603_;
v___y_587_ = v___y_604_;
v___y_588_ = v___y_605_;
v___y_589_ = v___x_606_;
goto v___jp_578_;
}
case 1:
{
lean_object* v___x_607_; 
v___x_607_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16));
v___y_579_ = v___y_597_;
v___y_580_ = v___y_596_;
v___y_581_ = v___y_595_;
v___y_582_ = v___y_598_;
v___y_583_ = v___y_599_;
v___y_584_ = v___y_602_;
v___y_585_ = v___y_601_;
v___y_586_ = v___y_603_;
v___y_587_ = v___y_604_;
v___y_588_ = v___y_605_;
v___y_589_ = v___x_607_;
goto v___jp_578_;
}
default: 
{
uint16_t v_port_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v_port_608_ = lean_ctor_get_uint16(v_port_600_, 0);
lean_dec_ref_known(v_port_600_, 0);
v___x_609_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16));
v___x_610_ = lean_uint16_to_nat(v_port_608_);
v___x_611_ = l_Nat_reprFast(v___x_610_);
v___x_612_ = lean_string_append(v___x_609_, v___x_611_);
lean_dec_ref(v___x_611_);
v___y_579_ = v___y_597_;
v___y_580_ = v___y_596_;
v___y_581_ = v___y_595_;
v___y_582_ = v___y_598_;
v___y_583_ = v___y_599_;
v___y_584_ = v___y_602_;
v___y_585_ = v___y_601_;
v___y_586_ = v___y_603_;
v___y_587_ = v___y_604_;
v___y_588_ = v___y_605_;
v___y_589_ = v___x_612_;
goto v___jp_578_;
}
}
}
v___jp_613_:
{
switch(lean_obj_tag(v___y_616_))
{
case 0:
{
v___y_519_ = v___y_614_;
v___y_520_ = v___y_615_;
v___y_521_ = v___y_617_;
v___y_522_ = v___y_618_;
goto v___jp_518_;
}
case 1:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16));
v___x_620_ = lean_string_append(v___y_618_, v___x_619_);
v___y_519_ = v___y_614_;
v___y_520_ = v___y_615_;
v___y_521_ = v___y_617_;
v___y_522_ = v___x_620_;
goto v___jp_518_;
}
default: 
{
uint16_t v_port_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v_port_621_ = lean_ctor_get_uint16(v___y_616_, 0);
lean_dec_ref_known(v___y_616_, 0);
v___x_622_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__16));
v___x_623_ = lean_uint16_to_nat(v_port_621_);
v___x_624_ = l_Nat_reprFast(v___x_623_);
v___x_625_ = lean_string_append(v___x_622_, v___x_624_);
lean_dec_ref(v___x_624_);
v___x_626_ = lean_string_append(v___y_618_, v___x_625_);
lean_dec_ref(v___x_625_);
v___y_519_ = v___y_614_;
v___y_520_ = v___y_615_;
v___y_521_ = v___y_617_;
v___y_522_ = v___x_626_;
goto v___jp_518_;
}
}
}
v___jp_627_:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; lean_object* v___x_636_; 
v___x_629_ = lean_byte_array_size(v_out_500_);
lean_inc_ref(v___y_628_);
v___x_630_ = lean_string_to_utf8(v___y_628_);
v___x_631_ = lean_unsigned_to_nat(0u);
v___x_632_ = lean_byte_array_size(v___x_630_);
v___x_633_ = 0;
v___x_634_ = lean_byte_array_copy_slice(v___x_630_, v___x_631_, v_out_500_, v___x_629_, v___x_632_, v___x_633_);
lean_dec_ref(v___x_630_);
v___x_635_ = 32;
v___x_636_ = lean_byte_array_push(v___x_634_, v___x_635_);
switch(lean_obj_tag(v_uri_504_))
{
case 0:
{
lean_object* v_path_637_; lean_object* v_query_638_; uint8_t v___x_639_; lean_object* v_pathStr_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v_path_637_ = lean_ctor_get(v_uri_504_, 0);
lean_inc_ref(v_path_637_);
v_query_638_ = lean_ctor_get(v_uri_504_, 1);
lean_inc(v_query_638_);
lean_dec_ref_known(v_uri_504_, 2);
v___x_639_ = 1;
v_pathStr_640_ = l_Std_Http_URI_Path_render(v_path_637_, v___x_639_, v___x_639_);
v___x_641_ = lean_string_utf8_byte_size(v_pathStr_640_);
v___x_642_ = lean_nat_dec_eq(v___x_641_, v___x_631_);
if (v___x_642_ == 0)
{
v___y_554_ = v___x_631_;
v___y_555_ = v___x_636_;
v___y_556_ = v_query_638_;
v___y_557_ = v___x_633_;
v___y_558_ = v_pathStr_640_;
goto v___jp_553_;
}
else
{
lean_object* v___x_643_; 
lean_dec_ref(v_pathStr_640_);
v___x_643_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__18));
v___y_554_ = v___x_631_;
v___y_555_ = v___x_636_;
v___y_556_ = v_query_638_;
v___y_557_ = v___x_633_;
v___y_558_ = v___x_643_;
goto v___jp_553_;
}
}
case 1:
{
lean_object* v_uri_644_; lean_object* v_authority_645_; 
v_uri_644_ = lean_ctor_get(v_uri_504_, 0);
lean_inc_ref(v_uri_644_);
lean_dec_ref_known(v_uri_504_, 1);
v_authority_645_ = lean_ctor_get(v_uri_644_, 1);
lean_inc(v_authority_645_);
if (lean_obj_tag(v_authority_645_) == 0)
{
lean_object* v_scheme_646_; lean_object* v_path_647_; lean_object* v_query_648_; lean_object* v___x_649_; 
v_scheme_646_ = lean_ctor_get(v_uri_644_, 0);
lean_inc_ref(v_scheme_646_);
v_path_647_ = lean_ctor_get(v_uri_644_, 2);
lean_inc_ref(v_path_647_);
v_query_648_ = lean_ctor_get(v_uri_644_, 3);
lean_inc(v_query_648_);
lean_dec_ref(v_uri_644_);
v___x_649_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__17));
v___y_562_ = v___x_631_;
v___y_563_ = v_query_648_;
v___y_564_ = v_path_647_;
v___y_565_ = v___x_636_;
v___y_566_ = v_scheme_646_;
v___y_567_ = v___x_649_;
v___y_568_ = v___x_633_;
v___y_569_ = v___x_633_;
goto v___jp_561_;
}
else
{
lean_object* v_val_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_682_; 
v_val_650_ = lean_ctor_get(v_authority_645_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v_authority_645_);
if (v_isSharedCheck_682_ == 0)
{
v___x_652_ = v_authority_645_;
v_isShared_653_ = v_isSharedCheck_682_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_val_650_);
lean_dec(v_authority_645_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_682_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v_scheme_654_; lean_object* v_path_655_; lean_object* v_query_656_; lean_object* v_host_657_; lean_object* v_port_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_680_; 
v_scheme_654_ = lean_ctor_get(v_uri_644_, 0);
lean_inc_ref(v_scheme_654_);
v_path_655_ = lean_ctor_get(v_uri_644_, 2);
lean_inc_ref(v_path_655_);
v_query_656_ = lean_ctor_get(v_uri_644_, 3);
lean_inc(v_query_656_);
lean_dec_ref(v_uri_644_);
v_host_657_ = lean_ctor_get(v_val_650_, 1);
v_port_658_ = lean_ctor_get(v_val_650_, 2);
v_isSharedCheck_680_ = !lean_is_exclusive(v_val_650_);
if (v_isSharedCheck_680_ == 0)
{
lean_object* v_unused_681_; 
v_unused_681_ = lean_ctor_get(v_val_650_, 0);
lean_dec(v_unused_681_);
v___x_660_ = v_val_650_;
v_isShared_661_ = v_isSharedCheck_680_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_port_658_);
lean_inc(v_host_657_);
lean_dec(v_val_650_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_680_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_662_ = lean_box(0);
lean_inc(v_port_658_);
lean_inc_ref(v_host_657_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_662_);
v___x_664_ = v___x_660_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_host_657_);
lean_ctor_set(v_reuseFailAlloc_679_, 2, v_port_658_);
v___x_664_ = v_reuseFailAlloc_679_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_666_; 
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v___x_664_);
v___x_666_ = v___x_652_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_678_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__19));
v___x_668_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__17));
switch(lean_obj_tag(v_host_657_))
{
case 0:
{
lean_object* v_name_669_; 
v_name_669_ = lean_ctor_get(v_host_657_, 0);
lean_inc_ref(v_name_669_);
lean_dec_ref_known(v_host_657_, 1);
v___y_595_ = v___x_666_;
v___y_596_ = v_query_656_;
v___y_597_ = v___x_631_;
v___y_598_ = v_path_655_;
v___y_599_ = v___x_667_;
v_port_600_ = v_port_658_;
v___y_601_ = v_scheme_654_;
v___y_602_ = v___x_636_;
v___y_603_ = v___x_668_;
v___y_604_ = v___x_633_;
v___y_605_ = v_name_669_;
goto v___jp_594_;
}
case 1:
{
lean_object* v_ipv4_670_; lean_object* v___x_671_; 
v_ipv4_670_ = lean_ctor_get(v_host_657_, 0);
lean_inc_ref(v_ipv4_670_);
lean_dec_ref_known(v_host_657_, 1);
v___x_671_ = lean_uv_ntop_v4(v_ipv4_670_);
lean_dec_ref(v_ipv4_670_);
v___y_595_ = v___x_666_;
v___y_596_ = v_query_656_;
v___y_597_ = v___x_631_;
v___y_598_ = v_path_655_;
v___y_599_ = v___x_667_;
v_port_600_ = v_port_658_;
v___y_601_ = v_scheme_654_;
v___y_602_ = v___x_636_;
v___y_603_ = v___x_668_;
v___y_604_ = v___x_633_;
v___y_605_ = v___x_671_;
goto v___jp_594_;
}
default: 
{
lean_object* v_ipv6_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_ipv6_672_ = lean_ctor_get(v_host_657_, 0);
lean_inc_ref(v_ipv6_672_);
lean_dec_ref_known(v_host_657_, 1);
v___x_673_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__20));
v___x_674_ = lean_uv_ntop_v6(v_ipv6_672_);
lean_dec_ref(v_ipv6_672_);
v___x_675_ = lean_string_append(v___x_673_, v___x_674_);
lean_dec_ref(v___x_674_);
v___x_676_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__21));
v___x_677_ = lean_string_append(v___x_675_, v___x_676_);
v___y_595_ = v___x_666_;
v___y_596_ = v_query_656_;
v___y_597_ = v___x_631_;
v___y_598_ = v_path_655_;
v___y_599_ = v___x_667_;
v_port_600_ = v_port_658_;
v___y_601_ = v_scheme_654_;
v___y_602_ = v___x_636_;
v___y_603_ = v___x_668_;
v___y_604_ = v___x_633_;
v___y_605_ = v___x_677_;
goto v___jp_594_;
}
}
}
}
}
}
}
}
case 2:
{
lean_object* v_authority_683_; lean_object* v_host_684_; 
v_authority_683_ = lean_ctor_get(v_uri_504_, 0);
lean_inc_ref(v_authority_683_);
lean_dec_ref_known(v_uri_504_, 1);
v_host_684_ = lean_ctor_get(v_authority_683_, 1);
lean_inc_ref(v_host_684_);
switch(lean_obj_tag(v_host_684_))
{
case 0:
{
lean_object* v_port_685_; lean_object* v_name_686_; 
v_port_685_ = lean_ctor_get(v_authority_683_, 2);
lean_inc(v_port_685_);
lean_dec_ref(v_authority_683_);
v_name_686_ = lean_ctor_get(v_host_684_, 0);
lean_inc_ref(v_name_686_);
lean_dec_ref_known(v_host_684_, 1);
v___y_614_ = v___x_631_;
v___y_615_ = v___x_636_;
v___y_616_ = v_port_685_;
v___y_617_ = v___x_633_;
v___y_618_ = v_name_686_;
goto v___jp_613_;
}
case 1:
{
lean_object* v_port_687_; lean_object* v_ipv4_688_; lean_object* v___x_689_; 
v_port_687_ = lean_ctor_get(v_authority_683_, 2);
lean_inc(v_port_687_);
lean_dec_ref(v_authority_683_);
v_ipv4_688_ = lean_ctor_get(v_host_684_, 0);
lean_inc_ref(v_ipv4_688_);
lean_dec_ref_known(v_host_684_, 1);
v___x_689_ = lean_uv_ntop_v4(v_ipv4_688_);
lean_dec_ref(v_ipv4_688_);
v___y_614_ = v___x_631_;
v___y_615_ = v___x_636_;
v___y_616_ = v_port_687_;
v___y_617_ = v___x_633_;
v___y_618_ = v___x_689_;
goto v___jp_613_;
}
default: 
{
lean_object* v_port_690_; lean_object* v_ipv6_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v_port_690_ = lean_ctor_get(v_authority_683_, 2);
lean_inc(v_port_690_);
lean_dec_ref(v_authority_683_);
v_ipv6_691_ = lean_ctor_get(v_host_684_, 0);
lean_inc_ref(v_ipv6_691_);
lean_dec_ref_known(v_host_684_, 1);
v___x_692_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__20));
v___x_693_ = lean_uv_ntop_v6(v_ipv6_691_);
lean_dec_ref(v_ipv6_691_);
v___x_694_ = lean_string_append(v___x_692_, v___x_693_);
lean_dec_ref(v___x_693_);
v___x_695_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__21));
v___x_696_ = lean_string_append(v___x_694_, v___x_695_);
v___y_614_ = v___x_631_;
v___y_615_ = v___x_636_;
v___y_616_ = v_port_690_;
v___y_617_ = v___x_633_;
v___y_618_ = v___x_696_;
goto v___jp_613_;
}
}
}
default: 
{
lean_object* v___x_697_; 
v___x_697_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__22));
v___y_519_ = v___x_631_;
v___y_520_ = v___x_636_;
v___y_521_ = v___x_633_;
v___y_522_ = v___x_697_;
goto v___jp_518_;
}
}
}
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__1(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__0));
v___x_740_ = lean_string_to_utf8(v___x_739_);
return v___x_740_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__2(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__1, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__1_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__1);
v___x_742_ = lean_byte_array_size(v___x_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(lean_object* v_out_743_, lean_object* v_r_744_){
_start:
{
lean_object* v_status_745_; uint8_t v_version_746_; lean_object* v_headers_747_; lean_object* v___y_749_; lean_object* v___y_761_; 
v_status_745_ = lean_ctor_get(v_r_744_, 0);
v_version_746_ = lean_ctor_get_uint8(v_r_744_, sizeof(void*)*2);
v_headers_747_ = lean_ctor_get(v_r_744_, 1);
switch(v_version_746_)
{
case 0:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; uint8_t v___x_785_; lean_object* v___x_786_; 
v___x_781_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__5);
v___x_782_ = lean_unsigned_to_nat(0u);
v___x_783_ = lean_byte_array_size(v_out_743_);
v___x_784_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__6);
v___x_785_ = 0;
v___x_786_ = lean_byte_array_copy_slice(v___x_781_, v___x_782_, v_out_743_, v___x_783_, v___x_784_, v___x_785_);
v___y_761_ = v___x_786_;
goto v___jp_760_;
}
case 1:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; lean_object* v___x_792_; 
v___x_787_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__8);
v___x_788_ = lean_unsigned_to_nat(0u);
v___x_789_ = lean_byte_array_size(v_out_743_);
v___x_790_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__9);
v___x_791_ = 0;
v___x_792_ = lean_byte_array_copy_slice(v___x_787_, v___x_788_, v_out_743_, v___x_789_, v___x_790_, v___x_791_);
v___y_761_ = v___x_792_;
goto v___jp_760_;
}
case 2:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; lean_object* v___x_798_; 
v___x_793_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__11);
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = lean_byte_array_size(v_out_743_);
v___x_796_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__12);
v___x_797_ = 0;
v___x_798_ = lean_byte_array_copy_slice(v___x_793_, v___x_794_, v_out_743_, v___x_795_, v___x_796_, v___x_797_);
v___y_761_ = v___x_798_;
goto v___jp_760_;
}
default: 
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; lean_object* v___x_804_; 
v___x_799_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__14);
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = lean_byte_array_size(v_out_743_);
v___x_802_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__15);
v___x_803_ = 0;
v___x_804_ = lean_byte_array_copy_slice(v___x_799_, v___x_800_, v_out_743_, v___x_801_, v___x_802_, v___x_803_);
v___y_761_ = v___x_804_;
goto v___jp_760_;
}
}
v___jp_748_:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_750_ = lean_byte_array_size(v___y_749_);
v___x_751_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__1);
v___x_752_ = lean_unsigned_to_nat(0u);
v___x_753_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__2);
v___x_754_ = 0;
v___x_755_ = lean_byte_array_copy_slice(v___x_751_, v___x_752_, v___y_749_, v___x_750_, v___x_753_, v___x_754_);
v___x_756_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___aux__1___closed__3));
v___x_757_ = l_Std_Http_Headers_fold___redArg(v_headers_747_, v___x_755_, v___x_756_);
v___x_758_ = lean_byte_array_size(v___x_757_);
v___x_759_ = lean_byte_array_copy_slice(v___x_751_, v___x_752_, v___x_757_, v___x_758_, v___x_753_, v___x_754_);
return v___x_759_;
}
v___jp_760_:
{
uint8_t v___x_762_; lean_object* v___x_763_; 
v___x_762_ = 32;
v___x_763_ = lean_byte_array_push(v___y_761_, v___x_762_);
if (lean_obj_tag(v_status_745_) == 4)
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; lean_object* v___x_769_; 
v___x_764_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__1, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__1_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__1);
v___x_765_ = lean_unsigned_to_nat(0u);
v___x_766_ = lean_byte_array_size(v___x_763_);
v___x_767_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__2, &l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__2_once, _init_l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___closed__2);
v___x_768_ = 0;
v___x_769_ = lean_byte_array_copy_slice(v___x_764_, v___x_765_, v___x_763_, v___x_766_, v___x_767_, v___x_768_);
v___y_749_ = v___x_769_;
goto v___jp_748_;
}
else
{
uint16_t v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; lean_object* v___x_780_; 
v___x_770_ = l_Std_Http_Status_toCode(v_status_745_);
v___x_771_ = lean_uint16_to_nat(v___x_770_);
v___x_772_ = l_Std_Http_Internal_appendNat(v___x_763_, v___x_771_);
v___x_773_ = lean_byte_array_push(v___x_772_, v___x_762_);
v___x_774_ = l_Std_Http_Status_reasonPhrase(v_status_745_);
v___x_775_ = lean_string_to_utf8(v___x_774_);
v___x_776_ = lean_unsigned_to_nat(0u);
v___x_777_ = lean_byte_array_size(v___x_773_);
v___x_778_ = lean_byte_array_size(v___x_775_);
v___x_779_ = 0;
v___x_780_ = lean_byte_array_copy_slice(v___x_775_, v___x_776_, v___x_773_, v___x_777_, v___x_778_, v___x_779_);
lean_dec_ref(v___x_775_);
v___y_749_ = v___x_780_;
goto v___jp_748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3___boxed(lean_object* v_out_805_, lean_object* v_r_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Std_Http_Protocol_H1_instEncodeV11Head___aux__3(v_out_805_, v_r_806_);
lean_dec_ref(v_r_806_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head(uint8_t v_dir_810_){
_start:
{
if (v_dir_810_ == 0)
{
lean_object* v___x_811_; 
v___x_811_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___closed__0));
return v___x_811_;
}
else
{
lean_object* v___x_812_; 
v___x_812_ = ((lean_object*)(l_Std_Http_Protocol_H1_instEncodeV11Head___closed__1));
return v___x_812_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head___boxed(lean_object* v_dir_813_){
_start:
{
uint8_t v_dir_boxed_814_; lean_object* v_res_815_; 
v_dir_boxed_814_ = lean_unbox(v_dir_813_);
v_res_815_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v_dir_boxed_814_);
return v_res_815_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0(void){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; uint8_t v___x_818_; uint8_t v___x_819_; lean_object* v___x_820_; 
v___x_816_ = l_Std_Http_Headers_empty;
v___x_817_ = lean_box(3);
v___x_818_ = 1;
v___x_819_ = 8;
v___x_820_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_820_, 0, v___x_817_);
lean_ctor_set(v___x_820_, 1, v___x_816_);
lean_ctor_set_uint8(v___x_820_, sizeof(void*)*2, v___x_819_);
lean_ctor_set_uint8(v___x_820_, sizeof(void*)*2 + 1, v___x_818_);
return v___x_820_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1(void){
_start:
{
lean_object* v___x_821_; uint8_t v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_821_ = l_Std_Http_Headers_empty;
v___x_822_ = 1;
v___x_823_ = lean_box(4);
v___x_824_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_824_, 0, v___x_823_);
lean_ctor_set(v___x_824_, 1, v___x_821_);
lean_ctor_set_uint8(v___x_824_, sizeof(void*)*2, v___x_822_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead(uint8_t v_dir_825_){
_start:
{
if (v_dir_825_ == 0)
{
lean_object* v___x_826_; 
v___x_826_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0, &l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0_once, _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__0);
return v___x_826_;
}
else
{
lean_object* v___x_827_; 
v___x_827_ = lean_obj_once(&l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1, &l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1_once, _init_l_Std_Http_Protocol_H1_instEmptyCollectionHead___closed__1);
return v___x_827_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead___boxed(lean_object* v_dir_828_){
_start:
{
uint8_t v_dir_boxed_829_; lean_object* v_res_830_; 
v_dir_boxed_829_ = lean_unbox(v_dir_828_);
v_res_830_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v_dir_boxed_829_);
return v_res_830_;
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
