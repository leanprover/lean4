// Lean compiler output
// Module: Std.Http.Data.URI.Parser
// Imports: import Init.While public import Init.Data.String.Basic public import Std.Internal.Parsec public import Std.Internal.Parsec.ByteArray public import Std.Http.Data.URI.Basic public import Std.Http.Data.URI.Config import Init.Data.String.Search
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ByteArray_toByteSlice(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_ByteSlice_toByteArray(lean_object*);
lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(lean_object*);
lean_object* l_ByteSlice_size(lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Http_URI_isValidDomainLabel(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* lean_uv_pton_v4(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_uv_pton_v6(lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object*, lean_object*);
extern lean_object* l_Std_Http_URI_Query_empty;
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f(lean_object*);
lean_object* l_Std_Http_URI_Query_insertEncoded(lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(lean_object*);
lean_object* l_Std_Http_URI_EncodedFragment_decode(lean_object*);
uint8_t l_Std_Http_Internal_instDecidableIsLowerCase(lean_object*);
lean_object* lean_string_data(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_List_head_x3f___redArg(lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_tryOpt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_tryOpt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_peekIs(lean_object*, lean_object*);
static const lean_string_object l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2___closed__0 = (const lean_object*)&l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "condition not satisfied"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__1 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__1_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "invalid scheme"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__2 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__2_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__2_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__3 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__3_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Init.Data.String.Basic"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__4 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__4_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "String.fromUTF8!"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid UTF-8 string"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6_value;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7;
static const lean_closure_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__8 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__8_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "scheme length limit is 0 (no scheme allowed)"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__9 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__9_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__9_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__0_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "port number too large: "};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__1 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__1_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "invalid port number: "};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__2 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1(uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "invalid percent encoding in user info"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1_value;
static const lean_closure_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__2 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___boxed(lean_object*);
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "invalid IPv6 address: "};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__0_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '91'"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2_value;
static const lean_closure_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '93'"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected at least one char"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__0_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "invalid IPv4 address: "};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__1 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "invalid domain name: "};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "invalid host"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2_value;
static const lean_closure_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "invalid port number"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__1 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__1_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '58'"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '64'"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0___boxed(lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "too many path segments (limit: "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "path too long (limit: "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " bytes)"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "invalid percent encoding in path segment"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4_value)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_URI_Parser_parsePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "require '/' in path"};
static const lean_object* l_Std_Http_URI_Parser_parsePath___closed__0 = (const lean_object*)&l_Std_Http_URI_Parser_parsePath___closed__0_value;
static const lean_ctor_object l_Std_Http_URI_Parser_parsePath___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_URI_Parser_parsePath___closed__0_value)}};
static const lean_object* l_Std_Http_URI_Parser_parsePath___closed__1 = (const lean_object*)&l_Std_Http_URI_Parser_parsePath___closed__1_value;
static const lean_string_object l_Std_Http_URI_Parser_parsePath___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "need a path"};
static const lean_object* l_Std_Http_URI_Parser_parsePath___closed__2 = (const lean_object*)&l_Std_Http_URI_Parser_parsePath___closed__2_value;
static const lean_ctor_object l_Std_Http_URI_Parser_parsePath___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_URI_Parser_parsePath___closed__2_value)}};
static const lean_object* l_Std_Http_URI_Parser_parsePath___closed__3 = (const lean_object*)&l_Std_Http_URI_Parser_parsePath___closed__3_value;
static const lean_array_object l_Std_Http_URI_Parser_parsePath___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_URI_Parser_parsePath___closed__4 = (const lean_object*)&l_Std_Http_URI_Parser_parsePath___closed__4_value;
static const lean_ctor_object l_Std_Http_URI_Parser_parsePath___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_URI_Parser_parsePath___closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Http_URI_Parser_parsePath___closed__5 = (const lean_object*)&l_Std_Http_URI_Parser_parsePath___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid query string"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__1 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__1_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__1_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "too many query parameters (limit: "};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "invalid percent encoding in fragment"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "//"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0_value;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_URI_Parser_parseURI___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '35'"};
static const lean_object* l_Std_Http_URI_Parser_parseURI___closed__0 = (const lean_object*)&l_Std_Http_URI_Parser_parseURI___closed__0_value;
static const lean_ctor_object l_Std_Http_URI_Parser_parseURI___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_URI_Parser_parseURI___closed__0_value)}};
static const lean_object* l_Std_Http_URI_Parser_parseURI___closed__1 = (const lean_object*)&l_Std_Http_URI_Parser_parseURI___closed__1_value;
static const lean_string_object l_Std_Http_URI_Parser_parseURI___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "invalid fragment parse encoding"};
static const lean_object* l_Std_Http_URI_Parser_parseURI___closed__2 = (const lean_object*)&l_Std_Http_URI_Parser_parseURI___closed__2_value;
static const lean_ctor_object l_Std_Http_URI_Parser_parseURI___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_URI_Parser_parseURI___closed__2_value)}};
static const lean_object* l_Std_Http_URI_Parser_parseURI___closed__3 = (const lean_object*)&l_Std_Http_URI_Parser_parseURI___closed__3_value;
static const lean_string_object l_Std_Http_URI_Parser_parseURI___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '63'"};
static const lean_object* l_Std_Http_URI_Parser_parseURI___closed__4 = (const lean_object*)&l_Std_Http_URI_Parser_parseURI___closed__4_value;
static const lean_ctor_object l_Std_Http_URI_Parser_parseURI___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_URI_Parser_parseURI___closed__4_value)}};
static const lean_object* l_Std_Http_URI_Parser_parseURI___closed__5 = (const lean_object*)&l_Std_Http_URI_Parser_parseURI___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURI(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '42'"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(lean_object*);
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "not origin"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "not http absolute uri with path"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "http"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "https"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "not http absolute uri"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__4 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__4_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__4_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "invalid fragment encoding"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___closed__1 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_uri(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withAuthority(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_relative(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURIReference(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_URI_Parser_parseHostHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "invalid host header"};
static const lean_object* l_Std_Http_URI_Parser_parseHostHeader___closed__0 = (const lean_object*)&l_Std_Http_URI_Parser_parseHostHeader___closed__0_value;
static const lean_ctor_object l_Std_Http_URI_Parser_parseHostHeader___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_URI_Parser_parseHostHeader___closed__0_value)}};
static const lean_object* l_Std_Http_URI_Parser_parseHostHeader___closed__1 = (const lean_object*)&l_Std_Http_URI_Parser_parseHostHeader___closed__1_value;
static const lean_string_object l_Std_Http_URI_Parser_parseHostHeader___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "invalid host header port"};
static const lean_object* l_Std_Http_URI_Parser_parseHostHeader___closed__2 = (const lean_object*)&l_Std_Http_URI_Parser_parseHostHeader___closed__2_value;
static const lean_ctor_object l_Std_Http_URI_Parser_parseHostHeader___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_URI_Parser_parseHostHeader___closed__2_value)}};
static const lean_object* l_Std_Http_URI_Parser_parseHostHeader___closed__3 = (const lean_object*)&l_Std_Http_URI_Parser_parseHostHeader___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_tryOpt___redArg(lean_object* v_p_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_3_; 
lean_inc_ref(v_a_2_);
v___x_3_ = lean_apply_1(v_p_1_, v_a_2_);
if (lean_obj_tag(v___x_3_) == 0)
{
lean_object* v_pos_4_; lean_object* v_res_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_13_; 
lean_dec_ref(v_a_2_);
v_pos_4_ = lean_ctor_get(v___x_3_, 0);
v_res_5_ = lean_ctor_get(v___x_3_, 1);
v_isSharedCheck_13_ = !lean_is_exclusive(v___x_3_);
if (v_isSharedCheck_13_ == 0)
{
v___x_7_ = v___x_3_;
v_isShared_8_ = v_isSharedCheck_13_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_res_5_);
lean_inc(v_pos_4_);
lean_dec(v___x_3_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_13_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_9_; lean_object* v___x_11_; 
v___x_9_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_9_, 0, v_res_5_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v___x_9_);
v___x_11_ = v___x_7_;
goto v_reusejp_10_;
}
else
{
lean_object* v_reuseFailAlloc_12_; 
v_reuseFailAlloc_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_12_, 0, v_pos_4_);
lean_ctor_set(v_reuseFailAlloc_12_, 1, v___x_9_);
v___x_11_ = v_reuseFailAlloc_12_;
goto v_reusejp_10_;
}
v_reusejp_10_:
{
return v___x_11_;
}
}
}
else
{
lean_object* v_err_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_27_; 
v_err_14_ = lean_ctor_get(v___x_3_, 1);
v_isSharedCheck_27_ = !lean_is_exclusive(v___x_3_);
if (v_isSharedCheck_27_ == 0)
{
lean_object* v_unused_28_; 
v_unused_28_ = lean_ctor_get(v___x_3_, 0);
lean_dec(v_unused_28_);
v___x_16_ = v___x_3_;
v_isShared_17_ = v_isSharedCheck_27_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_err_14_);
lean_dec(v___x_3_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_27_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v_idx_18_; uint8_t v___x_19_; 
v_idx_18_ = lean_ctor_get(v_a_2_, 1);
v___x_19_ = lean_nat_dec_eq(v_idx_18_, v_idx_18_);
if (v___x_19_ == 0)
{
lean_object* v___x_21_; 
if (v_isShared_17_ == 0)
{
lean_ctor_set(v___x_16_, 0, v_a_2_);
v___x_21_ = v___x_16_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_a_2_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_err_14_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
return v___x_21_;
}
}
else
{
lean_object* v___x_23_; lean_object* v___x_25_; 
lean_dec(v_err_14_);
v___x_23_ = lean_box(0);
if (v_isShared_17_ == 0)
{
lean_ctor_set_tag(v___x_16_, 0);
lean_ctor_set(v___x_16_, 1, v___x_23_);
lean_ctor_set(v___x_16_, 0, v_a_2_);
v___x_25_ = v___x_16_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_a_2_);
lean_ctor_set(v_reuseFailAlloc_26_, 1, v___x_23_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_tryOpt(lean_object* v_00_u03b1_29_, lean_object* v_p_30_, lean_object* v_a_31_){
_start:
{
lean_object* v___x_32_; 
lean_inc_ref(v_a_31_);
v___x_32_ = lean_apply_1(v_p_30_, v_a_31_);
if (lean_obj_tag(v___x_32_) == 0)
{
lean_object* v_pos_33_; lean_object* v_res_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_42_; 
lean_dec_ref(v_a_31_);
v_pos_33_ = lean_ctor_get(v___x_32_, 0);
v_res_34_ = lean_ctor_get(v___x_32_, 1);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_42_ == 0)
{
v___x_36_ = v___x_32_;
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_res_34_);
lean_inc(v_pos_33_);
lean_dec(v___x_32_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_40_; 
v___x_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_38_, 0, v_res_34_);
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 1, v___x_38_);
v___x_40_ = v___x_36_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v_pos_33_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
else
{
lean_object* v_err_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_56_; 
v_err_43_ = lean_ctor_get(v___x_32_, 1);
v_isSharedCheck_56_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_56_ == 0)
{
lean_object* v_unused_57_; 
v_unused_57_ = lean_ctor_get(v___x_32_, 0);
lean_dec(v_unused_57_);
v___x_45_ = v___x_32_;
v_isShared_46_ = v_isSharedCheck_56_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_err_43_);
lean_dec(v___x_32_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_56_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v_idx_47_; uint8_t v___x_48_; 
v_idx_47_ = lean_ctor_get(v_a_31_, 1);
v___x_48_ = lean_nat_dec_eq(v_idx_47_, v_idx_47_);
if (v___x_48_ == 0)
{
lean_object* v___x_50_; 
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 0, v_a_31_);
v___x_50_ = v___x_45_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_a_31_);
lean_ctor_set(v_reuseFailAlloc_51_, 1, v_err_43_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
else
{
lean_object* v___x_52_; lean_object* v___x_54_; 
lean_dec(v_err_43_);
v___x_52_ = lean_box(0);
if (v_isShared_46_ == 0)
{
lean_ctor_set_tag(v___x_45_, 0);
lean_ctor_set(v___x_45_, 1, v___x_52_);
lean_ctor_set(v___x_45_, 0, v_a_31_);
v___x_54_ = v___x_45_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v_a_31_);
lean_ctor_set(v_reuseFailAlloc_55_, 1, v___x_52_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_peekIs(lean_object* v_p_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_pos_61_; lean_object* v_array_65_; lean_object* v_idx_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v_array_65_ = lean_ctor_get(v_a_59_, 0);
v_idx_66_ = lean_ctor_get(v_a_59_, 1);
v___x_67_ = lean_byte_array_size(v_array_65_);
v___x_68_ = lean_nat_dec_lt(v_idx_66_, v___x_67_);
if (v___x_68_ == 0)
{
lean_dec_ref(v_p_58_);
v_pos_61_ = v_a_59_;
goto v___jp_60_;
}
else
{
uint8_t v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_69_ = lean_byte_array_fget(v_array_65_, v_idx_66_);
v___x_70_ = lean_box(v___x_69_);
v___x_71_ = lean_apply_1(v_p_58_, v___x_70_);
v___x_72_ = lean_unbox(v___x_71_);
if (v___x_72_ == 0)
{
v_pos_61_ = v_a_59_;
goto v___jp_60_;
}
else
{
lean_object* v___x_73_; 
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v_a_59_);
lean_ctor_set(v___x_73_, 1, v___x_71_);
return v___x_73_;
}
}
v___jp_60_:
{
uint8_t v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = 0;
v___x_63_ = lean_box(v___x_62_);
v___x_64_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_64_, 0, v_pos_61_);
lean_ctor_set(v___x_64_, 1, v___x_63_);
return v___x_64_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(lean_object* v_msg_75_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = ((lean_object*)(l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2___closed__0));
v___x_77_ = lean_panic_fn_borrowed(v___x_76_, v_msg_75_);
return v___x_77_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0(uint8_t v_c_78_){
_start:
{
uint8_t v___x_96_; uint8_t v___x_97_; 
v___x_96_ = 48;
v___x_97_ = lean_uint8_dec_le(v___x_96_, v_c_78_);
if (v___x_97_ == 0)
{
goto v___jp_91_;
}
else
{
uint8_t v___x_98_; uint8_t v___x_99_; 
v___x_98_ = 57;
v___x_99_ = lean_uint8_dec_le(v_c_78_, v___x_98_);
if (v___x_99_ == 0)
{
goto v___jp_91_;
}
else
{
return v___x_99_;
}
}
v___jp_79_:
{
uint8_t v___x_80_; uint8_t v___x_81_; 
v___x_80_ = 43;
v___x_81_ = lean_uint8_dec_eq(v_c_78_, v___x_80_);
if (v___x_81_ == 0)
{
uint8_t v___x_82_; uint8_t v___x_83_; 
v___x_82_ = 45;
v___x_83_ = lean_uint8_dec_eq(v_c_78_, v___x_82_);
if (v___x_83_ == 0)
{
uint8_t v___x_84_; uint8_t v___x_85_; 
v___x_84_ = 46;
v___x_85_ = lean_uint8_dec_eq(v_c_78_, v___x_84_);
return v___x_85_;
}
else
{
return v___x_83_;
}
}
else
{
return v___x_81_;
}
}
v___jp_86_:
{
uint8_t v___x_87_; uint8_t v___x_88_; 
v___x_87_ = 65;
v___x_88_ = lean_uint8_dec_le(v___x_87_, v_c_78_);
if (v___x_88_ == 0)
{
goto v___jp_79_;
}
else
{
uint8_t v___x_89_; uint8_t v___x_90_; 
v___x_89_ = 90;
v___x_90_ = lean_uint8_dec_le(v_c_78_, v___x_89_);
if (v___x_90_ == 0)
{
goto v___jp_79_;
}
else
{
return v___x_90_;
}
}
}
v___jp_91_:
{
uint8_t v___x_92_; uint8_t v___x_93_; 
v___x_92_ = 97;
v___x_93_ = lean_uint8_dec_le(v___x_92_, v_c_78_);
if (v___x_93_ == 0)
{
goto v___jp_86_;
}
else
{
uint8_t v___x_94_; uint8_t v___x_95_; 
v___x_94_ = 122;
v___x_95_ = lean_uint8_dec_le(v_c_78_, v___x_94_);
if (v___x_95_ == 0)
{
goto v___jp_86_;
}
else
{
return v___x_95_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___boxed(lean_object* v_c_100_){
_start:
{
uint8_t v_c_boxed_101_; uint8_t v_res_102_; lean_object* v_r_103_; 
v_c_boxed_101_ = lean_unbox(v_c_100_);
v_res_102_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0(v_c_boxed_101_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(lean_object* v_x_104_){
_start:
{
if (lean_obj_tag(v_x_104_) == 0)
{
uint8_t v___x_105_; 
v___x_105_ = 1;
return v___x_105_;
}
else
{
lean_object* v_head_106_; lean_object* v_tail_107_; uint32_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v_head_106_ = lean_ctor_get(v_x_104_, 0);
v_tail_107_ = lean_ctor_get(v_x_104_, 1);
v___x_137_ = lean_unbox_uint32(v_head_106_);
v___x_138_ = lean_uint32_to_nat(v___x_137_);
v___x_139_ = lean_unsigned_to_nat(128u);
v___x_140_ = lean_nat_dec_lt(v___x_138_, v___x_139_);
lean_dec(v___x_138_);
if (v___x_140_ == 0)
{
goto v___jp_108_;
}
else
{
uint32_t v___x_141_; uint32_t v___x_142_; uint8_t v___x_143_; 
v___x_141_ = 48;
v___x_142_ = lean_unbox_uint32(v_head_106_);
v___x_143_ = lean_uint32_dec_le(v___x_141_, v___x_142_);
if (v___x_143_ == 0)
{
goto v___jp_129_;
}
else
{
uint32_t v___x_144_; uint32_t v___x_145_; uint8_t v___x_146_; 
v___x_144_ = 57;
v___x_145_ = lean_unbox_uint32(v_head_106_);
v___x_146_ = lean_uint32_dec_le(v___x_145_, v___x_144_);
if (v___x_146_ == 0)
{
goto v___jp_129_;
}
else
{
v_x_104_ = v_tail_107_;
goto _start;
}
}
}
v___jp_108_:
{
uint32_t v___x_109_; uint32_t v___x_110_; uint8_t v___x_111_; 
v___x_109_ = 43;
v___x_110_ = lean_unbox_uint32(v_head_106_);
v___x_111_ = lean_uint32_dec_eq(v___x_110_, v___x_109_);
if (v___x_111_ == 0)
{
uint32_t v___x_112_; uint32_t v___x_113_; uint8_t v___x_114_; 
v___x_112_ = 45;
v___x_113_ = lean_unbox_uint32(v_head_106_);
v___x_114_ = lean_uint32_dec_eq(v___x_113_, v___x_112_);
if (v___x_114_ == 0)
{
uint32_t v___x_115_; uint32_t v___x_116_; uint8_t v___x_117_; 
v___x_115_ = 46;
v___x_116_ = lean_unbox_uint32(v_head_106_);
v___x_117_ = lean_uint32_dec_eq(v___x_116_, v___x_115_);
if (v___x_117_ == 0)
{
return v___x_117_;
}
else
{
v_x_104_ = v_tail_107_;
goto _start;
}
}
else
{
v_x_104_ = v_tail_107_;
goto _start;
}
}
else
{
v_x_104_ = v_tail_107_;
goto _start;
}
}
v___jp_121_:
{
uint32_t v___x_122_; uint32_t v___x_123_; uint8_t v___x_124_; 
v___x_122_ = 97;
v___x_123_ = lean_unbox_uint32(v_head_106_);
v___x_124_ = lean_uint32_dec_le(v___x_122_, v___x_123_);
if (v___x_124_ == 0)
{
goto v___jp_108_;
}
else
{
uint32_t v___x_125_; uint32_t v___x_126_; uint8_t v___x_127_; 
v___x_125_ = 122;
v___x_126_ = lean_unbox_uint32(v_head_106_);
v___x_127_ = lean_uint32_dec_le(v___x_126_, v___x_125_);
if (v___x_127_ == 0)
{
goto v___jp_108_;
}
else
{
v_x_104_ = v_tail_107_;
goto _start;
}
}
}
v___jp_129_:
{
uint32_t v___x_130_; uint32_t v___x_131_; uint8_t v___x_132_; 
v___x_130_ = 65;
v___x_131_ = lean_unbox_uint32(v_head_106_);
v___x_132_ = lean_uint32_dec_le(v___x_130_, v___x_131_);
if (v___x_132_ == 0)
{
goto v___jp_121_;
}
else
{
uint32_t v___x_133_; uint32_t v___x_134_; uint8_t v___x_135_; 
v___x_133_ = 90;
v___x_134_ = lean_unbox_uint32(v_head_106_);
v___x_135_ = lean_uint32_dec_le(v___x_134_, v___x_133_);
if (v___x_135_ == 0)
{
goto v___jp_121_;
}
else
{
v_x_104_ = v_tail_107_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1___boxed(lean_object* v_x_148_){
_start:
{
uint8_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(v_x_148_);
lean_dec(v_x_148_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(lean_object* v_s_151_, lean_object* v_p_152_){
_start:
{
uint32_t v___y_154_; lean_object* v___x_159_; uint8_t v_decide_160_; 
v___x_159_ = lean_string_utf8_byte_size(v_s_151_);
v_decide_160_ = lean_nat_dec_eq(v_p_152_, v___x_159_);
if (v_decide_160_ == 0)
{
uint32_t v___x_161_; uint32_t v___x_162_; uint8_t v___x_163_; 
v___x_161_ = lean_string_utf8_get_fast(v_s_151_, v_p_152_);
v___x_162_ = 65;
v___x_163_ = lean_uint32_dec_le(v___x_162_, v___x_161_);
if (v___x_163_ == 0)
{
v___y_154_ = v___x_161_;
goto v___jp_153_;
}
else
{
uint32_t v___x_164_; uint8_t v___x_165_; 
v___x_164_ = 90;
v___x_165_ = lean_uint32_dec_le(v___x_161_, v___x_164_);
if (v___x_165_ == 0)
{
v___y_154_ = v___x_161_;
goto v___jp_153_;
}
else
{
uint32_t v___x_166_; uint32_t v___x_167_; 
v___x_166_ = 32;
v___x_167_ = lean_uint32_add(v___x_161_, v___x_166_);
v___y_154_ = v___x_167_;
goto v___jp_153_;
}
}
}
else
{
lean_dec(v_p_152_);
return v_s_151_;
}
v___jp_153_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
lean_inc(v_p_152_);
v___x_155_ = lean_string_utf8_set(v_s_151_, v_p_152_, v___y_154_);
v___x_156_ = l_Char_utf8Size(v___y_154_);
v___x_157_ = lean_nat_add(v_p_152_, v___x_156_);
lean_dec(v___x_156_);
lean_dec(v_p_152_);
v_s_151_ = v___x_155_;
v_p_152_ = v___x_157_;
goto _start;
}
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_177_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6));
v___x_178_ = lean_unsigned_to_nat(46u);
v___x_179_ = lean_unsigned_to_nat(193u);
v___x_180_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5));
v___x_181_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__4));
v___x_182_ = l_mkPanicMessageWithDecl(v___x_181_, v___x_180_, v___x_179_, v___x_178_, v___x_177_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(lean_object* v_config_187_, lean_object* v_a_188_){
_start:
{
lean_object* v___y_193_; lean_object* v___y_197_; lean_object* v___y_198_; uint8_t v___y_199_; lean_object* v___y_202_; uint32_t v___y_203_; lean_object* v___y_204_; lean_object* v_maxSchemeLength_209_; lean_object* v___x_210_; lean_object* v___y_212_; lean_object* v___y_213_; uint8_t v___x_229_; lean_object* v___y_231_; lean_object* v___y_232_; uint8_t v___y_233_; lean_object* v_lower_234_; lean_object* v_upper_235_; lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_251_; uint8_t v___y_252_; lean_object* v___y_253_; 
v_maxSchemeLength_209_ = lean_ctor_get(v_config_187_, 0);
v___x_210_ = lean_unsigned_to_nat(0u);
v___x_229_ = lean_nat_dec_eq(v_maxSchemeLength_209_, v___x_210_);
if (v___x_229_ == 0)
{
lean_object* v_array_255_; lean_object* v_idx_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v_array_255_ = lean_ctor_get(v_a_188_, 0);
v_idx_256_ = lean_ctor_get(v_a_188_, 1);
v___x_257_ = lean_byte_array_size(v_array_255_);
v___x_258_ = lean_nat_dec_lt(v_idx_256_, v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_box(0);
v___x_260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_260_, 0, v_a_188_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
return v___x_260_;
}
else
{
lean_object* v___f_261_; lean_object* v_pos_263_; uint8_t v_res_264_; uint8_t v_c_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v_it_x27_279_; uint8_t v___x_285_; uint8_t v___x_286_; 
v___f_261_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__8));
v_c_276_ = lean_byte_array_fget(v_array_255_, v_idx_256_);
v___x_277_ = lean_unsigned_to_nat(1u);
v___x_278_ = lean_nat_add(v_idx_256_, v___x_277_);
lean_inc_ref(v_array_255_);
v_it_x27_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_279_, 0, v_array_255_);
lean_ctor_set(v_it_x27_279_, 1, v___x_278_);
v___x_285_ = 65;
v___x_286_ = lean_uint8_dec_le(v___x_285_, v_c_276_);
if (v___x_286_ == 0)
{
goto v___jp_280_;
}
else
{
uint8_t v___x_287_; uint8_t v___x_288_; 
v___x_287_ = 90;
v___x_288_ = lean_uint8_dec_le(v_c_276_, v___x_287_);
if (v___x_288_ == 0)
{
goto v___jp_280_;
}
else
{
lean_dec_ref(v_a_188_);
v_pos_263_ = v_it_x27_279_;
v_res_264_ = v_c_276_;
goto v___jp_262_;
}
}
v___jp_262_:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v_snd_268_; lean_object* v_fst_269_; lean_object* v_fst_270_; lean_object* v_array_271_; lean_object* v_idx_272_; lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = lean_nat_sub(v_maxSchemeLength_209_, v___x_265_);
lean_inc_ref(v_pos_263_);
v___x_267_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_261_, v___x_266_, v___x_210_, v_pos_263_);
lean_dec(v___x_266_);
v_snd_268_ = lean_ctor_get(v___x_267_, 1);
lean_inc(v_snd_268_);
v_fst_269_ = lean_ctor_get(v___x_267_, 0);
lean_inc(v_fst_269_);
lean_dec_ref(v___x_267_);
v_fst_270_ = lean_ctor_get(v_snd_268_, 0);
lean_inc(v_fst_270_);
lean_dec(v_snd_268_);
v_array_271_ = lean_ctor_get(v_pos_263_, 0);
lean_inc_ref(v_array_271_);
v_idx_272_ = lean_ctor_get(v_pos_263_, 1);
lean_inc(v_idx_272_);
lean_dec_ref(v_pos_263_);
v___x_273_ = lean_nat_add(v_idx_272_, v_fst_269_);
lean_dec(v_fst_269_);
v___x_274_ = lean_byte_array_size(v_array_271_);
v___x_275_ = lean_nat_dec_le(v_idx_272_, v___x_210_);
if (v___x_275_ == 0)
{
v___y_248_ = v_fst_270_;
v___y_249_ = v___x_274_;
v___y_250_ = v_array_271_;
v___y_251_ = v___x_273_;
v___y_252_ = v_res_264_;
v___y_253_ = v_idx_272_;
goto v___jp_247_;
}
else
{
lean_dec(v_idx_272_);
v___y_248_ = v_fst_270_;
v___y_249_ = v___x_274_;
v___y_250_ = v_array_271_;
v___y_251_ = v___x_273_;
v___y_252_ = v_res_264_;
v___y_253_ = v___x_210_;
goto v___jp_247_;
}
}
v___jp_280_:
{
uint8_t v___x_281_; uint8_t v___x_282_; 
v___x_281_ = 97;
v___x_282_ = lean_uint8_dec_le(v___x_281_, v_c_276_);
if (v___x_282_ == 0)
{
lean_dec_ref_known(v_it_x27_279_, 2);
goto v___jp_189_;
}
else
{
uint8_t v___x_283_; uint8_t v___x_284_; 
v___x_283_ = 122;
v___x_284_ = lean_uint8_dec_le(v_c_276_, v___x_283_);
if (v___x_284_ == 0)
{
lean_dec_ref_known(v_it_x27_279_, 2);
goto v___jp_189_;
}
else
{
lean_dec_ref(v_a_188_);
v_pos_263_ = v_it_x27_279_;
v_res_264_ = v_c_276_;
goto v___jp_262_;
}
}
}
}
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10));
v___x_290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_290_, 0, v_a_188_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
return v___x_290_;
}
v___jp_189_:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__1));
v___x_191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_191_, 0, v_a_188_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
return v___x_191_;
}
v___jp_192_:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__3));
v___x_195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_195_, 0, v___y_193_);
lean_ctor_set(v___x_195_, 1, v___x_194_);
return v___x_195_;
}
v___jp_196_:
{
if (v___y_199_ == 0)
{
lean_dec_ref(v___y_198_);
v___y_193_ = v___y_197_;
goto v___jp_192_;
}
else
{
lean_object* v___x_200_; 
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v___y_197_);
lean_ctor_set(v___x_200_, 1, v___y_198_);
return v___x_200_;
}
}
v___jp_201_:
{
uint32_t v___x_205_; uint8_t v___x_206_; 
v___x_205_ = 97;
v___x_206_ = lean_uint32_dec_le(v___x_205_, v___y_203_);
if (v___x_206_ == 0)
{
lean_dec_ref(v___y_204_);
v___y_193_ = v___y_202_;
goto v___jp_192_;
}
else
{
uint32_t v___x_207_; uint8_t v___x_208_; 
v___x_207_ = 122;
v___x_208_ = lean_uint32_dec_le(v___y_203_, v___x_207_);
v___y_197_ = v___y_202_;
v___y_198_ = v___y_204_;
v___y_199_ = v___x_208_;
goto v___jp_196_;
}
}
v___jp_211_:
{
lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_214_ = l_String_mapAux___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(v___y_213_, v___x_210_);
lean_inc_ref(v___x_214_);
v___x_215_ = l_Std_Http_Internal_instDecidableIsLowerCase(v___x_214_);
if (v___x_215_ == 0)
{
lean_dec_ref(v___x_214_);
v___y_193_ = v___y_212_;
goto v___jp_192_;
}
else
{
lean_object* v___x_216_; uint8_t v___x_217_; 
lean_inc_ref(v___x_214_);
v___x_216_ = lean_string_data(v___x_214_);
v___x_217_ = l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(v___x_216_);
if (v___x_217_ == 0)
{
lean_dec(v___x_216_);
v___y_197_ = v___y_212_;
v___y_198_ = v___x_214_;
v___y_199_ = v___x_217_;
goto v___jp_196_;
}
else
{
lean_object* v___x_218_; 
v___x_218_ = l_List_head_x3f___redArg(v___x_216_);
lean_dec(v___x_216_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_dec_ref(v___x_214_);
v___y_193_ = v___y_212_;
goto v___jp_192_;
}
else
{
lean_object* v_val_219_; uint32_t v___x_220_; uint32_t v___x_221_; uint8_t v___x_222_; 
v_val_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_val_219_);
lean_dec_ref_known(v___x_218_, 1);
v___x_220_ = 65;
v___x_221_ = lean_unbox_uint32(v_val_219_);
v___x_222_ = lean_uint32_dec_le(v___x_220_, v___x_221_);
if (v___x_222_ == 0)
{
uint32_t v___x_223_; 
v___x_223_ = lean_unbox_uint32(v_val_219_);
lean_dec(v_val_219_);
v___y_202_ = v___y_212_;
v___y_203_ = v___x_223_;
v___y_204_ = v___x_214_;
goto v___jp_201_;
}
else
{
uint32_t v___x_224_; uint32_t v___x_225_; uint8_t v___x_226_; 
v___x_224_ = 90;
v___x_225_ = lean_unbox_uint32(v_val_219_);
v___x_226_ = lean_uint32_dec_le(v___x_225_, v___x_224_);
if (v___x_226_ == 0)
{
uint32_t v___x_227_; 
v___x_227_ = lean_unbox_uint32(v_val_219_);
lean_dec(v_val_219_);
v___y_202_ = v___y_212_;
v___y_203_ = v___x_227_;
v___y_204_ = v___x_214_;
goto v___jp_201_;
}
else
{
lean_object* v___x_228_; 
lean_dec(v_val_219_);
v___x_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_228_, 0, v___y_212_);
lean_ctor_set(v___x_228_, 1, v___x_214_);
return v___x_228_;
}
}
}
}
}
}
v___jp_230_:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_236_ = l_ByteArray_toByteSlice(v___y_232_, v_lower_234_, v_upper_235_);
v___x_237_ = l_ByteArray_empty;
v___x_238_ = lean_byte_array_push(v___x_237_, v___y_233_);
v___x_239_ = l_ByteSlice_toByteArray(v___x_236_);
v___x_240_ = lean_byte_array_size(v___x_238_);
v___x_241_ = lean_byte_array_size(v___x_239_);
v___x_242_ = lean_byte_array_copy_slice(v___x_239_, v___x_210_, v___x_238_, v___x_240_, v___x_241_, v___x_229_);
lean_dec_ref(v___x_239_);
v___x_243_ = lean_string_validate_utf8(v___x_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec_ref(v___x_242_);
v___x_244_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_245_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_244_);
v___y_212_ = v___y_231_;
v___y_213_ = v___x_245_;
goto v___jp_211_;
}
else
{
lean_object* v___x_246_; 
v___x_246_ = lean_string_from_utf8_unchecked(v___x_242_);
v___y_212_ = v___y_231_;
v___y_213_ = v___x_246_;
goto v___jp_211_;
}
}
v___jp_247_:
{
uint8_t v___x_254_; 
v___x_254_ = lean_nat_dec_le(v___y_251_, v___y_249_);
if (v___x_254_ == 0)
{
lean_dec(v___y_251_);
v___y_231_ = v___y_248_;
v___y_232_ = v___y_250_;
v___y_233_ = v___y_252_;
v_lower_234_ = v___y_253_;
v_upper_235_ = v___y_249_;
goto v___jp_230_;
}
else
{
lean_dec(v___y_249_);
v___y_231_ = v___y_248_;
v___y_232_ = v___y_250_;
v___y_233_ = v___y_252_;
v_lower_234_ = v___y_253_;
v_upper_235_ = v___y_251_;
goto v___jp_230_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___boxed(lean_object* v_config_291_, lean_object* v_a_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_291_, v_a_292_);
lean_dec_ref(v_config_291_);
return v_res_293_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0(uint8_t v___y_294_){
_start:
{
uint8_t v___x_295_; uint8_t v___x_296_; 
v___x_295_ = 48;
v___x_296_ = lean_uint8_dec_le(v___x_295_, v___y_294_);
if (v___x_296_ == 0)
{
return v___x_296_;
}
else
{
uint8_t v___x_297_; uint8_t v___x_298_; 
v___x_297_ = 57;
v___x_298_ = lean_uint8_dec_le(v___y_294_, v___x_297_);
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0___boxed(lean_object* v___y_299_){
_start:
{
uint8_t v___y_560__boxed_300_; uint8_t v_res_301_; lean_object* v_r_302_; 
v___y_560__boxed_300_ = lean_unbox(v___y_299_);
v_res_301_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0(v___y_560__boxed_300_);
v_r_302_ = lean_box(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(lean_object* v_a_306_){
_start:
{
lean_object* v___f_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v_snd_311_; lean_object* v_fst_312_; lean_object* v_fst_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_366_; 
v___f_307_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__0));
v___x_308_ = lean_unsigned_to_nat(5u);
v___x_309_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_306_);
v___x_310_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_307_, v___x_308_, v___x_309_, v_a_306_);
v_snd_311_ = lean_ctor_get(v___x_310_, 1);
lean_inc(v_snd_311_);
v_fst_312_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_fst_312_);
lean_dec_ref(v___x_310_);
v_fst_313_ = lean_ctor_get(v_snd_311_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v_snd_311_);
if (v_isSharedCheck_366_ == 0)
{
lean_object* v_unused_367_; 
v_unused_367_ = lean_ctor_get(v_snd_311_, 1);
lean_dec(v_unused_367_);
v___x_315_ = v_snd_311_;
v_isShared_316_ = v_isSharedCheck_366_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_fst_313_);
lean_dec(v_snd_311_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_366_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___y_318_; lean_object* v_array_349_; lean_object* v_idx_350_; lean_object* v_lower_352_; lean_object* v_upper_353_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___y_363_; uint8_t v___x_365_; 
v_array_349_ = lean_ctor_get(v_a_306_, 0);
lean_inc_ref(v_array_349_);
v_idx_350_ = lean_ctor_get(v_a_306_, 1);
lean_inc(v_idx_350_);
lean_dec_ref(v_a_306_);
v___x_360_ = lean_nat_add(v_idx_350_, v_fst_312_);
lean_dec(v_fst_312_);
v___x_361_ = lean_byte_array_size(v_array_349_);
v___x_365_ = lean_nat_dec_le(v_idx_350_, v___x_309_);
if (v___x_365_ == 0)
{
v___y_363_ = v_idx_350_;
goto v___jp_362_;
}
else
{
lean_dec(v_idx_350_);
v___y_363_ = v___x_309_;
goto v___jp_362_;
}
v___jp_317_:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = lean_string_utf8_byte_size(v___y_318_);
lean_inc_ref(v___y_318_);
v___x_320_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_320_, 0, v___y_318_);
lean_ctor_set(v___x_320_, 1, v___x_309_);
lean_ctor_set(v___x_320_, 2, v___x_319_);
v___x_321_ = l_String_Slice_toNat_x3f(v___x_320_);
lean_dec_ref_known(v___x_320_, 3);
if (lean_obj_tag(v___x_321_) == 1)
{
lean_object* v_val_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_342_; 
lean_dec_ref(v___y_318_);
v_val_322_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_342_ == 0)
{
v___x_324_ = v___x_321_;
v_isShared_325_ = v_isSharedCheck_342_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_val_322_);
lean_dec(v___x_321_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_342_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_326_ = lean_unsigned_to_nat(65535u);
v___x_327_ = lean_nat_dec_lt(v___x_326_, v_val_322_);
if (v___x_327_ == 0)
{
uint16_t v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
lean_del_object(v___x_324_);
v___x_328_ = lean_uint16_of_nat(v_val_322_);
lean_dec(v_val_322_);
v___x_329_ = lean_box(v___x_328_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 1, v___x_329_);
v___x_331_ = v___x_315_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_fst_313_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v___x_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
else
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_333_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__1));
v___x_334_ = l_Nat_reprFast(v_val_322_);
v___x_335_ = lean_string_append(v___x_333_, v___x_334_);
lean_dec_ref(v___x_334_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 0, v___x_335_);
v___x_337_ = v___x_324_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_335_);
v___x_337_ = v_reuseFailAlloc_341_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_339_; 
if (v_isShared_316_ == 0)
{
lean_ctor_set_tag(v___x_315_, 1);
lean_ctor_set(v___x_315_, 1, v___x_337_);
v___x_339_ = v___x_315_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_fst_313_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_347_; 
lean_dec(v___x_321_);
v___x_343_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__2));
v___x_344_ = lean_string_append(v___x_343_, v___y_318_);
lean_dec_ref(v___y_318_);
v___x_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
if (v_isShared_316_ == 0)
{
lean_ctor_set_tag(v___x_315_, 1);
lean_ctor_set(v___x_315_, 1, v___x_345_);
v___x_347_ = v___x_315_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_fst_313_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v___x_345_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
v___jp_351_:
{
lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_354_ = l_ByteArray_toByteSlice(v_array_349_, v_lower_352_, v_upper_353_);
v___x_355_ = l_ByteSlice_toByteArray(v___x_354_);
v___x_356_ = lean_string_validate_utf8(v___x_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; lean_object* v___x_358_; 
lean_dec_ref(v___x_355_);
v___x_357_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_358_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_357_);
v___y_318_ = v___x_358_;
goto v___jp_317_;
}
else
{
lean_object* v___x_359_; 
v___x_359_ = lean_string_from_utf8_unchecked(v___x_355_);
v___y_318_ = v___x_359_;
goto v___jp_317_;
}
}
v___jp_362_:
{
uint8_t v___x_364_; 
v___x_364_ = lean_nat_dec_le(v___x_360_, v___x_361_);
if (v___x_364_ == 0)
{
lean_dec(v___x_360_);
v_lower_352_ = v___y_363_;
v_upper_353_ = v___x_361_;
goto v___jp_351_;
}
else
{
v_lower_352_ = v___y_363_;
v_upper_353_ = v___x_360_;
goto v___jp_351_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0(uint8_t v_x_368_){
_start:
{
uint8_t v___x_414_; uint8_t v___x_415_; 
v___x_414_ = 58;
v___x_415_ = lean_uint8_dec_eq(v_x_368_, v___x_414_);
if (v___x_415_ == 0)
{
uint8_t v___x_416_; uint8_t v___x_417_; 
v___x_416_ = 48;
v___x_417_ = lean_uint8_dec_le(v___x_416_, v_x_368_);
if (v___x_417_ == 0)
{
goto v___jp_409_;
}
else
{
uint8_t v___x_418_; uint8_t v___x_419_; 
v___x_418_ = 57;
v___x_419_ = lean_uint8_dec_le(v_x_368_, v___x_418_);
if (v___x_419_ == 0)
{
goto v___jp_409_;
}
else
{
return v___x_419_;
}
}
}
else
{
uint8_t v___x_420_; 
v___x_420_ = 0;
return v___x_420_;
}
v___jp_369_:
{
uint8_t v___x_370_; uint8_t v___x_371_; 
v___x_370_ = 45;
v___x_371_ = lean_uint8_dec_eq(v_x_368_, v___x_370_);
if (v___x_371_ == 0)
{
uint8_t v___x_372_; uint8_t v___x_373_; 
v___x_372_ = 46;
v___x_373_ = lean_uint8_dec_eq(v_x_368_, v___x_372_);
if (v___x_373_ == 0)
{
uint8_t v___x_374_; uint8_t v___x_375_; 
v___x_374_ = 95;
v___x_375_ = lean_uint8_dec_eq(v_x_368_, v___x_374_);
if (v___x_375_ == 0)
{
uint8_t v___x_376_; uint8_t v___x_377_; 
v___x_376_ = 126;
v___x_377_ = lean_uint8_dec_eq(v_x_368_, v___x_376_);
if (v___x_377_ == 0)
{
uint8_t v___x_378_; uint8_t v___x_379_; 
v___x_378_ = 33;
v___x_379_ = lean_uint8_dec_eq(v_x_368_, v___x_378_);
if (v___x_379_ == 0)
{
uint8_t v___x_380_; uint8_t v___x_381_; 
v___x_380_ = 36;
v___x_381_ = lean_uint8_dec_eq(v_x_368_, v___x_380_);
if (v___x_381_ == 0)
{
uint8_t v___x_382_; uint8_t v___x_383_; 
v___x_382_ = 38;
v___x_383_ = lean_uint8_dec_eq(v_x_368_, v___x_382_);
if (v___x_383_ == 0)
{
uint8_t v___x_384_; uint8_t v___x_385_; 
v___x_384_ = 39;
v___x_385_ = lean_uint8_dec_eq(v_x_368_, v___x_384_);
if (v___x_385_ == 0)
{
uint8_t v___x_386_; uint8_t v___x_387_; 
v___x_386_ = 40;
v___x_387_ = lean_uint8_dec_eq(v_x_368_, v___x_386_);
if (v___x_387_ == 0)
{
uint8_t v___x_388_; uint8_t v___x_389_; 
v___x_388_ = 41;
v___x_389_ = lean_uint8_dec_eq(v_x_368_, v___x_388_);
if (v___x_389_ == 0)
{
uint8_t v___x_390_; uint8_t v___x_391_; 
v___x_390_ = 42;
v___x_391_ = lean_uint8_dec_eq(v_x_368_, v___x_390_);
if (v___x_391_ == 0)
{
uint8_t v___x_392_; uint8_t v___x_393_; 
v___x_392_ = 43;
v___x_393_ = lean_uint8_dec_eq(v_x_368_, v___x_392_);
if (v___x_393_ == 0)
{
uint8_t v___x_394_; uint8_t v___x_395_; 
v___x_394_ = 44;
v___x_395_ = lean_uint8_dec_eq(v_x_368_, v___x_394_);
if (v___x_395_ == 0)
{
uint8_t v___x_396_; uint8_t v___x_397_; 
v___x_396_ = 59;
v___x_397_ = lean_uint8_dec_eq(v_x_368_, v___x_396_);
if (v___x_397_ == 0)
{
uint8_t v___x_398_; uint8_t v___x_399_; 
v___x_398_ = 61;
v___x_399_ = lean_uint8_dec_eq(v_x_368_, v___x_398_);
if (v___x_399_ == 0)
{
uint8_t v___x_400_; uint8_t v___x_401_; 
v___x_400_ = 58;
v___x_401_ = lean_uint8_dec_eq(v_x_368_, v___x_400_);
if (v___x_401_ == 0)
{
uint8_t v___x_402_; uint8_t v___x_403_; 
v___x_402_ = 37;
v___x_403_ = lean_uint8_dec_eq(v_x_368_, v___x_402_);
return v___x_403_;
}
else
{
return v___x_401_;
}
}
else
{
return v___x_399_;
}
}
else
{
return v___x_397_;
}
}
else
{
return v___x_395_;
}
}
else
{
return v___x_393_;
}
}
else
{
return v___x_391_;
}
}
else
{
return v___x_389_;
}
}
else
{
return v___x_387_;
}
}
else
{
return v___x_385_;
}
}
else
{
return v___x_383_;
}
}
else
{
return v___x_381_;
}
}
else
{
return v___x_379_;
}
}
else
{
return v___x_377_;
}
}
else
{
return v___x_375_;
}
}
else
{
return v___x_373_;
}
}
else
{
return v___x_371_;
}
}
v___jp_404_:
{
uint8_t v___x_405_; uint8_t v___x_406_; 
v___x_405_ = 65;
v___x_406_ = lean_uint8_dec_le(v___x_405_, v_x_368_);
if (v___x_406_ == 0)
{
goto v___jp_369_;
}
else
{
uint8_t v___x_407_; uint8_t v___x_408_; 
v___x_407_ = 90;
v___x_408_ = lean_uint8_dec_le(v_x_368_, v___x_407_);
if (v___x_408_ == 0)
{
goto v___jp_369_;
}
else
{
return v___x_408_;
}
}
}
v___jp_409_:
{
uint8_t v___x_410_; uint8_t v___x_411_; 
v___x_410_ = 97;
v___x_411_ = lean_uint8_dec_le(v___x_410_, v_x_368_);
if (v___x_411_ == 0)
{
goto v___jp_404_;
}
else
{
uint8_t v___x_412_; uint8_t v___x_413_; 
v___x_412_ = 122;
v___x_413_ = lean_uint8_dec_le(v_x_368_, v___x_412_);
if (v___x_413_ == 0)
{
goto v___jp_404_;
}
else
{
return v___x_413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___boxed(lean_object* v_x_421_){
_start:
{
uint8_t v_x_boxed_422_; uint8_t v_res_423_; lean_object* v_r_424_; 
v_x_boxed_422_ = lean_unbox(v_x_421_);
v_res_423_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0(v_x_boxed_422_);
v_r_424_ = lean_box(v_res_423_);
return v_r_424_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1(uint8_t v___x_425_, uint8_t v___x_426_, uint8_t v_x_427_){
_start:
{
uint8_t v___x_472_; uint8_t v___x_473_; 
v___x_472_ = 48;
v___x_473_ = lean_uint8_dec_le(v___x_472_, v_x_427_);
if (v___x_473_ == 0)
{
goto v___jp_467_;
}
else
{
uint8_t v___x_474_; uint8_t v___x_475_; 
v___x_474_ = 57;
v___x_475_ = lean_uint8_dec_le(v_x_427_, v___x_474_);
if (v___x_475_ == 0)
{
goto v___jp_467_;
}
else
{
return v___x_426_;
}
}
v___jp_428_:
{
uint8_t v___x_429_; uint8_t v___x_430_; 
v___x_429_ = 45;
v___x_430_ = lean_uint8_dec_eq(v_x_427_, v___x_429_);
if (v___x_430_ == 0)
{
uint8_t v___x_431_; uint8_t v___x_432_; 
v___x_431_ = 46;
v___x_432_ = lean_uint8_dec_eq(v_x_427_, v___x_431_);
if (v___x_432_ == 0)
{
uint8_t v___x_433_; uint8_t v___x_434_; 
v___x_433_ = 95;
v___x_434_ = lean_uint8_dec_eq(v_x_427_, v___x_433_);
if (v___x_434_ == 0)
{
uint8_t v___x_435_; uint8_t v___x_436_; 
v___x_435_ = 126;
v___x_436_ = lean_uint8_dec_eq(v_x_427_, v___x_435_);
if (v___x_436_ == 0)
{
uint8_t v___x_437_; uint8_t v___x_438_; 
v___x_437_ = 33;
v___x_438_ = lean_uint8_dec_eq(v_x_427_, v___x_437_);
if (v___x_438_ == 0)
{
uint8_t v___x_439_; uint8_t v___x_440_; 
v___x_439_ = 36;
v___x_440_ = lean_uint8_dec_eq(v_x_427_, v___x_439_);
if (v___x_440_ == 0)
{
uint8_t v___x_441_; uint8_t v___x_442_; 
v___x_441_ = 38;
v___x_442_ = lean_uint8_dec_eq(v_x_427_, v___x_441_);
if (v___x_442_ == 0)
{
uint8_t v___x_443_; uint8_t v___x_444_; 
v___x_443_ = 39;
v___x_444_ = lean_uint8_dec_eq(v_x_427_, v___x_443_);
if (v___x_444_ == 0)
{
uint8_t v___x_445_; uint8_t v___x_446_; 
v___x_445_ = 40;
v___x_446_ = lean_uint8_dec_eq(v_x_427_, v___x_445_);
if (v___x_446_ == 0)
{
uint8_t v___x_447_; uint8_t v___x_448_; 
v___x_447_ = 41;
v___x_448_ = lean_uint8_dec_eq(v_x_427_, v___x_447_);
if (v___x_448_ == 0)
{
uint8_t v___x_449_; uint8_t v___x_450_; 
v___x_449_ = 42;
v___x_450_ = lean_uint8_dec_eq(v_x_427_, v___x_449_);
if (v___x_450_ == 0)
{
uint8_t v___x_451_; uint8_t v___x_452_; 
v___x_451_ = 43;
v___x_452_ = lean_uint8_dec_eq(v_x_427_, v___x_451_);
if (v___x_452_ == 0)
{
uint8_t v___x_453_; uint8_t v___x_454_; 
v___x_453_ = 44;
v___x_454_ = lean_uint8_dec_eq(v_x_427_, v___x_453_);
if (v___x_454_ == 0)
{
uint8_t v___x_455_; uint8_t v___x_456_; 
v___x_455_ = 59;
v___x_456_ = lean_uint8_dec_eq(v_x_427_, v___x_455_);
if (v___x_456_ == 0)
{
uint8_t v___x_457_; uint8_t v___x_458_; 
v___x_457_ = 61;
v___x_458_ = lean_uint8_dec_eq(v_x_427_, v___x_457_);
if (v___x_458_ == 0)
{
uint8_t v___x_459_; 
v___x_459_ = lean_uint8_dec_eq(v_x_427_, v___x_425_);
if (v___x_459_ == 0)
{
uint8_t v___x_460_; uint8_t v___x_461_; 
v___x_460_ = 37;
v___x_461_ = lean_uint8_dec_eq(v_x_427_, v___x_460_);
return v___x_461_;
}
else
{
return v___x_426_;
}
}
else
{
return v___x_426_;
}
}
else
{
return v___x_426_;
}
}
else
{
return v___x_426_;
}
}
else
{
return v___x_426_;
}
}
else
{
return v___x_426_;
}
}
else
{
return v___x_426_;
}
}
else
{
return v___x_426_;
}
}
else
{
return v___x_426_;
}
}
else
{
return v___x_426_;
}
}
else
{
return v___x_426_;
}
}
else
{
return v___x_426_;
}
}
else
{
return v___x_426_;
}
}
else
{
return v___x_426_;
}
}
else
{
return v___x_426_;
}
}
else
{
return v___x_426_;
}
}
v___jp_462_:
{
uint8_t v___x_463_; uint8_t v___x_464_; 
v___x_463_ = 65;
v___x_464_ = lean_uint8_dec_le(v___x_463_, v_x_427_);
if (v___x_464_ == 0)
{
goto v___jp_428_;
}
else
{
uint8_t v___x_465_; uint8_t v___x_466_; 
v___x_465_ = 90;
v___x_466_ = lean_uint8_dec_le(v_x_427_, v___x_465_);
if (v___x_466_ == 0)
{
goto v___jp_428_;
}
else
{
return v___x_426_;
}
}
}
v___jp_467_:
{
uint8_t v___x_468_; uint8_t v___x_469_; 
v___x_468_ = 97;
v___x_469_ = lean_uint8_dec_le(v___x_468_, v_x_427_);
if (v___x_469_ == 0)
{
goto v___jp_462_;
}
else
{
uint8_t v___x_470_; uint8_t v___x_471_; 
v___x_470_ = 122;
v___x_471_ = lean_uint8_dec_le(v_x_427_, v___x_470_);
if (v___x_471_ == 0)
{
goto v___jp_462_;
}
else
{
return v___x_426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1___boxed(lean_object* v___x_476_, lean_object* v___x_477_, lean_object* v_x_478_){
_start:
{
uint8_t v___x_4626__boxed_479_; uint8_t v___x_4627__boxed_480_; uint8_t v_x_boxed_481_; uint8_t v_res_482_; lean_object* v_r_483_; 
v___x_4626__boxed_479_ = lean_unbox(v___x_476_);
v___x_4627__boxed_480_ = lean_unbox(v___x_477_);
v_x_boxed_481_ = lean_unbox(v_x_478_);
v_res_482_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1(v___x_4626__boxed_479_, v___x_4627__boxed_480_, v_x_boxed_481_);
v_r_483_ = lean_box(v_res_482_);
return v_r_483_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(lean_object* v_config_488_, lean_object* v_a_489_){
_start:
{
lean_object* v___y_491_; lean_object* v_userPassEncoded_492_; lean_object* v___y_493_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v_lower_500_; lean_object* v_upper_501_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_516_; lean_object* v_pos_517_; lean_object* v_maxUserInfoLength_519_; lean_object* v___f_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v_snd_523_; lean_object* v_fst_524_; lean_object* v_fst_525_; lean_object* v_array_526_; lean_object* v_idx_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_579_; 
v_maxUserInfoLength_519_ = lean_ctor_get(v_config_488_, 2);
v___f_520_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__2));
v___x_521_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_489_);
v___x_522_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_520_, v_maxUserInfoLength_519_, v___x_521_, v_a_489_);
v_snd_523_ = lean_ctor_get(v___x_522_, 1);
lean_inc(v_snd_523_);
v_fst_524_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_fst_524_);
lean_dec_ref(v___x_522_);
v_fst_525_ = lean_ctor_get(v_snd_523_, 0);
lean_inc(v_fst_525_);
lean_dec(v_snd_523_);
v_array_526_ = lean_ctor_get(v_a_489_, 0);
v_idx_527_ = lean_ctor_get(v_a_489_, 1);
v_isSharedCheck_579_ = !lean_is_exclusive(v_a_489_);
if (v_isSharedCheck_579_ == 0)
{
v___x_529_ = v_a_489_;
v_isShared_530_ = v_isSharedCheck_579_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_idx_527_);
lean_inc(v_array_526_);
lean_dec(v_a_489_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_579_;
goto v_resetjp_528_;
}
v___jp_490_:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_494_, 0, v___y_491_);
lean_ctor_set(v___x_494_, 1, v_userPassEncoded_492_);
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v___y_493_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
return v___x_495_;
}
v___jp_496_:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_502_ = l_ByteArray_toByteSlice(v___y_497_, v_lower_500_, v_upper_501_);
v___x_503_ = l_ByteSlice_toByteArray(v___x_502_);
v___x_504_ = l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(v___x_503_);
if (lean_obj_tag(v___x_504_) == 1)
{
v___y_491_ = v___y_499_;
v_userPassEncoded_492_ = v___x_504_;
v___y_493_ = v___y_498_;
goto v___jp_490_;
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; 
lean_dec(v___x_504_);
lean_dec_ref(v___y_499_);
v___x_505_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1));
v___x_506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_506_, 0, v___y_498_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
return v___x_506_;
}
}
v___jp_507_:
{
uint8_t v___x_514_; 
v___x_514_ = lean_nat_dec_le(v___y_508_, v___y_510_);
if (v___x_514_ == 0)
{
lean_dec(v___y_508_);
v___y_497_ = v___y_509_;
v___y_498_ = v___y_511_;
v___y_499_ = v___y_512_;
v_lower_500_ = v___y_513_;
v_upper_501_ = v___y_510_;
goto v___jp_496_;
}
else
{
lean_dec(v___y_510_);
v___y_497_ = v___y_509_;
v___y_498_ = v___y_511_;
v___y_499_ = v___y_512_;
v_lower_500_ = v___y_513_;
v_upper_501_ = v___y_508_;
goto v___jp_496_;
}
}
v___jp_515_:
{
lean_object* v___x_518_; 
v___x_518_ = lean_box(0);
v___y_491_ = v___y_516_;
v_userPassEncoded_492_ = v___x_518_;
v___y_493_ = v_pos_517_;
goto v___jp_490_;
}
v_resetjp_528_:
{
lean_object* v_lower_532_; lean_object* v_upper_533_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___y_576_; uint8_t v___x_578_; 
v___x_573_ = lean_nat_add(v_idx_527_, v_fst_524_);
lean_dec(v_fst_524_);
v___x_574_ = lean_byte_array_size(v_array_526_);
v___x_578_ = lean_nat_dec_le(v_idx_527_, v___x_521_);
if (v___x_578_ == 0)
{
v___y_576_ = v_idx_527_;
goto v___jp_575_;
}
else
{
lean_dec(v_idx_527_);
v___y_576_ = v___x_521_;
goto v___jp_575_;
}
v___jp_531_:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_534_ = l_ByteArray_toByteSlice(v_array_526_, v_lower_532_, v_upper_533_);
v___x_535_ = l_ByteSlice_toByteArray(v___x_534_);
v___x_536_ = l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(v___x_535_);
if (lean_obj_tag(v___x_536_) == 1)
{
lean_object* v_val_537_; lean_object* v_array_538_; lean_object* v_idx_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v_val_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_val_537_);
lean_dec_ref_known(v___x_536_, 1);
v_array_538_ = lean_ctor_get(v_fst_525_, 0);
v_idx_539_ = lean_ctor_get(v_fst_525_, 1);
v___x_540_ = lean_byte_array_size(v_array_538_);
v___x_541_ = lean_nat_dec_lt(v_idx_539_, v___x_540_);
if (v___x_541_ == 0)
{
lean_del_object(v___x_529_);
v___y_516_ = v_val_537_;
v_pos_517_ = v_fst_525_;
goto v___jp_515_;
}
else
{
uint8_t v___x_542_; uint8_t v___x_543_; uint8_t v___x_544_; 
v___x_542_ = lean_byte_array_fget(v_array_538_, v_idx_539_);
v___x_543_ = 58;
v___x_544_ = lean_uint8_dec_eq(v___x_542_, v___x_543_);
if (v___x_544_ == 0)
{
lean_del_object(v___x_529_);
v___y_516_ = v_val_537_;
v_pos_517_ = v_fst_525_;
goto v___jp_515_;
}
else
{
if (v___x_541_ == 0)
{
lean_object* v___x_545_; lean_object* v___x_547_; 
lean_dec(v_val_537_);
v___x_545_ = lean_box(0);
if (v_isShared_530_ == 0)
{
lean_ctor_set_tag(v___x_529_, 1);
lean_ctor_set(v___x_529_, 1, v___x_545_);
lean_ctor_set(v___x_529_, 0, v_fst_525_);
v___x_547_ = v___x_529_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_fst_525_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v___x_545_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
else
{
lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_566_; 
lean_inc(v_idx_539_);
lean_inc_ref(v_array_538_);
lean_del_object(v___x_529_);
v_isSharedCheck_566_ = !lean_is_exclusive(v_fst_525_);
if (v_isSharedCheck_566_ == 0)
{
lean_object* v_unused_567_; lean_object* v_unused_568_; 
v_unused_567_ = lean_ctor_get(v_fst_525_, 1);
lean_dec(v_unused_567_);
v_unused_568_ = lean_ctor_get(v_fst_525_, 0);
lean_dec(v_unused_568_);
v___x_550_ = v_fst_525_;
v_isShared_551_ = v_isSharedCheck_566_;
goto v_resetjp_549_;
}
else
{
lean_dec(v_fst_525_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_566_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___f_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_552_ = lean_box(v___x_543_);
v___x_553_ = lean_box(v___x_541_);
v___f_554_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1___boxed), 3, 2);
lean_closure_set(v___f_554_, 0, v___x_552_);
lean_closure_set(v___f_554_, 1, v___x_553_);
v___x_555_ = lean_unsigned_to_nat(1u);
v___x_556_ = lean_nat_add(v_idx_539_, v___x_555_);
lean_dec(v_idx_539_);
lean_inc(v___x_556_);
lean_inc_ref(v_array_538_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 1, v___x_556_);
v___x_558_ = v___x_550_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_array_538_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v___x_556_);
v___x_558_ = v_reuseFailAlloc_565_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_559_; lean_object* v_snd_560_; lean_object* v_fst_561_; lean_object* v_fst_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_559_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_554_, v_maxUserInfoLength_519_, v___x_521_, v___x_558_);
v_snd_560_ = lean_ctor_get(v___x_559_, 1);
lean_inc(v_snd_560_);
v_fst_561_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_fst_561_);
lean_dec_ref(v___x_559_);
v_fst_562_ = lean_ctor_get(v_snd_560_, 0);
lean_inc(v_fst_562_);
lean_dec(v_snd_560_);
v___x_563_ = lean_nat_add(v___x_556_, v_fst_561_);
lean_dec(v_fst_561_);
v___x_564_ = lean_nat_dec_le(v___x_556_, v___x_521_);
if (v___x_564_ == 0)
{
v___y_508_ = v___x_563_;
v___y_509_ = v_array_538_;
v___y_510_ = v___x_540_;
v___y_511_ = v_fst_562_;
v___y_512_ = v_val_537_;
v___y_513_ = v___x_556_;
goto v___jp_507_;
}
else
{
lean_dec(v___x_556_);
v___y_508_ = v___x_563_;
v___y_509_ = v_array_538_;
v___y_510_ = v___x_540_;
v___y_511_ = v_fst_562_;
v___y_512_ = v_val_537_;
v___y_513_ = v___x_521_;
goto v___jp_507_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_569_; lean_object* v___x_571_; 
lean_dec(v___x_536_);
v___x_569_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1));
if (v_isShared_530_ == 0)
{
lean_ctor_set_tag(v___x_529_, 1);
lean_ctor_set(v___x_529_, 1, v___x_569_);
lean_ctor_set(v___x_529_, 0, v_fst_525_);
v___x_571_ = v___x_529_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_fst_525_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
v___jp_575_:
{
uint8_t v___x_577_; 
v___x_577_ = lean_nat_dec_le(v___x_573_, v___x_574_);
if (v___x_577_ == 0)
{
lean_dec(v___x_573_);
v_lower_532_ = v___y_576_;
v_upper_533_ = v___x_574_;
goto v___jp_531_;
}
else
{
v_lower_532_ = v___y_576_;
v_upper_533_ = v___x_573_;
goto v___jp_531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___boxed(lean_object* v_config_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(v_config_580_, v_a_581_);
lean_dec_ref(v_config_580_);
return v_res_582_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(uint8_t v_x_583_){
_start:
{
uint8_t v___x_594_; uint8_t v___x_595_; 
v___x_594_ = 58;
v___x_595_ = lean_uint8_dec_eq(v_x_583_, v___x_594_);
if (v___x_595_ == 0)
{
uint8_t v___x_596_; uint8_t v___x_597_; 
v___x_596_ = 46;
v___x_597_ = lean_uint8_dec_eq(v_x_583_, v___x_596_);
if (v___x_597_ == 0)
{
uint8_t v___x_598_; uint8_t v___x_599_; 
v___x_598_ = 48;
v___x_599_ = lean_uint8_dec_le(v___x_598_, v_x_583_);
if (v___x_599_ == 0)
{
goto v___jp_589_;
}
else
{
uint8_t v___x_600_; uint8_t v___x_601_; 
v___x_600_ = 57;
v___x_601_ = lean_uint8_dec_le(v_x_583_, v___x_600_);
if (v___x_601_ == 0)
{
goto v___jp_589_;
}
else
{
return v___x_601_;
}
}
}
else
{
return v___x_597_;
}
}
else
{
return v___x_595_;
}
v___jp_584_:
{
uint8_t v___x_585_; uint8_t v___x_586_; 
v___x_585_ = 65;
v___x_586_ = lean_uint8_dec_le(v___x_585_, v_x_583_);
if (v___x_586_ == 0)
{
return v___x_586_;
}
else
{
uint8_t v___x_587_; uint8_t v___x_588_; 
v___x_587_ = 70;
v___x_588_ = lean_uint8_dec_le(v_x_583_, v___x_587_);
return v___x_588_;
}
}
v___jp_589_:
{
uint8_t v___x_590_; uint8_t v___x_591_; 
v___x_590_ = 97;
v___x_591_ = lean_uint8_dec_le(v___x_590_, v_x_583_);
if (v___x_591_ == 0)
{
goto v___jp_584_;
}
else
{
uint8_t v___x_592_; uint8_t v___x_593_; 
v___x_592_ = 102;
v___x_593_ = lean_uint8_dec_le(v_x_583_, v___x_592_);
if (v___x_593_ == 0)
{
goto v___jp_584_;
}
else
{
return v___x_593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___boxed(lean_object* v_x_602_){
_start:
{
uint8_t v_x_boxed_603_; uint8_t v_res_604_; lean_object* v_r_605_; 
v_x_boxed_603_ = lean_unbox(v_x_602_);
v_res_604_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(v_x_boxed_603_);
v_r_605_ = lean_box(v_res_604_);
return v_r_605_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(lean_object* v_a_617_){
_start:
{
lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v_array_628_; lean_object* v_idx_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v_array_628_ = lean_ctor_get(v_a_617_, 0);
v_idx_629_ = lean_ctor_get(v_a_617_, 1);
v___x_630_ = lean_byte_array_size(v_array_628_);
v___x_631_ = lean_nat_dec_lt(v_idx_629_, v___x_630_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_box(0);
v___x_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_633_, 0, v_a_617_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
return v___x_633_;
}
else
{
uint8_t v___x_634_; uint8_t v_got_635_; uint8_t v___x_636_; 
v___x_634_ = 91;
v_got_635_ = lean_byte_array_fget(v_array_628_, v_idx_629_);
v___x_636_ = lean_uint8_dec_eq(v_got_635_, v___x_634_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_638_, 0, v_a_617_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
return v___x_638_;
}
else
{
lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_714_; 
lean_inc(v_idx_629_);
lean_inc_ref(v_array_628_);
v_isSharedCheck_714_ = !lean_is_exclusive(v_a_617_);
if (v_isSharedCheck_714_ == 0)
{
lean_object* v_unused_715_; lean_object* v_unused_716_; 
v_unused_715_ = lean_ctor_get(v_a_617_, 1);
lean_dec(v_unused_715_);
v_unused_716_ = lean_ctor_get(v_a_617_, 0);
lean_dec(v_unused_716_);
v___x_640_ = v_a_617_;
v_isShared_641_ = v_isSharedCheck_714_;
goto v_resetjp_639_;
}
else
{
lean_dec(v_a_617_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_714_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___f_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_646_; 
v___f_642_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3));
v___x_643_ = lean_unsigned_to_nat(1u);
v___x_644_ = lean_nat_add(v_idx_629_, v___x_643_);
lean_dec(v_idx_629_);
lean_inc(v___x_644_);
lean_inc_ref(v_array_628_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v___x_644_);
v___x_646_ = v___x_640_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_array_628_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v___x_644_);
v___x_646_ = v_reuseFailAlloc_713_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v_snd_650_; lean_object* v_fst_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_712_; 
v___x_647_ = lean_unsigned_to_nat(256u);
v___x_648_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___x_646_);
v___x_649_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_642_, v___x_647_, v___x_648_, v___x_646_);
v_snd_650_ = lean_ctor_get(v___x_649_, 1);
v_fst_651_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_712_ == 0)
{
v___x_653_ = v___x_649_;
v_isShared_654_ = v_isSharedCheck_712_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_snd_650_);
lean_inc(v_fst_651_);
lean_dec(v___x_649_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_712_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v_fst_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_710_; 
v_fst_655_ = lean_ctor_get(v_snd_650_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v_snd_650_);
if (v_isSharedCheck_710_ == 0)
{
lean_object* v_unused_711_; 
v_unused_711_ = lean_ctor_get(v_snd_650_, 1);
lean_dec(v_unused_711_);
v___x_657_ = v_snd_650_;
v_isShared_658_ = v_isSharedCheck_710_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_fst_655_);
lean_dec(v_snd_650_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_710_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___y_660_; uint8_t v___x_694_; 
v___x_694_ = lean_nat_dec_eq(v_fst_651_, v___x_648_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___y_697_; uint8_t v___x_705_; 
lean_dec_ref(v___x_646_);
v___x_695_ = lean_nat_add(v___x_644_, v_fst_651_);
lean_dec(v_fst_651_);
v___x_705_ = lean_nat_dec_le(v___x_644_, v___x_648_);
if (v___x_705_ == 0)
{
v___y_697_ = v___x_644_;
goto v___jp_696_;
}
else
{
lean_dec(v___x_644_);
v___y_697_ = v___x_648_;
goto v___jp_696_;
}
v___jp_696_:
{
uint8_t v___x_698_; 
v___x_698_ = lean_nat_dec_le(v___x_695_, v___x_630_);
if (v___x_698_ == 0)
{
lean_object* v___x_700_; 
lean_dec(v___x_695_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 1, v___x_630_);
lean_ctor_set(v___x_653_, 0, v___y_697_);
v___x_700_ = v___x_653_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___y_697_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v___x_630_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
v___y_660_ = v___x_700_;
goto v___jp_659_;
}
}
else
{
lean_object* v___x_703_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 1, v___x_695_);
lean_ctor_set(v___x_653_, 0, v___y_697_);
v___x_703_ = v___x_653_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___y_697_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v___x_695_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
v___y_660_ = v___x_703_;
goto v___jp_659_;
}
}
}
}
else
{
lean_object* v___x_706_; lean_object* v___x_708_; 
lean_del_object(v___x_657_);
lean_dec(v_fst_655_);
lean_dec(v_fst_651_);
lean_dec(v___x_644_);
lean_dec_ref(v_array_628_);
v___x_706_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7));
if (v_isShared_654_ == 0)
{
lean_ctor_set_tag(v___x_653_, 1);
lean_ctor_set(v___x_653_, 1, v___x_706_);
lean_ctor_set(v___x_653_, 0, v___x_646_);
v___x_708_ = v___x_653_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_646_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
v___jp_659_:
{
lean_object* v_array_661_; lean_object* v_idx_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v_array_661_ = lean_ctor_get(v_fst_655_, 0);
v_idx_662_ = lean_ctor_get(v_fst_655_, 1);
v___x_663_ = lean_byte_array_size(v_array_661_);
v___x_664_ = lean_nat_dec_lt(v_idx_662_, v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_667_; 
lean_dec_ref(v___y_660_);
lean_dec_ref(v_array_628_);
v___x_665_ = lean_box(0);
if (v_isShared_658_ == 0)
{
lean_ctor_set_tag(v___x_657_, 1);
lean_ctor_set(v___x_657_, 1, v___x_665_);
v___x_667_ = v___x_657_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_fst_655_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
else
{
uint8_t v___x_669_; uint8_t v_got_670_; uint8_t v___x_671_; 
v___x_669_ = 93;
v_got_670_ = lean_byte_array_fget(v_array_661_, v_idx_662_);
v___x_671_ = lean_uint8_dec_eq(v_got_670_, v___x_669_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; lean_object* v___x_674_; 
lean_dec_ref(v___y_660_);
lean_dec_ref(v_array_628_);
v___x_672_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5));
if (v_isShared_658_ == 0)
{
lean_ctor_set_tag(v___x_657_, 1);
lean_ctor_set(v___x_657_, 1, v___x_672_);
v___x_674_ = v___x_657_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_fst_655_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v___x_672_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
else
{
lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_691_; 
lean_inc(v_idx_662_);
lean_inc_ref(v_array_661_);
lean_del_object(v___x_657_);
v_isSharedCheck_691_ = !lean_is_exclusive(v_fst_655_);
if (v_isSharedCheck_691_ == 0)
{
lean_object* v_unused_692_; lean_object* v_unused_693_; 
v_unused_692_ = lean_ctor_get(v_fst_655_, 1);
lean_dec(v_unused_692_);
v_unused_693_ = lean_ctor_get(v_fst_655_, 0);
lean_dec(v_unused_693_);
v___x_677_ = v_fst_655_;
v_isShared_678_ = v_isSharedCheck_691_;
goto v_resetjp_676_;
}
else
{
lean_dec(v_fst_655_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_691_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v_lower_679_; lean_object* v_upper_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_684_; 
v_lower_679_ = lean_ctor_get(v___y_660_, 0);
lean_inc(v_lower_679_);
v_upper_680_ = lean_ctor_get(v___y_660_, 1);
lean_inc(v_upper_680_);
lean_dec_ref(v___y_660_);
v___x_681_ = l_ByteArray_toByteSlice(v_array_628_, v_lower_679_, v_upper_680_);
v___x_682_ = lean_nat_add(v_idx_662_, v___x_643_);
lean_dec(v_idx_662_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 1, v___x_682_);
v___x_684_ = v___x_677_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_array_661_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v___x_682_);
v___x_684_ = v_reuseFailAlloc_690_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_685_ = l_ByteSlice_toByteArray(v___x_681_);
v___x_686_ = lean_string_validate_utf8(v___x_685_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; lean_object* v___x_688_; 
lean_dec_ref(v___x_685_);
v___x_687_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_688_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_687_);
v___y_619_ = v___x_684_;
v___y_620_ = v___x_688_;
goto v___jp_618_;
}
else
{
lean_object* v___x_689_; 
v___x_689_ = lean_string_from_utf8_unchecked(v___x_685_);
v___y_619_ = v___x_684_;
v___y_620_ = v___x_689_;
goto v___jp_618_;
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_618_:
{
lean_object* v___x_621_; 
v___x_621_ = lean_uv_pton_v6(v___y_620_);
if (lean_obj_tag(v___x_621_) == 1)
{
lean_object* v_val_622_; lean_object* v___x_623_; 
lean_dec_ref(v___y_620_);
v_val_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_val_622_);
lean_dec_ref_known(v___x_621_, 1);
v___x_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_623_, 0, v___y_619_);
lean_ctor_set(v___x_623_, 1, v_val_622_);
return v___x_623_;
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
lean_dec(v___x_621_);
v___x_624_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__0));
v___x_625_ = lean_string_append(v___x_624_, v___y_620_);
lean_dec_ref(v___y_620_);
v___x_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
v___x_627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_627_, 0, v___y_619_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
return v___x_627_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0(uint8_t v_x_717_){
_start:
{
uint8_t v___x_718_; uint8_t v___x_719_; 
v___x_718_ = 46;
v___x_719_ = lean_uint8_dec_eq(v_x_717_, v___x_718_);
if (v___x_719_ == 0)
{
uint8_t v___x_720_; uint8_t v___x_721_; 
v___x_720_ = 48;
v___x_721_ = lean_uint8_dec_le(v___x_720_, v_x_717_);
if (v___x_721_ == 0)
{
return v___x_721_;
}
else
{
uint8_t v___x_722_; uint8_t v___x_723_; 
v___x_722_ = 57;
v___x_723_ = lean_uint8_dec_le(v_x_717_, v___x_722_);
return v___x_723_;
}
}
else
{
return v___x_719_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0___boxed(lean_object* v_x_724_){
_start:
{
uint8_t v_x_boxed_725_; uint8_t v_res_726_; lean_object* v_r_727_; 
v_x_boxed_725_ = lean_unbox(v_x_724_);
v_res_726_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0(v_x_boxed_725_);
v_r_727_ = lean_box(v_res_726_);
return v_r_727_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(lean_object* v_a_730_){
_start:
{
lean_object* v___f_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v_snd_735_; lean_object* v_fst_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_781_; 
v___f_731_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__0));
v___x_732_ = lean_unsigned_to_nat(256u);
v___x_733_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_730_);
v___x_734_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_731_, v___x_732_, v___x_733_, v_a_730_);
v_snd_735_ = lean_ctor_get(v___x_734_, 1);
v_fst_736_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_781_ == 0)
{
v___x_738_ = v___x_734_;
v_isShared_739_ = v_isSharedCheck_781_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_snd_735_);
lean_inc(v_fst_736_);
lean_dec(v___x_734_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_781_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v_fst_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_779_; 
v_fst_740_ = lean_ctor_get(v_snd_735_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v_snd_735_);
if (v_isSharedCheck_779_ == 0)
{
lean_object* v_unused_780_; 
v_unused_780_ = lean_ctor_get(v_snd_735_, 1);
lean_dec(v_unused_780_);
v___x_742_ = v_snd_735_;
v_isShared_743_ = v_isSharedCheck_779_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_fst_740_);
lean_dec(v_snd_735_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_779_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___y_745_; uint8_t v___x_757_; 
v___x_757_ = lean_nat_dec_eq(v_fst_736_, v___x_733_);
if (v___x_757_ == 0)
{
lean_object* v_array_758_; lean_object* v_idx_759_; lean_object* v_lower_761_; lean_object* v_upper_762_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___y_772_; uint8_t v___x_774_; 
lean_del_object(v___x_738_);
v_array_758_ = lean_ctor_get(v_a_730_, 0);
lean_inc_ref(v_array_758_);
v_idx_759_ = lean_ctor_get(v_a_730_, 1);
lean_inc(v_idx_759_);
lean_dec_ref(v_a_730_);
v___x_769_ = lean_nat_add(v_idx_759_, v_fst_736_);
lean_dec(v_fst_736_);
v___x_770_ = lean_byte_array_size(v_array_758_);
v___x_774_ = lean_nat_dec_le(v_idx_759_, v___x_733_);
if (v___x_774_ == 0)
{
v___y_772_ = v_idx_759_;
goto v___jp_771_;
}
else
{
lean_dec(v_idx_759_);
v___y_772_ = v___x_733_;
goto v___jp_771_;
}
v___jp_760_:
{
lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_763_ = l_ByteArray_toByteSlice(v_array_758_, v_lower_761_, v_upper_762_);
v___x_764_ = l_ByteSlice_toByteArray(v___x_763_);
v___x_765_ = lean_string_validate_utf8(v___x_764_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; lean_object* v___x_767_; 
lean_dec_ref(v___x_764_);
v___x_766_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_767_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_766_);
v___y_745_ = v___x_767_;
goto v___jp_744_;
}
else
{
lean_object* v___x_768_; 
v___x_768_ = lean_string_from_utf8_unchecked(v___x_764_);
v___y_745_ = v___x_768_;
goto v___jp_744_;
}
}
v___jp_771_:
{
uint8_t v___x_773_; 
v___x_773_ = lean_nat_dec_le(v___x_769_, v___x_770_);
if (v___x_773_ == 0)
{
lean_dec(v___x_769_);
v_lower_761_ = v___y_772_;
v_upper_762_ = v___x_770_;
goto v___jp_760_;
}
else
{
v_lower_761_ = v___y_772_;
v_upper_762_ = v___x_769_;
goto v___jp_760_;
}
}
}
else
{
lean_object* v___x_775_; lean_object* v___x_777_; 
lean_del_object(v___x_742_);
lean_dec(v_fst_740_);
lean_dec(v_fst_736_);
v___x_775_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7));
if (v_isShared_739_ == 0)
{
lean_ctor_set_tag(v___x_738_, 1);
lean_ctor_set(v___x_738_, 1, v___x_775_);
lean_ctor_set(v___x_738_, 0, v_a_730_);
v___x_777_ = v___x_738_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_730_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
v___jp_744_:
{
lean_object* v___x_746_; 
v___x_746_ = lean_uv_pton_v4(v___y_745_);
if (lean_obj_tag(v___x_746_) == 1)
{
lean_object* v_val_747_; lean_object* v___x_749_; 
lean_dec_ref(v___y_745_);
v_val_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_val_747_);
lean_dec_ref_known(v___x_746_, 1);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 1, v_val_747_);
v___x_749_ = v___x_742_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_fst_740_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_val_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
else
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
lean_dec(v___x_746_);
v___x_751_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__1));
v___x_752_ = lean_string_append(v___x_751_, v___y_745_);
lean_dec_ref(v___y_745_);
v___x_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
if (v_isShared_743_ == 0)
{
lean_ctor_set_tag(v___x_742_, 1);
lean_ctor_set(v___x_742_, 1, v___x_753_);
v___x_755_ = v___x_742_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_fst_740_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg(){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0));
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___boxed(lean_object* v___dummy_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg();
return v_res_787_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0(void){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg();
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(lean_object* v_s_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___boxed(lean_object* v_s_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(v_s_791_);
lean_dec_ref(v_s_791_);
return v_res_792_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(uint8_t v___x_793_, uint8_t v_x_794_){
_start:
{
uint8_t v___x_810_; uint8_t v___x_811_; 
v___x_810_ = 48;
v___x_811_ = lean_uint8_dec_le(v___x_810_, v_x_794_);
if (v___x_811_ == 0)
{
goto v___jp_805_;
}
else
{
uint8_t v___x_812_; uint8_t v___x_813_; 
v___x_812_ = 57;
v___x_813_ = lean_uint8_dec_le(v_x_794_, v___x_812_);
if (v___x_813_ == 0)
{
goto v___jp_805_;
}
else
{
return v___x_793_;
}
}
v___jp_795_:
{
uint8_t v___x_796_; uint8_t v___x_797_; 
v___x_796_ = 45;
v___x_797_ = lean_uint8_dec_eq(v_x_794_, v___x_796_);
if (v___x_797_ == 0)
{
uint8_t v___x_798_; uint8_t v___x_799_; 
v___x_798_ = 46;
v___x_799_ = lean_uint8_dec_eq(v_x_794_, v___x_798_);
return v___x_799_;
}
else
{
return v___x_793_;
}
}
v___jp_800_:
{
uint8_t v___x_801_; uint8_t v___x_802_; 
v___x_801_ = 65;
v___x_802_ = lean_uint8_dec_le(v___x_801_, v_x_794_);
if (v___x_802_ == 0)
{
goto v___jp_795_;
}
else
{
uint8_t v___x_803_; uint8_t v___x_804_; 
v___x_803_ = 90;
v___x_804_ = lean_uint8_dec_le(v_x_794_, v___x_803_);
if (v___x_804_ == 0)
{
goto v___jp_795_;
}
else
{
return v___x_793_;
}
}
}
v___jp_805_:
{
uint8_t v___x_806_; uint8_t v___x_807_; 
v___x_806_ = 97;
v___x_807_ = lean_uint8_dec_le(v___x_806_, v_x_794_);
if (v___x_807_ == 0)
{
goto v___jp_800_;
}
else
{
uint8_t v___x_808_; uint8_t v___x_809_; 
v___x_808_ = 122;
v___x_809_ = lean_uint8_dec_le(v_x_794_, v___x_808_);
if (v___x_809_ == 0)
{
goto v___jp_800_;
}
else
{
return v___x_793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed(lean_object* v___x_814_, lean_object* v_x_815_){
_start:
{
uint8_t v___x_12906__boxed_816_; uint8_t v_x_boxed_817_; uint8_t v_res_818_; lean_object* v_r_819_; 
v___x_12906__boxed_816_ = lean_unbox(v___x_814_);
v_x_boxed_817_ = lean_unbox(v_x_815_);
v_res_818_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(v___x_12906__boxed_816_, v_x_boxed_817_);
v_r_819_ = lean_box(v_res_818_);
return v_r_819_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(lean_object* v___x_820_, lean_object* v___x_821_, lean_object* v_a_822_, uint8_t v_b_823_){
_start:
{
if (lean_obj_tag(v_a_822_) == 0)
{
lean_object* v_currPos_824_; lean_object* v_searcher_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_839_; 
v_currPos_824_ = lean_ctor_get(v_a_822_, 0);
v_searcher_825_ = lean_ctor_get(v_a_822_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v_a_822_);
if (v_isSharedCheck_839_ == 0)
{
v___x_827_ = v_a_822_;
v_isShared_828_ = v_isSharedCheck_839_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_searcher_825_);
lean_inc(v_currPos_824_);
lean_dec(v_a_822_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_839_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
uint8_t v___x_829_; uint8_t v_decide_830_; 
v___x_829_ = 0;
v_decide_830_ = lean_nat_dec_eq(v_searcher_825_, v___x_821_);
if (v_decide_830_ == 0)
{
uint32_t v___x_831_; uint32_t v___x_832_; uint8_t v___x_833_; 
v___x_831_ = 46;
v___x_832_ = lean_string_utf8_get_fast(v___x_820_, v_searcher_825_);
v___x_833_ = lean_uint32_dec_eq(v___x_832_, v___x_831_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_834_ = lean_string_utf8_next_fast(v___x_820_, v_searcher_825_);
lean_dec(v_searcher_825_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 1, v___x_834_);
v___x_836_ = v___x_827_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_currPos_824_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v___x_834_);
v___x_836_ = v_reuseFailAlloc_838_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
v_a_822_ = v___x_836_;
goto _start;
}
}
else
{
lean_del_object(v___x_827_);
lean_dec(v_searcher_825_);
lean_dec(v_currPos_824_);
return v___x_829_;
}
}
else
{
lean_del_object(v___x_827_);
lean_dec(v_searcher_825_);
lean_dec(v_currPos_824_);
return v___x_829_;
}
}
}
else
{
return v_b_823_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg___boxed(lean_object* v___x_840_, lean_object* v___x_841_, lean_object* v_a_842_, lean_object* v_b_843_){
_start:
{
uint8_t v_b_boxed_844_; uint8_t v_res_845_; lean_object* v_r_846_; 
v_b_boxed_844_ = lean_unbox(v_b_843_);
v_res_845_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_840_, v___x_841_, v_a_842_, v_b_boxed_844_);
lean_dec(v___x_841_);
lean_dec_ref(v___x_840_);
v_r_846_ = lean_box(v_res_845_);
return v_r_846_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(uint8_t v___x_847_, lean_object* v___x_848_, lean_object* v___x_849_, lean_object* v___x_850_, lean_object* v_a_851_, uint8_t v_b_852_){
_start:
{
uint8_t v___y_854_; lean_object* v_it_855_; lean_object* v_startInclusive_856_; lean_object* v_endExclusive_857_; uint8_t v___y_862_; 
if (v___x_847_ == 0)
{
uint8_t v___x_888_; 
v___x_888_ = 1;
v___y_862_ = v___x_888_;
goto v___jp_861_;
}
else
{
uint8_t v___x_889_; 
v___x_889_ = 0;
v___y_862_ = v___x_889_;
goto v___jp_861_;
}
v___jp_853_:
{
lean_object* v___x_858_; uint8_t v___x_859_; 
v___x_858_ = lean_string_utf8_extract_fast(v___x_848_, v_startInclusive_856_, v_endExclusive_857_);
lean_dec(v_endExclusive_857_);
lean_dec(v_startInclusive_856_);
v___x_859_ = l_Std_Http_URI_isValidDomainLabel(v___x_858_);
if (v___x_859_ == 0)
{
lean_dec(v_it_855_);
lean_dec(v___x_850_);
return v___x_859_;
}
else
{
v_a_851_ = v_it_855_;
v_b_852_ = v___y_854_;
goto _start;
}
}
v___jp_861_:
{
if (lean_obj_tag(v_a_851_) == 0)
{
lean_object* v_currPos_863_; lean_object* v_searcher_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_887_; 
v_currPos_863_ = lean_ctor_get(v_a_851_, 0);
v_searcher_864_ = lean_ctor_get(v_a_851_, 1);
v_isSharedCheck_887_ = !lean_is_exclusive(v_a_851_);
if (v_isSharedCheck_887_ == 0)
{
v___x_866_ = v_a_851_;
v_isShared_867_ = v_isSharedCheck_887_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_searcher_864_);
lean_inc(v_currPos_863_);
lean_dec(v_a_851_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_887_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
uint8_t v_decide_868_; 
v_decide_868_ = lean_nat_dec_eq(v_searcher_864_, v___x_850_);
if (v_decide_868_ == 0)
{
uint32_t v___x_869_; uint32_t v___x_870_; uint8_t v___x_871_; 
v___x_869_ = 46;
v___x_870_ = lean_string_utf8_get_fast(v___x_848_, v_searcher_864_);
v___x_871_ = lean_uint32_dec_eq(v___x_870_, v___x_869_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_872_ = lean_string_utf8_next_fast(v___x_848_, v_searcher_864_);
lean_dec(v_searcher_864_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 1, v___x_872_);
v___x_874_ = v___x_866_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_currPos_863_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v___x_872_);
v___x_874_ = v_reuseFailAlloc_876_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
v_a_851_ = v___x_874_;
goto _start;
}
}
else
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v_slice_880_; lean_object* v_nextIt_882_; 
v___x_877_ = lean_string_utf8_next_fast(v___x_848_, v_searcher_864_);
v___x_878_ = lean_nat_sub(v___x_877_, v_searcher_864_);
v___x_879_ = lean_nat_add(v_searcher_864_, v___x_878_);
lean_dec(v___x_878_);
v_slice_880_ = l_String_Slice_subslice_x21(v___x_849_, v_currPos_863_, v_searcher_864_);
lean_inc(v___x_879_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 1, v___x_879_);
lean_ctor_set(v___x_866_, 0, v___x_879_);
v_nextIt_882_ = v___x_866_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v___x_879_);
v_nextIt_882_ = v_reuseFailAlloc_885_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v_startInclusive_883_; lean_object* v_endExclusive_884_; 
v_startInclusive_883_ = lean_ctor_get(v_slice_880_, 0);
lean_inc(v_startInclusive_883_);
v_endExclusive_884_ = lean_ctor_get(v_slice_880_, 1);
lean_inc(v_endExclusive_884_);
lean_dec_ref(v_slice_880_);
v___y_854_ = v___y_862_;
v_it_855_ = v_nextIt_882_;
v_startInclusive_856_ = v_startInclusive_883_;
v_endExclusive_857_ = v_endExclusive_884_;
goto v___jp_853_;
}
}
}
else
{
lean_object* v___x_886_; 
lean_del_object(v___x_866_);
lean_dec(v_searcher_864_);
v___x_886_ = lean_box(1);
lean_inc(v___x_850_);
v___y_854_ = v___y_862_;
v_it_855_ = v___x_886_;
v_startInclusive_856_ = v_currPos_863_;
v_endExclusive_857_ = v___x_850_;
goto v___jp_853_;
}
}
}
else
{
lean_dec(v___x_850_);
return v_b_852_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg___boxed(lean_object* v___x_890_, lean_object* v___x_891_, lean_object* v___x_892_, lean_object* v___x_893_, lean_object* v_a_894_, lean_object* v_b_895_){
_start:
{
uint8_t v___x_12985__boxed_896_; uint8_t v_b_boxed_897_; uint8_t v_res_898_; lean_object* v_r_899_; 
v___x_12985__boxed_896_ = lean_unbox(v___x_890_);
v_b_boxed_897_ = lean_unbox(v_b_895_);
v_res_898_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_12985__boxed_896_, v___x_891_, v___x_892_, v___x_893_, v_a_894_, v_b_boxed_897_);
lean_dec_ref(v___x_892_);
lean_dec_ref(v___x_891_);
v_r_899_ = lean_box(v_res_898_);
return v_r_899_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(lean_object* v_config_907_, lean_object* v_a_908_){
_start:
{
lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; uint8_t v___y_920_; lean_object* v___y_924_; lean_object* v___y_925_; uint8_t v___y_926_; uint8_t v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; uint8_t v___y_933_; lean_object* v___y_940_; lean_object* v___y_941_; uint8_t v___y_942_; lean_object* v___y_943_; lean_object* v_lower_944_; lean_object* v_upper_945_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; uint8_t v___y_963_; lean_object* v___y_964_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_991_; lean_object* v_pos_992_; lean_object* v___y_1016_; lean_object* v_pos_1017_; lean_object* v_res_1018_; lean_object* v_array_1019_; lean_object* v_idx_1020_; lean_object* v_pos_1022_; lean_object* v_res_1023_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v_array_1019_ = lean_ctor_get(v_a_908_, 0);
v_idx_1020_ = lean_ctor_get(v_a_908_, 1);
v___x_1032_ = lean_byte_array_size(v_array_1019_);
v___x_1033_ = lean_nat_dec_lt(v_idx_1020_, v___x_1032_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; 
lean_inc(v_idx_1020_);
lean_inc_ref(v_array_1019_);
v___x_1034_ = lean_box(0);
v_pos_1022_ = v_a_908_;
v_res_1023_ = v___x_1034_;
goto v___jp_1021_;
}
else
{
uint8_t v___x_1035_; uint8_t v___x_1036_; uint8_t v___x_1037_; 
v___x_1035_ = lean_byte_array_fget(v_array_1019_, v_idx_1020_);
v___x_1036_ = 91;
v___x_1037_ = lean_uint8_dec_eq(v___x_1035_, v___x_1036_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; 
lean_inc(v_idx_1020_);
lean_inc_ref(v_array_1019_);
v___x_1038_ = lean_box(0);
v_pos_1022_ = v_a_908_;
v_res_1023_ = v___x_1038_;
goto v___jp_1021_;
}
else
{
lean_object* v___x_1039_; 
v___x_1039_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(v_a_908_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_pos_1040_; lean_object* v_res_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1049_; 
v_pos_1040_ = lean_ctor_get(v___x_1039_, 0);
v_res_1041_ = lean_ctor_get(v___x_1039_, 1);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1043_ = v___x_1039_;
v_isShared_1044_ = v_isSharedCheck_1049_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_res_1041_);
lean_inc(v_pos_1040_);
lean_dec(v___x_1039_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1049_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1045_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1045_, 0, v_res_1041_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 1, v___x_1045_);
v___x_1047_ = v___x_1043_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_pos_1040_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
else
{
lean_object* v_pos_1050_; lean_object* v_err_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
v_pos_1050_ = lean_ctor_get(v___x_1039_, 0);
v_err_1051_ = lean_ctor_get(v___x_1039_, 1);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1039_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_err_1051_);
lean_inc(v_pos_1050_);
lean_dec(v___x_1039_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_pos_1050_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_err_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
}
v___jp_909_:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_912_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0));
v___x_913_ = lean_string_append(v___x_912_, v___y_910_);
lean_dec_ref(v___y_910_);
v___x_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
v___x_915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_915_, 0, v___y_911_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
return v___x_915_;
}
v___jp_916_:
{
if (v___y_920_ == 0)
{
lean_dec_ref(v___y_919_);
v___y_910_ = v___y_917_;
v___y_911_ = v___y_918_;
goto v___jp_909_;
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; 
lean_dec_ref(v___y_917_);
v___x_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_921_, 0, v___y_919_);
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v___y_918_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
return v___x_922_;
}
}
v___jp_923_:
{
if (v___y_933_ == 0)
{
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_924_);
v___y_910_ = v___y_925_;
v___y_911_ = v___y_928_;
goto v___jp_909_;
}
else
{
uint8_t v___x_934_; 
lean_inc(v___y_930_);
v___x_934_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___y_926_, v___y_931_, v___y_929_, v___y_930_, v___y_932_, v___y_933_);
lean_dec_ref(v___y_929_);
if (v___x_934_ == 0)
{
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec(v___y_924_);
v___y_910_ = v___y_925_;
v___y_911_ = v___y_928_;
goto v___jp_909_;
}
else
{
lean_object* v___x_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v___x_935_ = lean_string_length(v___y_931_);
v___x_936_ = lean_unsigned_to_nat(255u);
v___x_937_ = lean_nat_dec_le(v___x_935_, v___x_936_);
if (v___x_937_ == 0)
{
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec(v___y_924_);
v___y_910_ = v___y_925_;
v___y_911_ = v___y_928_;
goto v___jp_909_;
}
else
{
uint8_t v___x_938_; 
v___x_938_ = lean_nat_dec_eq(v___y_930_, v___y_924_);
lean_dec(v___y_924_);
lean_dec(v___y_930_);
if (v___x_938_ == 0)
{
v___y_917_ = v___y_925_;
v___y_918_ = v___y_928_;
v___y_919_ = v___y_931_;
v___y_920_ = v___x_937_;
goto v___jp_916_;
}
else
{
v___y_917_ = v___y_925_;
v___y_918_ = v___y_928_;
v___y_919_ = v___y_931_;
v___y_920_ = v___y_927_;
goto v___jp_916_;
}
}
}
}
}
v___jp_939_:
{
lean_object* v___x_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
v___x_946_ = l_ByteArray_toByteSlice(v___y_941_, v_lower_944_, v_upper_945_);
v___x_947_ = l_ByteSlice_toByteArray(v___x_946_);
v___x_948_ = lean_string_validate_utf8(v___x_947_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; lean_object* v___x_950_; 
lean_dec_ref(v___x_947_);
lean_dec(v___y_940_);
v___x_949_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2));
v___x_950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_950_, 0, v___y_943_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
return v___x_950_;
}
else
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; uint8_t v___x_956_; 
v___x_951_ = lean_string_from_utf8_unchecked(v___x_947_);
lean_inc_n(v___y_940_, 2);
lean_inc_ref(v___x_951_);
v___x_952_ = l_String_mapAux___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(v___x_951_, v___y_940_);
v___x_953_ = lean_string_utf8_byte_size(v___x_952_);
lean_inc_ref(v___x_952_);
v___x_954_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set(v___x_954_, 1, v___y_940_);
lean_ctor_set(v___x_954_, 2, v___x_953_);
v___x_955_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0);
v___x_956_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_952_, v___x_953_, v___x_955_, v___x_948_);
if (v___x_956_ == 0)
{
v___y_924_ = v___y_940_;
v___y_925_ = v___x_951_;
v___y_926_ = v___x_956_;
v___y_927_ = v___y_942_;
v___y_928_ = v___y_943_;
v___y_929_ = v___x_954_;
v___y_930_ = v___x_953_;
v___y_931_ = v___x_952_;
v___y_932_ = v___x_955_;
v___y_933_ = v___x_948_;
goto v___jp_923_;
}
else
{
v___y_924_ = v___y_940_;
v___y_925_ = v___x_951_;
v___y_926_ = v___x_956_;
v___y_927_ = v___y_942_;
v___y_928_ = v___y_943_;
v___y_929_ = v___x_954_;
v___y_930_ = v___x_953_;
v___y_931_ = v___x_952_;
v___y_932_ = v___x_955_;
v___y_933_ = v___y_942_;
goto v___jp_923_;
}
}
}
v___jp_957_:
{
uint8_t v___x_965_; 
v___x_965_ = lean_nat_dec_le(v___y_961_, v___y_959_);
if (v___x_965_ == 0)
{
lean_dec(v___y_961_);
v___y_940_ = v___y_958_;
v___y_941_ = v___y_960_;
v___y_942_ = v___y_963_;
v___y_943_ = v___y_962_;
v_lower_944_ = v___y_964_;
v_upper_945_ = v___y_959_;
goto v___jp_939_;
}
else
{
lean_dec(v___y_959_);
v___y_940_ = v___y_958_;
v___y_941_ = v___y_960_;
v___y_942_ = v___y_963_;
v___y_943_ = v___y_962_;
v_lower_944_ = v___y_964_;
v_upper_945_ = v___y_961_;
goto v___jp_939_;
}
}
v___jp_966_:
{
lean_object* v_maxHostLength_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v_snd_972_; lean_object* v_fst_973_; lean_object* v_fst_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_988_; 
v_maxHostLength_969_ = lean_ctor_get(v_config_907_, 1);
v___x_970_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___y_968_);
lean_inc_ref(v___y_967_);
v___x_971_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___y_967_, v_maxHostLength_969_, v___x_970_, v___y_968_);
v_snd_972_ = lean_ctor_get(v___x_971_, 1);
lean_inc(v_snd_972_);
v_fst_973_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_fst_973_);
lean_dec_ref(v___x_971_);
v_fst_974_ = lean_ctor_get(v_snd_972_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v_snd_972_);
if (v_isSharedCheck_988_ == 0)
{
lean_object* v_unused_989_; 
v_unused_989_ = lean_ctor_get(v_snd_972_, 1);
lean_dec(v_unused_989_);
v___x_976_ = v_snd_972_;
v_isShared_977_ = v_isSharedCheck_988_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_fst_974_);
lean_dec(v_snd_972_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_988_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
uint8_t v___x_978_; 
v___x_978_ = lean_nat_dec_eq(v_fst_973_, v___x_970_);
if (v___x_978_ == 0)
{
lean_object* v_array_979_; lean_object* v_idx_980_; lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
lean_del_object(v___x_976_);
v_array_979_ = lean_ctor_get(v___y_968_, 0);
lean_inc_ref(v_array_979_);
v_idx_980_ = lean_ctor_get(v___y_968_, 1);
lean_inc(v_idx_980_);
lean_dec_ref(v___y_968_);
v___x_981_ = lean_nat_add(v_idx_980_, v_fst_973_);
lean_dec(v_fst_973_);
v___x_982_ = lean_byte_array_size(v_array_979_);
v___x_983_ = lean_nat_dec_le(v_idx_980_, v___x_970_);
if (v___x_983_ == 0)
{
v___y_958_ = v___x_970_;
v___y_959_ = v___x_982_;
v___y_960_ = v_array_979_;
v___y_961_ = v___x_981_;
v___y_962_ = v_fst_974_;
v___y_963_ = v___x_978_;
v___y_964_ = v_idx_980_;
goto v___jp_957_;
}
else
{
lean_dec(v_idx_980_);
v___y_958_ = v___x_970_;
v___y_959_ = v___x_982_;
v___y_960_ = v_array_979_;
v___y_961_ = v___x_981_;
v___y_962_ = v_fst_974_;
v___y_963_ = v___x_978_;
v___y_964_ = v___x_970_;
goto v___jp_957_;
}
}
else
{
lean_object* v___x_984_; lean_object* v___x_986_; 
lean_dec(v_fst_974_);
lean_dec(v_fst_973_);
v___x_984_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7));
if (v_isShared_977_ == 0)
{
lean_ctor_set_tag(v___x_976_, 1);
lean_ctor_set(v___x_976_, 1, v___x_984_);
lean_ctor_set(v___x_976_, 0, v___y_968_);
v___x_986_ = v___x_976_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___y_968_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v___x_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
v___jp_990_:
{
lean_object* v___x_993_; 
lean_inc_ref(v_pos_992_);
v___x_993_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(v_pos_992_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_pos_994_; lean_object* v_res_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1003_; 
lean_dec_ref(v_pos_992_);
v_pos_994_ = lean_ctor_get(v___x_993_, 0);
v_res_995_ = lean_ctor_get(v___x_993_, 1);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_997_ = v___x_993_;
v_isShared_998_ = v_isSharedCheck_1003_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_res_995_);
lean_inc(v_pos_994_);
lean_dec(v___x_993_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1003_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; lean_object* v___x_1001_; 
v___x_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_999_, 0, v_res_995_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 1, v___x_999_);
v___x_1001_ = v___x_997_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_pos_994_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
else
{
lean_object* v_err_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1013_; 
v_err_1004_ = lean_ctor_get(v___x_993_, 1);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1013_ == 0)
{
lean_object* v_unused_1014_; 
v_unused_1014_ = lean_ctor_get(v___x_993_, 0);
lean_dec(v_unused_1014_);
v___x_1006_ = v___x_993_;
v_isShared_1007_ = v_isSharedCheck_1013_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_err_1004_);
lean_dec(v___x_993_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1013_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v_idx_1008_; uint8_t v___x_1009_; 
v_idx_1008_ = lean_ctor_get(v_pos_992_, 1);
v___x_1009_ = lean_nat_dec_eq(v_idx_1008_, v_idx_1008_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1011_; 
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v_pos_992_);
v___x_1011_ = v___x_1006_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_pos_992_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_err_1004_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
else
{
lean_del_object(v___x_1006_);
lean_dec(v_err_1004_);
v___y_967_ = v___y_991_;
v___y_968_ = v_pos_992_;
goto v___jp_966_;
}
}
}
}
v___jp_1015_:
{
v___y_967_ = v___y_1016_;
v___y_968_ = v_pos_1017_;
goto v___jp_966_;
}
v___jp_1021_:
{
lean_object* v___f_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; 
v___f_1024_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3));
v___x_1025_ = lean_byte_array_size(v_array_1019_);
v___x_1026_ = lean_nat_dec_lt(v_idx_1020_, v___x_1025_);
if (v___x_1026_ == 0)
{
lean_dec(v_idx_1020_);
lean_dec_ref(v_array_1019_);
v___y_1016_ = v___f_1024_;
v_pos_1017_ = v_pos_1022_;
v_res_1018_ = v_res_1023_;
goto v___jp_1015_;
}
else
{
uint8_t v___x_1027_; uint8_t v___x_1028_; uint8_t v___x_1029_; 
v___x_1027_ = lean_byte_array_fget(v_array_1019_, v_idx_1020_);
lean_dec(v_idx_1020_);
lean_dec_ref(v_array_1019_);
v___x_1028_ = 48;
v___x_1029_ = lean_uint8_dec_le(v___x_1028_, v___x_1027_);
if (v___x_1029_ == 0)
{
v___y_1016_ = v___f_1024_;
v_pos_1017_ = v_pos_1022_;
v_res_1018_ = v_res_1023_;
goto v___jp_1015_;
}
else
{
uint8_t v___x_1030_; uint8_t v___x_1031_; 
v___x_1030_ = 57;
v___x_1031_ = lean_uint8_dec_le(v___x_1027_, v___x_1030_);
if (v___x_1031_ == 0)
{
v___y_1016_ = v___f_1024_;
v_pos_1017_ = v_pos_1022_;
v_res_1018_ = v_res_1023_;
goto v___jp_1015_;
}
else
{
v___y_991_ = v___f_1024_;
v_pos_992_ = v_pos_1022_;
goto v___jp_990_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___boxed(lean_object* v_config_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_1059_, v_a_1060_);
lean_dec_ref(v_config_1059_);
return v_res_1061_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(lean_object* v___x_1062_, lean_object* v___x_1063_, lean_object* v___x_1064_, lean_object* v_inst_1065_, lean_object* v_R_1066_, lean_object* v_a_1067_, uint8_t v_b_1068_, lean_object* v_c_1069_){
_start:
{
uint8_t v___x_1070_; 
v___x_1070_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_1062_, v___x_1064_, v_a_1067_, v_b_1068_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___boxed(lean_object* v___x_1071_, lean_object* v___x_1072_, lean_object* v___x_1073_, lean_object* v_inst_1074_, lean_object* v_R_1075_, lean_object* v_a_1076_, lean_object* v_b_1077_, lean_object* v_c_1078_){
_start:
{
uint8_t v_b_boxed_1079_; uint8_t v_res_1080_; lean_object* v_r_1081_; 
v_b_boxed_1079_ = lean_unbox(v_b_1077_);
v_res_1080_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(v___x_1071_, v___x_1072_, v___x_1073_, v_inst_1074_, v_R_1075_, v_a_1076_, v_b_boxed_1079_, v_c_1078_);
lean_dec(v___x_1073_);
lean_dec_ref(v___x_1072_);
lean_dec_ref(v___x_1071_);
v_r_1081_ = lean_box(v_res_1080_);
return v_r_1081_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(uint8_t v___x_1082_, lean_object* v___x_1083_, lean_object* v___x_1084_, lean_object* v___x_1085_, lean_object* v_inst_1086_, lean_object* v_R_1087_, lean_object* v_a_1088_, uint8_t v_b_1089_, lean_object* v_c_1090_){
_start:
{
uint8_t v___x_1091_; 
v___x_1091_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_1082_, v___x_1083_, v___x_1084_, v___x_1085_, v_a_1088_, v_b_1089_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___boxed(lean_object* v___x_1092_, lean_object* v___x_1093_, lean_object* v___x_1094_, lean_object* v___x_1095_, lean_object* v_inst_1096_, lean_object* v_R_1097_, lean_object* v_a_1098_, lean_object* v_b_1099_, lean_object* v_c_1100_){
_start:
{
uint8_t v___x_13390__boxed_1101_; uint8_t v_b_boxed_1102_; uint8_t v_res_1103_; lean_object* v_r_1104_; 
v___x_13390__boxed_1101_ = lean_unbox(v___x_1092_);
v_b_boxed_1102_ = lean_unbox(v_b_1099_);
v_res_1103_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(v___x_13390__boxed_1101_, v___x_1093_, v___x_1094_, v___x_1095_, v_inst_1096_, v_R_1097_, v_a_1098_, v_b_boxed_1102_, v_c_1100_);
lean_dec_ref(v___x_1094_);
lean_dec_ref(v___x_1093_);
v_r_1104_ = lean_box(v_res_1103_);
return v_r_1104_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(lean_object* v_config_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v_port_1119_; lean_object* v___y_1120_; lean_object* v___y_1124_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; uint8_t v_val_1136_; uint8_t v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v_pos_1147_; lean_object* v_array_1148_; lean_object* v_idx_1149_; lean_object* v_res_1150_; uint8_t v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v_pos_1165_; lean_object* v_pos_1168_; lean_object* v_res_1169_; lean_object* v_pos_1234_; lean_object* v_res_1235_; lean_object* v_err_1238_; lean_object* v___x_1243_; 
lean_inc_ref(v_a_1115_);
v___x_1243_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(v_config_1114_, v_a_1115_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_pos_1244_; lean_object* v_res_1245_; lean_object* v_array_1246_; lean_object* v_idx_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1263_; 
v_pos_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_pos_1244_);
v_res_1245_ = lean_ctor_get(v___x_1243_, 1);
lean_inc(v_res_1245_);
lean_dec_ref_known(v___x_1243_, 2);
v_array_1246_ = lean_ctor_get(v_pos_1244_, 0);
v_idx_1247_ = lean_ctor_get(v_pos_1244_, 1);
v_isSharedCheck_1263_ = !lean_is_exclusive(v_pos_1244_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1249_ = v_pos_1244_;
v_isShared_1250_ = v_isSharedCheck_1263_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_idx_1247_);
lean_inc(v_array_1246_);
lean_dec(v_pos_1244_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1263_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1251_ = lean_byte_array_size(v_array_1246_);
v___x_1252_ = lean_nat_dec_lt(v_idx_1247_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; 
lean_del_object(v___x_1249_);
lean_dec(v_idx_1247_);
lean_dec_ref(v_array_1246_);
lean_dec(v_res_1245_);
v___x_1253_ = lean_box(0);
v_err_1238_ = v___x_1253_;
goto v___jp_1237_;
}
else
{
uint8_t v___x_1254_; uint8_t v_got_1255_; uint8_t v___x_1256_; 
v___x_1254_ = 64;
v_got_1255_ = lean_byte_array_fget(v_array_1246_, v_idx_1247_);
v___x_1256_ = lean_uint8_dec_eq(v_got_1255_, v___x_1254_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; 
lean_del_object(v___x_1249_);
lean_dec(v_idx_1247_);
lean_dec_ref(v_array_1246_);
lean_dec(v_res_1245_);
v___x_1257_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5));
v_err_1238_ = v___x_1257_;
goto v___jp_1237_;
}
else
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1261_; 
lean_dec_ref(v_a_1115_);
v___x_1258_ = lean_unsigned_to_nat(1u);
v___x_1259_ = lean_nat_add(v_idx_1247_, v___x_1258_);
lean_dec(v_idx_1247_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 1, v___x_1259_);
v___x_1261_ = v___x_1249_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_array_1246_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
v_pos_1234_ = v___x_1261_;
v_res_1235_ = v_res_1245_;
goto v___jp_1233_;
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_pos_1264_; lean_object* v_res_1265_; 
lean_dec_ref(v_a_1115_);
v_pos_1264_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_pos_1264_);
v_res_1265_ = lean_ctor_get(v___x_1243_, 1);
lean_inc(v_res_1265_);
lean_dec_ref_known(v___x_1243_, 2);
v_pos_1234_ = v_pos_1264_;
v_res_1235_ = v_res_1265_;
goto v___jp_1233_;
}
else
{
lean_object* v_err_1266_; 
v_err_1266_ = lean_ctor_get(v___x_1243_, 1);
lean_inc(v_err_1266_);
lean_dec_ref_known(v___x_1243_, 2);
v_err_1238_ = v_err_1266_;
goto v___jp_1237_;
}
}
v___jp_1116_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1121_, 0, v___y_1117_);
lean_ctor_set(v___x_1121_, 1, v___y_1118_);
lean_ctor_set(v___x_1121_, 2, v_port_1119_);
v___x_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___y_1120_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
return v___x_1122_;
}
v___jp_1123_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__1));
v___x_1126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___y_1124_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
return v___x_1126_;
}
v___jp_1127_:
{
lean_object* v___x_1131_; 
v___x_1131_ = lean_box(1);
v___y_1117_ = v___y_1129_;
v___y_1118_ = v___y_1130_;
v_port_1119_ = v___x_1131_;
v___y_1120_ = v___y_1128_;
goto v___jp_1116_;
}
v___jp_1132_:
{
uint8_t v___x_1137_; uint8_t v___x_1138_; 
v___x_1137_ = 47;
v___x_1138_ = lean_uint8_dec_eq(v_val_1136_, v___x_1137_);
if (v___x_1138_ == 0)
{
uint8_t v___x_1139_; uint8_t v___x_1140_; 
v___x_1139_ = 63;
v___x_1140_ = lean_uint8_dec_eq(v_val_1136_, v___x_1139_);
if (v___x_1140_ == 0)
{
uint8_t v___x_1141_; uint8_t v___x_1142_; 
v___x_1141_ = 35;
v___x_1142_ = lean_uint8_dec_eq(v_val_1136_, v___x_1141_);
if (v___x_1142_ == 0)
{
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
v___y_1124_ = v___y_1133_;
goto v___jp_1123_;
}
else
{
v___y_1128_ = v___y_1133_;
v___y_1129_ = v___y_1134_;
v___y_1130_ = v___y_1135_;
goto v___jp_1127_;
}
}
else
{
v___y_1128_ = v___y_1133_;
v___y_1129_ = v___y_1134_;
v___y_1130_ = v___y_1135_;
goto v___jp_1127_;
}
}
else
{
v___y_1128_ = v___y_1133_;
v___y_1129_ = v___y_1134_;
v___y_1130_ = v___y_1135_;
goto v___jp_1127_;
}
}
v___jp_1143_:
{
lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___x_1151_ = lean_byte_array_size(v_array_1148_);
v___x_1152_ = lean_nat_dec_lt(v_idx_1149_, v___x_1151_);
if (v___x_1152_ == 0)
{
lean_dec(v_idx_1149_);
lean_dec_ref(v_array_1148_);
if (v___y_1144_ == 0)
{
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
v___y_1124_ = v_pos_1147_;
goto v___jp_1123_;
}
else
{
v___y_1128_ = v_pos_1147_;
v___y_1129_ = v___y_1145_;
v___y_1130_ = v___y_1146_;
goto v___jp_1127_;
}
}
else
{
uint8_t v___x_1153_; 
v___x_1153_ = lean_byte_array_fget(v_array_1148_, v_idx_1149_);
lean_dec(v_idx_1149_);
lean_dec_ref(v_array_1148_);
v___y_1133_ = v_pos_1147_;
v___y_1134_ = v___y_1145_;
v___y_1135_ = v___y_1146_;
v_val_1136_ = v___x_1153_;
goto v___jp_1132_;
}
}
v___jp_1154_:
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_box(0);
v___y_1144_ = v___y_1155_;
v___y_1145_ = v___y_1158_;
v___y_1146_ = v___y_1160_;
v_pos_1147_ = v___y_1159_;
v_array_1148_ = v___y_1157_;
v_idx_1149_ = v___y_1156_;
v_res_1150_ = v___x_1161_;
goto v___jp_1143_;
}
v___jp_1162_:
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_box(0);
v___y_1117_ = v___y_1163_;
v___y_1118_ = v___y_1164_;
v_port_1119_ = v___x_1166_;
v___y_1120_ = v_pos_1165_;
goto v___jp_1116_;
}
v___jp_1167_:
{
lean_object* v___x_1170_; 
v___x_1170_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_1114_, v_pos_1168_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_pos_1171_; lean_object* v_res_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1223_; 
v_pos_1171_ = lean_ctor_get(v___x_1170_, 0);
v_res_1172_ = lean_ctor_get(v___x_1170_, 1);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1174_ = v___x_1170_;
v_isShared_1175_ = v_isSharedCheck_1223_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_res_1172_);
lean_inc(v_pos_1171_);
lean_dec(v___x_1170_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1223_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v_array_1176_; lean_object* v_idx_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v_array_1176_ = lean_ctor_get(v_pos_1171_, 0);
v_idx_1177_ = lean_ctor_get(v_pos_1171_, 1);
v___x_1178_ = lean_byte_array_size(v_array_1176_);
v___x_1179_ = lean_nat_dec_lt(v_idx_1177_, v___x_1178_);
if (v___x_1179_ == 0)
{
lean_del_object(v___x_1174_);
v___y_1163_ = v_res_1169_;
v___y_1164_ = v_res_1172_;
v_pos_1165_ = v_pos_1171_;
goto v___jp_1162_;
}
else
{
uint8_t v___x_1180_; uint8_t v___x_1181_; uint8_t v___x_1182_; 
v___x_1180_ = lean_byte_array_fget(v_array_1176_, v_idx_1177_);
v___x_1181_ = 58;
v___x_1182_ = lean_uint8_dec_eq(v___x_1180_, v___x_1181_);
if (v___x_1182_ == 0)
{
lean_del_object(v___x_1174_);
v___y_1163_ = v_res_1169_;
v___y_1164_ = v_res_1172_;
v_pos_1165_ = v_pos_1171_;
goto v___jp_1162_;
}
else
{
if (v___x_1182_ == 0)
{
lean_del_object(v___x_1174_);
v___y_1163_ = v_res_1169_;
v___y_1164_ = v_res_1172_;
v_pos_1165_ = v_pos_1171_;
goto v___jp_1162_;
}
else
{
if (v___x_1179_ == 0)
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
lean_dec(v_res_1172_);
lean_dec(v_res_1169_);
v___x_1183_ = lean_box(0);
if (v_isShared_1175_ == 0)
{
lean_ctor_set_tag(v___x_1174_, 1);
lean_ctor_set(v___x_1174_, 1, v___x_1183_);
v___x_1185_ = v___x_1174_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_pos_1171_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
else
{
if (v___x_1182_ == 0)
{
lean_object* v___x_1187_; lean_object* v___x_1189_; 
lean_dec(v_res_1172_);
lean_dec(v_res_1169_);
v___x_1187_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_1175_ == 0)
{
lean_ctor_set_tag(v___x_1174_, 1);
lean_ctor_set(v___x_1174_, 1, v___x_1187_);
v___x_1189_ = v___x_1174_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_pos_1171_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
else
{
lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1220_; 
lean_inc(v_idx_1177_);
lean_inc_ref(v_array_1176_);
lean_del_object(v___x_1174_);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_pos_1171_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; lean_object* v_unused_1222_; 
v_unused_1221_ = lean_ctor_get(v_pos_1171_, 1);
lean_dec(v_unused_1221_);
v_unused_1222_ = lean_ctor_get(v_pos_1171_, 0);
lean_dec(v_unused_1222_);
v___x_1192_ = v_pos_1171_;
v_isShared_1193_ = v_isSharedCheck_1220_;
goto v_resetjp_1191_;
}
else
{
lean_dec(v_pos_1171_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1220_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1194_ = lean_unsigned_to_nat(1u);
v___x_1195_ = lean_nat_add(v_idx_1177_, v___x_1194_);
lean_dec(v_idx_1177_);
lean_inc(v___x_1195_);
lean_inc_ref(v_array_1176_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 1, v___x_1195_);
v___x_1197_ = v___x_1192_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_array_1176_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
uint8_t v___x_1198_; 
v___x_1198_ = lean_nat_dec_lt(v___x_1195_, v___x_1178_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; 
v___x_1199_ = lean_box(0);
v___y_1144_ = v___x_1182_;
v___y_1145_ = v_res_1169_;
v___y_1146_ = v_res_1172_;
v_pos_1147_ = v___x_1197_;
v_array_1148_ = v_array_1176_;
v_idx_1149_ = v___x_1195_;
v_res_1150_ = v___x_1199_;
goto v___jp_1143_;
}
else
{
uint8_t v___x_1200_; uint8_t v___x_1201_; uint8_t v___x_1202_; 
v___x_1200_ = lean_byte_array_fget(v_array_1176_, v___x_1195_);
v___x_1201_ = 48;
v___x_1202_ = lean_uint8_dec_le(v___x_1201_, v___x_1200_);
if (v___x_1202_ == 0)
{
v___y_1155_ = v___x_1182_;
v___y_1156_ = v___x_1195_;
v___y_1157_ = v_array_1176_;
v___y_1158_ = v_res_1169_;
v___y_1159_ = v___x_1197_;
v___y_1160_ = v_res_1172_;
goto v___jp_1154_;
}
else
{
uint8_t v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = 57;
v___x_1204_ = lean_uint8_dec_le(v___x_1200_, v___x_1203_);
if (v___x_1204_ == 0)
{
v___y_1155_ = v___x_1182_;
v___y_1156_ = v___x_1195_;
v___y_1157_ = v_array_1176_;
v___y_1158_ = v_res_1169_;
v___y_1159_ = v___x_1197_;
v___y_1160_ = v_res_1172_;
goto v___jp_1154_;
}
else
{
lean_object* v___x_1205_; 
lean_dec(v___x_1195_);
lean_dec_ref(v_array_1176_);
v___x_1205_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_1197_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_pos_1206_; lean_object* v_res_1207_; lean_object* v___x_1208_; uint16_t v___x_1209_; 
v_pos_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_pos_1206_);
v_res_1207_ = lean_ctor_get(v___x_1205_, 1);
lean_inc(v_res_1207_);
lean_dec_ref_known(v___x_1205_, 2);
v___x_1208_ = lean_alloc_ctor(2, 0, 2);
v___x_1209_ = lean_unbox(v_res_1207_);
lean_dec(v_res_1207_);
lean_ctor_set_uint16(v___x_1208_, 0, v___x_1209_);
v___y_1117_ = v_res_1169_;
v___y_1118_ = v_res_1172_;
v_port_1119_ = v___x_1208_;
v___y_1120_ = v_pos_1206_;
goto v___jp_1116_;
}
else
{
lean_object* v_pos_1210_; lean_object* v_err_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
lean_dec(v_res_1172_);
lean_dec(v_res_1169_);
v_pos_1210_ = lean_ctor_get(v___x_1205_, 0);
v_err_1211_ = lean_ctor_get(v___x_1205_, 1);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1205_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_err_1211_);
lean_inc(v_pos_1210_);
lean_dec(v___x_1205_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_pos_1210_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_err_1211_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
}
}
}
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
lean_object* v_pos_1224_; lean_object* v_err_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_dec(v_res_1169_);
v_pos_1224_ = lean_ctor_get(v___x_1170_, 0);
v_err_1225_ = lean_ctor_get(v___x_1170_, 1);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1170_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_err_1225_);
lean_inc(v_pos_1224_);
lean_dec(v___x_1170_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_pos_1224_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_err_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
v___jp_1233_:
{
lean_object* v___x_1236_; 
v___x_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1236_, 0, v_res_1235_);
v_pos_1168_ = v_pos_1234_;
v_res_1169_ = v___x_1236_;
goto v___jp_1167_;
}
v___jp_1237_:
{
lean_object* v_idx_1239_; uint8_t v___x_1240_; 
v_idx_1239_ = lean_ctor_get(v_a_1115_, 1);
v___x_1240_ = lean_nat_dec_eq(v_idx_1239_, v_idx_1239_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; 
v___x_1241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1241_, 0, v_a_1115_);
lean_ctor_set(v___x_1241_, 1, v_err_1238_);
return v___x_1241_;
}
else
{
lean_object* v___x_1242_; 
lean_dec(v_err_1238_);
v___x_1242_ = lean_box(0);
v_pos_1168_ = v_a_1115_;
v_res_1169_ = v___x_1242_;
goto v___jp_1167_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___boxed(lean_object* v_config_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_1267_, v_a_1268_);
lean_dec_ref(v_config_1267_);
return v_res_1269_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(uint8_t v_c_1270_){
_start:
{
uint8_t v___x_1318_; uint8_t v___x_1319_; 
v___x_1318_ = 48;
v___x_1319_ = lean_uint8_dec_le(v___x_1318_, v_c_1270_);
if (v___x_1319_ == 0)
{
goto v___jp_1313_;
}
else
{
uint8_t v___x_1320_; uint8_t v___x_1321_; 
v___x_1320_ = 57;
v___x_1321_ = lean_uint8_dec_le(v_c_1270_, v___x_1320_);
if (v___x_1321_ == 0)
{
goto v___jp_1313_;
}
else
{
return v___x_1321_;
}
}
v___jp_1271_:
{
uint8_t v___x_1272_; uint8_t v___x_1273_; 
v___x_1272_ = 45;
v___x_1273_ = lean_uint8_dec_eq(v_c_1270_, v___x_1272_);
if (v___x_1273_ == 0)
{
uint8_t v___x_1274_; uint8_t v___x_1275_; 
v___x_1274_ = 46;
v___x_1275_ = lean_uint8_dec_eq(v_c_1270_, v___x_1274_);
if (v___x_1275_ == 0)
{
uint8_t v___x_1276_; uint8_t v___x_1277_; 
v___x_1276_ = 95;
v___x_1277_ = lean_uint8_dec_eq(v_c_1270_, v___x_1276_);
if (v___x_1277_ == 0)
{
uint8_t v___x_1278_; uint8_t v___x_1279_; 
v___x_1278_ = 126;
v___x_1279_ = lean_uint8_dec_eq(v_c_1270_, v___x_1278_);
if (v___x_1279_ == 0)
{
uint8_t v___x_1280_; uint8_t v___x_1281_; 
v___x_1280_ = 33;
v___x_1281_ = lean_uint8_dec_eq(v_c_1270_, v___x_1280_);
if (v___x_1281_ == 0)
{
uint8_t v___x_1282_; uint8_t v___x_1283_; 
v___x_1282_ = 36;
v___x_1283_ = lean_uint8_dec_eq(v_c_1270_, v___x_1282_);
if (v___x_1283_ == 0)
{
uint8_t v___x_1284_; uint8_t v___x_1285_; 
v___x_1284_ = 38;
v___x_1285_ = lean_uint8_dec_eq(v_c_1270_, v___x_1284_);
if (v___x_1285_ == 0)
{
uint8_t v___x_1286_; uint8_t v___x_1287_; 
v___x_1286_ = 39;
v___x_1287_ = lean_uint8_dec_eq(v_c_1270_, v___x_1286_);
if (v___x_1287_ == 0)
{
uint8_t v___x_1288_; uint8_t v___x_1289_; 
v___x_1288_ = 40;
v___x_1289_ = lean_uint8_dec_eq(v_c_1270_, v___x_1288_);
if (v___x_1289_ == 0)
{
uint8_t v___x_1290_; uint8_t v___x_1291_; 
v___x_1290_ = 41;
v___x_1291_ = lean_uint8_dec_eq(v_c_1270_, v___x_1290_);
if (v___x_1291_ == 0)
{
uint8_t v___x_1292_; uint8_t v___x_1293_; 
v___x_1292_ = 42;
v___x_1293_ = lean_uint8_dec_eq(v_c_1270_, v___x_1292_);
if (v___x_1293_ == 0)
{
uint8_t v___x_1294_; uint8_t v___x_1295_; 
v___x_1294_ = 43;
v___x_1295_ = lean_uint8_dec_eq(v_c_1270_, v___x_1294_);
if (v___x_1295_ == 0)
{
uint8_t v___x_1296_; uint8_t v___x_1297_; 
v___x_1296_ = 44;
v___x_1297_ = lean_uint8_dec_eq(v_c_1270_, v___x_1296_);
if (v___x_1297_ == 0)
{
uint8_t v___x_1298_; uint8_t v___x_1299_; 
v___x_1298_ = 59;
v___x_1299_ = lean_uint8_dec_eq(v_c_1270_, v___x_1298_);
if (v___x_1299_ == 0)
{
uint8_t v___x_1300_; uint8_t v___x_1301_; 
v___x_1300_ = 61;
v___x_1301_ = lean_uint8_dec_eq(v_c_1270_, v___x_1300_);
if (v___x_1301_ == 0)
{
uint8_t v___x_1302_; uint8_t v___x_1303_; 
v___x_1302_ = 58;
v___x_1303_ = lean_uint8_dec_eq(v_c_1270_, v___x_1302_);
if (v___x_1303_ == 0)
{
uint8_t v___x_1304_; uint8_t v___x_1305_; 
v___x_1304_ = 64;
v___x_1305_ = lean_uint8_dec_eq(v_c_1270_, v___x_1304_);
if (v___x_1305_ == 0)
{
uint8_t v___x_1306_; uint8_t v___x_1307_; 
v___x_1306_ = 37;
v___x_1307_ = lean_uint8_dec_eq(v_c_1270_, v___x_1306_);
return v___x_1307_;
}
else
{
return v___x_1305_;
}
}
else
{
return v___x_1303_;
}
}
else
{
return v___x_1301_;
}
}
else
{
return v___x_1299_;
}
}
else
{
return v___x_1297_;
}
}
else
{
return v___x_1295_;
}
}
else
{
return v___x_1293_;
}
}
else
{
return v___x_1291_;
}
}
else
{
return v___x_1289_;
}
}
else
{
return v___x_1287_;
}
}
else
{
return v___x_1285_;
}
}
else
{
return v___x_1283_;
}
}
else
{
return v___x_1281_;
}
}
else
{
return v___x_1279_;
}
}
else
{
return v___x_1277_;
}
}
else
{
return v___x_1275_;
}
}
else
{
return v___x_1273_;
}
}
v___jp_1308_:
{
uint8_t v___x_1309_; uint8_t v___x_1310_; 
v___x_1309_ = 65;
v___x_1310_ = lean_uint8_dec_le(v___x_1309_, v_c_1270_);
if (v___x_1310_ == 0)
{
goto v___jp_1271_;
}
else
{
uint8_t v___x_1311_; uint8_t v___x_1312_; 
v___x_1311_ = 90;
v___x_1312_ = lean_uint8_dec_le(v_c_1270_, v___x_1311_);
if (v___x_1312_ == 0)
{
goto v___jp_1271_;
}
else
{
return v___x_1312_;
}
}
}
v___jp_1313_:
{
uint8_t v___x_1314_; uint8_t v___x_1315_; 
v___x_1314_ = 97;
v___x_1315_ = lean_uint8_dec_le(v___x_1314_, v_c_1270_);
if (v___x_1315_ == 0)
{
goto v___jp_1308_;
}
else
{
uint8_t v___x_1316_; uint8_t v___x_1317_; 
v___x_1316_ = 122;
v___x_1317_ = lean_uint8_dec_le(v_c_1270_, v___x_1316_);
if (v___x_1317_ == 0)
{
goto v___jp_1308_;
}
else
{
return v___x_1317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0___boxed(lean_object* v_c_1322_){
_start:
{
uint8_t v_c_boxed_1323_; uint8_t v_res_1324_; lean_object* v_r_1325_; 
v_c_boxed_1323_ = lean_unbox(v_c_1322_);
v_res_1324_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(v_c_boxed_1323_);
v_r_1325_ = lean_box(v_res_1324_);
return v_r_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(lean_object* v_config_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_maxSegmentLength_1329_; lean_object* v___f_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v_snd_1333_; lean_object* v_fst_1334_; lean_object* v_fst_1335_; lean_object* v_array_1336_; lean_object* v_idx_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1354_; 
v_maxSegmentLength_1329_ = lean_ctor_get(v_config_1327_, 3);
v___f_1330_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___closed__0));
v___x_1331_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1328_);
v___x_1332_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1330_, v_maxSegmentLength_1329_, v___x_1331_, v_a_1328_);
v_snd_1333_ = lean_ctor_get(v___x_1332_, 1);
lean_inc(v_snd_1333_);
v_fst_1334_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_fst_1334_);
lean_dec_ref(v___x_1332_);
v_fst_1335_ = lean_ctor_get(v_snd_1333_, 0);
lean_inc(v_fst_1335_);
lean_dec(v_snd_1333_);
v_array_1336_ = lean_ctor_get(v_a_1328_, 0);
v_idx_1337_ = lean_ctor_get(v_a_1328_, 1);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_a_1328_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1339_ = v_a_1328_;
v_isShared_1340_ = v_isSharedCheck_1354_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_idx_1337_);
lean_inc(v_array_1336_);
lean_dec(v_a_1328_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1354_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v_lower_1342_; lean_object* v_upper_1343_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___y_1351_; uint8_t v___x_1353_; 
v___x_1348_ = lean_nat_add(v_idx_1337_, v_fst_1334_);
lean_dec(v_fst_1334_);
v___x_1349_ = lean_byte_array_size(v_array_1336_);
v___x_1353_ = lean_nat_dec_le(v_idx_1337_, v___x_1331_);
if (v___x_1353_ == 0)
{
v___y_1351_ = v_idx_1337_;
goto v___jp_1350_;
}
else
{
lean_dec(v_idx_1337_);
v___y_1351_ = v___x_1331_;
goto v___jp_1350_;
}
v___jp_1341_:
{
lean_object* v___x_1344_; lean_object* v___x_1346_; 
v___x_1344_ = l_ByteArray_toByteSlice(v_array_1336_, v_lower_1342_, v_upper_1343_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 1, v___x_1344_);
lean_ctor_set(v___x_1339_, 0, v_fst_1335_);
v___x_1346_ = v___x_1339_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_fst_1335_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
v___jp_1350_:
{
uint8_t v___x_1352_; 
v___x_1352_ = lean_nat_dec_le(v___x_1348_, v___x_1349_);
if (v___x_1352_ == 0)
{
lean_dec(v___x_1348_);
v_lower_1342_ = v___y_1351_;
v_upper_1343_ = v___x_1349_;
goto v___jp_1341_;
}
else
{
v_lower_1342_ = v___y_1351_;
v_upper_1343_ = v___x_1348_;
goto v___jp_1341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___boxed(lean_object* v_config_1355_, lean_object* v_a_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1355_, v_a_1356_);
lean_dec_ref(v_config_1355_);
return v_res_1357_;
}
}
LEAN_EXPORT uint8_t l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(uint8_t v_c_1358_){
_start:
{
uint8_t v___x_1359_; uint8_t v___x_1360_; 
v___x_1359_ = 63;
v___x_1360_ = lean_uint8_dec_eq(v_c_1358_, v___x_1359_);
if (v___x_1360_ == 0)
{
uint8_t v___x_1361_; uint8_t v___x_1362_; 
v___x_1361_ = 35;
v___x_1362_ = lean_uint8_dec_eq(v_c_1358_, v___x_1361_);
return v___x_1362_;
}
else
{
return v___x_1360_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0___boxed(lean_object* v_c_1363_){
_start:
{
uint8_t v_c_boxed_1364_; uint8_t v_res_1365_; lean_object* v_r_1366_; 
v_c_boxed_1364_ = lean_unbox(v_c_1363_);
v_res_1365_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v_c_boxed_1364_);
v_r_1366_ = lean_box(v_res_1365_);
return v_r_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(lean_object* v_config_1374_, lean_object* v_a_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v_array_1401_; lean_object* v_idx_1402_; lean_object* v_fst_1403_; lean_object* v_snd_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1576_; 
v_array_1401_ = lean_ctor_get(v___y_1376_, 0);
v_idx_1402_ = lean_ctor_get(v___y_1376_, 1);
v_fst_1403_ = lean_ctor_get(v_a_1375_, 0);
v_snd_1404_ = lean_ctor_get(v_a_1375_, 1);
v_isSharedCheck_1576_ = !lean_is_exclusive(v_a_1375_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1406_ = v_a_1375_;
v_isShared_1407_ = v_isSharedCheck_1576_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_snd_1404_);
lean_inc(v_fst_1403_);
lean_dec(v_a_1375_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1576_;
goto v_resetjp_1405_;
}
v___jp_1377_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___y_1380_);
lean_ctor_set(v___x_1381_, 1, v___y_1378_);
v___x_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___y_1379_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
return v___x_1382_;
}
v___jp_1383_:
{
lean_object* v___x_1388_; uint8_t v___x_1389_; 
v___x_1388_ = lean_array_get_size(v___y_1387_);
v___x_1389_ = lean_nat_dec_le(v___y_1384_, v___x_1388_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
lean_dec(v___y_1384_);
v___x_1390_ = l_ByteArray_empty;
v___x_1391_ = lean_array_push(v___y_1387_, v___x_1390_);
v___x_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
lean_ctor_set(v___x_1392_, 1, v___y_1386_);
v_a_1375_ = v___x_1392_;
v___y_1376_ = v___y_1385_;
goto _start;
}
else
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v_config_1374_);
v___x_1394_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1395_ = l_Nat_reprFast(v___y_1384_);
v___x_1396_ = lean_string_append(v___x_1394_, v___x_1395_);
lean_dec_ref(v___x_1395_);
v___x_1397_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1398_ = lean_string_append(v___x_1396_, v___x_1397_);
v___x_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
v___x_1400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1400_, 0, v___y_1385_);
lean_ctor_set(v___x_1400_, 1, v___x_1399_);
return v___x_1400_;
}
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; uint8_t v___x_1409_; 
v___x_1408_ = lean_byte_array_size(v_array_1401_);
v___x_1409_ = lean_nat_dec_lt(v_idx_1402_, v___x_1408_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1411_; 
lean_dec_ref(v_config_1374_);
if (v_isShared_1407_ == 0)
{
v___x_1411_ = v___x_1406_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_fst_1403_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_snd_1404_);
v___x_1411_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1412_; 
v___x_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___y_1376_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
return v___x_1412_;
}
}
else
{
if (v___x_1409_ == 0)
{
lean_object* v___x_1415_; 
lean_dec_ref(v_config_1374_);
if (v_isShared_1407_ == 0)
{
v___x_1415_ = v___x_1406_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_fst_1403_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_snd_1404_);
v___x_1415_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
lean_object* v___x_1416_; 
v___x_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___y_1376_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
return v___x_1416_;
}
}
else
{
uint8_t v___y_1419_; uint8_t v___x_1519_; uint8_t v___x_1567_; 
v___x_1519_ = lean_byte_array_fget(v_array_1401_, v_idx_1402_);
v___x_1567_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1519_);
if (v___x_1567_ == 0)
{
uint8_t v___x_1568_; uint8_t v___x_1569_; 
v___x_1568_ = 47;
v___x_1569_ = lean_uint8_dec_eq(v___x_1519_, v___x_1568_);
if (v___x_1569_ == 0)
{
uint8_t v___x_1570_; uint8_t v___x_1571_; 
v___x_1570_ = 48;
v___x_1571_ = lean_uint8_dec_le(v___x_1570_, v___x_1519_);
if (v___x_1571_ == 0)
{
goto v___jp_1562_;
}
else
{
uint8_t v___x_1572_; uint8_t v___x_1573_; 
v___x_1572_ = 57;
v___x_1573_ = lean_uint8_dec_le(v___x_1519_, v___x_1572_);
if (v___x_1573_ == 0)
{
goto v___jp_1562_;
}
else
{
v___y_1419_ = v___x_1409_;
goto v___jp_1418_;
}
}
}
else
{
v___y_1419_ = v___x_1409_;
goto v___jp_1418_;
}
}
else
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
lean_del_object(v___x_1406_);
lean_dec_ref(v_config_1374_);
v___x_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1574_, 0, v_fst_1403_);
lean_ctor_set(v___x_1574_, 1, v_snd_1404_);
v___x_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___y_1376_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
return v___x_1575_;
}
v___jp_1418_:
{
if (v___y_1419_ == 0)
{
lean_object* v___x_1421_; 
lean_dec_ref(v_config_1374_);
if (v_isShared_1407_ == 0)
{
v___x_1421_ = v___x_1406_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_fst_1403_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_snd_1404_);
v___x_1421_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1422_; 
v___x_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___y_1376_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
return v___x_1422_;
}
}
else
{
lean_object* v_maxPathSegments_1424_; lean_object* v_maxTotalPathLength_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; 
v_maxPathSegments_1424_ = lean_ctor_get(v_config_1374_, 6);
v_maxTotalPathLength_1425_ = lean_ctor_get(v_config_1374_, 7);
v___x_1426_ = lean_array_get_size(v_fst_1403_);
v___x_1427_ = lean_nat_dec_le(v_maxPathSegments_1424_, v___x_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; 
v___x_1428_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1374_, v___y_1376_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_pos_1429_; lean_object* v_res_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1502_; 
v_pos_1429_ = lean_ctor_get(v___x_1428_, 0);
v_res_1430_ = lean_ctor_get(v___x_1428_, 1);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1432_ = v___x_1428_;
v_isShared_1433_ = v_isSharedCheck_1502_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_res_1430_);
lean_inc(v_pos_1429_);
lean_dec(v___x_1428_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1502_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
lean_inc(v_res_1430_);
v___x_1434_ = l_ByteSlice_toByteArray(v_res_1430_);
v___x_1435_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_1434_);
if (lean_obj_tag(v___x_1435_) == 1)
{
lean_object* v_val_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1497_; 
v_val_1436_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1438_ = v___x_1435_;
v_isShared_1439_ = v_isSharedCheck_1497_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_val_1436_);
lean_dec(v___x_1435_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1497_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v___x_1440_ = l_ByteSlice_size(v_res_1430_);
lean_dec(v_res_1430_);
v___x_1441_ = lean_nat_add(v_snd_1404_, v___x_1440_);
lean_dec(v___x_1440_);
lean_dec(v_snd_1404_);
v___x_1442_ = lean_nat_dec_lt(v_maxTotalPathLength_1425_, v___x_1441_);
if (v___x_1442_ == 0)
{
lean_object* v_array_1443_; lean_object* v_idx_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; 
v_array_1443_ = lean_ctor_get(v_pos_1429_, 0);
v_idx_1444_ = lean_ctor_get(v_pos_1429_, 1);
v___x_1445_ = lean_array_push(v_fst_1403_, v_val_1436_);
v___x_1446_ = lean_byte_array_size(v_array_1443_);
v___x_1447_ = lean_nat_dec_lt(v_idx_1444_, v___x_1446_);
if (v___x_1447_ == 0)
{
lean_del_object(v___x_1438_);
lean_del_object(v___x_1432_);
lean_del_object(v___x_1406_);
lean_dec_ref(v_config_1374_);
v___y_1378_ = v___x_1441_;
v___y_1379_ = v_pos_1429_;
v___y_1380_ = v___x_1445_;
goto v___jp_1377_;
}
else
{
uint8_t v___x_1448_; uint8_t v___x_1449_; uint8_t v___x_1450_; 
v___x_1448_ = lean_byte_array_fget(v_array_1443_, v_idx_1444_);
v___x_1449_ = 47;
v___x_1450_ = lean_uint8_dec_eq(v___x_1448_, v___x_1449_);
if (v___x_1450_ == 0)
{
lean_del_object(v___x_1438_);
lean_del_object(v___x_1432_);
lean_del_object(v___x_1406_);
lean_dec_ref(v_config_1374_);
v___y_1378_ = v___x_1441_;
v___y_1379_ = v_pos_1429_;
v___y_1380_ = v___x_1445_;
goto v___jp_1377_;
}
else
{
lean_object* v___x_1451_; lean_object* v___x_1452_; uint8_t v___x_1453_; 
v___x_1451_ = lean_unsigned_to_nat(1u);
v___x_1452_ = lean_nat_add(v___x_1441_, v___x_1451_);
lean_dec(v___x_1441_);
v___x_1453_ = lean_nat_dec_lt(v_maxTotalPathLength_1425_, v___x_1452_);
if (v___x_1453_ == 0)
{
lean_del_object(v___x_1438_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1454_; lean_object* v___x_1456_; 
lean_dec(v___x_1452_);
lean_dec_ref(v___x_1445_);
lean_del_object(v___x_1406_);
lean_dec_ref(v_config_1374_);
v___x_1454_ = lean_box(0);
if (v_isShared_1433_ == 0)
{
lean_ctor_set_tag(v___x_1432_, 1);
lean_ctor_set(v___x_1432_, 1, v___x_1454_);
v___x_1456_ = v___x_1432_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_pos_1429_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v___x_1454_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
else
{
lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1472_; 
lean_inc(v_idx_1444_);
lean_inc_ref(v_array_1443_);
lean_del_object(v___x_1432_);
v_isSharedCheck_1472_ = !lean_is_exclusive(v_pos_1429_);
if (v_isSharedCheck_1472_ == 0)
{
lean_object* v_unused_1473_; lean_object* v_unused_1474_; 
v_unused_1473_ = lean_ctor_get(v_pos_1429_, 1);
lean_dec(v_unused_1473_);
v_unused_1474_ = lean_ctor_get(v_pos_1429_, 0);
lean_dec(v_unused_1474_);
v___x_1459_ = v_pos_1429_;
v_isShared_1460_ = v_isSharedCheck_1472_;
goto v_resetjp_1458_;
}
else
{
lean_dec(v_pos_1429_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1472_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1461_; lean_object* v___x_1463_; 
v___x_1461_ = lean_nat_add(v_idx_1444_, v___x_1451_);
lean_dec(v_idx_1444_);
lean_inc(v___x_1461_);
lean_inc_ref(v_array_1443_);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 1, v___x_1461_);
v___x_1463_ = v___x_1459_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_array_1443_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v___x_1461_);
v___x_1463_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
uint8_t v___x_1464_; 
v___x_1464_ = lean_nat_dec_lt(v___x_1461_, v___x_1446_);
if (v___x_1464_ == 0)
{
lean_dec(v___x_1461_);
lean_dec_ref(v_array_1443_);
lean_del_object(v___x_1406_);
lean_inc(v_maxPathSegments_1424_);
v___y_1384_ = v_maxPathSegments_1424_;
v___y_1385_ = v___x_1463_;
v___y_1386_ = v___x_1452_;
v___y_1387_ = v___x_1445_;
goto v___jp_1383_;
}
else
{
uint8_t v___x_1465_; uint8_t v___x_1466_; 
v___x_1465_ = lean_byte_array_fget(v_array_1443_, v___x_1461_);
lean_dec(v___x_1461_);
lean_dec_ref(v_array_1443_);
v___x_1466_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1465_);
if (v___x_1466_ == 0)
{
lean_object* v___x_1468_; 
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 1, v___x_1452_);
lean_ctor_set(v___x_1406_, 0, v___x_1445_);
v___x_1468_ = v___x_1406_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v___x_1452_);
v___x_1468_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
v_a_1375_ = v___x_1468_;
v___y_1376_ = v___x_1463_;
goto _start;
}
}
else
{
lean_del_object(v___x_1406_);
lean_inc(v_maxPathSegments_1424_);
v___y_1384_ = v_maxPathSegments_1424_;
v___y_1385_ = v___x_1463_;
v___y_1386_ = v___x_1452_;
v___y_1387_ = v___x_1445_;
goto v___jp_1383_;
}
}
}
}
}
}
else
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1481_; 
lean_inc(v_maxTotalPathLength_1425_);
lean_dec(v___x_1452_);
lean_dec_ref(v___x_1445_);
lean_del_object(v___x_1406_);
lean_dec_ref(v_config_1374_);
v___x_1475_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1476_ = l_Nat_reprFast(v_maxTotalPathLength_1425_);
v___x_1477_ = lean_string_append(v___x_1475_, v___x_1476_);
lean_dec_ref(v___x_1476_);
v___x_1478_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1479_ = lean_string_append(v___x_1477_, v___x_1478_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v___x_1479_);
v___x_1481_ = v___x_1438_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1479_);
v___x_1481_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1483_; 
if (v_isShared_1433_ == 0)
{
lean_ctor_set_tag(v___x_1432_, 1);
lean_ctor_set(v___x_1432_, 1, v___x_1481_);
v___x_1483_ = v___x_1432_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_pos_1429_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v___x_1481_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
}
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1492_; 
lean_inc(v_maxTotalPathLength_1425_);
lean_dec(v___x_1441_);
lean_dec(v_val_1436_);
lean_del_object(v___x_1406_);
lean_dec(v_fst_1403_);
lean_dec_ref(v_config_1374_);
v___x_1486_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1487_ = l_Nat_reprFast(v_maxTotalPathLength_1425_);
v___x_1488_ = lean_string_append(v___x_1486_, v___x_1487_);
lean_dec_ref(v___x_1487_);
v___x_1489_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1490_ = lean_string_append(v___x_1488_, v___x_1489_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v___x_1490_);
v___x_1492_ = v___x_1438_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
lean_object* v___x_1494_; 
if (v_isShared_1433_ == 0)
{
lean_ctor_set_tag(v___x_1432_, 1);
lean_ctor_set(v___x_1432_, 1, v___x_1492_);
v___x_1494_ = v___x_1432_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_pos_1429_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v___x_1492_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
}
else
{
lean_object* v___x_1498_; lean_object* v___x_1500_; 
lean_dec(v___x_1435_);
lean_dec(v_res_1430_);
lean_del_object(v___x_1406_);
lean_dec(v_snd_1404_);
lean_dec(v_fst_1403_);
lean_dec_ref(v_config_1374_);
v___x_1498_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5));
if (v_isShared_1433_ == 0)
{
lean_ctor_set_tag(v___x_1432_, 1);
lean_ctor_set(v___x_1432_, 1, v___x_1498_);
v___x_1500_ = v___x_1432_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_pos_1429_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
else
{
lean_object* v_pos_1503_; lean_object* v_err_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
lean_del_object(v___x_1406_);
lean_dec(v_snd_1404_);
lean_dec(v_fst_1403_);
lean_dec_ref(v_config_1374_);
v_pos_1503_ = lean_ctor_get(v___x_1428_, 0);
v_err_1504_ = lean_ctor_get(v___x_1428_, 1);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1428_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_err_1504_);
lean_inc(v_pos_1503_);
lean_dec(v___x_1428_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_pos_1503_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_err_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
else
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
lean_inc(v_maxPathSegments_1424_);
lean_del_object(v___x_1406_);
lean_dec(v_snd_1404_);
lean_dec(v_fst_1403_);
lean_dec_ref(v_config_1374_);
v___x_1512_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1513_ = l_Nat_reprFast(v_maxPathSegments_1424_);
v___x_1514_ = lean_string_append(v___x_1512_, v___x_1513_);
lean_dec_ref(v___x_1513_);
v___x_1515_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1516_ = lean_string_append(v___x_1514_, v___x_1515_);
v___x_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
v___x_1518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___y_1376_);
lean_ctor_set(v___x_1518_, 1, v___x_1517_);
return v___x_1518_;
}
}
}
v___jp_1520_:
{
uint8_t v___x_1521_; uint8_t v___x_1522_; 
v___x_1521_ = 45;
v___x_1522_ = lean_uint8_dec_eq(v___x_1519_, v___x_1521_);
if (v___x_1522_ == 0)
{
uint8_t v___x_1523_; uint8_t v___x_1524_; 
v___x_1523_ = 46;
v___x_1524_ = lean_uint8_dec_eq(v___x_1519_, v___x_1523_);
if (v___x_1524_ == 0)
{
uint8_t v___x_1525_; uint8_t v___x_1526_; 
v___x_1525_ = 95;
v___x_1526_ = lean_uint8_dec_eq(v___x_1519_, v___x_1525_);
if (v___x_1526_ == 0)
{
uint8_t v___x_1527_; uint8_t v___x_1528_; 
v___x_1527_ = 126;
v___x_1528_ = lean_uint8_dec_eq(v___x_1519_, v___x_1527_);
if (v___x_1528_ == 0)
{
uint8_t v___x_1529_; uint8_t v___x_1530_; 
v___x_1529_ = 33;
v___x_1530_ = lean_uint8_dec_eq(v___x_1519_, v___x_1529_);
if (v___x_1530_ == 0)
{
uint8_t v___x_1531_; uint8_t v___x_1532_; 
v___x_1531_ = 36;
v___x_1532_ = lean_uint8_dec_eq(v___x_1519_, v___x_1531_);
if (v___x_1532_ == 0)
{
uint8_t v___x_1533_; uint8_t v___x_1534_; 
v___x_1533_ = 38;
v___x_1534_ = lean_uint8_dec_eq(v___x_1519_, v___x_1533_);
if (v___x_1534_ == 0)
{
uint8_t v___x_1535_; uint8_t v___x_1536_; 
v___x_1535_ = 39;
v___x_1536_ = lean_uint8_dec_eq(v___x_1519_, v___x_1535_);
if (v___x_1536_ == 0)
{
uint8_t v___x_1537_; uint8_t v___x_1538_; 
v___x_1537_ = 40;
v___x_1538_ = lean_uint8_dec_eq(v___x_1519_, v___x_1537_);
if (v___x_1538_ == 0)
{
uint8_t v___x_1539_; uint8_t v___x_1540_; 
v___x_1539_ = 41;
v___x_1540_ = lean_uint8_dec_eq(v___x_1519_, v___x_1539_);
if (v___x_1540_ == 0)
{
uint8_t v___x_1541_; uint8_t v___x_1542_; 
v___x_1541_ = 42;
v___x_1542_ = lean_uint8_dec_eq(v___x_1519_, v___x_1541_);
if (v___x_1542_ == 0)
{
uint8_t v___x_1543_; uint8_t v___x_1544_; 
v___x_1543_ = 43;
v___x_1544_ = lean_uint8_dec_eq(v___x_1519_, v___x_1543_);
if (v___x_1544_ == 0)
{
uint8_t v___x_1545_; uint8_t v___x_1546_; 
v___x_1545_ = 44;
v___x_1546_ = lean_uint8_dec_eq(v___x_1519_, v___x_1545_);
if (v___x_1546_ == 0)
{
uint8_t v___x_1547_; uint8_t v___x_1548_; 
v___x_1547_ = 59;
v___x_1548_ = lean_uint8_dec_eq(v___x_1519_, v___x_1547_);
if (v___x_1548_ == 0)
{
uint8_t v___x_1549_; uint8_t v___x_1550_; 
v___x_1549_ = 61;
v___x_1550_ = lean_uint8_dec_eq(v___x_1519_, v___x_1549_);
if (v___x_1550_ == 0)
{
uint8_t v___x_1551_; uint8_t v___x_1552_; 
v___x_1551_ = 58;
v___x_1552_ = lean_uint8_dec_eq(v___x_1519_, v___x_1551_);
if (v___x_1552_ == 0)
{
uint8_t v___x_1553_; uint8_t v___x_1554_; 
v___x_1553_ = 64;
v___x_1554_ = lean_uint8_dec_eq(v___x_1519_, v___x_1553_);
if (v___x_1554_ == 0)
{
uint8_t v___x_1555_; uint8_t v___x_1556_; 
v___x_1555_ = 37;
v___x_1556_ = lean_uint8_dec_eq(v___x_1519_, v___x_1555_);
v___y_1419_ = v___x_1556_;
goto v___jp_1418_;
}
else
{
v___y_1419_ = v___x_1409_;
goto v___jp_1418_;
}
}
else
{
v___y_1419_ = v___x_1409_;
goto v___jp_1418_;
}
}
else
{
v___y_1419_ = v___x_1409_;
goto v___jp_1418_;
}
}
else
{
v___y_1419_ = v___x_1409_;
goto v___jp_1418_;
}
}
else
{
v___y_1419_ = v___x_1409_;
goto v___jp_1418_;
}
}
else
{
v___y_1419_ = v___x_1409_;
goto v___jp_1418_;
}
}
else
{
v___y_1419_ = v___x_1409_;
goto v___jp_1418_;
}
}
else
{
v___y_1419_ = v___x_1409_;
goto v___jp_1418_;
}
}
else
{
v___y_1419_ = v___x_1409_;
goto v___jp_1418_;
}
}
else
{
v___y_1419_ = v___x_1409_;
goto v___jp_1418_;
}
}
else
{
v___y_1419_ = v___x_1409_;
goto v___jp_1418_;
}
}
else
{
v___y_1419_ = v___x_1409_;
goto v___jp_1418_;
}
}
else
{
v___y_1419_ = v___x_1409_;
goto v___jp_1418_;
}
}
else
{
v___y_1419_ = v___x_1409_;
goto v___jp_1418_;
}
}
else
{
v___y_1419_ = v___x_1409_;
goto v___jp_1418_;
}
}
else
{
v___y_1419_ = v___x_1409_;
goto v___jp_1418_;
}
}
else
{
v___y_1419_ = v___x_1409_;
goto v___jp_1418_;
}
}
v___jp_1557_:
{
uint8_t v___x_1558_; uint8_t v___x_1559_; 
v___x_1558_ = 65;
v___x_1559_ = lean_uint8_dec_le(v___x_1558_, v___x_1519_);
if (v___x_1559_ == 0)
{
goto v___jp_1520_;
}
else
{
uint8_t v___x_1560_; uint8_t v___x_1561_; 
v___x_1560_ = 90;
v___x_1561_ = lean_uint8_dec_le(v___x_1519_, v___x_1560_);
if (v___x_1561_ == 0)
{
goto v___jp_1520_;
}
else
{
v___y_1419_ = v___x_1409_;
goto v___jp_1418_;
}
}
}
v___jp_1562_:
{
uint8_t v___x_1563_; uint8_t v___x_1564_; 
v___x_1563_ = 97;
v___x_1564_ = lean_uint8_dec_le(v___x_1563_, v___x_1519_);
if (v___x_1564_ == 0)
{
goto v___jp_1557_;
}
else
{
uint8_t v___x_1565_; uint8_t v___x_1566_; 
v___x_1565_ = 122;
v___x_1566_ = lean_uint8_dec_le(v___x_1519_, v___x_1565_);
if (v___x_1566_ == 0)
{
goto v___jp_1557_;
}
else
{
v___y_1419_ = v___x_1409_;
goto v___jp_1418_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(lean_object* v_config_1577_, lean_object* v_a_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v_array_1604_; lean_object* v_idx_1605_; lean_object* v_fst_1606_; lean_object* v_snd_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1779_; 
v_array_1604_ = lean_ctor_get(v___y_1579_, 0);
v_idx_1605_ = lean_ctor_get(v___y_1579_, 1);
v_fst_1606_ = lean_ctor_get(v_a_1578_, 0);
v_snd_1607_ = lean_ctor_get(v_a_1578_, 1);
v_isSharedCheck_1779_ = !lean_is_exclusive(v_a_1578_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1609_ = v_a_1578_;
v_isShared_1610_ = v_isSharedCheck_1779_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_snd_1607_);
lean_inc(v_fst_1606_);
lean_dec(v_a_1578_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1779_;
goto v_resetjp_1608_;
}
v___jp_1580_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___y_1581_);
lean_ctor_set(v___x_1584_, 1, v___y_1582_);
v___x_1585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___y_1583_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
return v___x_1585_;
}
v___jp_1586_:
{
lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1591_ = lean_array_get_size(v___y_1587_);
v___x_1592_ = lean_nat_dec_le(v___y_1590_, v___x_1591_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
lean_dec(v___y_1590_);
v___x_1593_ = l_ByteArray_empty;
v___x_1594_ = lean_array_push(v___y_1587_, v___x_1593_);
v___x_1595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
lean_ctor_set(v___x_1595_, 1, v___y_1588_);
v___x_1596_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_1577_, v___x_1595_, v___y_1589_);
return v___x_1596_;
}
else
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec_ref(v_config_1577_);
v___x_1597_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1598_ = l_Nat_reprFast(v___y_1590_);
v___x_1599_ = lean_string_append(v___x_1597_, v___x_1598_);
lean_dec_ref(v___x_1598_);
v___x_1600_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1601_ = lean_string_append(v___x_1599_, v___x_1600_);
v___x_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
v___x_1603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___y_1589_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
return v___x_1603_;
}
}
v_resetjp_1608_:
{
lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1611_ = lean_byte_array_size(v_array_1604_);
v___x_1612_ = lean_nat_dec_lt(v_idx_1605_, v___x_1611_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1614_; 
lean_dec_ref(v_config_1577_);
if (v_isShared_1610_ == 0)
{
v___x_1614_ = v___x_1609_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_fst_1606_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v_snd_1607_);
v___x_1614_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
lean_object* v___x_1615_; 
v___x_1615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___y_1579_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
return v___x_1615_;
}
}
else
{
if (v___x_1612_ == 0)
{
lean_object* v___x_1618_; 
lean_dec_ref(v_config_1577_);
if (v_isShared_1610_ == 0)
{
v___x_1618_ = v___x_1609_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_fst_1606_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_snd_1607_);
v___x_1618_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
lean_object* v___x_1619_; 
v___x_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___y_1579_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
return v___x_1619_;
}
}
else
{
uint8_t v___y_1622_; uint8_t v___x_1722_; uint8_t v___x_1770_; 
v___x_1722_ = lean_byte_array_fget(v_array_1604_, v_idx_1605_);
v___x_1770_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1722_);
if (v___x_1770_ == 0)
{
uint8_t v___x_1771_; uint8_t v___x_1772_; 
v___x_1771_ = 47;
v___x_1772_ = lean_uint8_dec_eq(v___x_1722_, v___x_1771_);
if (v___x_1772_ == 0)
{
uint8_t v___x_1773_; uint8_t v___x_1774_; 
v___x_1773_ = 48;
v___x_1774_ = lean_uint8_dec_le(v___x_1773_, v___x_1722_);
if (v___x_1774_ == 0)
{
goto v___jp_1765_;
}
else
{
uint8_t v___x_1775_; uint8_t v___x_1776_; 
v___x_1775_ = 57;
v___x_1776_ = lean_uint8_dec_le(v___x_1722_, v___x_1775_);
if (v___x_1776_ == 0)
{
goto v___jp_1765_;
}
else
{
v___y_1622_ = v___x_1612_;
goto v___jp_1621_;
}
}
}
else
{
v___y_1622_ = v___x_1612_;
goto v___jp_1621_;
}
}
else
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
lean_del_object(v___x_1609_);
lean_dec_ref(v_config_1577_);
v___x_1777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1777_, 0, v_fst_1606_);
lean_ctor_set(v___x_1777_, 1, v_snd_1607_);
v___x_1778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___y_1579_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
return v___x_1778_;
}
v___jp_1621_:
{
if (v___y_1622_ == 0)
{
lean_object* v___x_1624_; 
lean_dec_ref(v_config_1577_);
if (v_isShared_1610_ == 0)
{
v___x_1624_ = v___x_1609_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_fst_1606_);
lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_snd_1607_);
v___x_1624_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
lean_object* v___x_1625_; 
v___x_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___y_1579_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
return v___x_1625_;
}
}
else
{
lean_object* v_maxPathSegments_1627_; lean_object* v_maxTotalPathLength_1628_; lean_object* v___x_1629_; uint8_t v___x_1630_; 
v_maxPathSegments_1627_ = lean_ctor_get(v_config_1577_, 6);
v_maxTotalPathLength_1628_ = lean_ctor_get(v_config_1577_, 7);
v___x_1629_ = lean_array_get_size(v_fst_1606_);
v___x_1630_ = lean_nat_dec_le(v_maxPathSegments_1627_, v___x_1629_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; 
v___x_1631_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1577_, v___y_1579_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_pos_1632_; lean_object* v_res_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1705_; 
v_pos_1632_ = lean_ctor_get(v___x_1631_, 0);
v_res_1633_ = lean_ctor_get(v___x_1631_, 1);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1635_ = v___x_1631_;
v_isShared_1636_ = v_isSharedCheck_1705_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_res_1633_);
lean_inc(v_pos_1632_);
lean_dec(v___x_1631_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1705_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
lean_inc(v_res_1633_);
v___x_1637_ = l_ByteSlice_toByteArray(v_res_1633_);
v___x_1638_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_1637_);
if (lean_obj_tag(v___x_1638_) == 1)
{
lean_object* v_val_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1700_; 
v_val_1639_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1641_ = v___x_1638_;
v_isShared_1642_ = v_isSharedCheck_1700_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_val_1639_);
lean_dec(v___x_1638_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1700_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; uint8_t v___x_1645_; 
v___x_1643_ = l_ByteSlice_size(v_res_1633_);
lean_dec(v_res_1633_);
v___x_1644_ = lean_nat_add(v_snd_1607_, v___x_1643_);
lean_dec(v___x_1643_);
lean_dec(v_snd_1607_);
v___x_1645_ = lean_nat_dec_lt(v_maxTotalPathLength_1628_, v___x_1644_);
if (v___x_1645_ == 0)
{
lean_object* v_array_1646_; lean_object* v_idx_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; uint8_t v___x_1650_; 
v_array_1646_ = lean_ctor_get(v_pos_1632_, 0);
v_idx_1647_ = lean_ctor_get(v_pos_1632_, 1);
v___x_1648_ = lean_array_push(v_fst_1606_, v_val_1639_);
v___x_1649_ = lean_byte_array_size(v_array_1646_);
v___x_1650_ = lean_nat_dec_lt(v_idx_1647_, v___x_1649_);
if (v___x_1650_ == 0)
{
lean_del_object(v___x_1641_);
lean_del_object(v___x_1635_);
lean_del_object(v___x_1609_);
lean_dec_ref(v_config_1577_);
v___y_1581_ = v___x_1648_;
v___y_1582_ = v___x_1644_;
v___y_1583_ = v_pos_1632_;
goto v___jp_1580_;
}
else
{
uint8_t v___x_1651_; uint8_t v___x_1652_; uint8_t v___x_1653_; 
v___x_1651_ = lean_byte_array_fget(v_array_1646_, v_idx_1647_);
v___x_1652_ = 47;
v___x_1653_ = lean_uint8_dec_eq(v___x_1651_, v___x_1652_);
if (v___x_1653_ == 0)
{
lean_del_object(v___x_1641_);
lean_del_object(v___x_1635_);
lean_del_object(v___x_1609_);
lean_dec_ref(v_config_1577_);
v___y_1581_ = v___x_1648_;
v___y_1582_ = v___x_1644_;
v___y_1583_ = v_pos_1632_;
goto v___jp_1580_;
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1654_ = lean_unsigned_to_nat(1u);
v___x_1655_ = lean_nat_add(v___x_1644_, v___x_1654_);
lean_dec(v___x_1644_);
v___x_1656_ = lean_nat_dec_lt(v_maxTotalPathLength_1628_, v___x_1655_);
if (v___x_1656_ == 0)
{
lean_del_object(v___x_1641_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1657_; lean_object* v___x_1659_; 
lean_dec(v___x_1655_);
lean_dec_ref(v___x_1648_);
lean_del_object(v___x_1609_);
lean_dec_ref(v_config_1577_);
v___x_1657_ = lean_box(0);
if (v_isShared_1636_ == 0)
{
lean_ctor_set_tag(v___x_1635_, 1);
lean_ctor_set(v___x_1635_, 1, v___x_1657_);
v___x_1659_ = v___x_1635_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_pos_1632_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
else
{
lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1675_; 
lean_inc(v_idx_1647_);
lean_inc_ref(v_array_1646_);
lean_del_object(v___x_1635_);
v_isSharedCheck_1675_ = !lean_is_exclusive(v_pos_1632_);
if (v_isSharedCheck_1675_ == 0)
{
lean_object* v_unused_1676_; lean_object* v_unused_1677_; 
v_unused_1676_ = lean_ctor_get(v_pos_1632_, 1);
lean_dec(v_unused_1676_);
v_unused_1677_ = lean_ctor_get(v_pos_1632_, 0);
lean_dec(v_unused_1677_);
v___x_1662_ = v_pos_1632_;
v_isShared_1663_ = v_isSharedCheck_1675_;
goto v_resetjp_1661_;
}
else
{
lean_dec(v_pos_1632_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1675_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1664_; lean_object* v___x_1666_; 
v___x_1664_ = lean_nat_add(v_idx_1647_, v___x_1654_);
lean_dec(v_idx_1647_);
lean_inc(v___x_1664_);
lean_inc_ref(v_array_1646_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 1, v___x_1664_);
v___x_1666_ = v___x_1662_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_array_1646_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v___x_1664_);
v___x_1666_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
uint8_t v___x_1667_; 
v___x_1667_ = lean_nat_dec_lt(v___x_1664_, v___x_1649_);
if (v___x_1667_ == 0)
{
lean_dec(v___x_1664_);
lean_dec_ref(v_array_1646_);
lean_del_object(v___x_1609_);
lean_inc(v_maxPathSegments_1627_);
v___y_1587_ = v___x_1648_;
v___y_1588_ = v___x_1655_;
v___y_1589_ = v___x_1666_;
v___y_1590_ = v_maxPathSegments_1627_;
goto v___jp_1586_;
}
else
{
uint8_t v___x_1668_; uint8_t v___x_1669_; 
v___x_1668_ = lean_byte_array_fget(v_array_1646_, v___x_1664_);
lean_dec(v___x_1664_);
lean_dec_ref(v_array_1646_);
v___x_1669_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1668_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1671_; 
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 1, v___x_1655_);
lean_ctor_set(v___x_1609_, 0, v___x_1648_);
v___x_1671_ = v___x_1609_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1648_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v___x_1655_);
v___x_1671_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
lean_object* v___x_1672_; 
v___x_1672_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_1577_, v___x_1671_, v___x_1666_);
return v___x_1672_;
}
}
else
{
lean_del_object(v___x_1609_);
lean_inc(v_maxPathSegments_1627_);
v___y_1587_ = v___x_1648_;
v___y_1588_ = v___x_1655_;
v___y_1589_ = v___x_1666_;
v___y_1590_ = v_maxPathSegments_1627_;
goto v___jp_1586_;
}
}
}
}
}
}
else
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1684_; 
lean_inc(v_maxTotalPathLength_1628_);
lean_dec(v___x_1655_);
lean_dec_ref(v___x_1648_);
lean_del_object(v___x_1609_);
lean_dec_ref(v_config_1577_);
v___x_1678_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1679_ = l_Nat_reprFast(v_maxTotalPathLength_1628_);
v___x_1680_ = lean_string_append(v___x_1678_, v___x_1679_);
lean_dec_ref(v___x_1679_);
v___x_1681_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1682_ = lean_string_append(v___x_1680_, v___x_1681_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v___x_1682_);
v___x_1684_ = v___x_1641_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1682_);
v___x_1684_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
lean_object* v___x_1686_; 
if (v_isShared_1636_ == 0)
{
lean_ctor_set_tag(v___x_1635_, 1);
lean_ctor_set(v___x_1635_, 1, v___x_1684_);
v___x_1686_ = v___x_1635_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_pos_1632_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v___x_1684_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
}
}
else
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1695_; 
lean_inc(v_maxTotalPathLength_1628_);
lean_dec(v___x_1644_);
lean_dec(v_val_1639_);
lean_del_object(v___x_1609_);
lean_dec(v_fst_1606_);
lean_dec_ref(v_config_1577_);
v___x_1689_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1690_ = l_Nat_reprFast(v_maxTotalPathLength_1628_);
v___x_1691_ = lean_string_append(v___x_1689_, v___x_1690_);
lean_dec_ref(v___x_1690_);
v___x_1692_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1693_ = lean_string_append(v___x_1691_, v___x_1692_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v___x_1693_);
v___x_1695_ = v___x_1641_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1693_);
v___x_1695_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
lean_object* v___x_1697_; 
if (v_isShared_1636_ == 0)
{
lean_ctor_set_tag(v___x_1635_, 1);
lean_ctor_set(v___x_1635_, 1, v___x_1695_);
v___x_1697_ = v___x_1635_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_pos_1632_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v___x_1695_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
}
else
{
lean_object* v___x_1701_; lean_object* v___x_1703_; 
lean_dec(v___x_1638_);
lean_dec(v_res_1633_);
lean_del_object(v___x_1609_);
lean_dec(v_snd_1607_);
lean_dec(v_fst_1606_);
lean_dec_ref(v_config_1577_);
v___x_1701_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5));
if (v_isShared_1636_ == 0)
{
lean_ctor_set_tag(v___x_1635_, 1);
lean_ctor_set(v___x_1635_, 1, v___x_1701_);
v___x_1703_ = v___x_1635_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_pos_1632_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v___x_1701_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
else
{
lean_object* v_pos_1706_; lean_object* v_err_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_del_object(v___x_1609_);
lean_dec(v_snd_1607_);
lean_dec(v_fst_1606_);
lean_dec_ref(v_config_1577_);
v_pos_1706_ = lean_ctor_get(v___x_1631_, 0);
v_err_1707_ = lean_ctor_get(v___x_1631_, 1);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1631_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_err_1707_);
lean_inc(v_pos_1706_);
lean_dec(v___x_1631_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_pos_1706_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_err_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
else
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
lean_inc(v_maxPathSegments_1627_);
lean_del_object(v___x_1609_);
lean_dec(v_snd_1607_);
lean_dec(v_fst_1606_);
lean_dec_ref(v_config_1577_);
v___x_1715_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1716_ = l_Nat_reprFast(v_maxPathSegments_1627_);
v___x_1717_ = lean_string_append(v___x_1715_, v___x_1716_);
lean_dec_ref(v___x_1716_);
v___x_1718_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1719_ = lean_string_append(v___x_1717_, v___x_1718_);
v___x_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1719_);
v___x_1721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1721_, 0, v___y_1579_);
lean_ctor_set(v___x_1721_, 1, v___x_1720_);
return v___x_1721_;
}
}
}
v___jp_1723_:
{
uint8_t v___x_1724_; uint8_t v___x_1725_; 
v___x_1724_ = 45;
v___x_1725_ = lean_uint8_dec_eq(v___x_1722_, v___x_1724_);
if (v___x_1725_ == 0)
{
uint8_t v___x_1726_; uint8_t v___x_1727_; 
v___x_1726_ = 46;
v___x_1727_ = lean_uint8_dec_eq(v___x_1722_, v___x_1726_);
if (v___x_1727_ == 0)
{
uint8_t v___x_1728_; uint8_t v___x_1729_; 
v___x_1728_ = 95;
v___x_1729_ = lean_uint8_dec_eq(v___x_1722_, v___x_1728_);
if (v___x_1729_ == 0)
{
uint8_t v___x_1730_; uint8_t v___x_1731_; 
v___x_1730_ = 126;
v___x_1731_ = lean_uint8_dec_eq(v___x_1722_, v___x_1730_);
if (v___x_1731_ == 0)
{
uint8_t v___x_1732_; uint8_t v___x_1733_; 
v___x_1732_ = 33;
v___x_1733_ = lean_uint8_dec_eq(v___x_1722_, v___x_1732_);
if (v___x_1733_ == 0)
{
uint8_t v___x_1734_; uint8_t v___x_1735_; 
v___x_1734_ = 36;
v___x_1735_ = lean_uint8_dec_eq(v___x_1722_, v___x_1734_);
if (v___x_1735_ == 0)
{
uint8_t v___x_1736_; uint8_t v___x_1737_; 
v___x_1736_ = 38;
v___x_1737_ = lean_uint8_dec_eq(v___x_1722_, v___x_1736_);
if (v___x_1737_ == 0)
{
uint8_t v___x_1738_; uint8_t v___x_1739_; 
v___x_1738_ = 39;
v___x_1739_ = lean_uint8_dec_eq(v___x_1722_, v___x_1738_);
if (v___x_1739_ == 0)
{
uint8_t v___x_1740_; uint8_t v___x_1741_; 
v___x_1740_ = 40;
v___x_1741_ = lean_uint8_dec_eq(v___x_1722_, v___x_1740_);
if (v___x_1741_ == 0)
{
uint8_t v___x_1742_; uint8_t v___x_1743_; 
v___x_1742_ = 41;
v___x_1743_ = lean_uint8_dec_eq(v___x_1722_, v___x_1742_);
if (v___x_1743_ == 0)
{
uint8_t v___x_1744_; uint8_t v___x_1745_; 
v___x_1744_ = 42;
v___x_1745_ = lean_uint8_dec_eq(v___x_1722_, v___x_1744_);
if (v___x_1745_ == 0)
{
uint8_t v___x_1746_; uint8_t v___x_1747_; 
v___x_1746_ = 43;
v___x_1747_ = lean_uint8_dec_eq(v___x_1722_, v___x_1746_);
if (v___x_1747_ == 0)
{
uint8_t v___x_1748_; uint8_t v___x_1749_; 
v___x_1748_ = 44;
v___x_1749_ = lean_uint8_dec_eq(v___x_1722_, v___x_1748_);
if (v___x_1749_ == 0)
{
uint8_t v___x_1750_; uint8_t v___x_1751_; 
v___x_1750_ = 59;
v___x_1751_ = lean_uint8_dec_eq(v___x_1722_, v___x_1750_);
if (v___x_1751_ == 0)
{
uint8_t v___x_1752_; uint8_t v___x_1753_; 
v___x_1752_ = 61;
v___x_1753_ = lean_uint8_dec_eq(v___x_1722_, v___x_1752_);
if (v___x_1753_ == 0)
{
uint8_t v___x_1754_; uint8_t v___x_1755_; 
v___x_1754_ = 58;
v___x_1755_ = lean_uint8_dec_eq(v___x_1722_, v___x_1754_);
if (v___x_1755_ == 0)
{
uint8_t v___x_1756_; uint8_t v___x_1757_; 
v___x_1756_ = 64;
v___x_1757_ = lean_uint8_dec_eq(v___x_1722_, v___x_1756_);
if (v___x_1757_ == 0)
{
uint8_t v___x_1758_; uint8_t v___x_1759_; 
v___x_1758_ = 37;
v___x_1759_ = lean_uint8_dec_eq(v___x_1722_, v___x_1758_);
v___y_1622_ = v___x_1759_;
goto v___jp_1621_;
}
else
{
v___y_1622_ = v___x_1612_;
goto v___jp_1621_;
}
}
else
{
v___y_1622_ = v___x_1612_;
goto v___jp_1621_;
}
}
else
{
v___y_1622_ = v___x_1612_;
goto v___jp_1621_;
}
}
else
{
v___y_1622_ = v___x_1612_;
goto v___jp_1621_;
}
}
else
{
v___y_1622_ = v___x_1612_;
goto v___jp_1621_;
}
}
else
{
v___y_1622_ = v___x_1612_;
goto v___jp_1621_;
}
}
else
{
v___y_1622_ = v___x_1612_;
goto v___jp_1621_;
}
}
else
{
v___y_1622_ = v___x_1612_;
goto v___jp_1621_;
}
}
else
{
v___y_1622_ = v___x_1612_;
goto v___jp_1621_;
}
}
else
{
v___y_1622_ = v___x_1612_;
goto v___jp_1621_;
}
}
else
{
v___y_1622_ = v___x_1612_;
goto v___jp_1621_;
}
}
else
{
v___y_1622_ = v___x_1612_;
goto v___jp_1621_;
}
}
else
{
v___y_1622_ = v___x_1612_;
goto v___jp_1621_;
}
}
else
{
v___y_1622_ = v___x_1612_;
goto v___jp_1621_;
}
}
else
{
v___y_1622_ = v___x_1612_;
goto v___jp_1621_;
}
}
else
{
v___y_1622_ = v___x_1612_;
goto v___jp_1621_;
}
}
else
{
v___y_1622_ = v___x_1612_;
goto v___jp_1621_;
}
}
v___jp_1760_:
{
uint8_t v___x_1761_; uint8_t v___x_1762_; 
v___x_1761_ = 65;
v___x_1762_ = lean_uint8_dec_le(v___x_1761_, v___x_1722_);
if (v___x_1762_ == 0)
{
goto v___jp_1723_;
}
else
{
uint8_t v___x_1763_; uint8_t v___x_1764_; 
v___x_1763_ = 90;
v___x_1764_ = lean_uint8_dec_le(v___x_1722_, v___x_1763_);
if (v___x_1764_ == 0)
{
goto v___jp_1723_;
}
else
{
v___y_1622_ = v___x_1612_;
goto v___jp_1621_;
}
}
}
v___jp_1765_:
{
uint8_t v___x_1766_; uint8_t v___x_1767_; 
v___x_1766_ = 97;
v___x_1767_ = lean_uint8_dec_le(v___x_1766_, v___x_1722_);
if (v___x_1767_ == 0)
{
goto v___jp_1760_;
}
else
{
uint8_t v___x_1768_; uint8_t v___x_1769_; 
v___x_1768_ = 122;
v___x_1769_ = lean_uint8_dec_le(v___x_1722_, v___x_1768_);
if (v___x_1769_ == 0)
{
goto v___jp_1760_;
}
else
{
v___y_1622_ = v___x_1612_;
goto v___jp_1621_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath(lean_object* v_config_1791_, uint8_t v_forceAbsolute_1792_, uint8_t v_allowEmpty_1793_, lean_object* v_a_1794_){
_start:
{
lean_object* v___y_1796_; lean_object* v___y_1800_; lean_object* v_array_1803_; lean_object* v_idx_1804_; uint8_t v_isAbsolute_1805_; lean_object* v___x_1806_; lean_object* v_segments_1807_; uint8_t v_isAbsolute_1809_; lean_object* v_totalLength_1810_; lean_object* v___y_1811_; lean_object* v_pos_1835_; lean_object* v_array_1836_; lean_object* v_idx_1837_; lean_object* v___y_1846_; uint8_t v___y_1850_; lean_object* v_pos_1851_; uint8_t v_res_1852_; uint8_t v___y_1854_; lean_object* v_pos_1855_; uint8_t v_res_1856_; lean_object* v___y_1864_; uint8_t v___y_1865_; uint8_t v___y_1866_; uint8_t v___y_1875_; lean_object* v_pos_1876_; uint8_t v_res_1877_; lean_object* v_pos_1879_; lean_object* v_array_1880_; lean_object* v_idx_1881_; uint8_t v_res_1882_; lean_object* v___x_1886_; uint8_t v___x_1887_; 
v_array_1803_ = lean_ctor_get(v_a_1794_, 0);
lean_inc_ref(v_array_1803_);
v_idx_1804_ = lean_ctor_get(v_a_1794_, 1);
lean_inc(v_idx_1804_);
v_isAbsolute_1805_ = 0;
v___x_1806_ = lean_unsigned_to_nat(0u);
v_segments_1807_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__4));
v___x_1886_ = lean_byte_array_size(v_array_1803_);
v___x_1887_ = lean_nat_dec_lt(v_idx_1804_, v___x_1886_);
if (v___x_1887_ == 0)
{
v_pos_1879_ = v_a_1794_;
v_array_1880_ = v_array_1803_;
v_idx_1881_ = v_idx_1804_;
v_res_1882_ = v_isAbsolute_1805_;
goto v___jp_1878_;
}
else
{
uint8_t v___x_1888_; uint8_t v___x_1938_; uint8_t v___x_1939_; 
v___x_1888_ = lean_byte_array_fget(v_array_1803_, v_idx_1804_);
v___x_1938_ = 48;
v___x_1939_ = lean_uint8_dec_le(v___x_1938_, v___x_1888_);
if (v___x_1939_ == 0)
{
goto v___jp_1933_;
}
else
{
uint8_t v___x_1940_; uint8_t v___x_1941_; 
v___x_1940_ = 57;
v___x_1941_ = lean_uint8_dec_le(v___x_1888_, v___x_1940_);
if (v___x_1941_ == 0)
{
goto v___jp_1933_;
}
else
{
v_pos_1879_ = v_a_1794_;
v_array_1880_ = v_array_1803_;
v_idx_1881_ = v_idx_1804_;
v_res_1882_ = v___x_1941_;
goto v___jp_1878_;
}
}
v___jp_1889_:
{
uint8_t v___x_1890_; uint8_t v___x_1891_; 
v___x_1890_ = 45;
v___x_1891_ = lean_uint8_dec_eq(v___x_1888_, v___x_1890_);
if (v___x_1891_ == 0)
{
uint8_t v___x_1892_; uint8_t v___x_1893_; 
v___x_1892_ = 46;
v___x_1893_ = lean_uint8_dec_eq(v___x_1888_, v___x_1892_);
if (v___x_1893_ == 0)
{
uint8_t v___x_1894_; uint8_t v___x_1895_; 
v___x_1894_ = 95;
v___x_1895_ = lean_uint8_dec_eq(v___x_1888_, v___x_1894_);
if (v___x_1895_ == 0)
{
uint8_t v___x_1896_; uint8_t v___x_1897_; 
v___x_1896_ = 126;
v___x_1897_ = lean_uint8_dec_eq(v___x_1888_, v___x_1896_);
if (v___x_1897_ == 0)
{
uint8_t v___x_1898_; uint8_t v___x_1899_; 
v___x_1898_ = 33;
v___x_1899_ = lean_uint8_dec_eq(v___x_1888_, v___x_1898_);
if (v___x_1899_ == 0)
{
uint8_t v___x_1900_; uint8_t v___x_1901_; 
v___x_1900_ = 36;
v___x_1901_ = lean_uint8_dec_eq(v___x_1888_, v___x_1900_);
if (v___x_1901_ == 0)
{
uint8_t v___x_1902_; uint8_t v___x_1903_; 
v___x_1902_ = 38;
v___x_1903_ = lean_uint8_dec_eq(v___x_1888_, v___x_1902_);
if (v___x_1903_ == 0)
{
uint8_t v___x_1904_; uint8_t v___x_1905_; 
v___x_1904_ = 39;
v___x_1905_ = lean_uint8_dec_eq(v___x_1888_, v___x_1904_);
if (v___x_1905_ == 0)
{
uint8_t v___x_1906_; uint8_t v___x_1907_; 
v___x_1906_ = 40;
v___x_1907_ = lean_uint8_dec_eq(v___x_1888_, v___x_1906_);
if (v___x_1907_ == 0)
{
uint8_t v___x_1908_; uint8_t v___x_1909_; 
v___x_1908_ = 41;
v___x_1909_ = lean_uint8_dec_eq(v___x_1888_, v___x_1908_);
if (v___x_1909_ == 0)
{
uint8_t v___x_1910_; uint8_t v___x_1911_; 
v___x_1910_ = 42;
v___x_1911_ = lean_uint8_dec_eq(v___x_1888_, v___x_1910_);
if (v___x_1911_ == 0)
{
uint8_t v___x_1912_; uint8_t v___x_1913_; 
v___x_1912_ = 43;
v___x_1913_ = lean_uint8_dec_eq(v___x_1888_, v___x_1912_);
if (v___x_1913_ == 0)
{
uint8_t v___x_1914_; uint8_t v___x_1915_; 
v___x_1914_ = 44;
v___x_1915_ = lean_uint8_dec_eq(v___x_1888_, v___x_1914_);
if (v___x_1915_ == 0)
{
uint8_t v___x_1916_; uint8_t v___x_1917_; 
v___x_1916_ = 59;
v___x_1917_ = lean_uint8_dec_eq(v___x_1888_, v___x_1916_);
if (v___x_1917_ == 0)
{
uint8_t v___x_1918_; uint8_t v___x_1919_; 
v___x_1918_ = 61;
v___x_1919_ = lean_uint8_dec_eq(v___x_1888_, v___x_1918_);
if (v___x_1919_ == 0)
{
uint8_t v___x_1920_; uint8_t v___x_1921_; 
v___x_1920_ = 58;
v___x_1921_ = lean_uint8_dec_eq(v___x_1888_, v___x_1920_);
if (v___x_1921_ == 0)
{
uint8_t v___x_1922_; uint8_t v___x_1923_; 
v___x_1922_ = 64;
v___x_1923_ = lean_uint8_dec_eq(v___x_1888_, v___x_1922_);
if (v___x_1923_ == 0)
{
uint8_t v___x_1924_; uint8_t v___x_1925_; 
v___x_1924_ = 37;
v___x_1925_ = lean_uint8_dec_eq(v___x_1888_, v___x_1924_);
if (v___x_1925_ == 0)
{
uint8_t v___x_1926_; uint8_t v___x_1927_; 
v___x_1926_ = 47;
v___x_1927_ = lean_uint8_dec_eq(v___x_1888_, v___x_1926_);
if (v___x_1927_ == 0)
{
v_pos_1879_ = v_a_1794_;
v_array_1880_ = v_array_1803_;
v_idx_1881_ = v_idx_1804_;
v_res_1882_ = v_isAbsolute_1805_;
goto v___jp_1878_;
}
else
{
v_pos_1879_ = v_a_1794_;
v_array_1880_ = v_array_1803_;
v_idx_1881_ = v_idx_1804_;
v_res_1882_ = v___x_1927_;
goto v___jp_1878_;
}
}
else
{
v_pos_1879_ = v_a_1794_;
v_array_1880_ = v_array_1803_;
v_idx_1881_ = v_idx_1804_;
v_res_1882_ = v___x_1925_;
goto v___jp_1878_;
}
}
else
{
v_pos_1879_ = v_a_1794_;
v_array_1880_ = v_array_1803_;
v_idx_1881_ = v_idx_1804_;
v_res_1882_ = v___x_1923_;
goto v___jp_1878_;
}
}
else
{
v_pos_1879_ = v_a_1794_;
v_array_1880_ = v_array_1803_;
v_idx_1881_ = v_idx_1804_;
v_res_1882_ = v___x_1921_;
goto v___jp_1878_;
}
}
else
{
v_pos_1879_ = v_a_1794_;
v_array_1880_ = v_array_1803_;
v_idx_1881_ = v_idx_1804_;
v_res_1882_ = v___x_1919_;
goto v___jp_1878_;
}
}
else
{
v_pos_1879_ = v_a_1794_;
v_array_1880_ = v_array_1803_;
v_idx_1881_ = v_idx_1804_;
v_res_1882_ = v___x_1917_;
goto v___jp_1878_;
}
}
else
{
v_pos_1879_ = v_a_1794_;
v_array_1880_ = v_array_1803_;
v_idx_1881_ = v_idx_1804_;
v_res_1882_ = v___x_1915_;
goto v___jp_1878_;
}
}
else
{
v_pos_1879_ = v_a_1794_;
v_array_1880_ = v_array_1803_;
v_idx_1881_ = v_idx_1804_;
v_res_1882_ = v___x_1913_;
goto v___jp_1878_;
}
}
else
{
v_pos_1879_ = v_a_1794_;
v_array_1880_ = v_array_1803_;
v_idx_1881_ = v_idx_1804_;
v_res_1882_ = v___x_1911_;
goto v___jp_1878_;
}
}
else
{
v_pos_1879_ = v_a_1794_;
v_array_1880_ = v_array_1803_;
v_idx_1881_ = v_idx_1804_;
v_res_1882_ = v___x_1909_;
goto v___jp_1878_;
}
}
else
{
v_pos_1879_ = v_a_1794_;
v_array_1880_ = v_array_1803_;
v_idx_1881_ = v_idx_1804_;
v_res_1882_ = v___x_1907_;
goto v___jp_1878_;
}
}
else
{
v_pos_1879_ = v_a_1794_;
v_array_1880_ = v_array_1803_;
v_idx_1881_ = v_idx_1804_;
v_res_1882_ = v___x_1905_;
goto v___jp_1878_;
}
}
else
{
v_pos_1879_ = v_a_1794_;
v_array_1880_ = v_array_1803_;
v_idx_1881_ = v_idx_1804_;
v_res_1882_ = v___x_1903_;
goto v___jp_1878_;
}
}
else
{
v_pos_1879_ = v_a_1794_;
v_array_1880_ = v_array_1803_;
v_idx_1881_ = v_idx_1804_;
v_res_1882_ = v___x_1901_;
goto v___jp_1878_;
}
}
else
{
v_pos_1879_ = v_a_1794_;
v_array_1880_ = v_array_1803_;
v_idx_1881_ = v_idx_1804_;
v_res_1882_ = v___x_1899_;
goto v___jp_1878_;
}
}
else
{
v_pos_1879_ = v_a_1794_;
v_array_1880_ = v_array_1803_;
v_idx_1881_ = v_idx_1804_;
v_res_1882_ = v___x_1897_;
goto v___jp_1878_;
}
}
else
{
v_pos_1879_ = v_a_1794_;
v_array_1880_ = v_array_1803_;
v_idx_1881_ = v_idx_1804_;
v_res_1882_ = v___x_1895_;
goto v___jp_1878_;
}
}
else
{
v_pos_1879_ = v_a_1794_;
v_array_1880_ = v_array_1803_;
v_idx_1881_ = v_idx_1804_;
v_res_1882_ = v___x_1893_;
goto v___jp_1878_;
}
}
else
{
v_pos_1879_ = v_a_1794_;
v_array_1880_ = v_array_1803_;
v_idx_1881_ = v_idx_1804_;
v_res_1882_ = v___x_1891_;
goto v___jp_1878_;
}
}
v___jp_1928_:
{
uint8_t v___x_1929_; uint8_t v___x_1930_; 
v___x_1929_ = 65;
v___x_1930_ = lean_uint8_dec_le(v___x_1929_, v___x_1888_);
if (v___x_1930_ == 0)
{
goto v___jp_1889_;
}
else
{
uint8_t v___x_1931_; uint8_t v___x_1932_; 
v___x_1931_ = 90;
v___x_1932_ = lean_uint8_dec_le(v___x_1888_, v___x_1931_);
if (v___x_1932_ == 0)
{
goto v___jp_1889_;
}
else
{
v_pos_1879_ = v_a_1794_;
v_array_1880_ = v_array_1803_;
v_idx_1881_ = v_idx_1804_;
v_res_1882_ = v___x_1932_;
goto v___jp_1878_;
}
}
}
v___jp_1933_:
{
uint8_t v___x_1934_; uint8_t v___x_1935_; 
v___x_1934_ = 97;
v___x_1935_ = lean_uint8_dec_le(v___x_1934_, v___x_1888_);
if (v___x_1935_ == 0)
{
goto v___jp_1928_;
}
else
{
uint8_t v___x_1936_; uint8_t v___x_1937_; 
v___x_1936_ = 122;
v___x_1937_ = lean_uint8_dec_le(v___x_1888_, v___x_1936_);
if (v___x_1937_ == 0)
{
goto v___jp_1928_;
}
else
{
v_pos_1879_ = v_a_1794_;
v_array_1880_ = v_array_1803_;
v_idx_1881_ = v_idx_1804_;
v_res_1882_ = v___x_1937_;
goto v___jp_1878_;
}
}
}
}
v___jp_1795_:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__1));
v___x_1798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1798_, 0, v___y_1796_);
lean_ctor_set(v___x_1798_, 1, v___x_1797_);
return v___x_1798_;
}
v___jp_1799_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__3));
v___x_1802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___y_1800_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
return v___x_1802_;
}
v___jp_1808_:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1812_, 0, v_segments_1807_);
lean_ctor_set(v___x_1812_, 1, v_totalLength_1810_);
v___x_1813_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(v_config_1791_, v___x_1812_, v___y_1811_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_res_1814_; lean_object* v_pos_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1824_; 
v_res_1814_ = lean_ctor_get(v___x_1813_, 1);
v_pos_1815_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1817_ = v___x_1813_;
v_isShared_1818_ = v_isSharedCheck_1824_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_res_1814_);
lean_inc(v_pos_1815_);
lean_dec(v___x_1813_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1824_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v_fst_1819_; lean_object* v___x_1820_; lean_object* v___x_1822_; 
v_fst_1819_ = lean_ctor_get(v_res_1814_, 0);
lean_inc(v_fst_1819_);
lean_dec(v_res_1814_);
v___x_1820_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1820_, 0, v_fst_1819_);
lean_ctor_set_uint8(v___x_1820_, sizeof(void*)*1, v_isAbsolute_1809_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 1, v___x_1820_);
v___x_1822_ = v___x_1817_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_pos_1815_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
else
{
lean_object* v_pos_1825_; lean_object* v_err_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
v_pos_1825_ = lean_ctor_get(v___x_1813_, 0);
v_err_1826_ = lean_ctor_get(v___x_1813_, 1);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1813_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_err_1826_);
lean_inc(v_pos_1825_);
lean_dec(v___x_1813_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_pos_1825_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v_err_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
v___jp_1834_:
{
lean_object* v___x_1838_; uint8_t v___x_1839_; 
v___x_1838_ = lean_byte_array_size(v_array_1836_);
v___x_1839_ = lean_nat_dec_lt(v_idx_1837_, v___x_1838_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
lean_dec(v_idx_1837_);
lean_dec_ref(v_array_1836_);
lean_dec_ref(v_config_1791_);
v___x_1840_ = lean_box(0);
v___x_1841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1841_, 0, v_pos_1835_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
return v___x_1841_;
}
else
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
lean_dec_ref(v_pos_1835_);
v___x_1842_ = lean_unsigned_to_nat(1u);
v___x_1843_ = lean_nat_add(v_idx_1837_, v___x_1842_);
lean_dec(v_idx_1837_);
v___x_1844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1844_, 0, v_array_1836_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v_isAbsolute_1809_ = v___x_1839_;
v_totalLength_1810_ = v___x_1842_;
v___y_1811_ = v___x_1844_;
goto v___jp_1808_;
}
}
v___jp_1845_:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__5));
v___x_1848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___y_1846_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
return v___x_1848_;
}
v___jp_1849_:
{
if (v_allowEmpty_1793_ == 0)
{
v___y_1796_ = v_pos_1851_;
goto v___jp_1795_;
}
else
{
if (v_res_1852_ == 0)
{
if (v___y_1850_ == 0)
{
v___y_1846_ = v_pos_1851_;
goto v___jp_1845_;
}
else
{
v___y_1796_ = v_pos_1851_;
goto v___jp_1795_;
}
}
else
{
v___y_1846_ = v_pos_1851_;
goto v___jp_1845_;
}
}
}
v___jp_1853_:
{
if (v_res_1856_ == 0)
{
if (v_forceAbsolute_1792_ == 0)
{
v_isAbsolute_1809_ = v_isAbsolute_1805_;
v_totalLength_1810_ = v___x_1806_;
v___y_1811_ = v_pos_1855_;
goto v___jp_1808_;
}
else
{
lean_object* v_array_1857_; lean_object* v_idx_1858_; lean_object* v___x_1859_; uint8_t v___x_1860_; 
lean_dec_ref(v_config_1791_);
v_array_1857_ = lean_ctor_get(v_pos_1855_, 0);
v_idx_1858_ = lean_ctor_get(v_pos_1855_, 1);
v___x_1859_ = lean_byte_array_size(v_array_1857_);
v___x_1860_ = lean_nat_dec_lt(v_idx_1858_, v___x_1859_);
if (v___x_1860_ == 0)
{
v___y_1850_ = v___y_1854_;
v_pos_1851_ = v_pos_1855_;
v_res_1852_ = v_forceAbsolute_1792_;
goto v___jp_1849_;
}
else
{
v___y_1850_ = v___y_1854_;
v_pos_1851_ = v_pos_1855_;
v_res_1852_ = v_res_1856_;
goto v___jp_1849_;
}
}
}
else
{
lean_object* v_array_1861_; lean_object* v_idx_1862_; 
v_array_1861_ = lean_ctor_get(v_pos_1855_, 0);
lean_inc_ref(v_array_1861_);
v_idx_1862_ = lean_ctor_get(v_pos_1855_, 1);
lean_inc(v_idx_1862_);
v_pos_1835_ = v_pos_1855_;
v_array_1836_ = v_array_1861_;
v_idx_1837_ = v_idx_1862_;
goto v___jp_1834_;
}
}
v___jp_1863_:
{
lean_object* v_array_1867_; lean_object* v_idx_1868_; lean_object* v___x_1869_; uint8_t v___x_1870_; 
v_array_1867_ = lean_ctor_get(v___y_1864_, 0);
v_idx_1868_ = lean_ctor_get(v___y_1864_, 1);
v___x_1869_ = lean_byte_array_size(v_array_1867_);
v___x_1870_ = lean_nat_dec_lt(v_idx_1868_, v___x_1869_);
if (v___x_1870_ == 0)
{
v___y_1854_ = v___y_1865_;
v_pos_1855_ = v___y_1864_;
v_res_1856_ = v___y_1866_;
goto v___jp_1853_;
}
else
{
uint8_t v___x_1871_; uint8_t v___x_1872_; uint8_t v___x_1873_; 
v___x_1871_ = lean_byte_array_fget(v_array_1867_, v_idx_1868_);
v___x_1872_ = 47;
v___x_1873_ = lean_uint8_dec_eq(v___x_1871_, v___x_1872_);
if (v___x_1873_ == 0)
{
v___y_1854_ = v___y_1865_;
v_pos_1855_ = v___y_1864_;
v_res_1856_ = v___y_1866_;
goto v___jp_1853_;
}
else
{
lean_inc(v_idx_1868_);
lean_inc_ref(v_array_1867_);
v_pos_1835_ = v___y_1864_;
v_array_1836_ = v_array_1867_;
v_idx_1837_ = v_idx_1868_;
goto v___jp_1834_;
}
}
}
v___jp_1874_:
{
if (v_allowEmpty_1793_ == 0)
{
if (v_res_1877_ == 0)
{
if (v___y_1875_ == 0)
{
lean_dec_ref(v_config_1791_);
v___y_1800_ = v_pos_1876_;
goto v___jp_1799_;
}
else
{
v___y_1864_ = v_pos_1876_;
v___y_1865_ = v___y_1875_;
v___y_1866_ = v_res_1877_;
goto v___jp_1863_;
}
}
else
{
lean_dec_ref(v_config_1791_);
v___y_1800_ = v_pos_1876_;
goto v___jp_1799_;
}
}
else
{
v___y_1864_ = v_pos_1876_;
v___y_1865_ = v___y_1875_;
v___y_1866_ = v_isAbsolute_1805_;
goto v___jp_1863_;
}
}
v___jp_1878_:
{
lean_object* v___x_1883_; uint8_t v___x_1884_; 
v___x_1883_ = lean_byte_array_size(v_array_1880_);
lean_dec_ref(v_array_1880_);
v___x_1884_ = lean_nat_dec_lt(v_idx_1881_, v___x_1883_);
lean_dec(v_idx_1881_);
if (v___x_1884_ == 0)
{
uint8_t v___x_1885_; 
v___x_1885_ = 1;
v___y_1875_ = v_res_1882_;
v_pos_1876_ = v_pos_1879_;
v_res_1877_ = v___x_1885_;
goto v___jp_1874_;
}
else
{
v___y_1875_ = v_res_1882_;
v_pos_1876_ = v_pos_1879_;
v_res_1877_ = v_isAbsolute_1805_;
goto v___jp_1874_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath___boxed(lean_object* v_config_1942_, lean_object* v_forceAbsolute_1943_, lean_object* v_allowEmpty_1944_, lean_object* v_a_1945_){
_start:
{
uint8_t v_forceAbsolute_boxed_1946_; uint8_t v_allowEmpty_boxed_1947_; lean_object* v_res_1948_; 
v_forceAbsolute_boxed_1946_ = lean_unbox(v_forceAbsolute_1943_);
v_allowEmpty_boxed_1947_ = lean_unbox(v_allowEmpty_1944_);
v_res_1948_ = l_Std_Http_URI_Parser_parsePath(v_config_1942_, v_forceAbsolute_boxed_1946_, v_allowEmpty_boxed_1947_, v_a_1945_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0(lean_object* v_config_1949_, lean_object* v_inst_1950_, lean_object* v_a_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v___x_1953_; 
v___x_1953_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(v_config_1949_, v_a_1951_, v___y_1952_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0(lean_object* v_config_1954_, lean_object* v_inst_1955_, lean_object* v_a_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_1954_, v_a_1956_, v___y_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg(){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0));
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg___boxed(lean_object* v___dummy_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg();
return v_res_1962_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg();
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(lean_object* v_s_1964_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___boxed(lean_object* v_s_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(v_s_1966_);
lean_dec_ref(v_s_1966_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg(){
_start:
{
lean_object* v___x_1969_; 
v___x_1969_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0));
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg___boxed(lean_object* v___dummy_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg();
return v_res_1971_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg();
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(lean_object* v_s_1973_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___boxed(lean_object* v_s_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(v_s_1975_);
lean_dec_ref(v_s_1975_);
return v_res_1976_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(uint8_t v_c_1977_){
_start:
{
uint8_t v___x_2029_; uint8_t v___x_2030_; 
v___x_2029_ = 48;
v___x_2030_ = lean_uint8_dec_le(v___x_2029_, v_c_1977_);
if (v___x_2030_ == 0)
{
goto v___jp_2024_;
}
else
{
uint8_t v___x_2031_; uint8_t v___x_2032_; 
v___x_2031_ = 57;
v___x_2032_ = lean_uint8_dec_le(v_c_1977_, v___x_2031_);
if (v___x_2032_ == 0)
{
goto v___jp_2024_;
}
else
{
return v___x_2032_;
}
}
v___jp_1978_:
{
uint8_t v___x_1979_; uint8_t v___x_1980_; 
v___x_1979_ = 45;
v___x_1980_ = lean_uint8_dec_eq(v_c_1977_, v___x_1979_);
if (v___x_1980_ == 0)
{
uint8_t v___x_1981_; uint8_t v___x_1982_; 
v___x_1981_ = 46;
v___x_1982_ = lean_uint8_dec_eq(v_c_1977_, v___x_1981_);
if (v___x_1982_ == 0)
{
uint8_t v___x_1983_; uint8_t v___x_1984_; 
v___x_1983_ = 95;
v___x_1984_ = lean_uint8_dec_eq(v_c_1977_, v___x_1983_);
if (v___x_1984_ == 0)
{
uint8_t v___x_1985_; uint8_t v___x_1986_; 
v___x_1985_ = 126;
v___x_1986_ = lean_uint8_dec_eq(v_c_1977_, v___x_1985_);
if (v___x_1986_ == 0)
{
uint8_t v___x_1987_; uint8_t v___x_1988_; 
v___x_1987_ = 33;
v___x_1988_ = lean_uint8_dec_eq(v_c_1977_, v___x_1987_);
if (v___x_1988_ == 0)
{
uint8_t v___x_1989_; uint8_t v___x_1990_; 
v___x_1989_ = 36;
v___x_1990_ = lean_uint8_dec_eq(v_c_1977_, v___x_1989_);
if (v___x_1990_ == 0)
{
uint8_t v___x_1991_; uint8_t v___x_1992_; 
v___x_1991_ = 38;
v___x_1992_ = lean_uint8_dec_eq(v_c_1977_, v___x_1991_);
if (v___x_1992_ == 0)
{
uint8_t v___x_1993_; uint8_t v___x_1994_; 
v___x_1993_ = 39;
v___x_1994_ = lean_uint8_dec_eq(v_c_1977_, v___x_1993_);
if (v___x_1994_ == 0)
{
uint8_t v___x_1995_; uint8_t v___x_1996_; 
v___x_1995_ = 40;
v___x_1996_ = lean_uint8_dec_eq(v_c_1977_, v___x_1995_);
if (v___x_1996_ == 0)
{
uint8_t v___x_1997_; uint8_t v___x_1998_; 
v___x_1997_ = 41;
v___x_1998_ = lean_uint8_dec_eq(v_c_1977_, v___x_1997_);
if (v___x_1998_ == 0)
{
uint8_t v___x_1999_; uint8_t v___x_2000_; 
v___x_1999_ = 42;
v___x_2000_ = lean_uint8_dec_eq(v_c_1977_, v___x_1999_);
if (v___x_2000_ == 0)
{
uint8_t v___x_2001_; uint8_t v___x_2002_; 
v___x_2001_ = 43;
v___x_2002_ = lean_uint8_dec_eq(v_c_1977_, v___x_2001_);
if (v___x_2002_ == 0)
{
uint8_t v___x_2003_; uint8_t v___x_2004_; 
v___x_2003_ = 44;
v___x_2004_ = lean_uint8_dec_eq(v_c_1977_, v___x_2003_);
if (v___x_2004_ == 0)
{
uint8_t v___x_2005_; uint8_t v___x_2006_; 
v___x_2005_ = 59;
v___x_2006_ = lean_uint8_dec_eq(v_c_1977_, v___x_2005_);
if (v___x_2006_ == 0)
{
uint8_t v___x_2007_; uint8_t v___x_2008_; 
v___x_2007_ = 61;
v___x_2008_ = lean_uint8_dec_eq(v_c_1977_, v___x_2007_);
if (v___x_2008_ == 0)
{
uint8_t v___x_2009_; uint8_t v___x_2010_; 
v___x_2009_ = 58;
v___x_2010_ = lean_uint8_dec_eq(v_c_1977_, v___x_2009_);
if (v___x_2010_ == 0)
{
uint8_t v___x_2011_; uint8_t v___x_2012_; 
v___x_2011_ = 64;
v___x_2012_ = lean_uint8_dec_eq(v_c_1977_, v___x_2011_);
if (v___x_2012_ == 0)
{
uint8_t v___x_2013_; uint8_t v___x_2014_; 
v___x_2013_ = 47;
v___x_2014_ = lean_uint8_dec_eq(v_c_1977_, v___x_2013_);
if (v___x_2014_ == 0)
{
uint8_t v___x_2015_; uint8_t v___x_2016_; 
v___x_2015_ = 63;
v___x_2016_ = lean_uint8_dec_eq(v_c_1977_, v___x_2015_);
if (v___x_2016_ == 0)
{
uint8_t v___x_2017_; uint8_t v___x_2018_; 
v___x_2017_ = 37;
v___x_2018_ = lean_uint8_dec_eq(v_c_1977_, v___x_2017_);
return v___x_2018_;
}
else
{
return v___x_2016_;
}
}
else
{
return v___x_2014_;
}
}
else
{
return v___x_2012_;
}
}
else
{
return v___x_2010_;
}
}
else
{
return v___x_2008_;
}
}
else
{
return v___x_2006_;
}
}
else
{
return v___x_2004_;
}
}
else
{
return v___x_2002_;
}
}
else
{
return v___x_2000_;
}
}
else
{
return v___x_1998_;
}
}
else
{
return v___x_1996_;
}
}
else
{
return v___x_1994_;
}
}
else
{
return v___x_1992_;
}
}
else
{
return v___x_1990_;
}
}
else
{
return v___x_1988_;
}
}
else
{
return v___x_1986_;
}
}
else
{
return v___x_1984_;
}
}
else
{
return v___x_1982_;
}
}
else
{
return v___x_1980_;
}
}
v___jp_2019_:
{
uint8_t v___x_2020_; uint8_t v___x_2021_; 
v___x_2020_ = 65;
v___x_2021_ = lean_uint8_dec_le(v___x_2020_, v_c_1977_);
if (v___x_2021_ == 0)
{
goto v___jp_1978_;
}
else
{
uint8_t v___x_2022_; uint8_t v___x_2023_; 
v___x_2022_ = 90;
v___x_2023_ = lean_uint8_dec_le(v_c_1977_, v___x_2022_);
if (v___x_2023_ == 0)
{
goto v___jp_1978_;
}
else
{
return v___x_2023_;
}
}
}
v___jp_2024_:
{
uint8_t v___x_2025_; uint8_t v___x_2026_; 
v___x_2025_ = 97;
v___x_2026_ = lean_uint8_dec_le(v___x_2025_, v_c_1977_);
if (v___x_2026_ == 0)
{
goto v___jp_2019_;
}
else
{
uint8_t v___x_2027_; uint8_t v___x_2028_; 
v___x_2027_ = 122;
v___x_2028_ = lean_uint8_dec_le(v_c_1977_, v___x_2027_);
if (v___x_2028_ == 0)
{
goto v___jp_2019_;
}
else
{
return v___x_2028_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0___boxed(lean_object* v_c_2033_){
_start:
{
uint8_t v_c_boxed_2034_; uint8_t v_res_2035_; lean_object* v_r_2036_; 
v_c_boxed_2034_ = lean_unbox(v_c_2033_);
v_res_2035_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(v_c_boxed_2034_);
v_r_2036_ = lean_box(v_res_2035_);
return v_r_2036_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(lean_object* v___x_2037_, lean_object* v___x_2038_, lean_object* v_a_2039_, lean_object* v_b_2040_){
_start:
{
lean_object* v_it_2042_; 
if (lean_obj_tag(v_a_2039_) == 0)
{
lean_object* v_currPos_2046_; lean_object* v_searcher_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2073_; 
v_currPos_2046_ = lean_ctor_get(v_a_2039_, 0);
v_searcher_2047_ = lean_ctor_get(v_a_2039_, 1);
v_isSharedCheck_2073_ = !lean_is_exclusive(v_a_2039_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2049_ = v_a_2039_;
v_isShared_2050_ = v_isSharedCheck_2073_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_searcher_2047_);
lean_inc(v_currPos_2046_);
lean_dec(v_a_2039_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2073_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v_str_2051_; lean_object* v_startInclusive_2052_; lean_object* v_endExclusive_2053_; lean_object* v___x_2054_; uint8_t v_decide_2055_; 
v_str_2051_ = lean_ctor_get(v___x_2037_, 0);
v_startInclusive_2052_ = lean_ctor_get(v___x_2037_, 1);
v_endExclusive_2053_ = lean_ctor_get(v___x_2037_, 2);
v___x_2054_ = lean_nat_sub(v_endExclusive_2053_, v_startInclusive_2052_);
v_decide_2055_ = lean_nat_dec_eq(v_searcher_2047_, v___x_2054_);
lean_dec(v___x_2054_);
if (v_decide_2055_ == 0)
{
uint32_t v___x_2056_; lean_object* v___x_2057_; uint32_t v___x_2058_; uint8_t v___x_2059_; 
v___x_2056_ = 38;
v___x_2057_ = lean_nat_add(v_startInclusive_2052_, v_searcher_2047_);
v___x_2058_ = lean_string_utf8_get_fast(v_str_2051_, v___x_2057_);
v___x_2059_ = lean_uint32_dec_eq(v___x_2058_, v___x_2056_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2063_; 
lean_dec(v_searcher_2047_);
v___x_2060_ = lean_string_utf8_next_fast(v_str_2051_, v___x_2057_);
lean_dec(v___x_2057_);
v___x_2061_ = lean_nat_sub(v___x_2060_, v_startInclusive_2052_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 1, v___x_2061_);
v___x_2063_ = v___x_2049_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_currPos_2046_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v___x_2061_);
v___x_2063_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
v_a_2039_ = v___x_2063_;
goto _start;
}
}
else
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v_nextIt_2070_; 
lean_dec(v_currPos_2046_);
v___x_2066_ = lean_string_utf8_next_fast(v_str_2051_, v___x_2057_);
v___x_2067_ = lean_nat_sub(v___x_2066_, v___x_2057_);
lean_dec(v___x_2057_);
v___x_2068_ = lean_nat_add(v_searcher_2047_, v___x_2067_);
lean_dec(v___x_2067_);
lean_dec(v_searcher_2047_);
lean_inc(v___x_2068_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 1, v___x_2068_);
lean_ctor_set(v___x_2049_, 0, v___x_2068_);
v_nextIt_2070_ = v___x_2049_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2068_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v___x_2068_);
v_nextIt_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
v_it_2042_ = v_nextIt_2070_;
goto v___jp_2041_;
}
}
}
else
{
lean_object* v___x_2072_; 
lean_del_object(v___x_2049_);
lean_dec(v_searcher_2047_);
lean_dec(v_currPos_2046_);
v___x_2072_ = lean_box(1);
v_it_2042_ = v___x_2072_;
goto v___jp_2041_;
}
}
}
else
{
return v_b_2040_;
}
v___jp_2041_:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = lean_unsigned_to_nat(1u);
v___x_2044_ = lean_nat_add(v_b_2040_, v___x_2043_);
lean_dec(v_b_2040_);
v_a_2039_ = v_it_2042_;
v_b_2040_ = v___x_2044_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg___boxed(lean_object* v___x_2074_, lean_object* v___x_2075_, lean_object* v_a_2076_, lean_object* v_b_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2074_, v___x_2075_, v_a_2076_, v_b_2077_);
lean_dec(v___x_2075_);
lean_dec_ref(v___x_2074_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(lean_object* v___x_2079_, lean_object* v___x_2080_, lean_object* v___x_2081_, lean_object* v_a_2082_, lean_object* v_b_2083_){
_start:
{
lean_object* v_it_2085_; 
if (lean_obj_tag(v_a_2082_) == 0)
{
lean_object* v_currPos_2089_; lean_object* v_searcher_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2116_; 
v_currPos_2089_ = lean_ctor_get(v_a_2082_, 0);
v_searcher_2090_ = lean_ctor_get(v_a_2082_, 1);
v_isSharedCheck_2116_ = !lean_is_exclusive(v_a_2082_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2092_ = v_a_2082_;
v_isShared_2093_ = v_isSharedCheck_2116_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_searcher_2090_);
lean_inc(v_currPos_2089_);
lean_dec(v_a_2082_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2116_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v_str_2094_; lean_object* v_startInclusive_2095_; lean_object* v_endExclusive_2096_; lean_object* v___x_2097_; uint8_t v_decide_2098_; 
v_str_2094_ = lean_ctor_get(v___x_2080_, 0);
v_startInclusive_2095_ = lean_ctor_get(v___x_2080_, 1);
v_endExclusive_2096_ = lean_ctor_get(v___x_2080_, 2);
v___x_2097_ = lean_nat_sub(v_endExclusive_2096_, v_startInclusive_2095_);
v_decide_2098_ = lean_nat_dec_eq(v_searcher_2090_, v___x_2097_);
lean_dec(v___x_2097_);
if (v_decide_2098_ == 0)
{
lean_object* v___x_2099_; uint32_t v___x_2100_; uint32_t v___x_2101_; uint8_t v___x_2102_; 
v___x_2099_ = lean_nat_add(v_startInclusive_2095_, v_searcher_2090_);
v___x_2100_ = lean_string_utf8_get_fast(v_str_2094_, v___x_2099_);
v___x_2101_ = 38;
v___x_2102_ = lean_uint32_dec_eq(v___x_2100_, v___x_2101_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2106_; 
lean_dec(v_searcher_2090_);
v___x_2103_ = lean_string_utf8_next_fast(v_str_2094_, v___x_2099_);
lean_dec(v___x_2099_);
v___x_2104_ = lean_nat_sub(v___x_2103_, v_startInclusive_2095_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 1, v___x_2104_);
v___x_2106_ = v___x_2092_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_currPos_2089_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2107_; 
v___x_2107_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2080_, v___x_2081_, v___x_2106_, v_b_2083_);
return v___x_2107_;
}
}
else
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v_nextIt_2113_; 
lean_dec(v_currPos_2089_);
v___x_2109_ = lean_string_utf8_next_fast(v_str_2094_, v___x_2099_);
v___x_2110_ = lean_nat_sub(v___x_2109_, v___x_2099_);
lean_dec(v___x_2099_);
v___x_2111_ = lean_nat_add(v_searcher_2090_, v___x_2110_);
lean_dec(v___x_2110_);
lean_dec(v_searcher_2090_);
lean_inc(v___x_2111_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 1, v___x_2111_);
lean_ctor_set(v___x_2092_, 0, v___x_2111_);
v_nextIt_2113_ = v___x_2092_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2111_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v___x_2111_);
v_nextIt_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
v_it_2085_ = v_nextIt_2113_;
goto v___jp_2084_;
}
}
}
else
{
lean_object* v___x_2115_; 
lean_del_object(v___x_2092_);
lean_dec(v_searcher_2090_);
lean_dec(v_currPos_2089_);
v___x_2115_ = lean_box(1);
v_it_2085_ = v___x_2115_;
goto v___jp_2084_;
}
}
}
else
{
return v_b_2083_;
}
v___jp_2084_:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2086_ = lean_unsigned_to_nat(1u);
v___x_2087_ = lean_nat_add(v_b_2083_, v___x_2086_);
lean_dec(v_b_2083_);
v___x_2088_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2080_, v___x_2081_, v_it_2085_, v___x_2087_);
return v___x_2088_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg___boxed(lean_object* v___x_2117_, lean_object* v___x_2118_, lean_object* v___x_2119_, lean_object* v_a_2120_, lean_object* v_b_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2117_, v___x_2118_, v___x_2119_, v_a_2120_, v_b_2121_);
lean_dec(v___x_2119_);
lean_dec_ref(v___x_2118_);
lean_dec_ref(v___x_2117_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(lean_object* v_out_2123_, lean_object* v_a_2124_, lean_object* v_b_2125_){
_start:
{
if (lean_obj_tag(v_a_2124_) == 0)
{
lean_object* v_currPos_2126_; lean_object* v_searcher_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2166_; 
v_currPos_2126_ = lean_ctor_get(v_a_2124_, 0);
v_searcher_2127_ = lean_ctor_get(v_a_2124_, 1);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_a_2124_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2129_ = v_a_2124_;
v_isShared_2130_ = v_isSharedCheck_2166_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_searcher_2127_);
lean_inc(v_currPos_2126_);
lean_dec(v_a_2124_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2166_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v_str_2131_; lean_object* v_startInclusive_2132_; lean_object* v_endExclusive_2133_; lean_object* v_it_2135_; lean_object* v_startInclusive_2136_; lean_object* v_endExclusive_2137_; lean_object* v___x_2144_; uint8_t v_decide_2145_; 
v_str_2131_ = lean_ctor_get(v_out_2123_, 0);
v_startInclusive_2132_ = lean_ctor_get(v_out_2123_, 1);
v_endExclusive_2133_ = lean_ctor_get(v_out_2123_, 2);
v___x_2144_ = lean_nat_sub(v_endExclusive_2133_, v_startInclusive_2132_);
v_decide_2145_ = lean_nat_dec_eq(v_searcher_2127_, v___x_2144_);
if (v_decide_2145_ == 0)
{
uint32_t v___x_2146_; lean_object* v___x_2147_; uint32_t v___x_2148_; uint8_t v___x_2149_; 
lean_dec(v___x_2144_);
v___x_2146_ = 61;
v___x_2147_ = lean_nat_add(v_startInclusive_2132_, v_searcher_2127_);
v___x_2148_ = lean_string_utf8_get_fast(v_str_2131_, v___x_2147_);
v___x_2149_ = lean_uint32_dec_eq(v___x_2148_, v___x_2146_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2153_; 
lean_dec(v_searcher_2127_);
v___x_2150_ = lean_string_utf8_next_fast(v_str_2131_, v___x_2147_);
lean_dec(v___x_2147_);
v___x_2151_ = lean_nat_sub(v___x_2150_, v_startInclusive_2132_);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 1, v___x_2151_);
v___x_2153_ = v___x_2129_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_currPos_2126_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v___x_2151_);
v___x_2153_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
v_a_2124_ = v___x_2153_;
goto _start;
}
}
else
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v_slice_2159_; lean_object* v_nextIt_2161_; 
v___x_2156_ = lean_string_utf8_next_fast(v_str_2131_, v___x_2147_);
v___x_2157_ = lean_nat_sub(v___x_2156_, v___x_2147_);
lean_dec(v___x_2147_);
v___x_2158_ = lean_nat_add(v_searcher_2127_, v___x_2157_);
lean_dec(v___x_2157_);
v_slice_2159_ = l_String_Slice_subslice_x21(v_out_2123_, v_currPos_2126_, v_searcher_2127_);
lean_inc(v___x_2158_);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 1, v___x_2158_);
lean_ctor_set(v___x_2129_, 0, v___x_2158_);
v_nextIt_2161_ = v___x_2129_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v___x_2158_);
v_nextIt_2161_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
lean_object* v_startInclusive_2162_; lean_object* v_endExclusive_2163_; 
v_startInclusive_2162_ = lean_ctor_get(v_slice_2159_, 0);
lean_inc(v_startInclusive_2162_);
v_endExclusive_2163_ = lean_ctor_get(v_slice_2159_, 1);
lean_inc(v_endExclusive_2163_);
lean_dec_ref(v_slice_2159_);
v_it_2135_ = v_nextIt_2161_;
v_startInclusive_2136_ = v_startInclusive_2162_;
v_endExclusive_2137_ = v_endExclusive_2163_;
goto v___jp_2134_;
}
}
}
else
{
lean_object* v___x_2165_; 
lean_del_object(v___x_2129_);
lean_dec(v_searcher_2127_);
v___x_2165_ = lean_box(1);
v_it_2135_ = v___x_2165_;
v_startInclusive_2136_ = v_currPos_2126_;
v_endExclusive_2137_ = v___x_2144_;
goto v___jp_2134_;
}
v___jp_2134_:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2138_ = lean_nat_add(v_startInclusive_2132_, v_startInclusive_2136_);
lean_dec(v_startInclusive_2136_);
v___x_2139_ = lean_nat_add(v_startInclusive_2132_, v_endExclusive_2137_);
lean_dec(v_endExclusive_2137_);
lean_inc_ref(v_str_2131_);
v___x_2140_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2140_, 0, v_str_2131_);
lean_ctor_set(v___x_2140_, 1, v___x_2138_);
lean_ctor_set(v___x_2140_, 2, v___x_2139_);
v___x_2141_ = l_String_Slice_toString(v___x_2140_);
lean_dec_ref_known(v___x_2140_, 3);
v___x_2142_ = lean_array_push(v_b_2125_, v___x_2141_);
v_a_2124_ = v_it_2135_;
v_b_2125_ = v___x_2142_;
goto _start;
}
}
}
else
{
return v_b_2125_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg___boxed(lean_object* v_out_2167_, lean_object* v_a_2168_, lean_object* v_b_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_2167_, v_a_2168_, v_b_2169_);
lean_dec_ref(v_out_2167_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(lean_object* v___x_2174_, lean_object* v___x_2175_, lean_object* v___x_2176_, lean_object* v_a_2177_, lean_object* v_b_2178_){
_start:
{
lean_object* v_it_2180_; lean_object* v_startInclusive_2181_; lean_object* v_endExclusive_2182_; 
if (lean_obj_tag(v_a_2177_) == 0)
{
lean_object* v_currPos_2207_; lean_object* v_searcher_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2237_; 
v_currPos_2207_ = lean_ctor_get(v_a_2177_, 0);
v_searcher_2208_ = lean_ctor_get(v_a_2177_, 1);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_a_2177_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2210_ = v_a_2177_;
v_isShared_2211_ = v_isSharedCheck_2237_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_searcher_2208_);
lean_inc(v_currPos_2207_);
lean_dec(v_a_2177_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2237_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v_str_2212_; lean_object* v_startInclusive_2213_; lean_object* v_endExclusive_2214_; lean_object* v___x_2215_; uint8_t v_decide_2216_; 
v_str_2212_ = lean_ctor_get(v___x_2175_, 0);
v_startInclusive_2213_ = lean_ctor_get(v___x_2175_, 1);
v_endExclusive_2214_ = lean_ctor_get(v___x_2175_, 2);
v___x_2215_ = lean_nat_sub(v_endExclusive_2214_, v_startInclusive_2213_);
v_decide_2216_ = lean_nat_dec_eq(v_searcher_2208_, v___x_2215_);
lean_dec(v___x_2215_);
if (v_decide_2216_ == 0)
{
uint32_t v___x_2217_; lean_object* v___x_2218_; uint32_t v___x_2219_; uint8_t v___x_2220_; 
v___x_2217_ = 38;
v___x_2218_ = lean_nat_add(v_startInclusive_2213_, v_searcher_2208_);
v___x_2219_ = lean_string_utf8_get_fast(v_str_2212_, v___x_2218_);
v___x_2220_ = lean_uint32_dec_eq(v___x_2219_, v___x_2217_);
if (v___x_2220_ == 0)
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
lean_dec(v_searcher_2208_);
v___x_2221_ = lean_string_utf8_next_fast(v_str_2212_, v___x_2218_);
lean_dec(v___x_2218_);
v___x_2222_ = lean_nat_sub(v___x_2221_, v_startInclusive_2213_);
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 1, v___x_2222_);
v___x_2224_ = v___x_2210_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_currPos_2207_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
v_a_2177_ = v___x_2224_;
goto _start;
}
}
else
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v_slice_2230_; lean_object* v_nextIt_2232_; 
v___x_2227_ = lean_string_utf8_next_fast(v_str_2212_, v___x_2218_);
v___x_2228_ = lean_nat_sub(v___x_2227_, v___x_2218_);
lean_dec(v___x_2218_);
v___x_2229_ = lean_nat_add(v_searcher_2208_, v___x_2228_);
lean_dec(v___x_2228_);
v_slice_2230_ = l_String_Slice_subslice_x21(v___x_2175_, v_currPos_2207_, v_searcher_2208_);
lean_inc(v___x_2229_);
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 1, v___x_2229_);
lean_ctor_set(v___x_2210_, 0, v___x_2229_);
v_nextIt_2232_ = v___x_2210_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2229_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v___x_2229_);
v_nextIt_2232_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
lean_object* v_startInclusive_2233_; lean_object* v_endExclusive_2234_; 
v_startInclusive_2233_ = lean_ctor_get(v_slice_2230_, 0);
lean_inc(v_startInclusive_2233_);
v_endExclusive_2234_ = lean_ctor_get(v_slice_2230_, 1);
lean_inc(v_endExclusive_2234_);
lean_dec_ref(v_slice_2230_);
v_it_2180_ = v_nextIt_2232_;
v_startInclusive_2181_ = v_startInclusive_2233_;
v_endExclusive_2182_ = v_endExclusive_2234_;
goto v___jp_2179_;
}
}
}
else
{
lean_object* v___x_2236_; 
lean_del_object(v___x_2210_);
lean_dec(v_searcher_2208_);
v___x_2236_ = lean_box(1);
lean_inc(v___x_2176_);
v_it_2180_ = v___x_2236_;
v_startInclusive_2181_ = v_currPos_2207_;
v_endExclusive_2182_ = v___x_2176_;
goto v___jp_2179_;
}
}
}
else
{
lean_object* v___x_2238_; 
lean_dec(v___x_2176_);
lean_dec_ref(v___x_2174_);
v___x_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2238_, 0, v_b_2178_);
return v___x_2238_;
}
v___jp_2179_:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
lean_inc_ref(v___x_2174_);
v___x_2183_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2174_);
lean_ctor_set(v___x_2183_, 1, v_startInclusive_2181_);
lean_ctor_set(v___x_2183_, 2, v_endExclusive_2182_);
v___x_2184_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
v___x_2185_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0));
v___x_2186_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_2183_, v___x_2184_, v___x_2185_);
lean_dec_ref_known(v___x_2183_, 3);
v___x_2187_ = lean_array_to_list(v___x_2186_);
if (lean_obj_tag(v___x_2187_) == 0)
{
v_a_2177_ = v_it_2180_;
goto _start;
}
else
{
lean_object* v_tail_2189_; 
v_tail_2189_ = lean_ctor_get(v___x_2187_, 1);
if (lean_obj_tag(v_tail_2189_) == 0)
{
lean_object* v_head_2190_; lean_object* v___x_2191_; 
v_head_2190_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_head_2190_);
lean_dec_ref_known(v___x_2187_, 2);
v___x_2191_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2190_);
lean_dec(v_head_2190_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v___x_2192_; 
lean_dec(v_it_2180_);
lean_dec_ref(v_b_2178_);
lean_dec(v___x_2176_);
lean_dec_ref(v___x_2174_);
v___x_2192_ = lean_box(0);
return v___x_2192_;
}
else
{
lean_object* v_val_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v_val_2193_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_val_2193_);
lean_dec_ref_known(v___x_2191_, 1);
v___x_2194_ = lean_box(0);
v___x_2195_ = l_Std_Http_URI_Query_insertEncoded(v_b_2178_, v_val_2193_, v___x_2194_);
v_a_2177_ = v_it_2180_;
v_b_2178_ = v___x_2195_;
goto _start;
}
}
else
{
lean_object* v_head_2197_; lean_object* v___x_2198_; 
lean_inc(v_tail_2189_);
v_head_2197_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_head_2197_);
lean_dec_ref_known(v___x_2187_, 2);
v___x_2198_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2197_);
lean_dec(v_head_2197_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v___x_2199_; 
lean_dec(v_tail_2189_);
lean_dec(v_it_2180_);
lean_dec_ref(v_b_2178_);
lean_dec(v___x_2176_);
lean_dec_ref(v___x_2174_);
v___x_2199_ = lean_box(0);
return v___x_2199_;
}
else
{
lean_object* v_val_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v_val_2200_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_val_2200_);
lean_dec_ref_known(v___x_2198_, 1);
v___x_2201_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1));
v___x_2202_ = l_String_intercalate(v___x_2201_, v_tail_2189_);
v___x_2203_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2202_);
lean_dec_ref(v___x_2202_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v___x_2204_; 
lean_dec(v_val_2200_);
lean_dec(v_it_2180_);
lean_dec_ref(v_b_2178_);
lean_dec(v___x_2176_);
lean_dec_ref(v___x_2174_);
v___x_2204_ = lean_box(0);
return v___x_2204_;
}
else
{
lean_object* v___x_2205_; 
v___x_2205_ = l_Std_Http_URI_Query_insertEncoded(v_b_2178_, v_val_2200_, v___x_2203_);
v_a_2177_ = v_it_2180_;
v_b_2178_ = v___x_2205_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___boxed(lean_object* v___x_2239_, lean_object* v___x_2240_, lean_object* v___x_2241_, lean_object* v_a_2242_, lean_object* v_b_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2239_, v___x_2240_, v___x_2241_, v_a_2242_, v_b_2243_);
lean_dec_ref(v___x_2240_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(lean_object* v___x_2245_, lean_object* v___x_2246_, lean_object* v___x_2247_, lean_object* v_a_2248_, lean_object* v_b_2249_){
_start:
{
lean_object* v_it_2251_; lean_object* v_startInclusive_2252_; lean_object* v_endExclusive_2253_; 
if (lean_obj_tag(v_a_2248_) == 0)
{
lean_object* v_currPos_2278_; lean_object* v_searcher_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2308_; 
v_currPos_2278_ = lean_ctor_get(v_a_2248_, 0);
v_searcher_2279_ = lean_ctor_get(v_a_2248_, 1);
v_isSharedCheck_2308_ = !lean_is_exclusive(v_a_2248_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2281_ = v_a_2248_;
v_isShared_2282_ = v_isSharedCheck_2308_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_searcher_2279_);
lean_inc(v_currPos_2278_);
lean_dec(v_a_2248_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2308_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v_str_2283_; lean_object* v_startInclusive_2284_; lean_object* v_endExclusive_2285_; lean_object* v___x_2286_; uint8_t v_decide_2287_; 
v_str_2283_ = lean_ctor_get(v___x_2246_, 0);
v_startInclusive_2284_ = lean_ctor_get(v___x_2246_, 1);
v_endExclusive_2285_ = lean_ctor_get(v___x_2246_, 2);
v___x_2286_ = lean_nat_sub(v_endExclusive_2285_, v_startInclusive_2284_);
v_decide_2287_ = lean_nat_dec_eq(v_searcher_2279_, v___x_2286_);
lean_dec(v___x_2286_);
if (v_decide_2287_ == 0)
{
lean_object* v___x_2288_; uint32_t v___x_2289_; uint32_t v___x_2290_; uint8_t v___x_2291_; 
v___x_2288_ = lean_nat_add(v_startInclusive_2284_, v_searcher_2279_);
v___x_2289_ = lean_string_utf8_get_fast(v_str_2283_, v___x_2288_);
v___x_2290_ = 38;
v___x_2291_ = lean_uint32_dec_eq(v___x_2289_, v___x_2290_);
if (v___x_2291_ == 0)
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2295_; 
lean_dec(v_searcher_2279_);
v___x_2292_ = lean_string_utf8_next_fast(v_str_2283_, v___x_2288_);
lean_dec(v___x_2288_);
v___x_2293_ = lean_nat_sub(v___x_2292_, v_startInclusive_2284_);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 1, v___x_2293_);
v___x_2295_ = v___x_2281_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_currPos_2278_);
lean_ctor_set(v_reuseFailAlloc_2297_, 1, v___x_2293_);
v___x_2295_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
lean_object* v___x_2296_; 
v___x_2296_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2245_, v___x_2246_, v___x_2247_, v___x_2295_, v_b_2249_);
return v___x_2296_;
}
}
else
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v_slice_2301_; lean_object* v_nextIt_2303_; 
v___x_2298_ = lean_string_utf8_next_fast(v_str_2283_, v___x_2288_);
v___x_2299_ = lean_nat_sub(v___x_2298_, v___x_2288_);
lean_dec(v___x_2288_);
v___x_2300_ = lean_nat_add(v_searcher_2279_, v___x_2299_);
lean_dec(v___x_2299_);
v_slice_2301_ = l_String_Slice_subslice_x21(v___x_2246_, v_currPos_2278_, v_searcher_2279_);
lean_inc(v___x_2300_);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 1, v___x_2300_);
lean_ctor_set(v___x_2281_, 0, v___x_2300_);
v_nextIt_2303_ = v___x_2281_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2306_, 1, v___x_2300_);
v_nextIt_2303_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
lean_object* v_startInclusive_2304_; lean_object* v_endExclusive_2305_; 
v_startInclusive_2304_ = lean_ctor_get(v_slice_2301_, 0);
lean_inc(v_startInclusive_2304_);
v_endExclusive_2305_ = lean_ctor_get(v_slice_2301_, 1);
lean_inc(v_endExclusive_2305_);
lean_dec_ref(v_slice_2301_);
v_it_2251_ = v_nextIt_2303_;
v_startInclusive_2252_ = v_startInclusive_2304_;
v_endExclusive_2253_ = v_endExclusive_2305_;
goto v___jp_2250_;
}
}
}
else
{
lean_object* v___x_2307_; 
lean_del_object(v___x_2281_);
lean_dec(v_searcher_2279_);
v___x_2307_ = lean_box(1);
lean_inc(v___x_2247_);
v_it_2251_ = v___x_2307_;
v_startInclusive_2252_ = v_currPos_2278_;
v_endExclusive_2253_ = v___x_2247_;
goto v___jp_2250_;
}
}
}
else
{
lean_object* v___x_2309_; 
lean_dec(v___x_2247_);
lean_dec_ref(v___x_2245_);
v___x_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2309_, 0, v_b_2249_);
return v___x_2309_;
}
v___jp_2250_:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
lean_inc_ref(v___x_2245_);
v___x_2254_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2245_);
lean_ctor_set(v___x_2254_, 1, v_startInclusive_2252_);
lean_ctor_set(v___x_2254_, 2, v_endExclusive_2253_);
v___x_2255_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
v___x_2256_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0));
v___x_2257_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_2254_, v___x_2255_, v___x_2256_);
lean_dec_ref_known(v___x_2254_, 3);
v___x_2258_ = lean_array_to_list(v___x_2257_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v___x_2259_; 
v___x_2259_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2245_, v___x_2246_, v___x_2247_, v_it_2251_, v_b_2249_);
return v___x_2259_;
}
else
{
lean_object* v_tail_2260_; 
v_tail_2260_ = lean_ctor_get(v___x_2258_, 1);
if (lean_obj_tag(v_tail_2260_) == 0)
{
lean_object* v_head_2261_; lean_object* v___x_2262_; 
v_head_2261_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_head_2261_);
lean_dec_ref_known(v___x_2258_, 2);
v___x_2262_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2261_);
lean_dec(v_head_2261_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v___x_2263_; 
lean_dec(v_it_2251_);
lean_dec_ref(v_b_2249_);
lean_dec(v___x_2247_);
lean_dec_ref(v___x_2245_);
v___x_2263_ = lean_box(0);
return v___x_2263_;
}
else
{
lean_object* v_val_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v_val_2264_ = lean_ctor_get(v___x_2262_, 0);
lean_inc(v_val_2264_);
lean_dec_ref_known(v___x_2262_, 1);
v___x_2265_ = lean_box(0);
v___x_2266_ = l_Std_Http_URI_Query_insertEncoded(v_b_2249_, v_val_2264_, v___x_2265_);
v___x_2267_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2245_, v___x_2246_, v___x_2247_, v_it_2251_, v___x_2266_);
return v___x_2267_;
}
}
else
{
lean_object* v_head_2268_; lean_object* v___x_2269_; 
lean_inc(v_tail_2260_);
v_head_2268_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_head_2268_);
lean_dec_ref_known(v___x_2258_, 2);
v___x_2269_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2268_);
lean_dec(v_head_2268_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v___x_2270_; 
lean_dec(v_tail_2260_);
lean_dec(v_it_2251_);
lean_dec_ref(v_b_2249_);
lean_dec(v___x_2247_);
lean_dec_ref(v___x_2245_);
v___x_2270_ = lean_box(0);
return v___x_2270_;
}
else
{
lean_object* v_val_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v_val_2271_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_val_2271_);
lean_dec_ref_known(v___x_2269_, 1);
v___x_2272_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1));
v___x_2273_ = l_String_intercalate(v___x_2272_, v_tail_2260_);
v___x_2274_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2273_);
lean_dec_ref(v___x_2273_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v___x_2275_; 
lean_dec(v_val_2271_);
lean_dec(v_it_2251_);
lean_dec_ref(v_b_2249_);
lean_dec(v___x_2247_);
lean_dec_ref(v___x_2245_);
v___x_2275_ = lean_box(0);
return v___x_2275_;
}
else
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = l_Std_Http_URI_Query_insertEncoded(v_b_2249_, v_val_2271_, v___x_2274_);
v___x_2277_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2245_, v___x_2246_, v___x_2247_, v_it_2251_, v___x_2276_);
return v___x_2277_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg___boxed(lean_object* v___x_2310_, lean_object* v___x_2311_, lean_object* v___x_2312_, lean_object* v_a_2313_, lean_object* v_b_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2310_, v___x_2311_, v___x_2312_, v_a_2313_, v_b_2314_);
lean_dec_ref(v___x_2311_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(lean_object* v_config_2321_, lean_object* v_a_2322_){
_start:
{
lean_object* v_maxQueryLength_2323_; lean_object* v_maxQueryParams_2324_; lean_object* v___f_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v_snd_2328_; lean_object* v_fst_2329_; lean_object* v_fst_2330_; lean_object* v_array_2331_; lean_object* v_idx_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2382_; 
v_maxQueryLength_2323_ = lean_ctor_get(v_config_2321_, 4);
lean_inc(v_maxQueryLength_2323_);
v_maxQueryParams_2324_ = lean_ctor_get(v_config_2321_, 8);
lean_inc(v_maxQueryParams_2324_);
lean_dec_ref(v_config_2321_);
v___f_2325_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2326_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2322_);
v___x_2327_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2325_, v_maxQueryLength_2323_, v___x_2326_, v_a_2322_);
lean_dec(v_maxQueryLength_2323_);
v_snd_2328_ = lean_ctor_get(v___x_2327_, 1);
lean_inc(v_snd_2328_);
v_fst_2329_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_fst_2329_);
lean_dec_ref(v___x_2327_);
v_fst_2330_ = lean_ctor_get(v_snd_2328_, 0);
lean_inc(v_fst_2330_);
lean_dec(v_snd_2328_);
v_array_2331_ = lean_ctor_get(v_a_2322_, 0);
v_idx_2332_ = lean_ctor_get(v_a_2322_, 1);
v_isSharedCheck_2382_ = !lean_is_exclusive(v_a_2322_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2334_ = v_a_2322_;
v_isShared_2335_ = v_isSharedCheck_2382_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_idx_2332_);
lean_inc(v_array_2331_);
lean_dec(v_a_2322_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2382_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v_lower_2337_; lean_object* v_upper_2338_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___y_2379_; uint8_t v___x_2381_; 
v___x_2376_ = lean_nat_add(v_idx_2332_, v_fst_2329_);
lean_dec(v_fst_2329_);
v___x_2377_ = lean_byte_array_size(v_array_2331_);
v___x_2381_ = lean_nat_dec_le(v_idx_2332_, v___x_2326_);
if (v___x_2381_ == 0)
{
v___y_2379_ = v_idx_2332_;
goto v___jp_2378_;
}
else
{
lean_dec(v_idx_2332_);
v___y_2379_ = v___x_2326_;
goto v___jp_2378_;
}
v___jp_2336_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; uint8_t v___x_2341_; 
v___x_2339_ = l_ByteArray_toByteSlice(v_array_2331_, v_lower_2337_, v_upper_2338_);
v___x_2340_ = l_ByteSlice_toByteArray(v___x_2339_);
v___x_2341_ = lean_string_validate_utf8(v___x_2340_);
if (v___x_2341_ == 0)
{
lean_object* v___x_2342_; lean_object* v___x_2344_; 
lean_dec_ref(v___x_2340_);
lean_dec(v_maxQueryParams_2324_);
v___x_2342_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2335_ == 0)
{
lean_ctor_set_tag(v___x_2334_, 1);
lean_ctor_set(v___x_2334_, 1, v___x_2342_);
lean_ctor_set(v___x_2334_, 0, v_fst_2330_);
v___x_2344_ = v___x_2334_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_fst_2330_);
lean_ctor_set(v_reuseFailAlloc_2345_, 1, v___x_2342_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
else
{
lean_object* v___x_2346_; lean_object* v___x_2347_; uint8_t v___x_2348_; 
v___x_2346_ = lean_string_from_utf8_unchecked(v___x_2340_);
v___x_2347_ = lean_string_utf8_byte_size(v___x_2346_);
v___x_2348_ = lean_nat_dec_eq(v___x_2347_, v___x_2326_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; uint8_t v___x_2352_; 
lean_inc_ref(v___x_2346_);
v___x_2349_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2346_);
lean_ctor_set(v___x_2349_, 1, v___x_2326_);
lean_ctor_set(v___x_2349_, 2, v___x_2347_);
v___x_2350_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0);
v___x_2351_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2346_, v___x_2349_, v___x_2347_, v___x_2350_, v___x_2326_);
v___x_2352_ = lean_nat_dec_lt(v_maxQueryParams_2324_, v___x_2351_);
lean_dec(v___x_2351_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
lean_dec(v_maxQueryParams_2324_);
v___x_2353_ = l_Std_Http_URI_Query_empty;
v___x_2354_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2346_, v___x_2349_, v___x_2347_, v___x_2350_, v___x_2353_);
lean_dec_ref_known(v___x_2349_, 3);
if (lean_obj_tag(v___x_2354_) == 1)
{
lean_object* v_val_2355_; lean_object* v___x_2357_; 
v_val_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc(v_val_2355_);
lean_dec_ref_known(v___x_2354_, 1);
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 1, v_val_2355_);
lean_ctor_set(v___x_2334_, 0, v_fst_2330_);
v___x_2357_ = v___x_2334_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_fst_2330_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v_val_2355_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
else
{
lean_object* v___x_2359_; lean_object* v___x_2361_; 
lean_dec(v___x_2354_);
v___x_2359_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2335_ == 0)
{
lean_ctor_set_tag(v___x_2334_, 1);
lean_ctor_set(v___x_2334_, 1, v___x_2359_);
lean_ctor_set(v___x_2334_, 0, v_fst_2330_);
v___x_2361_ = v___x_2334_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_fst_2330_);
lean_ctor_set(v_reuseFailAlloc_2362_, 1, v___x_2359_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
else
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2370_; 
lean_dec_ref_known(v___x_2349_, 3);
lean_dec_ref(v___x_2346_);
v___x_2363_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3));
v___x_2364_ = l_Nat_reprFast(v_maxQueryParams_2324_);
v___x_2365_ = lean_string_append(v___x_2363_, v___x_2364_);
lean_dec_ref(v___x_2364_);
v___x_2366_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_2367_ = lean_string_append(v___x_2365_, v___x_2366_);
v___x_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
if (v_isShared_2335_ == 0)
{
lean_ctor_set_tag(v___x_2334_, 1);
lean_ctor_set(v___x_2334_, 1, v___x_2368_);
lean_ctor_set(v___x_2334_, 0, v_fst_2330_);
v___x_2370_ = v___x_2334_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_fst_2330_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v___x_2368_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
else
{
lean_object* v___x_2372_; lean_object* v___x_2374_; 
lean_dec_ref(v___x_2346_);
lean_dec(v_maxQueryParams_2324_);
v___x_2372_ = l_Std_Http_URI_Query_empty;
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 1, v___x_2372_);
lean_ctor_set(v___x_2334_, 0, v_fst_2330_);
v___x_2374_ = v___x_2334_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_fst_2330_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v___x_2372_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
v___jp_2378_:
{
uint8_t v___x_2380_; 
v___x_2380_ = lean_nat_dec_le(v___x_2376_, v___x_2377_);
if (v___x_2380_ == 0)
{
lean_dec(v___x_2376_);
v_lower_2337_ = v___y_2379_;
v_upper_2338_ = v___x_2377_;
goto v___jp_2336_;
}
else
{
v_lower_2337_ = v___y_2379_;
v_upper_2338_ = v___x_2376_;
goto v___jp_2336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(lean_object* v___x_2383_, lean_object* v___x_2384_, lean_object* v___x_2385_, lean_object* v_inst_2386_, lean_object* v_R_2387_, lean_object* v_a_2388_, lean_object* v_b_2389_, lean_object* v_c_2390_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2383_, v___x_2384_, v___x_2385_, v_a_2388_, v_b_2389_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___boxed(lean_object* v___x_2392_, lean_object* v___x_2393_, lean_object* v___x_2394_, lean_object* v_inst_2395_, lean_object* v_R_2396_, lean_object* v_a_2397_, lean_object* v_b_2398_, lean_object* v_c_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(v___x_2392_, v___x_2393_, v___x_2394_, v_inst_2395_, v_R_2396_, v_a_2397_, v_b_2398_, v_c_2399_);
lean_dec(v___x_2394_);
lean_dec_ref(v___x_2393_);
lean_dec_ref(v___x_2392_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(lean_object* v_out_2401_, lean_object* v_inst_2402_, lean_object* v_R_2403_, lean_object* v_a_2404_, lean_object* v_b_2405_){
_start:
{
lean_object* v___x_2406_; 
v___x_2406_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_2401_, v_a_2404_, v_b_2405_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___boxed(lean_object* v_out_2407_, lean_object* v_inst_2408_, lean_object* v_R_2409_, lean_object* v_a_2410_, lean_object* v_b_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(v_out_2407_, v_inst_2408_, v_R_2409_, v_a_2410_, v_b_2411_);
lean_dec_ref(v_out_2407_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(lean_object* v___x_2413_, lean_object* v___x_2414_, lean_object* v___x_2415_, lean_object* v_inst_2416_, lean_object* v_R_2417_, lean_object* v_a_2418_, lean_object* v_b_2419_, lean_object* v_c_2420_){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2413_, v___x_2414_, v___x_2415_, v_a_2418_, v_b_2419_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___boxed(lean_object* v___x_2422_, lean_object* v___x_2423_, lean_object* v___x_2424_, lean_object* v_inst_2425_, lean_object* v_R_2426_, lean_object* v_a_2427_, lean_object* v_b_2428_, lean_object* v_c_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(v___x_2422_, v___x_2423_, v___x_2424_, v_inst_2425_, v_R_2426_, v_a_2427_, v_b_2428_, v_c_2429_);
lean_dec_ref(v___x_2423_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(lean_object* v___x_2431_, lean_object* v___x_2432_, lean_object* v___x_2433_, lean_object* v_inst_2434_, lean_object* v_R_2435_, lean_object* v_a_2436_, lean_object* v_b_2437_, lean_object* v_c_2438_){
_start:
{
lean_object* v___x_2439_; 
v___x_2439_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2432_, v___x_2433_, v_a_2436_, v_b_2437_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___boxed(lean_object* v___x_2440_, lean_object* v___x_2441_, lean_object* v___x_2442_, lean_object* v_inst_2443_, lean_object* v_R_2444_, lean_object* v_a_2445_, lean_object* v_b_2446_, lean_object* v_c_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(v___x_2440_, v___x_2441_, v___x_2442_, v_inst_2443_, v_R_2444_, v_a_2445_, v_b_2446_, v_c_2447_);
lean_dec(v___x_2442_);
lean_dec_ref(v___x_2441_);
lean_dec_ref(v___x_2440_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(lean_object* v___x_2449_, lean_object* v___x_2450_, lean_object* v___x_2451_, lean_object* v_inst_2452_, lean_object* v_R_2453_, lean_object* v_a_2454_, lean_object* v_b_2455_, lean_object* v_c_2456_){
_start:
{
lean_object* v___x_2457_; 
v___x_2457_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2449_, v___x_2450_, v___x_2451_, v_a_2454_, v_b_2455_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___boxed(lean_object* v___x_2458_, lean_object* v___x_2459_, lean_object* v___x_2460_, lean_object* v_inst_2461_, lean_object* v_R_2462_, lean_object* v_a_2463_, lean_object* v_b_2464_, lean_object* v_c_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(v___x_2458_, v___x_2459_, v___x_2460_, v_inst_2461_, v_R_2462_, v_a_2463_, v_b_2464_, v_c_2465_);
lean_dec_ref(v___x_2459_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(lean_object* v_config_2470_, lean_object* v_a_2471_){
_start:
{
lean_object* v_maxFragmentLength_2472_; lean_object* v___f_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v_snd_2476_; lean_object* v_fst_2477_; lean_object* v_fst_2478_; lean_object* v_array_2479_; lean_object* v_idx_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2504_; 
v_maxFragmentLength_2472_ = lean_ctor_get(v_config_2470_, 5);
v___f_2473_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2474_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2471_);
v___x_2475_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2473_, v_maxFragmentLength_2472_, v___x_2474_, v_a_2471_);
v_snd_2476_ = lean_ctor_get(v___x_2475_, 1);
lean_inc(v_snd_2476_);
v_fst_2477_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_fst_2477_);
lean_dec_ref(v___x_2475_);
v_fst_2478_ = lean_ctor_get(v_snd_2476_, 0);
lean_inc(v_fst_2478_);
lean_dec(v_snd_2476_);
v_array_2479_ = lean_ctor_get(v_a_2471_, 0);
v_idx_2480_ = lean_ctor_get(v_a_2471_, 1);
v_isSharedCheck_2504_ = !lean_is_exclusive(v_a_2471_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2482_ = v_a_2471_;
v_isShared_2483_ = v_isSharedCheck_2504_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_idx_2480_);
lean_inc(v_array_2479_);
lean_dec(v_a_2471_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2504_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v_lower_2485_; lean_object* v_upper_2486_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___y_2501_; uint8_t v___x_2503_; 
v___x_2498_ = lean_nat_add(v_idx_2480_, v_fst_2477_);
lean_dec(v_fst_2477_);
v___x_2499_ = lean_byte_array_size(v_array_2479_);
v___x_2503_ = lean_nat_dec_le(v_idx_2480_, v___x_2474_);
if (v___x_2503_ == 0)
{
v___y_2501_ = v_idx_2480_;
goto v___jp_2500_;
}
else
{
lean_dec(v_idx_2480_);
v___y_2501_ = v___x_2474_;
goto v___jp_2500_;
}
v___jp_2484_:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2487_ = l_ByteArray_toByteSlice(v_array_2479_, v_lower_2485_, v_upper_2486_);
v___x_2488_ = l_ByteSlice_toByteArray(v___x_2487_);
v___x_2489_ = l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(v___x_2488_);
if (lean_obj_tag(v___x_2489_) == 1)
{
lean_object* v_val_2490_; lean_object* v___x_2492_; 
v_val_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_val_2490_);
lean_dec_ref_known(v___x_2489_, 1);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 1, v_val_2490_);
lean_ctor_set(v___x_2482_, 0, v_fst_2478_);
v___x_2492_ = v___x_2482_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_fst_2478_);
lean_ctor_set(v_reuseFailAlloc_2493_, 1, v_val_2490_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
else
{
lean_object* v___x_2494_; lean_object* v___x_2496_; 
lean_dec(v___x_2489_);
v___x_2494_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1));
if (v_isShared_2483_ == 0)
{
lean_ctor_set_tag(v___x_2482_, 1);
lean_ctor_set(v___x_2482_, 1, v___x_2494_);
lean_ctor_set(v___x_2482_, 0, v_fst_2478_);
v___x_2496_ = v___x_2482_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_fst_2478_);
lean_ctor_set(v_reuseFailAlloc_2497_, 1, v___x_2494_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
v___jp_2500_:
{
uint8_t v___x_2502_; 
v___x_2502_ = lean_nat_dec_le(v___x_2498_, v___x_2499_);
if (v___x_2502_ == 0)
{
lean_dec(v___x_2498_);
v_lower_2485_ = v___y_2501_;
v_upper_2486_ = v___x_2499_;
goto v___jp_2484_;
}
else
{
v_lower_2485_ = v___y_2501_;
v_upper_2486_ = v___x_2498_;
goto v___jp_2484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___boxed(lean_object* v_config_2505_, lean_object* v_a_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2505_, v_a_2506_);
lean_dec_ref(v_config_2505_);
return v_res_2507_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1(void){
_start:
{
lean_object* v___x_2509_; lean_object* v_utf8_2510_; 
v___x_2509_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0));
v_utf8_2510_ = lean_string_to_utf8(v___x_2509_);
return v_utf8_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(lean_object* v_config_2511_, lean_object* v_a_2512_){
_start:
{
uint8_t v___y_2514_; lean_object* v_pos_2515_; lean_object* v_res_2516_; lean_object* v___y_2538_; uint8_t v___y_2539_; lean_object* v_err_2540_; lean_object* v_pos_2546_; lean_object* v_utf8_2554_; lean_object* v___x_2555_; 
v_utf8_2554_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1);
lean_inc_ref(v_a_2512_);
v___x_2555_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_2554_, v_a_2512_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_pos_2556_; 
lean_dec_ref(v_a_2512_);
v_pos_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_pos_2556_);
lean_dec_ref_known(v___x_2555_, 2);
v_pos_2546_ = v_pos_2556_;
goto v___jp_2545_;
}
else
{
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_pos_2557_; 
lean_dec_ref(v_a_2512_);
v_pos_2557_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_pos_2557_);
lean_dec_ref_known(v___x_2555_, 2);
v_pos_2546_ = v_pos_2557_;
goto v___jp_2545_;
}
else
{
lean_object* v_err_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2589_; 
v_err_2558_ = lean_ctor_get(v___x_2555_, 1);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2589_ == 0)
{
lean_object* v_unused_2590_; 
v_unused_2590_ = lean_ctor_get(v___x_2555_, 0);
lean_dec(v_unused_2590_);
v___x_2560_ = v___x_2555_;
v_isShared_2561_ = v_isSharedCheck_2589_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_err_2558_);
lean_dec(v___x_2555_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2589_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v_idx_2562_; uint8_t v___x_2563_; 
v_idx_2562_ = lean_ctor_get(v_a_2512_, 1);
v___x_2563_ = lean_nat_dec_eq(v_idx_2562_, v_idx_2562_);
if (v___x_2563_ == 0)
{
lean_object* v___x_2565_; 
lean_dec_ref(v_config_2511_);
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 0, v_a_2512_);
v___x_2565_ = v___x_2560_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2512_);
lean_ctor_set(v_reuseFailAlloc_2566_, 1, v_err_2558_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
else
{
uint8_t v___x_2567_; lean_object* v___x_2568_; 
lean_del_object(v___x_2560_);
lean_dec(v_err_2558_);
v___x_2567_ = 0;
v___x_2568_ = l_Std_Http_URI_Parser_parsePath(v_config_2511_, v___x_2567_, v___x_2563_, v_a_2512_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_pos_2569_; lean_object* v_res_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2579_; 
v_pos_2569_ = lean_ctor_get(v___x_2568_, 0);
v_res_2570_ = lean_ctor_get(v___x_2568_, 1);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2572_ = v___x_2568_;
v_isShared_2573_ = v_isSharedCheck_2579_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_res_2570_);
lean_inc(v_pos_2569_);
lean_dec(v___x_2568_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2579_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2574_ = lean_box(0);
v___x_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
lean_ctor_set(v___x_2575_, 1, v_res_2570_);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 1, v___x_2575_);
v___x_2577_ = v___x_2572_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_pos_2569_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v___x_2575_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
else
{
lean_object* v_pos_2580_; lean_object* v_err_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
v_pos_2580_ = lean_ctor_get(v___x_2568_, 0);
v_err_2581_ = lean_ctor_get(v___x_2568_, 1);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2583_ = v___x_2568_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_err_2581_);
lean_inc(v_pos_2580_);
lean_dec(v___x_2568_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_pos_2580_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v_err_2581_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
}
}
}
v___jp_2513_:
{
lean_object* v___x_2517_; 
v___x_2517_ = l_Std_Http_URI_Parser_parsePath(v_config_2511_, v___y_2514_, v___y_2514_, v_pos_2515_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_pos_2518_; lean_object* v_res_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2527_; 
v_pos_2518_ = lean_ctor_get(v___x_2517_, 0);
v_res_2519_ = lean_ctor_get(v___x_2517_, 1);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2521_ = v___x_2517_;
v_isShared_2522_ = v_isSharedCheck_2527_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_res_2519_);
lean_inc(v_pos_2518_);
lean_dec(v___x_2517_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2527_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2523_; lean_object* v___x_2525_; 
v___x_2523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2523_, 0, v_res_2516_);
lean_ctor_set(v___x_2523_, 1, v_res_2519_);
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 1, v___x_2523_);
v___x_2525_ = v___x_2521_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_pos_2518_);
lean_ctor_set(v_reuseFailAlloc_2526_, 1, v___x_2523_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
else
{
lean_object* v_pos_2528_; lean_object* v_err_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2536_; 
lean_dec(v_res_2516_);
v_pos_2528_ = lean_ctor_get(v___x_2517_, 0);
v_err_2529_ = lean_ctor_get(v___x_2517_, 1);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2531_ = v___x_2517_;
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_err_2529_);
lean_inc(v_pos_2528_);
lean_dec(v___x_2517_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_pos_2528_);
lean_ctor_set(v_reuseFailAlloc_2535_, 1, v_err_2529_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
v___jp_2537_:
{
lean_object* v_idx_2541_; uint8_t v___x_2542_; 
v_idx_2541_ = lean_ctor_get(v___y_2538_, 1);
v___x_2542_ = lean_nat_dec_eq(v_idx_2541_, v_idx_2541_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; 
lean_dec_ref(v_config_2511_);
v___x_2543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___y_2538_);
lean_ctor_set(v___x_2543_, 1, v_err_2540_);
return v___x_2543_;
}
else
{
lean_object* v___x_2544_; 
lean_dec(v_err_2540_);
v___x_2544_ = lean_box(0);
v___y_2514_ = v___y_2539_;
v_pos_2515_ = v___y_2538_;
v_res_2516_ = v___x_2544_;
goto v___jp_2513_;
}
}
v___jp_2545_:
{
uint8_t v___x_2547_; lean_object* v___x_2548_; 
v___x_2547_ = 1;
lean_inc_ref(v_pos_2546_);
v___x_2548_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_2511_, v_pos_2546_);
if (lean_obj_tag(v___x_2548_) == 0)
{
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_pos_2549_; lean_object* v_res_2550_; lean_object* v___x_2551_; 
lean_dec_ref(v_pos_2546_);
v_pos_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_pos_2549_);
v_res_2550_ = lean_ctor_get(v___x_2548_, 1);
lean_inc(v_res_2550_);
lean_dec_ref_known(v___x_2548_, 2);
v___x_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2551_, 0, v_res_2550_);
v___y_2514_ = v___x_2547_;
v_pos_2515_ = v_pos_2549_;
v_res_2516_ = v___x_2551_;
goto v___jp_2513_;
}
else
{
lean_object* v_err_2552_; 
v_err_2552_ = lean_ctor_get(v___x_2548_, 1);
lean_inc(v_err_2552_);
lean_dec_ref_known(v___x_2548_, 2);
v___y_2538_ = v_pos_2546_;
v___y_2539_ = v___x_2547_;
v_err_2540_ = v_err_2552_;
goto v___jp_2537_;
}
}
else
{
lean_object* v_err_2553_; 
v_err_2553_ = lean_ctor_get(v___x_2548_, 1);
lean_inc(v_err_2553_);
lean_dec_ref_known(v___x_2548_, 2);
v___y_2538_ = v_pos_2546_;
v___y_2539_ = v___x_2547_;
v_err_2540_ = v_err_2553_;
goto v___jp_2537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURI(lean_object* v_config_2600_, lean_object* v_a_2601_){
_start:
{
lean_object* v___x_2602_; 
v___x_2602_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_2600_, v_a_2601_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_pos_2603_; lean_object* v_res_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2735_; 
v_pos_2603_ = lean_ctor_get(v___x_2602_, 0);
v_res_2604_ = lean_ctor_get(v___x_2602_, 1);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2606_ = v___x_2602_;
v_isShared_2607_ = v_isSharedCheck_2735_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_res_2604_);
lean_inc(v_pos_2603_);
lean_dec(v___x_2602_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2735_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v_array_2608_; lean_object* v_idx_2609_; lean_object* v___x_2610_; uint8_t v___x_2611_; 
v_array_2608_ = lean_ctor_get(v_pos_2603_, 0);
v_idx_2609_ = lean_ctor_get(v_pos_2603_, 1);
v___x_2610_ = lean_byte_array_size(v_array_2608_);
v___x_2611_ = lean_nat_dec_lt(v_idx_2609_, v___x_2610_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; lean_object* v___x_2614_; 
lean_dec(v_res_2604_);
lean_dec_ref(v_config_2600_);
v___x_2612_ = lean_box(0);
if (v_isShared_2607_ == 0)
{
lean_ctor_set_tag(v___x_2606_, 1);
lean_ctor_set(v___x_2606_, 1, v___x_2612_);
v___x_2614_ = v___x_2606_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_pos_2603_);
lean_ctor_set(v_reuseFailAlloc_2615_, 1, v___x_2612_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
else
{
uint8_t v___x_2616_; uint8_t v_got_2617_; uint8_t v___x_2618_; 
v___x_2616_ = 58;
v_got_2617_ = lean_byte_array_fget(v_array_2608_, v_idx_2609_);
v___x_2618_ = lean_uint8_dec_eq(v_got_2617_, v___x_2616_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2619_; lean_object* v___x_2621_; 
lean_dec(v_res_2604_);
lean_dec_ref(v_config_2600_);
v___x_2619_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_2607_ == 0)
{
lean_ctor_set_tag(v___x_2606_, 1);
lean_ctor_set(v___x_2606_, 1, v___x_2619_);
v___x_2621_ = v___x_2606_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_pos_2603_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v___x_2619_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
else
{
lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2732_; 
lean_inc(v_idx_2609_);
lean_inc_ref(v_array_2608_);
v_isSharedCheck_2732_ = !lean_is_exclusive(v_pos_2603_);
if (v_isSharedCheck_2732_ == 0)
{
lean_object* v_unused_2733_; lean_object* v_unused_2734_; 
v_unused_2733_ = lean_ctor_get(v_pos_2603_, 1);
lean_dec(v_unused_2733_);
v_unused_2734_ = lean_ctor_get(v_pos_2603_, 0);
lean_dec(v_unused_2734_);
v___x_2624_ = v_pos_2603_;
v_isShared_2625_ = v_isSharedCheck_2732_;
goto v_resetjp_2623_;
}
else
{
lean_dec(v_pos_2603_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2732_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2629_; 
v___x_2626_ = lean_unsigned_to_nat(1u);
v___x_2627_ = lean_nat_add(v_idx_2609_, v___x_2626_);
lean_dec(v_idx_2609_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 1, v___x_2627_);
v___x_2629_ = v___x_2624_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_array_2608_);
lean_ctor_set(v_reuseFailAlloc_2731_, 1, v___x_2627_);
v___x_2629_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
lean_object* v___x_2630_; 
lean_inc_ref(v_config_2600_);
v___x_2630_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2600_, v___x_2629_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_res_2631_; lean_object* v_pos_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2721_; 
v_res_2631_ = lean_ctor_get(v___x_2630_, 1);
v_pos_2632_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2634_ = v___x_2630_;
v_isShared_2635_ = v_isSharedCheck_2721_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_res_2631_);
lean_inc(v_pos_2632_);
lean_dec(v___x_2630_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2721_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v_fst_2636_; lean_object* v_snd_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2720_; 
v_fst_2636_ = lean_ctor_get(v_res_2631_, 0);
v_snd_2637_ = lean_ctor_get(v_res_2631_, 1);
v_isSharedCheck_2720_ = !lean_is_exclusive(v_res_2631_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2639_ = v_res_2631_;
v_isShared_2640_ = v_isSharedCheck_2720_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_snd_2637_);
lean_inc(v_fst_2636_);
lean_dec(v_res_2631_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2720_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___y_2642_; lean_object* v_pos_2643_; lean_object* v_res_2644_; lean_object* v___y_2650_; lean_object* v_idx_2651_; lean_object* v_pos_2652_; lean_object* v_err_2653_; lean_object* v_pos_2661_; lean_object* v_array_2662_; lean_object* v_idx_2663_; lean_object* v_res_2664_; lean_object* v_array_2683_; lean_object* v_idx_2684_; lean_object* v_pos_2686_; lean_object* v_array_2687_; lean_object* v_idx_2688_; lean_object* v_err_2689_; lean_object* v___x_2693_; uint8_t v___x_2694_; 
v_array_2683_ = lean_ctor_get(v_pos_2632_, 0);
lean_inc_ref(v_array_2683_);
v_idx_2684_ = lean_ctor_get(v_pos_2632_, 1);
lean_inc(v_idx_2684_);
v___x_2693_ = lean_byte_array_size(v_array_2683_);
v___x_2694_ = lean_nat_dec_lt(v_idx_2684_, v___x_2693_);
if (v___x_2694_ == 0)
{
lean_object* v___x_2695_; 
v___x_2695_ = lean_box(0);
lean_inc(v_idx_2684_);
v_pos_2686_ = v_pos_2632_;
v_array_2687_ = v_array_2683_;
v_idx_2688_ = v_idx_2684_;
v_err_2689_ = v___x_2695_;
goto v___jp_2685_;
}
else
{
uint8_t v___x_2696_; uint8_t v_got_2697_; uint8_t v___x_2698_; 
v___x_2696_ = 63;
v_got_2697_ = lean_byte_array_fget(v_array_2683_, v_idx_2684_);
v___x_2698_ = lean_uint8_dec_eq(v_got_2697_, v___x_2696_);
if (v___x_2698_ == 0)
{
lean_object* v___x_2699_; 
v___x_2699_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_2684_);
v_pos_2686_ = v_pos_2632_;
v_array_2687_ = v_array_2683_;
v_idx_2688_ = v_idx_2684_;
v_err_2689_ = v___x_2699_;
goto v___jp_2685_;
}
else
{
lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2717_; 
v_isSharedCheck_2717_ = !lean_is_exclusive(v_pos_2632_);
if (v_isSharedCheck_2717_ == 0)
{
lean_object* v_unused_2718_; lean_object* v_unused_2719_; 
v_unused_2718_ = lean_ctor_get(v_pos_2632_, 1);
lean_dec(v_unused_2718_);
v_unused_2719_ = lean_ctor_get(v_pos_2632_, 0);
lean_dec(v_unused_2719_);
v___x_2701_ = v_pos_2632_;
v_isShared_2702_ = v_isSharedCheck_2717_;
goto v_resetjp_2700_;
}
else
{
lean_dec(v_pos_2632_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2717_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2703_; lean_object* v___x_2705_; 
v___x_2703_ = lean_nat_add(v_idx_2684_, v___x_2626_);
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 1, v___x_2703_);
v___x_2705_ = v___x_2701_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_array_2683_);
lean_ctor_set(v_reuseFailAlloc_2716_, 1, v___x_2703_);
v___x_2705_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
lean_object* v___x_2706_; 
lean_inc_ref(v_config_2600_);
v___x_2706_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2600_, v___x_2705_);
if (lean_obj_tag(v___x_2706_) == 0)
{
lean_object* v_pos_2707_; lean_object* v_res_2708_; lean_object* v_array_2709_; lean_object* v_idx_2710_; lean_object* v___x_2711_; 
lean_dec(v_idx_2684_);
v_pos_2707_ = lean_ctor_get(v___x_2706_, 0);
lean_inc(v_pos_2707_);
v_res_2708_ = lean_ctor_get(v___x_2706_, 1);
lean_inc(v_res_2708_);
lean_dec_ref_known(v___x_2706_, 2);
v_array_2709_ = lean_ctor_get(v_pos_2707_, 0);
lean_inc_ref(v_array_2709_);
v_idx_2710_ = lean_ctor_get(v_pos_2707_, 1);
lean_inc(v_idx_2710_);
v___x_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2711_, 0, v_res_2708_);
v_pos_2661_ = v_pos_2707_;
v_array_2662_ = v_array_2709_;
v_idx_2663_ = v_idx_2710_;
v_res_2664_ = v___x_2711_;
goto v___jp_2660_;
}
else
{
lean_object* v_pos_2712_; lean_object* v_err_2713_; lean_object* v_array_2714_; lean_object* v_idx_2715_; 
v_pos_2712_ = lean_ctor_get(v___x_2706_, 0);
lean_inc(v_pos_2712_);
v_err_2713_ = lean_ctor_get(v___x_2706_, 1);
lean_inc(v_err_2713_);
lean_dec_ref_known(v___x_2706_, 2);
v_array_2714_ = lean_ctor_get(v_pos_2712_, 0);
lean_inc_ref(v_array_2714_);
v_idx_2715_ = lean_ctor_get(v_pos_2712_, 1);
lean_inc(v_idx_2715_);
v_pos_2686_ = v_pos_2712_;
v_array_2687_ = v_array_2714_;
v_idx_2688_ = v_idx_2715_;
v_err_2689_ = v_err_2713_;
goto v___jp_2685_;
}
}
}
}
}
v___jp_2641_:
{
lean_object* v___x_2645_; lean_object* v___x_2647_; 
v___x_2645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2645_, 0, v_res_2604_);
lean_ctor_set(v___x_2645_, 1, v_fst_2636_);
lean_ctor_set(v___x_2645_, 2, v_snd_2637_);
lean_ctor_set(v___x_2645_, 3, v___y_2642_);
lean_ctor_set(v___x_2645_, 4, v_res_2644_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 1, v___x_2645_);
lean_ctor_set(v___x_2634_, 0, v_pos_2643_);
v___x_2647_ = v___x_2634_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_pos_2643_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v___x_2645_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
v___jp_2649_:
{
lean_object* v_idx_2654_; uint8_t v___x_2655_; 
v_idx_2654_ = lean_ctor_get(v_pos_2652_, 1);
v___x_2655_ = lean_nat_dec_eq(v_idx_2651_, v_idx_2654_);
lean_dec(v_idx_2651_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2657_; 
lean_dec(v___y_2650_);
lean_dec(v_snd_2637_);
lean_dec(v_fst_2636_);
lean_del_object(v___x_2634_);
lean_dec(v_res_2604_);
if (v_isShared_2607_ == 0)
{
lean_ctor_set_tag(v___x_2606_, 1);
lean_ctor_set(v___x_2606_, 1, v_err_2653_);
lean_ctor_set(v___x_2606_, 0, v_pos_2652_);
v___x_2657_ = v___x_2606_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_pos_2652_);
lean_ctor_set(v_reuseFailAlloc_2658_, 1, v_err_2653_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
else
{
lean_object* v___x_2659_; 
lean_dec(v_err_2653_);
lean_del_object(v___x_2606_);
v___x_2659_ = lean_box(0);
v___y_2642_ = v___y_2650_;
v_pos_2643_ = v_pos_2652_;
v_res_2644_ = v___x_2659_;
goto v___jp_2641_;
}
}
v___jp_2660_:
{
lean_object* v___x_2665_; uint8_t v___x_2666_; 
v___x_2665_ = lean_byte_array_size(v_array_2662_);
v___x_2666_ = lean_nat_dec_lt(v_idx_2663_, v___x_2665_);
if (v___x_2666_ == 0)
{
lean_object* v___x_2667_; 
lean_dec_ref(v_array_2662_);
lean_del_object(v___x_2639_);
lean_dec_ref(v_config_2600_);
v___x_2667_ = lean_box(0);
v___y_2650_ = v_res_2664_;
v_idx_2651_ = v_idx_2663_;
v_pos_2652_ = v_pos_2661_;
v_err_2653_ = v___x_2667_;
goto v___jp_2649_;
}
else
{
uint8_t v___x_2668_; uint8_t v_got_2669_; uint8_t v___x_2670_; 
v___x_2668_ = 35;
v_got_2669_ = lean_byte_array_fget(v_array_2662_, v_idx_2663_);
v___x_2670_ = lean_uint8_dec_eq(v_got_2669_, v___x_2668_);
if (v___x_2670_ == 0)
{
lean_object* v___x_2671_; 
lean_dec_ref(v_array_2662_);
lean_del_object(v___x_2639_);
lean_dec_ref(v_config_2600_);
v___x_2671_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v___y_2650_ = v_res_2664_;
v_idx_2651_ = v_idx_2663_;
v_pos_2652_ = v_pos_2661_;
v_err_2653_ = v___x_2671_;
goto v___jp_2649_;
}
else
{
lean_object* v___x_2672_; lean_object* v___x_2674_; 
lean_dec_ref(v_pos_2661_);
v___x_2672_ = lean_nat_add(v_idx_2663_, v___x_2626_);
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 1, v___x_2672_);
lean_ctor_set(v___x_2639_, 0, v_array_2662_);
v___x_2674_ = v___x_2639_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_array_2662_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v___x_2672_);
v___x_2674_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
lean_object* v___x_2675_; 
v___x_2675_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2600_, v___x_2674_);
lean_dec_ref(v_config_2600_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_pos_2676_; lean_object* v_res_2677_; lean_object* v___x_2678_; 
v_pos_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_pos_2676_);
v_res_2677_ = lean_ctor_get(v___x_2675_, 1);
lean_inc(v_res_2677_);
lean_dec_ref_known(v___x_2675_, 2);
v___x_2678_ = l_Std_Http_URI_EncodedFragment_decode(v_res_2677_);
lean_dec(v_res_2677_);
if (lean_obj_tag(v___x_2678_) == 1)
{
lean_dec(v_idx_2663_);
lean_del_object(v___x_2606_);
v___y_2642_ = v_res_2664_;
v_pos_2643_ = v_pos_2676_;
v_res_2644_ = v___x_2678_;
goto v___jp_2641_;
}
else
{
lean_object* v___x_2679_; 
lean_dec(v___x_2678_);
v___x_2679_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__3));
v___y_2650_ = v_res_2664_;
v_idx_2651_ = v_idx_2663_;
v_pos_2652_ = v_pos_2676_;
v_err_2653_ = v___x_2679_;
goto v___jp_2649_;
}
}
else
{
lean_object* v_pos_2680_; lean_object* v_err_2681_; 
v_pos_2680_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_pos_2680_);
v_err_2681_ = lean_ctor_get(v___x_2675_, 1);
lean_inc(v_err_2681_);
lean_dec_ref_known(v___x_2675_, 2);
v___y_2650_ = v_res_2664_;
v_idx_2651_ = v_idx_2663_;
v_pos_2652_ = v_pos_2680_;
v_err_2653_ = v_err_2681_;
goto v___jp_2649_;
}
}
}
}
}
v___jp_2685_:
{
uint8_t v___x_2690_; 
v___x_2690_ = lean_nat_dec_eq(v_idx_2684_, v_idx_2688_);
lean_dec(v_idx_2684_);
if (v___x_2690_ == 0)
{
lean_object* v___x_2691_; 
lean_dec(v_idx_2688_);
lean_dec_ref(v_array_2687_);
lean_del_object(v___x_2639_);
lean_dec(v_snd_2637_);
lean_dec(v_fst_2636_);
lean_del_object(v___x_2634_);
lean_del_object(v___x_2606_);
lean_dec(v_res_2604_);
lean_dec_ref(v_config_2600_);
v___x_2691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2691_, 0, v_pos_2686_);
lean_ctor_set(v___x_2691_, 1, v_err_2689_);
return v___x_2691_;
}
else
{
lean_object* v___x_2692_; 
lean_dec(v_err_2689_);
v___x_2692_ = lean_box(0);
v_pos_2661_ = v_pos_2686_;
v_array_2662_ = v_array_2687_;
v_idx_2663_ = v_idx_2688_;
v_res_2664_ = v___x_2692_;
goto v___jp_2660_;
}
}
}
}
}
else
{
lean_object* v_pos_2722_; lean_object* v_err_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
lean_del_object(v___x_2606_);
lean_dec(v_res_2604_);
lean_dec_ref(v_config_2600_);
v_pos_2722_ = lean_ctor_get(v___x_2630_, 0);
v_err_2723_ = lean_ctor_get(v___x_2630_, 1);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2630_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_err_2723_);
lean_inc(v_pos_2722_);
lean_dec(v___x_2630_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_pos_2722_);
lean_ctor_set(v_reuseFailAlloc_2729_, 1, v_err_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
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
lean_object* v_pos_2736_; lean_object* v_err_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec_ref(v_config_2600_);
v_pos_2736_ = lean_ctor_get(v___x_2602_, 0);
v_err_2737_ = lean_ctor_get(v___x_2602_, 1);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2602_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_err_2737_);
lean_inc(v_pos_2736_);
lean_dec(v___x_2602_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_pos_2736_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v_err_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(lean_object* v_a_2748_){
_start:
{
lean_object* v_array_2749_; lean_object* v_idx_2750_; lean_object* v___x_2751_; uint8_t v___x_2752_; 
v_array_2749_ = lean_ctor_get(v_a_2748_, 0);
v_idx_2750_ = lean_ctor_get(v_a_2748_, 1);
v___x_2751_ = lean_byte_array_size(v_array_2749_);
v___x_2752_ = lean_nat_dec_lt(v_idx_2750_, v___x_2751_);
if (v___x_2752_ == 0)
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2753_ = lean_box(0);
v___x_2754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2754_, 0, v_a_2748_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
return v___x_2754_;
}
else
{
uint8_t v___x_2755_; uint8_t v_got_2756_; uint8_t v___x_2757_; 
v___x_2755_ = 42;
v_got_2756_ = lean_byte_array_fget(v_array_2749_, v_idx_2750_);
v___x_2757_ = lean_uint8_dec_eq(v_got_2756_, v___x_2755_);
if (v___x_2757_ == 0)
{
lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2758_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1));
v___x_2759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2759_, 0, v_a_2748_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
return v___x_2759_;
}
else
{
lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2770_; 
lean_inc(v_idx_2750_);
lean_inc_ref(v_array_2749_);
v_isSharedCheck_2770_ = !lean_is_exclusive(v_a_2748_);
if (v_isSharedCheck_2770_ == 0)
{
lean_object* v_unused_2771_; lean_object* v_unused_2772_; 
v_unused_2771_ = lean_ctor_get(v_a_2748_, 1);
lean_dec(v_unused_2771_);
v_unused_2772_ = lean_ctor_get(v_a_2748_, 0);
lean_dec(v_unused_2772_);
v___x_2761_ = v_a_2748_;
v_isShared_2762_ = v_isSharedCheck_2770_;
goto v_resetjp_2760_;
}
else
{
lean_dec(v_a_2748_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2770_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2766_; 
v___x_2763_ = lean_unsigned_to_nat(1u);
v___x_2764_ = lean_nat_add(v_idx_2750_, v___x_2763_);
lean_dec(v_idx_2750_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 1, v___x_2764_);
v___x_2766_ = v___x_2761_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_array_2749_);
lean_ctor_set(v_reuseFailAlloc_2769_, 1, v___x_2764_);
v___x_2766_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = lean_box(3);
v___x_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2766_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
return v___x_2768_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(lean_object* v_config_2776_, lean_object* v_a_2777_){
_start:
{
lean_object* v_array_2781_; lean_object* v_idx_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; 
v_array_2781_ = lean_ctor_get(v_a_2777_, 0);
v_idx_2782_ = lean_ctor_get(v_a_2777_, 1);
v___x_2783_ = lean_byte_array_size(v_array_2781_);
v___x_2784_ = lean_nat_dec_lt(v_idx_2782_, v___x_2783_);
if (v___x_2784_ == 0)
{
lean_dec_ref(v_config_2776_);
goto v___jp_2778_;
}
else
{
uint8_t v___x_2785_; uint8_t v___x_2786_; uint8_t v___x_2787_; 
v___x_2785_ = lean_byte_array_fget(v_array_2781_, v_idx_2782_);
v___x_2786_ = 47;
v___x_2787_ = lean_uint8_dec_eq(v___x_2785_, v___x_2786_);
if (v___x_2787_ == 0)
{
lean_dec_ref(v_config_2776_);
goto v___jp_2778_;
}
else
{
lean_object* v___x_2788_; 
lean_inc_ref(v_a_2777_);
lean_inc_ref(v_config_2776_);
v___x_2788_ = l_Std_Http_URI_Parser_parsePath(v_config_2776_, v___x_2787_, v___x_2787_, v_a_2777_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_pos_2789_; lean_object* v_res_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2835_; 
v_pos_2789_ = lean_ctor_get(v___x_2788_, 0);
v_res_2790_ = lean_ctor_get(v___x_2788_, 1);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2792_ = v___x_2788_;
v_isShared_2793_ = v_isSharedCheck_2835_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_res_2790_);
lean_inc(v_pos_2789_);
lean_dec(v___x_2788_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2835_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v_pos_2795_; lean_object* v_res_2796_; lean_object* v_array_2801_; lean_object* v_idx_2802_; lean_object* v_pos_2804_; lean_object* v_idx_2805_; lean_object* v_err_2806_; lean_object* v___x_2810_; uint8_t v___x_2811_; 
v_array_2801_ = lean_ctor_get(v_pos_2789_, 0);
v_idx_2802_ = lean_ctor_get(v_pos_2789_, 1);
lean_inc(v_idx_2802_);
v___x_2810_ = lean_byte_array_size(v_array_2801_);
v___x_2811_ = lean_nat_dec_lt(v_idx_2802_, v___x_2810_);
if (v___x_2811_ == 0)
{
lean_object* v___x_2812_; 
lean_dec_ref(v_config_2776_);
v___x_2812_ = lean_box(0);
lean_inc(v_idx_2802_);
v_pos_2804_ = v_pos_2789_;
v_idx_2805_ = v_idx_2802_;
v_err_2806_ = v___x_2812_;
goto v___jp_2803_;
}
else
{
uint8_t v___x_2813_; uint8_t v_got_2814_; uint8_t v___x_2815_; 
v___x_2813_ = 63;
v_got_2814_ = lean_byte_array_fget(v_array_2801_, v_idx_2802_);
v___x_2815_ = lean_uint8_dec_eq(v_got_2814_, v___x_2813_);
if (v___x_2815_ == 0)
{
lean_object* v___x_2816_; 
lean_dec_ref(v_config_2776_);
v___x_2816_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_2802_);
v_pos_2804_ = v_pos_2789_;
v_idx_2805_ = v_idx_2802_;
v_err_2806_ = v___x_2816_;
goto v___jp_2803_;
}
else
{
lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2832_; 
lean_inc_ref(v_array_2801_);
v_isSharedCheck_2832_ = !lean_is_exclusive(v_pos_2789_);
if (v_isSharedCheck_2832_ == 0)
{
lean_object* v_unused_2833_; lean_object* v_unused_2834_; 
v_unused_2833_ = lean_ctor_get(v_pos_2789_, 1);
lean_dec(v_unused_2833_);
v_unused_2834_ = lean_ctor_get(v_pos_2789_, 0);
lean_dec(v_unused_2834_);
v___x_2818_ = v_pos_2789_;
v_isShared_2819_ = v_isSharedCheck_2832_;
goto v_resetjp_2817_;
}
else
{
lean_dec(v_pos_2789_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2832_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2823_; 
v___x_2820_ = lean_unsigned_to_nat(1u);
v___x_2821_ = lean_nat_add(v_idx_2802_, v___x_2820_);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 1, v___x_2821_);
v___x_2823_ = v___x_2818_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_array_2801_);
lean_ctor_set(v_reuseFailAlloc_2831_, 1, v___x_2821_);
v___x_2823_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
lean_object* v___x_2824_; 
v___x_2824_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2776_, v___x_2823_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v_pos_2825_; lean_object* v_res_2826_; lean_object* v___x_2827_; 
lean_dec(v_idx_2802_);
lean_dec_ref(v_a_2777_);
v_pos_2825_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_pos_2825_);
v_res_2826_ = lean_ctor_get(v___x_2824_, 1);
lean_inc(v_res_2826_);
lean_dec_ref_known(v___x_2824_, 2);
v___x_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2827_, 0, v_res_2826_);
v_pos_2795_ = v_pos_2825_;
v_res_2796_ = v___x_2827_;
goto v___jp_2794_;
}
else
{
lean_object* v_pos_2828_; lean_object* v_err_2829_; lean_object* v_idx_2830_; 
v_pos_2828_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_pos_2828_);
v_err_2829_ = lean_ctor_get(v___x_2824_, 1);
lean_inc(v_err_2829_);
lean_dec_ref_known(v___x_2824_, 2);
v_idx_2830_ = lean_ctor_get(v_pos_2828_, 1);
lean_inc(v_idx_2830_);
v_pos_2804_ = v_pos_2828_;
v_idx_2805_ = v_idx_2830_;
v_err_2806_ = v_err_2829_;
goto v___jp_2803_;
}
}
}
}
}
v___jp_2794_:
{
lean_object* v___x_2797_; lean_object* v___x_2799_; 
v___x_2797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2797_, 0, v_res_2790_);
lean_ctor_set(v___x_2797_, 1, v_res_2796_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 1, v___x_2797_);
lean_ctor_set(v___x_2792_, 0, v_pos_2795_);
v___x_2799_ = v___x_2792_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_pos_2795_);
lean_ctor_set(v_reuseFailAlloc_2800_, 1, v___x_2797_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
v___jp_2803_:
{
uint8_t v___x_2807_; 
v___x_2807_ = lean_nat_dec_eq(v_idx_2802_, v_idx_2805_);
lean_dec(v_idx_2805_);
lean_dec(v_idx_2802_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2808_; 
lean_dec_ref(v_pos_2804_);
lean_del_object(v___x_2792_);
lean_dec(v_res_2790_);
v___x_2808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2808_, 0, v_a_2777_);
lean_ctor_set(v___x_2808_, 1, v_err_2806_);
return v___x_2808_;
}
else
{
lean_object* v___x_2809_; 
lean_dec(v_err_2806_);
lean_dec_ref(v_a_2777_);
v___x_2809_ = lean_box(0);
v_pos_2795_ = v_pos_2804_;
v_res_2796_ = v___x_2809_;
goto v___jp_2794_;
}
}
}
}
else
{
lean_object* v_err_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
lean_dec_ref(v_config_2776_);
v_err_2836_ = lean_ctor_get(v___x_2788_, 1);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2843_ == 0)
{
lean_object* v_unused_2844_; 
v_unused_2844_ = lean_ctor_get(v___x_2788_, 0);
lean_dec(v_unused_2844_);
v___x_2838_ = v___x_2788_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_err_2836_);
lean_dec(v___x_2788_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 0, v_a_2777_);
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2777_);
lean_ctor_set(v_reuseFailAlloc_2842_, 1, v_err_2836_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
}
}
v___jp_2778_:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2779_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1));
v___x_2780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2780_, 0, v_a_2777_);
lean_ctor_set(v___x_2780_, 1, v___x_2779_);
return v___x_2780_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(lean_object* v_config_2845_, lean_object* v_scheme_2846_, lean_object* v_a_2847_){
_start:
{
lean_object* v_array_2848_; lean_object* v_idx_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; 
v_array_2848_ = lean_ctor_get(v_a_2847_, 0);
v_idx_2849_ = lean_ctor_get(v_a_2847_, 1);
v___x_2850_ = lean_byte_array_size(v_array_2848_);
v___x_2851_ = lean_nat_dec_lt(v_idx_2849_, v___x_2850_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
lean_dec_ref(v_scheme_2846_);
lean_dec_ref(v_config_2845_);
v___x_2852_ = lean_box(0);
v___x_2853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2853_, 0, v_a_2847_);
lean_ctor_set(v___x_2853_, 1, v___x_2852_);
return v___x_2853_;
}
else
{
uint8_t v___x_2854_; uint8_t v_got_2855_; uint8_t v___x_2856_; 
v___x_2854_ = 58;
v_got_2855_ = lean_byte_array_fget(v_array_2848_, v_idx_2849_);
v___x_2856_ = lean_uint8_dec_eq(v_got_2855_, v___x_2854_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; lean_object* v___x_2858_; 
lean_dec_ref(v_scheme_2846_);
lean_dec_ref(v_config_2845_);
v___x_2857_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
v___x_2858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2858_, 0, v_a_2847_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
return v___x_2858_;
}
else
{
lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2933_; 
lean_inc(v_idx_2849_);
lean_inc_ref(v_array_2848_);
v_isSharedCheck_2933_ = !lean_is_exclusive(v_a_2847_);
if (v_isSharedCheck_2933_ == 0)
{
lean_object* v_unused_2934_; lean_object* v_unused_2935_; 
v_unused_2934_ = lean_ctor_get(v_a_2847_, 1);
lean_dec(v_unused_2934_);
v_unused_2935_ = lean_ctor_get(v_a_2847_, 0);
lean_dec(v_unused_2935_);
v___x_2860_ = v_a_2847_;
v_isShared_2861_ = v_isSharedCheck_2933_;
goto v_resetjp_2859_;
}
else
{
lean_dec(v_a_2847_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2933_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2865_; 
v___x_2862_ = lean_unsigned_to_nat(1u);
v___x_2863_ = lean_nat_add(v_idx_2849_, v___x_2862_);
lean_dec(v_idx_2849_);
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 1, v___x_2863_);
v___x_2865_ = v___x_2860_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_array_2848_);
lean_ctor_set(v_reuseFailAlloc_2932_, 1, v___x_2863_);
v___x_2865_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
lean_object* v___x_2866_; 
lean_inc_ref(v_config_2845_);
v___x_2866_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2845_, v___x_2865_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_res_2867_; lean_object* v_pos_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2922_; 
v_res_2867_ = lean_ctor_get(v___x_2866_, 1);
v_pos_2868_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2870_ = v___x_2866_;
v_isShared_2871_ = v_isSharedCheck_2922_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_res_2867_);
lean_inc(v_pos_2868_);
lean_dec(v___x_2866_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2922_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v_fst_2872_; lean_object* v_snd_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2921_; 
v_fst_2872_ = lean_ctor_get(v_res_2867_, 0);
v_snd_2873_ = lean_ctor_get(v_res_2867_, 1);
v_isSharedCheck_2921_ = !lean_is_exclusive(v_res_2867_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2875_ = v_res_2867_;
v_isShared_2876_ = v_isSharedCheck_2921_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_snd_2873_);
lean_inc(v_fst_2872_);
lean_dec(v_res_2867_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2921_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v_pos_2878_; lean_object* v_res_2879_; lean_object* v_array_2886_; lean_object* v_idx_2887_; lean_object* v_pos_2889_; lean_object* v_idx_2890_; lean_object* v_err_2891_; lean_object* v___x_2897_; uint8_t v___x_2898_; 
v_array_2886_ = lean_ctor_get(v_pos_2868_, 0);
v_idx_2887_ = lean_ctor_get(v_pos_2868_, 1);
lean_inc(v_idx_2887_);
v___x_2897_ = lean_byte_array_size(v_array_2886_);
v___x_2898_ = lean_nat_dec_lt(v_idx_2887_, v___x_2897_);
if (v___x_2898_ == 0)
{
lean_object* v___x_2899_; 
lean_dec_ref(v_config_2845_);
v___x_2899_ = lean_box(0);
lean_inc(v_idx_2887_);
v_pos_2889_ = v_pos_2868_;
v_idx_2890_ = v_idx_2887_;
v_err_2891_ = v___x_2899_;
goto v___jp_2888_;
}
else
{
uint8_t v___x_2900_; uint8_t v_got_2901_; uint8_t v___x_2902_; 
v___x_2900_ = 63;
v_got_2901_ = lean_byte_array_fget(v_array_2886_, v_idx_2887_);
v___x_2902_ = lean_uint8_dec_eq(v_got_2901_, v___x_2900_);
if (v___x_2902_ == 0)
{
lean_object* v___x_2903_; 
lean_dec_ref(v_config_2845_);
v___x_2903_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_2887_);
v_pos_2889_ = v_pos_2868_;
v_idx_2890_ = v_idx_2887_;
v_err_2891_ = v___x_2903_;
goto v___jp_2888_;
}
else
{
lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2918_; 
lean_inc_ref(v_array_2886_);
v_isSharedCheck_2918_ = !lean_is_exclusive(v_pos_2868_);
if (v_isSharedCheck_2918_ == 0)
{
lean_object* v_unused_2919_; lean_object* v_unused_2920_; 
v_unused_2919_ = lean_ctor_get(v_pos_2868_, 1);
lean_dec(v_unused_2919_);
v_unused_2920_ = lean_ctor_get(v_pos_2868_, 0);
lean_dec(v_unused_2920_);
v___x_2905_ = v_pos_2868_;
v_isShared_2906_ = v_isSharedCheck_2918_;
goto v_resetjp_2904_;
}
else
{
lean_dec(v_pos_2868_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2918_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2907_; lean_object* v___x_2909_; 
v___x_2907_ = lean_nat_add(v_idx_2887_, v___x_2862_);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 1, v___x_2907_);
v___x_2909_ = v___x_2905_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_array_2886_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v___x_2907_);
v___x_2909_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
lean_object* v___x_2910_; 
v___x_2910_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2845_, v___x_2909_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_pos_2911_; lean_object* v_res_2912_; lean_object* v___x_2913_; 
lean_dec(v_idx_2887_);
lean_del_object(v___x_2875_);
v_pos_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_pos_2911_);
v_res_2912_ = lean_ctor_get(v___x_2910_, 1);
lean_inc(v_res_2912_);
lean_dec_ref_known(v___x_2910_, 2);
v___x_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2913_, 0, v_res_2912_);
v_pos_2878_ = v_pos_2911_;
v_res_2879_ = v___x_2913_;
goto v___jp_2877_;
}
else
{
lean_object* v_pos_2914_; lean_object* v_err_2915_; lean_object* v_idx_2916_; 
v_pos_2914_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_pos_2914_);
v_err_2915_ = lean_ctor_get(v___x_2910_, 1);
lean_inc(v_err_2915_);
lean_dec_ref_known(v___x_2910_, 2);
v_idx_2916_ = lean_ctor_get(v_pos_2914_, 1);
lean_inc(v_idx_2916_);
v_pos_2889_ = v_pos_2914_;
v_idx_2890_ = v_idx_2916_;
v_err_2891_ = v_err_2915_;
goto v___jp_2888_;
}
}
}
}
}
v___jp_2877_:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2884_; 
v___x_2880_ = lean_box(0);
v___x_2881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2881_, 0, v_scheme_2846_);
lean_ctor_set(v___x_2881_, 1, v_fst_2872_);
lean_ctor_set(v___x_2881_, 2, v_snd_2873_);
lean_ctor_set(v___x_2881_, 3, v_res_2879_);
lean_ctor_set(v___x_2881_, 4, v___x_2880_);
v___x_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 1, v___x_2882_);
lean_ctor_set(v___x_2870_, 0, v_pos_2878_);
v___x_2884_ = v___x_2870_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_pos_2878_);
lean_ctor_set(v_reuseFailAlloc_2885_, 1, v___x_2882_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
v___jp_2888_:
{
uint8_t v___x_2892_; 
v___x_2892_ = lean_nat_dec_eq(v_idx_2887_, v_idx_2890_);
lean_dec(v_idx_2890_);
lean_dec(v_idx_2887_);
if (v___x_2892_ == 0)
{
lean_object* v___x_2894_; 
lean_dec(v_snd_2873_);
lean_dec(v_fst_2872_);
lean_del_object(v___x_2870_);
lean_dec_ref(v_scheme_2846_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set_tag(v___x_2875_, 1);
lean_ctor_set(v___x_2875_, 1, v_err_2891_);
lean_ctor_set(v___x_2875_, 0, v_pos_2889_);
v___x_2894_ = v___x_2875_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_pos_2889_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v_err_2891_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
else
{
lean_object* v___x_2896_; 
lean_dec(v_err_2891_);
lean_del_object(v___x_2875_);
v___x_2896_ = lean_box(0);
v_pos_2878_ = v_pos_2889_;
v_res_2879_ = v___x_2896_;
goto v___jp_2877_;
}
}
}
}
}
else
{
lean_object* v_pos_2923_; lean_object* v_err_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2931_; 
lean_dec_ref(v_scheme_2846_);
lean_dec_ref(v_config_2845_);
v_pos_2923_ = lean_ctor_get(v___x_2866_, 0);
v_err_2924_ = lean_ctor_get(v___x_2866_, 1);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2926_ = v___x_2866_;
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_err_2924_);
lean_inc(v_pos_2923_);
lean_dec(v___x_2866_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2929_; 
if (v_isShared_2927_ == 0)
{
v___x_2929_ = v___x_2926_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_pos_2923_);
lean_ctor_set(v_reuseFailAlloc_2930_, 1, v_err_2924_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(lean_object* v_config_2944_, lean_object* v_a_2945_){
_start:
{
lean_object* v___x_2949_; 
lean_inc_ref(v_a_2945_);
v___x_2949_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_2944_, v_a_2945_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_pos_2950_; lean_object* v_res_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_3047_; 
v_pos_2950_ = lean_ctor_get(v___x_2949_, 0);
v_res_2951_ = lean_ctor_get(v___x_2949_, 1);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_2953_ = v___x_2949_;
v_isShared_2954_ = v_isSharedCheck_3047_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_res_2951_);
lean_inc(v_pos_2950_);
lean_dec(v___x_2949_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_3047_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v_pos_2958_; lean_object* v_res_2959_; lean_object* v_idx_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v_pos_2970_; lean_object* v_idx_2971_; lean_object* v_err_2972_; lean_object* v___x_3041_; uint8_t v___x_3042_; 
v___x_3041_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2));
v___x_3042_ = lean_string_dec_eq(v_res_2951_, v___x_3041_);
if (v___x_3042_ == 0)
{
lean_object* v___x_3043_; uint8_t v___x_3044_; 
v___x_3043_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3));
v___x_3044_ = lean_string_dec_eq(v_res_2951_, v___x_3043_);
if (v___x_3044_ == 0)
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
lean_del_object(v___x_2953_);
lean_dec(v_res_2951_);
lean_dec(v_pos_2950_);
lean_dec_ref(v_config_2944_);
v___x_3045_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5));
v___x_3046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3046_, 0, v_a_2945_);
lean_ctor_set(v___x_3046_, 1, v___x_3045_);
return v___x_3046_;
}
else
{
goto v___jp_2976_;
}
}
else
{
goto v___jp_2976_;
}
v___jp_2955_:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2964_; 
v___x_2960_ = lean_box(0);
v___x_2961_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2961_, 0, v_res_2951_);
lean_ctor_set(v___x_2961_, 1, v___y_2956_);
lean_ctor_set(v___x_2961_, 2, v___y_2957_);
lean_ctor_set(v___x_2961_, 3, v_res_2959_);
lean_ctor_set(v___x_2961_, 4, v___x_2960_);
v___x_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 1, v___x_2962_);
lean_ctor_set(v___x_2953_, 0, v_pos_2958_);
v___x_2964_ = v___x_2953_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_pos_2958_);
lean_ctor_set(v_reuseFailAlloc_2965_, 1, v___x_2962_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
v___jp_2966_:
{
uint8_t v___x_2973_; 
v___x_2973_ = lean_nat_dec_eq(v_idx_2967_, v_idx_2971_);
lean_dec(v_idx_2971_);
lean_dec(v_idx_2967_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; 
lean_dec_ref(v_pos_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_del_object(v___x_2953_);
lean_dec(v_res_2951_);
v___x_2974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2974_, 0, v_a_2945_);
lean_ctor_set(v___x_2974_, 1, v_err_2972_);
return v___x_2974_;
}
else
{
lean_object* v___x_2975_; 
lean_dec(v_err_2972_);
lean_dec_ref(v_a_2945_);
v___x_2975_ = lean_box(0);
v___y_2956_ = v___y_2968_;
v___y_2957_ = v___y_2969_;
v_pos_2958_ = v_pos_2970_;
v_res_2959_ = v___x_2975_;
goto v___jp_2955_;
}
}
v___jp_2976_:
{
lean_object* v_array_2977_; lean_object* v_idx_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_3040_; 
v_array_2977_ = lean_ctor_get(v_pos_2950_, 0);
v_idx_2978_ = lean_ctor_get(v_pos_2950_, 1);
v_isSharedCheck_3040_ = !lean_is_exclusive(v_pos_2950_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_2980_ = v_pos_2950_;
v_isShared_2981_ = v_isSharedCheck_3040_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_idx_2978_);
lean_inc(v_array_2977_);
lean_dec(v_pos_2950_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_3040_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2982_; uint8_t v___x_2983_; 
v___x_2982_ = lean_byte_array_size(v_array_2977_);
v___x_2983_ = lean_nat_dec_lt(v_idx_2978_, v___x_2982_);
if (v___x_2983_ == 0)
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
lean_del_object(v___x_2980_);
lean_dec(v_idx_2978_);
lean_dec_ref(v_array_2977_);
lean_del_object(v___x_2953_);
lean_dec(v_res_2951_);
lean_dec_ref(v_config_2944_);
v___x_2984_ = lean_box(0);
v___x_2985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2985_, 0, v_a_2945_);
lean_ctor_set(v___x_2985_, 1, v___x_2984_);
return v___x_2985_;
}
else
{
uint8_t v___x_2986_; uint8_t v_got_2987_; uint8_t v___x_2988_; 
v___x_2986_ = 58;
v_got_2987_ = lean_byte_array_fget(v_array_2977_, v_idx_2978_);
v___x_2988_ = lean_uint8_dec_eq(v_got_2987_, v___x_2986_);
if (v___x_2988_ == 0)
{
lean_object* v___x_2989_; lean_object* v___x_2990_; 
lean_del_object(v___x_2980_);
lean_dec(v_idx_2978_);
lean_dec_ref(v_array_2977_);
lean_del_object(v___x_2953_);
lean_dec(v_res_2951_);
lean_dec_ref(v_config_2944_);
v___x_2989_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
v___x_2990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2990_, 0, v_a_2945_);
lean_ctor_set(v___x_2990_, 1, v___x_2989_);
return v___x_2990_;
}
else
{
lean_object* v___x_2991_; lean_object* v___x_2992_; uint8_t v___x_2993_; 
v___x_2991_ = lean_unsigned_to_nat(1u);
v___x_2992_ = lean_nat_add(v_idx_2978_, v___x_2991_);
lean_dec(v_idx_2978_);
v___x_2993_ = lean_nat_dec_lt(v___x_2992_, v___x_2982_);
if (v___x_2993_ == 0)
{
lean_dec(v___x_2992_);
lean_del_object(v___x_2980_);
lean_dec_ref(v_array_2977_);
lean_del_object(v___x_2953_);
lean_dec(v_res_2951_);
lean_dec_ref(v_config_2944_);
goto v___jp_2946_;
}
else
{
uint8_t v___x_2994_; uint8_t v___x_2995_; uint8_t v___x_2996_; 
v___x_2994_ = lean_byte_array_fget(v_array_2977_, v___x_2992_);
v___x_2995_ = 47;
v___x_2996_ = lean_uint8_dec_eq(v___x_2994_, v___x_2995_);
if (v___x_2996_ == 0)
{
lean_dec(v___x_2992_);
lean_del_object(v___x_2980_);
lean_dec_ref(v_array_2977_);
lean_del_object(v___x_2953_);
lean_dec(v_res_2951_);
lean_dec_ref(v_config_2944_);
goto v___jp_2946_;
}
else
{
lean_object* v___x_2998_; 
if (v_isShared_2981_ == 0)
{
lean_ctor_set(v___x_2980_, 1, v___x_2992_);
v___x_2998_ = v___x_2980_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_array_2977_);
lean_ctor_set(v_reuseFailAlloc_3039_, 1, v___x_2992_);
v___x_2998_ = v_reuseFailAlloc_3039_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
lean_object* v___x_2999_; 
lean_inc_ref(v_config_2944_);
v___x_2999_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2944_, v___x_2998_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_res_3000_; lean_object* v_pos_3001_; lean_object* v_fst_3002_; lean_object* v_snd_3003_; lean_object* v_array_3004_; lean_object* v_idx_3005_; lean_object* v___x_3006_; uint8_t v___x_3007_; 
v_res_3000_ = lean_ctor_get(v___x_2999_, 1);
lean_inc(v_res_3000_);
v_pos_3001_ = lean_ctor_get(v___x_2999_, 0);
lean_inc(v_pos_3001_);
lean_dec_ref_known(v___x_2999_, 2);
v_fst_3002_ = lean_ctor_get(v_res_3000_, 0);
lean_inc(v_fst_3002_);
v_snd_3003_ = lean_ctor_get(v_res_3000_, 1);
lean_inc(v_snd_3003_);
lean_dec(v_res_3000_);
v_array_3004_ = lean_ctor_get(v_pos_3001_, 0);
v_idx_3005_ = lean_ctor_get(v_pos_3001_, 1);
lean_inc(v_idx_3005_);
v___x_3006_ = lean_byte_array_size(v_array_3004_);
v___x_3007_ = lean_nat_dec_lt(v_idx_3005_, v___x_3006_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; 
lean_dec_ref(v_config_2944_);
v___x_3008_ = lean_box(0);
lean_inc(v_idx_3005_);
v_idx_2967_ = v_idx_3005_;
v___y_2968_ = v_fst_3002_;
v___y_2969_ = v_snd_3003_;
v_pos_2970_ = v_pos_3001_;
v_idx_2971_ = v_idx_3005_;
v_err_2972_ = v___x_3008_;
goto v___jp_2966_;
}
else
{
uint8_t v___x_3009_; uint8_t v_got_3010_; uint8_t v___x_3011_; 
v___x_3009_ = 63;
v_got_3010_ = lean_byte_array_fget(v_array_3004_, v_idx_3005_);
v___x_3011_ = lean_uint8_dec_eq(v_got_3010_, v___x_3009_);
if (v___x_3011_ == 0)
{
lean_object* v___x_3012_; 
lean_dec_ref(v_config_2944_);
v___x_3012_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_3005_);
v_idx_2967_ = v_idx_3005_;
v___y_2968_ = v_fst_3002_;
v___y_2969_ = v_snd_3003_;
v_pos_2970_ = v_pos_3001_;
v_idx_2971_ = v_idx_3005_;
v_err_2972_ = v___x_3012_;
goto v___jp_2966_;
}
else
{
lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3027_; 
lean_inc_ref(v_array_3004_);
v_isSharedCheck_3027_ = !lean_is_exclusive(v_pos_3001_);
if (v_isSharedCheck_3027_ == 0)
{
lean_object* v_unused_3028_; lean_object* v_unused_3029_; 
v_unused_3028_ = lean_ctor_get(v_pos_3001_, 1);
lean_dec(v_unused_3028_);
v_unused_3029_ = lean_ctor_get(v_pos_3001_, 0);
lean_dec(v_unused_3029_);
v___x_3014_ = v_pos_3001_;
v_isShared_3015_ = v_isSharedCheck_3027_;
goto v_resetjp_3013_;
}
else
{
lean_dec(v_pos_3001_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3027_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3016_; lean_object* v___x_3018_; 
v___x_3016_ = lean_nat_add(v_idx_3005_, v___x_2991_);
if (v_isShared_3015_ == 0)
{
lean_ctor_set(v___x_3014_, 1, v___x_3016_);
v___x_3018_ = v___x_3014_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_array_3004_);
lean_ctor_set(v_reuseFailAlloc_3026_, 1, v___x_3016_);
v___x_3018_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
lean_object* v___x_3019_; 
v___x_3019_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2944_, v___x_3018_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_pos_3020_; lean_object* v_res_3021_; lean_object* v___x_3022_; 
lean_dec(v_idx_3005_);
lean_dec_ref(v_a_2945_);
v_pos_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_pos_3020_);
v_res_3021_ = lean_ctor_get(v___x_3019_, 1);
lean_inc(v_res_3021_);
lean_dec_ref_known(v___x_3019_, 2);
v___x_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3022_, 0, v_res_3021_);
v___y_2956_ = v_fst_3002_;
v___y_2957_ = v_snd_3003_;
v_pos_2958_ = v_pos_3020_;
v_res_2959_ = v___x_3022_;
goto v___jp_2955_;
}
else
{
lean_object* v_pos_3023_; lean_object* v_err_3024_; lean_object* v_idx_3025_; 
v_pos_3023_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_pos_3023_);
v_err_3024_ = lean_ctor_get(v___x_3019_, 1);
lean_inc(v_err_3024_);
lean_dec_ref_known(v___x_3019_, 2);
v_idx_3025_ = lean_ctor_get(v_pos_3023_, 1);
lean_inc(v_idx_3025_);
v_idx_2967_ = v_idx_3005_;
v___y_2968_ = v_fst_3002_;
v___y_2969_ = v_snd_3003_;
v_pos_2970_ = v_pos_3023_;
v_idx_2971_ = v_idx_3025_;
v_err_2972_ = v_err_3024_;
goto v___jp_2966_;
}
}
}
}
}
}
else
{
lean_object* v_err_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
lean_del_object(v___x_2953_);
lean_dec(v_res_2951_);
lean_dec_ref(v_config_2944_);
v_err_3030_ = lean_ctor_get(v___x_2999_, 1);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3037_ == 0)
{
lean_object* v_unused_3038_; 
v_unused_3038_ = lean_ctor_get(v___x_2999_, 0);
lean_dec(v_unused_3038_);
v___x_3032_ = v___x_2999_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_err_3030_);
lean_dec(v___x_2999_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3035_; 
if (v_isShared_3033_ == 0)
{
lean_ctor_set(v___x_3032_, 0, v_a_2945_);
v___x_3035_ = v___x_3032_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_2945_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v_err_3030_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
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
lean_object* v_err_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
lean_dec_ref(v_config_2944_);
v_err_3048_ = lean_ctor_get(v___x_2949_, 1);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_3055_ == 0)
{
lean_object* v_unused_3056_; 
v_unused_3056_ = lean_ctor_get(v___x_2949_, 0);
lean_dec(v_unused_3056_);
v___x_3050_ = v___x_2949_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_err_3048_);
lean_dec(v___x_2949_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 0, v_a_2945_);
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_2945_);
lean_ctor_set(v_reuseFailAlloc_3054_, 1, v_err_3048_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
v___jp_2946_:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2947_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1));
v___x_2948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2948_, 0, v_a_2945_);
lean_ctor_set(v___x_2948_, 1, v___x_2947_);
return v___x_2948_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(lean_object* v_config_3057_, lean_object* v_a_3058_){
_start:
{
lean_object* v___x_3059_; 
lean_inc_ref(v_a_3058_);
v___x_3059_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3057_, v_a_3058_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_pos_3060_; lean_object* v_res_3061_; lean_object* v___x_3062_; 
v_pos_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_pos_3060_);
v_res_3061_ = lean_ctor_get(v___x_3059_, 1);
lean_inc(v_res_3061_);
lean_dec_ref_known(v___x_3059_, 2);
v___x_3062_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(v_config_3057_, v_res_3061_, v_pos_3060_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_dec_ref(v_a_3058_);
return v___x_3062_;
}
else
{
lean_object* v_err_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3070_; 
v_err_3063_ = lean_ctor_get(v___x_3062_, 1);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3070_ == 0)
{
lean_object* v_unused_3071_; 
v_unused_3071_ = lean_ctor_get(v___x_3062_, 0);
lean_dec(v_unused_3071_);
v___x_3065_ = v___x_3062_;
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_err_3063_);
lean_dec(v___x_3062_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3068_; 
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 0, v_a_3058_);
v___x_3068_ = v___x_3065_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3058_);
lean_ctor_set(v_reuseFailAlloc_3069_, 1, v_err_3063_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
else
{
lean_object* v_err_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3079_; 
lean_dec_ref(v_config_3057_);
v_err_3072_ = lean_ctor_get(v___x_3059_, 1);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3079_ == 0)
{
lean_object* v_unused_3080_; 
v_unused_3080_ = lean_ctor_get(v___x_3059_, 0);
lean_dec(v_unused_3080_);
v___x_3074_ = v___x_3059_;
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_err_3072_);
lean_dec(v___x_3059_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3077_; 
if (v_isShared_3075_ == 0)
{
lean_ctor_set(v___x_3074_, 0, v_a_3058_);
v___x_3077_ = v___x_3074_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_a_3058_);
lean_ctor_set(v_reuseFailAlloc_3078_, 1, v_err_3072_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(lean_object* v_config_3081_, lean_object* v_a_3082_){
_start:
{
lean_object* v___x_3083_; 
lean_inc_ref(v_a_3082_);
v___x_3083_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_3081_, v_a_3082_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_pos_3084_; lean_object* v_res_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3137_; 
v_pos_3084_ = lean_ctor_get(v___x_3083_, 0);
v_res_3085_ = lean_ctor_get(v___x_3083_, 1);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3087_ = v___x_3083_;
v_isShared_3088_ = v_isSharedCheck_3137_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_res_3085_);
lean_inc(v_pos_3084_);
lean_dec(v___x_3083_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3137_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v_array_3089_; lean_object* v_idx_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3136_; 
v_array_3089_ = lean_ctor_get(v_pos_3084_, 0);
v_idx_3090_ = lean_ctor_get(v_pos_3084_, 1);
v_isSharedCheck_3136_ = !lean_is_exclusive(v_pos_3084_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3092_ = v_pos_3084_;
v_isShared_3093_ = v_isSharedCheck_3136_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_idx_3090_);
lean_inc(v_array_3089_);
lean_dec(v_pos_3084_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3136_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3094_; uint8_t v___x_3095_; 
v___x_3094_ = lean_byte_array_size(v_array_3089_);
v___x_3095_ = lean_nat_dec_lt(v_idx_3090_, v___x_3094_);
if (v___x_3095_ == 0)
{
lean_object* v___x_3096_; lean_object* v___x_3098_; 
lean_del_object(v___x_3092_);
lean_dec(v_idx_3090_);
lean_dec_ref(v_array_3089_);
lean_dec(v_res_3085_);
v___x_3096_ = lean_box(0);
if (v_isShared_3088_ == 0)
{
lean_ctor_set_tag(v___x_3087_, 1);
lean_ctor_set(v___x_3087_, 1, v___x_3096_);
lean_ctor_set(v___x_3087_, 0, v_a_3082_);
v___x_3098_ = v___x_3087_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3082_);
lean_ctor_set(v_reuseFailAlloc_3099_, 1, v___x_3096_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
else
{
uint8_t v___x_3100_; uint8_t v_got_3101_; uint8_t v___x_3102_; 
v___x_3100_ = 58;
v_got_3101_ = lean_byte_array_fget(v_array_3089_, v_idx_3090_);
v___x_3102_ = lean_uint8_dec_eq(v_got_3101_, v___x_3100_);
if (v___x_3102_ == 0)
{
lean_object* v___x_3103_; lean_object* v___x_3105_; 
lean_del_object(v___x_3092_);
lean_dec(v_idx_3090_);
lean_dec_ref(v_array_3089_);
lean_dec(v_res_3085_);
v___x_3103_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_3088_ == 0)
{
lean_ctor_set_tag(v___x_3087_, 1);
lean_ctor_set(v___x_3087_, 1, v___x_3103_);
lean_ctor_set(v___x_3087_, 0, v_a_3082_);
v___x_3105_ = v___x_3087_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_a_3082_);
lean_ctor_set(v_reuseFailAlloc_3106_, 1, v___x_3103_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
else
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3110_; 
lean_del_object(v___x_3087_);
v___x_3107_ = lean_unsigned_to_nat(1u);
v___x_3108_ = lean_nat_add(v_idx_3090_, v___x_3107_);
lean_dec(v_idx_3090_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 1, v___x_3108_);
v___x_3110_ = v___x_3092_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_array_3089_);
lean_ctor_set(v_reuseFailAlloc_3135_, 1, v___x_3108_);
v___x_3110_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
lean_object* v___x_3111_; 
v___x_3111_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_3110_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v_pos_3112_; lean_object* v_res_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3125_; 
lean_dec_ref(v_a_3082_);
v_pos_3112_ = lean_ctor_get(v___x_3111_, 0);
v_res_3113_ = lean_ctor_get(v___x_3111_, 1);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3115_ = v___x_3111_;
v_isShared_3116_ = v_isSharedCheck_3125_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_res_3113_);
lean_inc(v_pos_3112_);
lean_dec(v___x_3111_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3125_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; uint16_t v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3123_; 
v___x_3117_ = lean_box(0);
v___x_3118_ = lean_alloc_ctor(2, 0, 2);
v___x_3119_ = lean_unbox(v_res_3113_);
lean_dec(v_res_3113_);
lean_ctor_set_uint16(v___x_3118_, 0, v___x_3119_);
v___x_3120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3117_);
lean_ctor_set(v___x_3120_, 1, v_res_3085_);
lean_ctor_set(v___x_3120_, 2, v___x_3118_);
v___x_3121_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3120_);
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 1, v___x_3121_);
v___x_3123_ = v___x_3115_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_pos_3112_);
lean_ctor_set(v_reuseFailAlloc_3124_, 1, v___x_3121_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
else
{
lean_object* v_err_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
lean_dec(v_res_3085_);
v_err_3126_ = lean_ctor_get(v___x_3111_, 1);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3133_ == 0)
{
lean_object* v_unused_3134_; 
v_unused_3134_ = lean_ctor_get(v___x_3111_, 0);
lean_dec(v_unused_3134_);
v___x_3128_ = v___x_3111_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_err_3126_);
lean_dec(v___x_3111_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3131_; 
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 0, v_a_3082_);
v___x_3131_ = v___x_3128_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3082_);
lean_ctor_set(v_reuseFailAlloc_3132_, 1, v_err_3126_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
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
lean_object* v_err_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
v_err_3138_ = lean_ctor_get(v___x_3083_, 1);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3145_ == 0)
{
lean_object* v_unused_3146_; 
v_unused_3146_ = lean_ctor_get(v___x_3083_, 0);
lean_dec(v_unused_3146_);
v___x_3140_ = v___x_3083_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_err_3138_);
lean_dec(v___x_3083_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 0, v_a_3082_);
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_3082_);
lean_ctor_set(v_reuseFailAlloc_3144_, 1, v_err_3138_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority___boxed(lean_object* v_config_3147_, lean_object* v_a_3148_){
_start:
{
lean_object* v_res_3149_; 
v_res_3149_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3147_, v_a_3148_);
lean_dec_ref(v_config_3147_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object* v_config_3150_, lean_object* v_a_3151_){
_start:
{
lean_object* v___x_3152_; 
lean_inc_ref(v_a_3151_);
v___x_3152_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(v_a_3151_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_dec_ref(v_a_3151_);
lean_dec_ref(v_config_3150_);
return v___x_3152_;
}
else
{
lean_object* v_pos_3153_; lean_object* v_idx_3154_; lean_object* v_idx_3155_; uint8_t v___x_3156_; 
v_pos_3153_ = lean_ctor_get(v___x_3152_, 0);
v_idx_3154_ = lean_ctor_get(v_a_3151_, 1);
lean_inc(v_idx_3154_);
lean_dec_ref(v_a_3151_);
v_idx_3155_ = lean_ctor_get(v_pos_3153_, 1);
v___x_3156_ = lean_nat_dec_eq(v_idx_3154_, v_idx_3155_);
lean_dec(v_idx_3154_);
if (v___x_3156_ == 0)
{
lean_dec_ref(v_config_3150_);
return v___x_3152_;
}
else
{
lean_object* v___x_3157_; 
lean_inc(v_idx_3155_);
lean_inc(v_pos_3153_);
lean_dec_ref_known(v___x_3152_, 2);
lean_inc_ref(v_config_3150_);
v___x_3157_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(v_config_3150_, v_pos_3153_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_dec(v_idx_3155_);
lean_dec_ref(v_config_3150_);
return v___x_3157_;
}
else
{
lean_object* v_pos_3158_; lean_object* v_idx_3159_; uint8_t v___x_3160_; 
v_pos_3158_ = lean_ctor_get(v___x_3157_, 0);
v_idx_3159_ = lean_ctor_get(v_pos_3158_, 1);
v___x_3160_ = lean_nat_dec_eq(v_idx_3155_, v_idx_3159_);
lean_dec(v_idx_3155_);
if (v___x_3160_ == 0)
{
lean_dec_ref(v_config_3150_);
return v___x_3157_;
}
else
{
lean_object* v___x_3161_; 
lean_inc(v_idx_3159_);
lean_inc(v_pos_3158_);
lean_dec_ref_known(v___x_3157_, 2);
lean_inc_ref(v_config_3150_);
v___x_3161_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(v_config_3150_, v_pos_3158_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_dec(v_idx_3159_);
lean_dec_ref(v_config_3150_);
return v___x_3161_;
}
else
{
lean_object* v_pos_3162_; lean_object* v_idx_3163_; uint8_t v___x_3164_; 
v_pos_3162_ = lean_ctor_get(v___x_3161_, 0);
v_idx_3163_ = lean_ctor_get(v_pos_3162_, 1);
v___x_3164_ = lean_nat_dec_eq(v_idx_3159_, v_idx_3163_);
lean_dec(v_idx_3159_);
if (v___x_3164_ == 0)
{
lean_dec_ref(v_config_3150_);
return v___x_3161_;
}
else
{
lean_object* v___x_3165_; 
lean_inc(v_idx_3163_);
lean_inc(v_pos_3162_);
lean_dec_ref_known(v___x_3161_, 2);
v___x_3165_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3150_, v_pos_3162_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_dec(v_idx_3163_);
lean_dec_ref(v_config_3150_);
return v___x_3165_;
}
else
{
lean_object* v_pos_3166_; lean_object* v_idx_3167_; uint8_t v___x_3168_; 
v_pos_3166_ = lean_ctor_get(v___x_3165_, 0);
v_idx_3167_ = lean_ctor_get(v_pos_3166_, 1);
v___x_3168_ = lean_nat_dec_eq(v_idx_3163_, v_idx_3167_);
lean_dec(v_idx_3163_);
if (v___x_3168_ == 0)
{
lean_dec_ref(v_config_3150_);
return v___x_3165_;
}
else
{
lean_object* v___x_3169_; 
lean_inc(v_pos_3166_);
lean_dec_ref_known(v___x_3165_, 2);
v___x_3169_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(v_config_3150_, v_pos_3166_);
return v___x_3169_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(lean_object* v_config_3173_, lean_object* v_a_3174_){
_start:
{
lean_object* v___x_3175_; 
v___x_3175_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_3173_, v_a_3174_);
if (lean_obj_tag(v___x_3175_) == 0)
{
lean_object* v_pos_3176_; lean_object* v_res_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3190_; 
v_pos_3176_ = lean_ctor_get(v___x_3175_, 0);
v_res_3177_ = lean_ctor_get(v___x_3175_, 1);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3179_ = v___x_3175_;
v_isShared_3180_ = v_isSharedCheck_3190_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_res_3177_);
lean_inc(v_pos_3176_);
lean_dec(v___x_3175_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3190_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3181_; 
v___x_3181_ = l_Std_Http_URI_EncodedFragment_decode(v_res_3177_);
lean_dec(v_res_3177_);
if (lean_obj_tag(v___x_3181_) == 1)
{
lean_object* v_val_3182_; lean_object* v___x_3184_; 
v_val_3182_ = lean_ctor_get(v___x_3181_, 0);
lean_inc(v_val_3182_);
lean_dec_ref_known(v___x_3181_, 1);
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 1, v_val_3182_);
v___x_3184_ = v___x_3179_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_pos_3176_);
lean_ctor_set(v_reuseFailAlloc_3185_, 1, v_val_3182_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
else
{
lean_object* v___x_3186_; lean_object* v___x_3188_; 
lean_dec(v___x_3181_);
v___x_3186_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___closed__1));
if (v_isShared_3180_ == 0)
{
lean_ctor_set_tag(v___x_3179_, 1);
lean_ctor_set(v___x_3179_, 1, v___x_3186_);
v___x_3188_ = v___x_3179_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_pos_3176_);
lean_ctor_set(v_reuseFailAlloc_3189_, 1, v___x_3186_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
}
else
{
lean_object* v_pos_3191_; lean_object* v_err_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3199_; 
v_pos_3191_ = lean_ctor_get(v___x_3175_, 0);
v_err_3192_ = lean_ctor_get(v___x_3175_, 1);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3194_ = v___x_3175_;
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_err_3192_);
lean_inc(v_pos_3191_);
lean_dec(v___x_3175_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3197_; 
if (v_isShared_3195_ == 0)
{
v___x_3197_ = v___x_3194_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_pos_3191_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v_err_3192_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___boxed(lean_object* v_config_3200_, lean_object* v_a_3201_){
_start:
{
lean_object* v_res_3202_; 
v_res_3202_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3200_, v_a_3201_);
lean_dec_ref(v_config_3200_);
return v_res_3202_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_uri(lean_object* v_config_3203_, lean_object* v_a_3204_){
_start:
{
lean_object* v___x_3205_; 
lean_inc_ref(v_a_3204_);
v___x_3205_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3203_, v_a_3204_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v_pos_3206_; lean_object* v_res_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3336_; 
v_pos_3206_ = lean_ctor_get(v___x_3205_, 0);
v_res_3207_ = lean_ctor_get(v___x_3205_, 1);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3209_ = v___x_3205_;
v_isShared_3210_ = v_isSharedCheck_3336_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_res_3207_);
lean_inc(v_pos_3206_);
lean_dec(v___x_3205_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3336_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v_array_3211_; lean_object* v_idx_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3335_; 
v_array_3211_ = lean_ctor_get(v_pos_3206_, 0);
v_idx_3212_ = lean_ctor_get(v_pos_3206_, 1);
v_isSharedCheck_3335_ = !lean_is_exclusive(v_pos_3206_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3214_ = v_pos_3206_;
v_isShared_3215_ = v_isSharedCheck_3335_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_idx_3212_);
lean_inc(v_array_3211_);
lean_dec(v_pos_3206_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3335_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3216_; uint8_t v___x_3217_; 
v___x_3216_ = lean_byte_array_size(v_array_3211_);
v___x_3217_ = lean_nat_dec_lt(v_idx_3212_, v___x_3216_);
if (v___x_3217_ == 0)
{
lean_object* v___x_3218_; lean_object* v___x_3220_; 
lean_del_object(v___x_3214_);
lean_dec(v_idx_3212_);
lean_dec_ref(v_array_3211_);
lean_dec(v_res_3207_);
lean_dec_ref(v_config_3203_);
v___x_3218_ = lean_box(0);
if (v_isShared_3210_ == 0)
{
lean_ctor_set_tag(v___x_3209_, 1);
lean_ctor_set(v___x_3209_, 1, v___x_3218_);
lean_ctor_set(v___x_3209_, 0, v_a_3204_);
v___x_3220_ = v___x_3209_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3204_);
lean_ctor_set(v_reuseFailAlloc_3221_, 1, v___x_3218_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
else
{
uint8_t v___x_3222_; uint8_t v_got_3223_; uint8_t v___x_3224_; 
v___x_3222_ = 58;
v_got_3223_ = lean_byte_array_fget(v_array_3211_, v_idx_3212_);
v___x_3224_ = lean_uint8_dec_eq(v_got_3223_, v___x_3222_);
if (v___x_3224_ == 0)
{
lean_object* v___x_3225_; lean_object* v___x_3227_; 
lean_del_object(v___x_3214_);
lean_dec(v_idx_3212_);
lean_dec_ref(v_array_3211_);
lean_dec(v_res_3207_);
lean_dec_ref(v_config_3203_);
v___x_3225_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_3210_ == 0)
{
lean_ctor_set_tag(v___x_3209_, 1);
lean_ctor_set(v___x_3209_, 1, v___x_3225_);
lean_ctor_set(v___x_3209_, 0, v_a_3204_);
v___x_3227_ = v___x_3209_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_a_3204_);
lean_ctor_set(v_reuseFailAlloc_3228_, 1, v___x_3225_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
else
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3232_; 
v___x_3229_ = lean_unsigned_to_nat(1u);
v___x_3230_ = lean_nat_add(v_idx_3212_, v___x_3229_);
lean_dec(v_idx_3212_);
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 1, v___x_3230_);
v___x_3232_ = v___x_3214_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_array_3211_);
lean_ctor_set(v_reuseFailAlloc_3334_, 1, v___x_3230_);
v___x_3232_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
lean_object* v___x_3233_; 
lean_inc_ref(v_config_3203_);
v___x_3233_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_3203_, v___x_3232_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v_res_3234_; lean_object* v_pos_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3324_; 
v_res_3234_ = lean_ctor_get(v___x_3233_, 1);
v_pos_3235_ = lean_ctor_get(v___x_3233_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3237_ = v___x_3233_;
v_isShared_3238_ = v_isSharedCheck_3324_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_res_3234_);
lean_inc(v_pos_3235_);
lean_dec(v___x_3233_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3324_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v_fst_3239_; lean_object* v_snd_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3323_; 
v_fst_3239_ = lean_ctor_get(v_res_3234_, 0);
v_snd_3240_ = lean_ctor_get(v_res_3234_, 1);
v_isSharedCheck_3323_ = !lean_is_exclusive(v_res_3234_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3242_ = v_res_3234_;
v_isShared_3243_ = v_isSharedCheck_3323_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_snd_3240_);
lean_inc(v_fst_3239_);
lean_dec(v_res_3234_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3323_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___y_3245_; lean_object* v_pos_3246_; lean_object* v_res_3247_; lean_object* v_idx_3254_; lean_object* v___y_3255_; lean_object* v_pos_3256_; lean_object* v_err_3257_; lean_object* v_pos_3265_; lean_object* v_array_3266_; lean_object* v_idx_3267_; lean_object* v_res_3268_; lean_object* v_array_3286_; lean_object* v_idx_3287_; lean_object* v_pos_3289_; lean_object* v_array_3290_; lean_object* v_idx_3291_; lean_object* v_err_3292_; lean_object* v___x_3296_; uint8_t v___x_3297_; 
v_array_3286_ = lean_ctor_get(v_pos_3235_, 0);
lean_inc_ref(v_array_3286_);
v_idx_3287_ = lean_ctor_get(v_pos_3235_, 1);
lean_inc(v_idx_3287_);
v___x_3296_ = lean_byte_array_size(v_array_3286_);
v___x_3297_ = lean_nat_dec_lt(v_idx_3287_, v___x_3296_);
if (v___x_3297_ == 0)
{
lean_object* v___x_3298_; 
v___x_3298_ = lean_box(0);
lean_inc(v_idx_3287_);
v_pos_3289_ = v_pos_3235_;
v_array_3290_ = v_array_3286_;
v_idx_3291_ = v_idx_3287_;
v_err_3292_ = v___x_3298_;
goto v___jp_3288_;
}
else
{
uint8_t v___x_3299_; uint8_t v_got_3300_; uint8_t v___x_3301_; 
v___x_3299_ = 63;
v_got_3300_ = lean_byte_array_fget(v_array_3286_, v_idx_3287_);
v___x_3301_ = lean_uint8_dec_eq(v_got_3300_, v___x_3299_);
if (v___x_3301_ == 0)
{
lean_object* v___x_3302_; 
v___x_3302_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_3287_);
v_pos_3289_ = v_pos_3235_;
v_array_3290_ = v_array_3286_;
v_idx_3291_ = v_idx_3287_;
v_err_3292_ = v___x_3302_;
goto v___jp_3288_;
}
else
{
lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3320_; 
v_isSharedCheck_3320_ = !lean_is_exclusive(v_pos_3235_);
if (v_isSharedCheck_3320_ == 0)
{
lean_object* v_unused_3321_; lean_object* v_unused_3322_; 
v_unused_3321_ = lean_ctor_get(v_pos_3235_, 1);
lean_dec(v_unused_3321_);
v_unused_3322_ = lean_ctor_get(v_pos_3235_, 0);
lean_dec(v_unused_3322_);
v___x_3304_ = v_pos_3235_;
v_isShared_3305_ = v_isSharedCheck_3320_;
goto v_resetjp_3303_;
}
else
{
lean_dec(v_pos_3235_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3320_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3306_; lean_object* v___x_3308_; 
v___x_3306_ = lean_nat_add(v_idx_3287_, v___x_3229_);
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 1, v___x_3306_);
v___x_3308_ = v___x_3304_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_array_3286_);
lean_ctor_set(v_reuseFailAlloc_3319_, 1, v___x_3306_);
v___x_3308_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
lean_object* v___x_3309_; 
lean_inc_ref(v_config_3203_);
v___x_3309_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3203_, v___x_3308_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v_pos_3310_; lean_object* v_res_3311_; lean_object* v_array_3312_; lean_object* v_idx_3313_; lean_object* v___x_3314_; 
lean_dec(v_idx_3287_);
v_pos_3310_ = lean_ctor_get(v___x_3309_, 0);
lean_inc(v_pos_3310_);
v_res_3311_ = lean_ctor_get(v___x_3309_, 1);
lean_inc(v_res_3311_);
lean_dec_ref_known(v___x_3309_, 2);
v_array_3312_ = lean_ctor_get(v_pos_3310_, 0);
lean_inc_ref(v_array_3312_);
v_idx_3313_ = lean_ctor_get(v_pos_3310_, 1);
lean_inc(v_idx_3313_);
v___x_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3314_, 0, v_res_3311_);
v_pos_3265_ = v_pos_3310_;
v_array_3266_ = v_array_3312_;
v_idx_3267_ = v_idx_3313_;
v_res_3268_ = v___x_3314_;
goto v___jp_3264_;
}
else
{
lean_object* v_pos_3315_; lean_object* v_err_3316_; lean_object* v_array_3317_; lean_object* v_idx_3318_; 
v_pos_3315_ = lean_ctor_get(v___x_3309_, 0);
lean_inc(v_pos_3315_);
v_err_3316_ = lean_ctor_get(v___x_3309_, 1);
lean_inc(v_err_3316_);
lean_dec_ref_known(v___x_3309_, 2);
v_array_3317_ = lean_ctor_get(v_pos_3315_, 0);
lean_inc_ref(v_array_3317_);
v_idx_3318_ = lean_ctor_get(v_pos_3315_, 1);
lean_inc(v_idx_3318_);
v_pos_3289_ = v_pos_3315_;
v_array_3290_ = v_array_3317_;
v_idx_3291_ = v_idx_3318_;
v_err_3292_ = v_err_3316_;
goto v___jp_3288_;
}
}
}
}
}
v___jp_3244_:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3251_; 
v___x_3248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3248_, 0, v_res_3207_);
lean_ctor_set(v___x_3248_, 1, v_fst_3239_);
lean_ctor_set(v___x_3248_, 2, v_snd_3240_);
lean_ctor_set(v___x_3248_, 3, v___y_3245_);
lean_ctor_set(v___x_3248_, 4, v_res_3247_);
v___x_3249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3248_);
if (v_isShared_3238_ == 0)
{
lean_ctor_set(v___x_3237_, 1, v___x_3249_);
lean_ctor_set(v___x_3237_, 0, v_pos_3246_);
v___x_3251_ = v___x_3237_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_pos_3246_);
lean_ctor_set(v_reuseFailAlloc_3252_, 1, v___x_3249_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
v___jp_3253_:
{
lean_object* v_idx_3258_; uint8_t v___x_3259_; 
v_idx_3258_ = lean_ctor_get(v_pos_3256_, 1);
v___x_3259_ = lean_nat_dec_eq(v_idx_3254_, v_idx_3258_);
lean_dec(v_idx_3254_);
if (v___x_3259_ == 0)
{
lean_object* v___x_3261_; 
lean_dec_ref(v_pos_3256_);
lean_dec(v___y_3255_);
lean_dec(v_snd_3240_);
lean_dec(v_fst_3239_);
lean_del_object(v___x_3237_);
lean_dec(v_res_3207_);
if (v_isShared_3210_ == 0)
{
lean_ctor_set_tag(v___x_3209_, 1);
lean_ctor_set(v___x_3209_, 1, v_err_3257_);
lean_ctor_set(v___x_3209_, 0, v_a_3204_);
v___x_3261_ = v___x_3209_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3204_);
lean_ctor_set(v_reuseFailAlloc_3262_, 1, v_err_3257_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
else
{
lean_object* v___x_3263_; 
lean_dec(v_err_3257_);
lean_del_object(v___x_3209_);
lean_dec_ref(v_a_3204_);
v___x_3263_ = lean_box(0);
v___y_3245_ = v___y_3255_;
v_pos_3246_ = v_pos_3256_;
v_res_3247_ = v___x_3263_;
goto v___jp_3244_;
}
}
v___jp_3264_:
{
lean_object* v___x_3269_; uint8_t v___x_3270_; 
v___x_3269_ = lean_byte_array_size(v_array_3266_);
v___x_3270_ = lean_nat_dec_lt(v_idx_3267_, v___x_3269_);
if (v___x_3270_ == 0)
{
lean_object* v___x_3271_; 
lean_dec_ref(v_array_3266_);
lean_del_object(v___x_3242_);
lean_dec_ref(v_config_3203_);
v___x_3271_ = lean_box(0);
v_idx_3254_ = v_idx_3267_;
v___y_3255_ = v_res_3268_;
v_pos_3256_ = v_pos_3265_;
v_err_3257_ = v___x_3271_;
goto v___jp_3253_;
}
else
{
uint8_t v___x_3272_; uint8_t v_got_3273_; uint8_t v___x_3274_; 
v___x_3272_ = 35;
v_got_3273_ = lean_byte_array_fget(v_array_3266_, v_idx_3267_);
v___x_3274_ = lean_uint8_dec_eq(v_got_3273_, v___x_3272_);
if (v___x_3274_ == 0)
{
lean_object* v___x_3275_; 
lean_dec_ref(v_array_3266_);
lean_del_object(v___x_3242_);
lean_dec_ref(v_config_3203_);
v___x_3275_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v_idx_3254_ = v_idx_3267_;
v___y_3255_ = v_res_3268_;
v_pos_3256_ = v_pos_3265_;
v_err_3257_ = v___x_3275_;
goto v___jp_3253_;
}
else
{
lean_object* v___x_3276_; lean_object* v___x_3278_; 
lean_dec_ref(v_pos_3265_);
v___x_3276_ = lean_nat_add(v_idx_3267_, v___x_3229_);
if (v_isShared_3243_ == 0)
{
lean_ctor_set(v___x_3242_, 1, v___x_3276_);
lean_ctor_set(v___x_3242_, 0, v_array_3266_);
v___x_3278_ = v___x_3242_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_array_3266_);
lean_ctor_set(v_reuseFailAlloc_3285_, 1, v___x_3276_);
v___x_3278_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
lean_object* v___x_3279_; 
v___x_3279_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3203_, v___x_3278_);
lean_dec_ref(v_config_3203_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v_pos_3280_; lean_object* v_res_3281_; lean_object* v___x_3282_; 
lean_dec(v_idx_3267_);
lean_del_object(v___x_3209_);
lean_dec_ref(v_a_3204_);
v_pos_3280_ = lean_ctor_get(v___x_3279_, 0);
lean_inc(v_pos_3280_);
v_res_3281_ = lean_ctor_get(v___x_3279_, 1);
lean_inc(v_res_3281_);
lean_dec_ref_known(v___x_3279_, 2);
v___x_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3282_, 0, v_res_3281_);
v___y_3245_ = v_res_3268_;
v_pos_3246_ = v_pos_3280_;
v_res_3247_ = v___x_3282_;
goto v___jp_3244_;
}
else
{
lean_object* v_pos_3283_; lean_object* v_err_3284_; 
v_pos_3283_ = lean_ctor_get(v___x_3279_, 0);
lean_inc(v_pos_3283_);
v_err_3284_ = lean_ctor_get(v___x_3279_, 1);
lean_inc(v_err_3284_);
lean_dec_ref_known(v___x_3279_, 2);
v_idx_3254_ = v_idx_3267_;
v___y_3255_ = v_res_3268_;
v_pos_3256_ = v_pos_3283_;
v_err_3257_ = v_err_3284_;
goto v___jp_3253_;
}
}
}
}
}
v___jp_3288_:
{
uint8_t v___x_3293_; 
v___x_3293_ = lean_nat_dec_eq(v_idx_3287_, v_idx_3291_);
lean_dec(v_idx_3287_);
if (v___x_3293_ == 0)
{
lean_object* v___x_3294_; 
lean_dec(v_idx_3291_);
lean_dec_ref(v_array_3290_);
lean_dec_ref(v_pos_3289_);
lean_del_object(v___x_3242_);
lean_dec(v_snd_3240_);
lean_dec(v_fst_3239_);
lean_del_object(v___x_3237_);
lean_del_object(v___x_3209_);
lean_dec(v_res_3207_);
lean_dec_ref(v_config_3203_);
v___x_3294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3294_, 0, v_a_3204_);
lean_ctor_set(v___x_3294_, 1, v_err_3292_);
return v___x_3294_;
}
else
{
lean_object* v___x_3295_; 
lean_dec(v_err_3292_);
v___x_3295_ = lean_box(0);
v_pos_3265_ = v_pos_3289_;
v_array_3266_ = v_array_3290_;
v_idx_3267_ = v_idx_3291_;
v_res_3268_ = v___x_3295_;
goto v___jp_3264_;
}
}
}
}
}
else
{
lean_object* v_err_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3332_; 
lean_del_object(v___x_3209_);
lean_dec(v_res_3207_);
lean_dec_ref(v_config_3203_);
v_err_3325_ = lean_ctor_get(v___x_3233_, 1);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3332_ == 0)
{
lean_object* v_unused_3333_; 
v_unused_3333_ = lean_ctor_get(v___x_3233_, 0);
lean_dec(v_unused_3333_);
v___x_3327_ = v___x_3233_;
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_err_3325_);
lean_dec(v___x_3233_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 0, v_a_3204_);
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3204_);
lean_ctor_set(v_reuseFailAlloc_3331_, 1, v_err_3325_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
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
lean_object* v_err_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3344_; 
lean_dec_ref(v_config_3203_);
v_err_3337_ = lean_ctor_get(v___x_3205_, 1);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3344_ == 0)
{
lean_object* v_unused_3345_; 
v_unused_3345_ = lean_ctor_get(v___x_3205_, 0);
lean_dec(v_unused_3345_);
v___x_3339_ = v___x_3205_;
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_err_3337_);
lean_dec(v___x_3205_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3342_; 
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 0, v_a_3204_);
v___x_3342_ = v___x_3339_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3204_);
lean_ctor_set(v_reuseFailAlloc_3343_, 1, v_err_3337_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withAuthority(lean_object* v_config_3346_, lean_object* v_a_3347_){
_start:
{
lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v_pos_3352_; lean_object* v_res_3353_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v_idx_3360_; lean_object* v___y_3361_; lean_object* v_pos_3362_; lean_object* v_err_3363_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v_pos_3379_; lean_object* v_array_3380_; lean_object* v_idx_3381_; lean_object* v_res_3382_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v_idx_3402_; lean_object* v_pos_3403_; lean_object* v_array_3404_; lean_object* v_idx_3405_; lean_object* v_err_3406_; lean_object* v_pos_3411_; lean_object* v_utf8_3467_; lean_object* v___x_3468_; 
v_utf8_3467_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1);
lean_inc_ref(v_a_3347_);
v___x_3468_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_3467_, v_a_3347_);
if (lean_obj_tag(v___x_3468_) == 0)
{
lean_object* v_pos_3469_; 
v_pos_3469_ = lean_ctor_get(v___x_3468_, 0);
lean_inc(v_pos_3469_);
lean_dec_ref_known(v___x_3468_, 2);
v_pos_3411_ = v_pos_3469_;
goto v___jp_3410_;
}
else
{
if (lean_obj_tag(v___x_3468_) == 0)
{
lean_object* v_pos_3470_; 
v_pos_3470_ = lean_ctor_get(v___x_3468_, 0);
lean_inc(v_pos_3470_);
lean_dec_ref_known(v___x_3468_, 2);
v_pos_3411_ = v_pos_3470_;
goto v___jp_3410_;
}
else
{
lean_object* v_err_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
lean_dec_ref(v_config_3346_);
v_err_3471_ = lean_ctor_get(v___x_3468_, 1);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3478_ == 0)
{
lean_object* v_unused_3479_; 
v_unused_3479_ = lean_ctor_get(v___x_3468_, 0);
lean_dec(v_unused_3479_);
v___x_3473_ = v___x_3468_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_err_3471_);
lean_dec(v___x_3468_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 0, v_a_3347_);
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3347_);
lean_ctor_set(v_reuseFailAlloc_3477_, 1, v_err_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
v___jp_3348_:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3354_, 0, v___y_3349_);
v___x_3355_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3354_);
lean_ctor_set(v___x_3355_, 1, v___y_3350_);
lean_ctor_set(v___x_3355_, 2, v___y_3351_);
lean_ctor_set(v___x_3355_, 3, v_res_3353_);
v___x_3356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3356_, 0, v_pos_3352_);
lean_ctor_set(v___x_3356_, 1, v___x_3355_);
return v___x_3356_;
}
v___jp_3357_:
{
lean_object* v_idx_3364_; uint8_t v___x_3365_; 
v_idx_3364_ = lean_ctor_get(v_pos_3362_, 1);
v___x_3365_ = lean_nat_dec_eq(v_idx_3360_, v_idx_3364_);
lean_dec(v_idx_3360_);
if (v___x_3365_ == 0)
{
lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3372_; 
lean_dec(v___y_3361_);
lean_dec_ref(v___y_3359_);
lean_dec_ref(v___y_3358_);
v_isSharedCheck_3372_ = !lean_is_exclusive(v_pos_3362_);
if (v_isSharedCheck_3372_ == 0)
{
lean_object* v_unused_3373_; lean_object* v_unused_3374_; 
v_unused_3373_ = lean_ctor_get(v_pos_3362_, 1);
lean_dec(v_unused_3373_);
v_unused_3374_ = lean_ctor_get(v_pos_3362_, 0);
lean_dec(v_unused_3374_);
v___x_3367_ = v_pos_3362_;
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
else
{
lean_dec(v_pos_3362_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
lean_ctor_set_tag(v___x_3367_, 1);
lean_ctor_set(v___x_3367_, 1, v_err_3363_);
lean_ctor_set(v___x_3367_, 0, v_a_3347_);
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3347_);
lean_ctor_set(v_reuseFailAlloc_3371_, 1, v_err_3363_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
else
{
lean_object* v___x_3375_; 
lean_dec(v_err_3363_);
lean_dec_ref(v_a_3347_);
v___x_3375_ = lean_box(0);
v___y_3349_ = v___y_3358_;
v___y_3350_ = v___y_3359_;
v___y_3351_ = v___y_3361_;
v_pos_3352_ = v_pos_3362_;
v_res_3353_ = v___x_3375_;
goto v___jp_3348_;
}
}
v___jp_3376_:
{
lean_object* v___x_3383_; uint8_t v___x_3384_; 
v___x_3383_ = lean_byte_array_size(v_array_3380_);
v___x_3384_ = lean_nat_dec_lt(v_idx_3381_, v___x_3383_);
if (v___x_3384_ == 0)
{
lean_object* v___x_3385_; 
lean_dec_ref(v_array_3380_);
lean_dec_ref(v_config_3346_);
v___x_3385_ = lean_box(0);
v___y_3358_ = v___y_3377_;
v___y_3359_ = v___y_3378_;
v_idx_3360_ = v_idx_3381_;
v___y_3361_ = v_res_3382_;
v_pos_3362_ = v_pos_3379_;
v_err_3363_ = v___x_3385_;
goto v___jp_3357_;
}
else
{
uint8_t v___x_3386_; uint8_t v_got_3387_; uint8_t v___x_3388_; 
v___x_3386_ = 35;
v_got_3387_ = lean_byte_array_fget(v_array_3380_, v_idx_3381_);
v___x_3388_ = lean_uint8_dec_eq(v_got_3387_, v___x_3386_);
if (v___x_3388_ == 0)
{
lean_object* v___x_3389_; 
lean_dec_ref(v_array_3380_);
lean_dec_ref(v_config_3346_);
v___x_3389_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v___y_3358_ = v___y_3377_;
v___y_3359_ = v___y_3378_;
v_idx_3360_ = v_idx_3381_;
v___y_3361_ = v_res_3382_;
v_pos_3362_ = v_pos_3379_;
v_err_3363_ = v___x_3389_;
goto v___jp_3357_;
}
else
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
lean_dec_ref(v_pos_3379_);
v___x_3390_ = lean_unsigned_to_nat(1u);
v___x_3391_ = lean_nat_add(v_idx_3381_, v___x_3390_);
v___x_3392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3392_, 0, v_array_3380_);
lean_ctor_set(v___x_3392_, 1, v___x_3391_);
v___x_3393_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3346_, v___x_3392_);
lean_dec_ref(v_config_3346_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_pos_3394_; lean_object* v_res_3395_; lean_object* v___x_3396_; 
lean_dec(v_idx_3381_);
lean_dec_ref(v_a_3347_);
v_pos_3394_ = lean_ctor_get(v___x_3393_, 0);
lean_inc(v_pos_3394_);
v_res_3395_ = lean_ctor_get(v___x_3393_, 1);
lean_inc(v_res_3395_);
lean_dec_ref_known(v___x_3393_, 2);
v___x_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3396_, 0, v_res_3395_);
v___y_3349_ = v___y_3377_;
v___y_3350_ = v___y_3378_;
v___y_3351_ = v_res_3382_;
v_pos_3352_ = v_pos_3394_;
v_res_3353_ = v___x_3396_;
goto v___jp_3348_;
}
else
{
lean_object* v_pos_3397_; lean_object* v_err_3398_; 
v_pos_3397_ = lean_ctor_get(v___x_3393_, 0);
lean_inc(v_pos_3397_);
v_err_3398_ = lean_ctor_get(v___x_3393_, 1);
lean_inc(v_err_3398_);
lean_dec_ref_known(v___x_3393_, 2);
v___y_3358_ = v___y_3377_;
v___y_3359_ = v___y_3378_;
v_idx_3360_ = v_idx_3381_;
v___y_3361_ = v_res_3382_;
v_pos_3362_ = v_pos_3397_;
v_err_3363_ = v_err_3398_;
goto v___jp_3357_;
}
}
}
}
v___jp_3399_:
{
uint8_t v___x_3407_; 
v___x_3407_ = lean_nat_dec_eq(v_idx_3402_, v_idx_3405_);
lean_dec(v_idx_3402_);
if (v___x_3407_ == 0)
{
lean_object* v___x_3408_; 
lean_dec(v_idx_3405_);
lean_dec_ref(v_array_3404_);
lean_dec_ref(v_pos_3403_);
lean_dec_ref(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec_ref(v_config_3346_);
v___x_3408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3408_, 0, v_a_3347_);
lean_ctor_set(v___x_3408_, 1, v_err_3406_);
return v___x_3408_;
}
else
{
lean_object* v___x_3409_; 
lean_dec(v_err_3406_);
v___x_3409_ = lean_box(0);
v___y_3377_ = v___y_3400_;
v___y_3378_ = v___y_3401_;
v_pos_3379_ = v_pos_3403_;
v_array_3380_ = v_array_3404_;
v_idx_3381_ = v_idx_3405_;
v_res_3382_ = v___x_3409_;
goto v___jp_3376_;
}
}
v___jp_3410_:
{
lean_object* v___x_3412_; 
v___x_3412_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_3346_, v_pos_3411_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v_pos_3413_; lean_object* v_res_3414_; uint8_t v___x_3415_; lean_object* v___x_3416_; 
v_pos_3413_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_pos_3413_);
v_res_3414_ = lean_ctor_get(v___x_3412_, 1);
lean_inc(v_res_3414_);
lean_dec_ref_known(v___x_3412_, 2);
v___x_3415_ = 1;
lean_inc_ref(v_config_3346_);
v___x_3416_ = l_Std_Http_URI_Parser_parsePath(v_config_3346_, v___x_3415_, v___x_3415_, v_pos_3413_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_pos_3417_; lean_object* v_res_3418_; lean_object* v_array_3419_; lean_object* v_idx_3420_; lean_object* v___x_3421_; uint8_t v___x_3422_; 
v_pos_3417_ = lean_ctor_get(v___x_3416_, 0);
lean_inc(v_pos_3417_);
v_res_3418_ = lean_ctor_get(v___x_3416_, 1);
lean_inc(v_res_3418_);
lean_dec_ref_known(v___x_3416_, 2);
v_array_3419_ = lean_ctor_get(v_pos_3417_, 0);
lean_inc_ref(v_array_3419_);
v_idx_3420_ = lean_ctor_get(v_pos_3417_, 1);
lean_inc(v_idx_3420_);
v___x_3421_ = lean_byte_array_size(v_array_3419_);
v___x_3422_ = lean_nat_dec_lt(v_idx_3420_, v___x_3421_);
if (v___x_3422_ == 0)
{
lean_object* v___x_3423_; 
v___x_3423_ = lean_box(0);
lean_inc(v_idx_3420_);
v___y_3400_ = v_res_3414_;
v___y_3401_ = v_res_3418_;
v_idx_3402_ = v_idx_3420_;
v_pos_3403_ = v_pos_3417_;
v_array_3404_ = v_array_3419_;
v_idx_3405_ = v_idx_3420_;
v_err_3406_ = v___x_3423_;
goto v___jp_3399_;
}
else
{
uint8_t v___x_3424_; uint8_t v_got_3425_; uint8_t v___x_3426_; 
v___x_3424_ = 63;
v_got_3425_ = lean_byte_array_fget(v_array_3419_, v_idx_3420_);
v___x_3426_ = lean_uint8_dec_eq(v_got_3425_, v___x_3424_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; 
v___x_3427_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_3420_);
v___y_3400_ = v_res_3414_;
v___y_3401_ = v_res_3418_;
v_idx_3402_ = v_idx_3420_;
v_pos_3403_ = v_pos_3417_;
v_array_3404_ = v_array_3419_;
v_idx_3405_ = v_idx_3420_;
v_err_3406_ = v___x_3427_;
goto v___jp_3399_;
}
else
{
lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3446_; 
v_isSharedCheck_3446_ = !lean_is_exclusive(v_pos_3417_);
if (v_isSharedCheck_3446_ == 0)
{
lean_object* v_unused_3447_; lean_object* v_unused_3448_; 
v_unused_3447_ = lean_ctor_get(v_pos_3417_, 1);
lean_dec(v_unused_3447_);
v_unused_3448_ = lean_ctor_get(v_pos_3417_, 0);
lean_dec(v_unused_3448_);
v___x_3429_ = v_pos_3417_;
v_isShared_3430_ = v_isSharedCheck_3446_;
goto v_resetjp_3428_;
}
else
{
lean_dec(v_pos_3417_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3446_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3434_; 
v___x_3431_ = lean_unsigned_to_nat(1u);
v___x_3432_ = lean_nat_add(v_idx_3420_, v___x_3431_);
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 1, v___x_3432_);
v___x_3434_ = v___x_3429_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_array_3419_);
lean_ctor_set(v_reuseFailAlloc_3445_, 1, v___x_3432_);
v___x_3434_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
lean_object* v___x_3435_; 
lean_inc_ref(v_config_3346_);
v___x_3435_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3346_, v___x_3434_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v_pos_3436_; lean_object* v_res_3437_; lean_object* v_array_3438_; lean_object* v_idx_3439_; lean_object* v___x_3440_; 
lean_dec(v_idx_3420_);
v_pos_3436_ = lean_ctor_get(v___x_3435_, 0);
lean_inc(v_pos_3436_);
v_res_3437_ = lean_ctor_get(v___x_3435_, 1);
lean_inc(v_res_3437_);
lean_dec_ref_known(v___x_3435_, 2);
v_array_3438_ = lean_ctor_get(v_pos_3436_, 0);
lean_inc_ref(v_array_3438_);
v_idx_3439_ = lean_ctor_get(v_pos_3436_, 1);
lean_inc(v_idx_3439_);
v___x_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3440_, 0, v_res_3437_);
v___y_3377_ = v_res_3414_;
v___y_3378_ = v_res_3418_;
v_pos_3379_ = v_pos_3436_;
v_array_3380_ = v_array_3438_;
v_idx_3381_ = v_idx_3439_;
v_res_3382_ = v___x_3440_;
goto v___jp_3376_;
}
else
{
lean_object* v_pos_3441_; lean_object* v_err_3442_; lean_object* v_array_3443_; lean_object* v_idx_3444_; 
v_pos_3441_ = lean_ctor_get(v___x_3435_, 0);
lean_inc(v_pos_3441_);
v_err_3442_ = lean_ctor_get(v___x_3435_, 1);
lean_inc(v_err_3442_);
lean_dec_ref_known(v___x_3435_, 2);
v_array_3443_ = lean_ctor_get(v_pos_3441_, 0);
lean_inc_ref(v_array_3443_);
v_idx_3444_ = lean_ctor_get(v_pos_3441_, 1);
lean_inc(v_idx_3444_);
v___y_3400_ = v_res_3414_;
v___y_3401_ = v_res_3418_;
v_idx_3402_ = v_idx_3420_;
v_pos_3403_ = v_pos_3441_;
v_array_3404_ = v_array_3443_;
v_idx_3405_ = v_idx_3444_;
v_err_3406_ = v_err_3442_;
goto v___jp_3399_;
}
}
}
}
}
}
else
{
lean_object* v_err_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3456_; 
lean_dec(v_res_3414_);
lean_dec_ref(v_config_3346_);
v_err_3449_ = lean_ctor_get(v___x_3416_, 1);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3456_ == 0)
{
lean_object* v_unused_3457_; 
v_unused_3457_ = lean_ctor_get(v___x_3416_, 0);
lean_dec(v_unused_3457_);
v___x_3451_ = v___x_3416_;
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_err_3449_);
lean_dec(v___x_3416_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3454_; 
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 0, v_a_3347_);
v___x_3454_ = v___x_3451_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3347_);
lean_ctor_set(v_reuseFailAlloc_3455_, 1, v_err_3449_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
}
else
{
lean_object* v_err_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3465_; 
lean_dec_ref(v_config_3346_);
v_err_3458_ = lean_ctor_get(v___x_3412_, 1);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3465_ == 0)
{
lean_object* v_unused_3466_; 
v_unused_3466_ = lean_ctor_get(v___x_3412_, 0);
lean_dec(v_unused_3466_);
v___x_3460_ = v___x_3412_;
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_err_3458_);
lean_dec(v___x_3412_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3463_; 
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 0, v_a_3347_);
v___x_3463_ = v___x_3460_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_a_3347_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_err_3458_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath(lean_object* v_config_3480_, lean_object* v_a_3481_){
_start:
{
uint8_t v___x_3482_; uint8_t v___x_3483_; lean_object* v___x_3484_; 
v___x_3482_ = 0;
v___x_3483_ = 1;
lean_inc_ref(v_config_3480_);
v___x_3484_ = l_Std_Http_URI_Parser_parsePath(v_config_3480_, v___x_3482_, v___x_3483_, v_a_3481_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_object* v_pos_3485_; lean_object* v_res_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3567_; 
v_pos_3485_ = lean_ctor_get(v___x_3484_, 0);
v_res_3486_ = lean_ctor_get(v___x_3484_, 1);
v_isSharedCheck_3567_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3488_ = v___x_3484_;
v_isShared_3489_ = v_isSharedCheck_3567_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_res_3486_);
lean_inc(v_pos_3485_);
lean_dec(v___x_3484_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3567_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___y_3491_; lean_object* v_pos_3492_; lean_object* v_res_3493_; lean_object* v___y_3500_; lean_object* v_idx_3501_; lean_object* v_pos_3502_; lean_object* v_err_3503_; lean_object* v_pos_3509_; lean_object* v_array_3510_; lean_object* v_idx_3511_; lean_object* v_res_3512_; lean_object* v_array_3529_; lean_object* v_idx_3530_; lean_object* v_pos_3532_; lean_object* v_array_3533_; lean_object* v_idx_3534_; lean_object* v_err_3535_; lean_object* v___x_3539_; uint8_t v___x_3540_; 
v_array_3529_ = lean_ctor_get(v_pos_3485_, 0);
lean_inc_ref(v_array_3529_);
v_idx_3530_ = lean_ctor_get(v_pos_3485_, 1);
lean_inc(v_idx_3530_);
v___x_3539_ = lean_byte_array_size(v_array_3529_);
v___x_3540_ = lean_nat_dec_lt(v_idx_3530_, v___x_3539_);
if (v___x_3540_ == 0)
{
lean_object* v___x_3541_; 
v___x_3541_ = lean_box(0);
lean_inc(v_idx_3530_);
v_pos_3532_ = v_pos_3485_;
v_array_3533_ = v_array_3529_;
v_idx_3534_ = v_idx_3530_;
v_err_3535_ = v___x_3541_;
goto v___jp_3531_;
}
else
{
uint8_t v___x_3542_; uint8_t v_got_3543_; uint8_t v___x_3544_; 
v___x_3542_ = 63;
v_got_3543_ = lean_byte_array_fget(v_array_3529_, v_idx_3530_);
v___x_3544_ = lean_uint8_dec_eq(v_got_3543_, v___x_3542_);
if (v___x_3544_ == 0)
{
lean_object* v___x_3545_; 
v___x_3545_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_3530_);
v_pos_3532_ = v_pos_3485_;
v_array_3533_ = v_array_3529_;
v_idx_3534_ = v_idx_3530_;
v_err_3535_ = v___x_3545_;
goto v___jp_3531_;
}
else
{
lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3564_; 
v_isSharedCheck_3564_ = !lean_is_exclusive(v_pos_3485_);
if (v_isSharedCheck_3564_ == 0)
{
lean_object* v_unused_3565_; lean_object* v_unused_3566_; 
v_unused_3565_ = lean_ctor_get(v_pos_3485_, 1);
lean_dec(v_unused_3565_);
v_unused_3566_ = lean_ctor_get(v_pos_3485_, 0);
lean_dec(v_unused_3566_);
v___x_3547_ = v_pos_3485_;
v_isShared_3548_ = v_isSharedCheck_3564_;
goto v_resetjp_3546_;
}
else
{
lean_dec(v_pos_3485_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3564_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3552_; 
v___x_3549_ = lean_unsigned_to_nat(1u);
v___x_3550_ = lean_nat_add(v_idx_3530_, v___x_3549_);
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 1, v___x_3550_);
v___x_3552_ = v___x_3547_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_array_3529_);
lean_ctor_set(v_reuseFailAlloc_3563_, 1, v___x_3550_);
v___x_3552_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
lean_object* v___x_3553_; 
lean_inc_ref(v_config_3480_);
v___x_3553_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3480_, v___x_3552_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_pos_3554_; lean_object* v_res_3555_; lean_object* v_array_3556_; lean_object* v_idx_3557_; lean_object* v___x_3558_; 
lean_dec(v_idx_3530_);
v_pos_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_pos_3554_);
v_res_3555_ = lean_ctor_get(v___x_3553_, 1);
lean_inc(v_res_3555_);
lean_dec_ref_known(v___x_3553_, 2);
v_array_3556_ = lean_ctor_get(v_pos_3554_, 0);
lean_inc_ref(v_array_3556_);
v_idx_3557_ = lean_ctor_get(v_pos_3554_, 1);
lean_inc(v_idx_3557_);
v___x_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3558_, 0, v_res_3555_);
v_pos_3509_ = v_pos_3554_;
v_array_3510_ = v_array_3556_;
v_idx_3511_ = v_idx_3557_;
v_res_3512_ = v___x_3558_;
goto v___jp_3508_;
}
else
{
lean_object* v_pos_3559_; lean_object* v_err_3560_; lean_object* v_array_3561_; lean_object* v_idx_3562_; 
v_pos_3559_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_pos_3559_);
v_err_3560_ = lean_ctor_get(v___x_3553_, 1);
lean_inc(v_err_3560_);
lean_dec_ref_known(v___x_3553_, 2);
v_array_3561_ = lean_ctor_get(v_pos_3559_, 0);
lean_inc_ref(v_array_3561_);
v_idx_3562_ = lean_ctor_get(v_pos_3559_, 1);
lean_inc(v_idx_3562_);
v_pos_3532_ = v_pos_3559_;
v_array_3533_ = v_array_3561_;
v_idx_3534_ = v_idx_3562_;
v_err_3535_ = v_err_3560_;
goto v___jp_3531_;
}
}
}
}
}
v___jp_3490_:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3497_; 
v___x_3494_ = lean_box(0);
v___x_3495_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3494_);
lean_ctor_set(v___x_3495_, 1, v_res_3486_);
lean_ctor_set(v___x_3495_, 2, v___y_3491_);
lean_ctor_set(v___x_3495_, 3, v_res_3493_);
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 1, v___x_3495_);
lean_ctor_set(v___x_3488_, 0, v_pos_3492_);
v___x_3497_ = v___x_3488_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_pos_3492_);
lean_ctor_set(v_reuseFailAlloc_3498_, 1, v___x_3495_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
v___jp_3499_:
{
lean_object* v_idx_3504_; uint8_t v___x_3505_; 
v_idx_3504_ = lean_ctor_get(v_pos_3502_, 1);
v___x_3505_ = lean_nat_dec_eq(v_idx_3501_, v_idx_3504_);
lean_dec(v_idx_3501_);
if (v___x_3505_ == 0)
{
lean_object* v___x_3506_; 
lean_dec(v___y_3500_);
lean_del_object(v___x_3488_);
lean_dec(v_res_3486_);
v___x_3506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3506_, 0, v_pos_3502_);
lean_ctor_set(v___x_3506_, 1, v_err_3503_);
return v___x_3506_;
}
else
{
lean_object* v___x_3507_; 
lean_dec(v_err_3503_);
v___x_3507_ = lean_box(0);
v___y_3491_ = v___y_3500_;
v_pos_3492_ = v_pos_3502_;
v_res_3493_ = v___x_3507_;
goto v___jp_3490_;
}
}
v___jp_3508_:
{
lean_object* v___x_3513_; uint8_t v___x_3514_; 
v___x_3513_ = lean_byte_array_size(v_array_3510_);
v___x_3514_ = lean_nat_dec_lt(v_idx_3511_, v___x_3513_);
if (v___x_3514_ == 0)
{
lean_object* v___x_3515_; 
lean_dec_ref(v_array_3510_);
lean_dec_ref(v_config_3480_);
v___x_3515_ = lean_box(0);
v___y_3500_ = v_res_3512_;
v_idx_3501_ = v_idx_3511_;
v_pos_3502_ = v_pos_3509_;
v_err_3503_ = v___x_3515_;
goto v___jp_3499_;
}
else
{
uint8_t v___x_3516_; uint8_t v_got_3517_; uint8_t v___x_3518_; 
v___x_3516_ = 35;
v_got_3517_ = lean_byte_array_fget(v_array_3510_, v_idx_3511_);
v___x_3518_ = lean_uint8_dec_eq(v_got_3517_, v___x_3516_);
if (v___x_3518_ == 0)
{
lean_object* v___x_3519_; 
lean_dec_ref(v_array_3510_);
lean_dec_ref(v_config_3480_);
v___x_3519_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v___y_3500_ = v_res_3512_;
v_idx_3501_ = v_idx_3511_;
v_pos_3502_ = v_pos_3509_;
v_err_3503_ = v___x_3519_;
goto v___jp_3499_;
}
else
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
lean_dec_ref(v_pos_3509_);
v___x_3520_ = lean_unsigned_to_nat(1u);
v___x_3521_ = lean_nat_add(v_idx_3511_, v___x_3520_);
v___x_3522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3522_, 0, v_array_3510_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
v___x_3523_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3480_, v___x_3522_);
lean_dec_ref(v_config_3480_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_pos_3524_; lean_object* v_res_3525_; lean_object* v___x_3526_; 
lean_dec(v_idx_3511_);
v_pos_3524_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_pos_3524_);
v_res_3525_ = lean_ctor_get(v___x_3523_, 1);
lean_inc(v_res_3525_);
lean_dec_ref_known(v___x_3523_, 2);
v___x_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3526_, 0, v_res_3525_);
v___y_3491_ = v_res_3512_;
v_pos_3492_ = v_pos_3524_;
v_res_3493_ = v___x_3526_;
goto v___jp_3490_;
}
else
{
lean_object* v_pos_3527_; lean_object* v_err_3528_; 
v_pos_3527_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_pos_3527_);
v_err_3528_ = lean_ctor_get(v___x_3523_, 1);
lean_inc(v_err_3528_);
lean_dec_ref_known(v___x_3523_, 2);
v___y_3500_ = v_res_3512_;
v_idx_3501_ = v_idx_3511_;
v_pos_3502_ = v_pos_3527_;
v_err_3503_ = v_err_3528_;
goto v___jp_3499_;
}
}
}
}
v___jp_3531_:
{
uint8_t v___x_3536_; 
v___x_3536_ = lean_nat_dec_eq(v_idx_3530_, v_idx_3534_);
lean_dec(v_idx_3530_);
if (v___x_3536_ == 0)
{
lean_object* v___x_3537_; 
lean_dec(v_idx_3534_);
lean_dec_ref(v_array_3533_);
lean_del_object(v___x_3488_);
lean_dec(v_res_3486_);
lean_dec_ref(v_config_3480_);
v___x_3537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3537_, 0, v_pos_3532_);
lean_ctor_set(v___x_3537_, 1, v_err_3535_);
return v___x_3537_;
}
else
{
lean_object* v___x_3538_; 
lean_dec(v_err_3535_);
v___x_3538_ = lean_box(0);
v_pos_3509_ = v_pos_3532_;
v_array_3510_ = v_array_3533_;
v_idx_3511_ = v_idx_3534_;
v_res_3512_ = v___x_3538_;
goto v___jp_3508_;
}
}
}
}
else
{
lean_object* v_pos_3568_; lean_object* v_err_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_dec_ref(v_config_3480_);
v_pos_3568_ = lean_ctor_get(v___x_3484_, 0);
v_err_3569_ = lean_ctor_get(v___x_3484_, 1);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3484_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_err_3569_);
lean_inc(v_pos_3568_);
lean_dec(v___x_3484_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_pos_3568_);
lean_ctor_set(v_reuseFailAlloc_3575_, 1, v_err_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_relative(lean_object* v_config_3577_, lean_object* v_a_3578_){
_start:
{
lean_object* v___y_3580_; lean_object* v___x_3600_; 
lean_inc_ref(v_a_3578_);
lean_inc_ref(v_config_3577_);
v___x_3600_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withAuthority(v_config_3577_, v_a_3578_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_dec_ref(v_a_3578_);
lean_dec_ref(v_config_3577_);
v___y_3580_ = v___x_3600_;
goto v___jp_3579_;
}
else
{
lean_object* v_pos_3601_; lean_object* v_idx_3602_; lean_object* v_idx_3603_; uint8_t v___x_3604_; 
v_pos_3601_ = lean_ctor_get(v___x_3600_, 0);
v_idx_3602_ = lean_ctor_get(v_a_3578_, 1);
lean_inc(v_idx_3602_);
lean_dec_ref(v_a_3578_);
v_idx_3603_ = lean_ctor_get(v_pos_3601_, 1);
v___x_3604_ = lean_nat_dec_eq(v_idx_3602_, v_idx_3603_);
lean_dec(v_idx_3602_);
if (v___x_3604_ == 0)
{
lean_dec_ref(v_config_3577_);
v___y_3580_ = v___x_3600_;
goto v___jp_3579_;
}
else
{
lean_object* v___x_3605_; 
lean_inc(v_pos_3601_);
lean_dec_ref_known(v___x_3600_, 2);
v___x_3605_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath(v_config_3577_, v_pos_3601_);
v___y_3580_ = v___x_3605_;
goto v___jp_3579_;
}
}
v___jp_3579_:
{
if (lean_obj_tag(v___y_3580_) == 0)
{
lean_object* v_pos_3581_; lean_object* v_res_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3590_; 
v_pos_3581_ = lean_ctor_get(v___y_3580_, 0);
v_res_3582_ = lean_ctor_get(v___y_3580_, 1);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___y_3580_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3584_ = v___y_3580_;
v_isShared_3585_ = v_isSharedCheck_3590_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_res_3582_);
lean_inc(v_pos_3581_);
lean_dec(v___y_3580_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3590_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3586_; lean_object* v___x_3588_; 
v___x_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3586_, 0, v_res_3582_);
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 1, v___x_3586_);
v___x_3588_ = v___x_3584_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_pos_3581_);
lean_ctor_set(v_reuseFailAlloc_3589_, 1, v___x_3586_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
else
{
lean_object* v_pos_3591_; lean_object* v_err_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3599_; 
v_pos_3591_ = lean_ctor_get(v___y_3580_, 0);
v_err_3592_ = lean_ctor_get(v___y_3580_, 1);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___y_3580_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3594_ = v___y_3580_;
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_err_3592_);
lean_inc(v_pos_3591_);
lean_dec(v___y_3580_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3597_; 
if (v_isShared_3595_ == 0)
{
v___x_3597_ = v___x_3594_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_pos_3591_);
lean_ctor_set(v_reuseFailAlloc_3598_, 1, v_err_3592_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURIReference(lean_object* v_config_3606_, lean_object* v_a_3607_){
_start:
{
lean_object* v___y_3609_; lean_object* v_pos_3610_; lean_object* v___x_3615_; 
lean_inc_ref(v_a_3607_);
lean_inc_ref(v_config_3606_);
v___x_3615_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_uri(v_config_3606_, v_a_3607_);
if (lean_obj_tag(v___x_3615_) == 0)
{
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_dec_ref(v_a_3607_);
lean_dec_ref(v_config_3606_);
return v___x_3615_;
}
else
{
lean_object* v_pos_3616_; 
v_pos_3616_ = lean_ctor_get(v___x_3615_, 0);
lean_inc(v_pos_3616_);
v___y_3609_ = v___x_3615_;
v_pos_3610_ = v_pos_3616_;
goto v___jp_3608_;
}
}
else
{
lean_object* v_err_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
v_err_3617_ = lean_ctor_get(v___x_3615_, 1);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3624_ == 0)
{
lean_object* v_unused_3625_; 
v_unused_3625_ = lean_ctor_get(v___x_3615_, 0);
lean_dec(v_unused_3625_);
v___x_3619_ = v___x_3615_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_err_3617_);
lean_dec(v___x_3615_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
lean_inc_ref(v_a_3607_);
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 0, v_a_3607_);
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3607_);
lean_ctor_set(v_reuseFailAlloc_3623_, 1, v_err_3617_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
lean_inc_ref(v_a_3607_);
v___y_3609_ = v___x_3622_;
v_pos_3610_ = v_a_3607_;
goto v___jp_3608_;
}
}
}
v___jp_3608_:
{
lean_object* v_idx_3611_; lean_object* v_idx_3612_; uint8_t v___x_3613_; 
v_idx_3611_ = lean_ctor_get(v_a_3607_, 1);
lean_inc(v_idx_3611_);
lean_dec_ref(v_a_3607_);
v_idx_3612_ = lean_ctor_get(v_pos_3610_, 1);
v___x_3613_ = lean_nat_dec_eq(v_idx_3611_, v_idx_3612_);
lean_dec(v_idx_3611_);
if (v___x_3613_ == 0)
{
lean_dec_ref(v_pos_3610_);
lean_dec_ref(v_config_3606_);
return v___y_3609_;
}
else
{
lean_object* v___x_3614_; 
lean_dec_ref(v___y_3609_);
v___x_3614_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_relative(v_config_3606_, v_pos_3610_);
return v___x_3614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader(lean_object* v_config_3632_, lean_object* v_a_3633_){
_start:
{
lean_object* v___x_3634_; 
v___x_3634_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_3632_, v_a_3633_);
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_object* v_pos_3635_; lean_object* v_res_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3709_; 
v_pos_3635_ = lean_ctor_get(v___x_3634_, 0);
v_res_3636_ = lean_ctor_get(v___x_3634_, 1);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3638_ = v___x_3634_;
v_isShared_3639_ = v_isSharedCheck_3709_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_res_3636_);
lean_inc(v_pos_3635_);
lean_dec(v___x_3634_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3709_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v_port_3641_; lean_object* v___y_3642_; lean_object* v_pos_3656_; lean_object* v_pos_3659_; lean_object* v_array_3660_; lean_object* v_idx_3661_; lean_object* v_array_3667_; lean_object* v_idx_3668_; lean_object* v___x_3669_; uint8_t v___x_3670_; 
v_array_3667_ = lean_ctor_get(v_pos_3635_, 0);
v_idx_3668_ = lean_ctor_get(v_pos_3635_, 1);
v___x_3669_ = lean_byte_array_size(v_array_3667_);
v___x_3670_ = lean_nat_dec_lt(v_idx_3668_, v___x_3669_);
if (v___x_3670_ == 0)
{
v_pos_3656_ = v_pos_3635_;
goto v___jp_3655_;
}
else
{
uint8_t v___x_3671_; uint8_t v___x_3672_; uint8_t v___x_3673_; 
v___x_3671_ = lean_byte_array_fget(v_array_3667_, v_idx_3668_);
v___x_3672_ = 58;
v___x_3673_ = lean_uint8_dec_eq(v___x_3671_, v___x_3672_);
if (v___x_3673_ == 0)
{
v_pos_3656_ = v_pos_3635_;
goto v___jp_3655_;
}
else
{
if (v___x_3670_ == 0)
{
lean_object* v___x_3674_; lean_object* v___x_3675_; 
lean_del_object(v___x_3638_);
lean_dec(v_res_3636_);
v___x_3674_ = lean_box(0);
v___x_3675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3675_, 0, v_pos_3635_);
lean_ctor_set(v___x_3675_, 1, v___x_3674_);
return v___x_3675_;
}
else
{
if (v___x_3673_ == 0)
{
lean_object* v___x_3676_; lean_object* v___x_3677_; 
lean_del_object(v___x_3638_);
lean_dec(v_res_3636_);
v___x_3676_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
v___x_3677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3677_, 0, v_pos_3635_);
lean_ctor_set(v___x_3677_, 1, v___x_3676_);
return v___x_3677_;
}
else
{
lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3706_; 
lean_inc(v_idx_3668_);
lean_inc_ref(v_array_3667_);
v_isSharedCheck_3706_ = !lean_is_exclusive(v_pos_3635_);
if (v_isSharedCheck_3706_ == 0)
{
lean_object* v_unused_3707_; lean_object* v_unused_3708_; 
v_unused_3707_ = lean_ctor_get(v_pos_3635_, 1);
lean_dec(v_unused_3707_);
v_unused_3708_ = lean_ctor_get(v_pos_3635_, 0);
lean_dec(v_unused_3708_);
v___x_3679_ = v_pos_3635_;
v_isShared_3680_ = v_isSharedCheck_3706_;
goto v_resetjp_3678_;
}
else
{
lean_dec(v_pos_3635_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3706_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3684_; 
v___x_3681_ = lean_unsigned_to_nat(1u);
v___x_3682_ = lean_nat_add(v_idx_3668_, v___x_3681_);
lean_dec(v_idx_3668_);
lean_inc(v___x_3682_);
lean_inc_ref(v_array_3667_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 1, v___x_3682_);
v___x_3684_ = v___x_3679_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_array_3667_);
lean_ctor_set(v_reuseFailAlloc_3705_, 1, v___x_3682_);
v___x_3684_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
uint8_t v___x_3685_; 
v___x_3685_ = lean_nat_dec_lt(v___x_3682_, v___x_3669_);
if (v___x_3685_ == 0)
{
v_pos_3659_ = v___x_3684_;
v_array_3660_ = v_array_3667_;
v_idx_3661_ = v___x_3682_;
goto v___jp_3658_;
}
else
{
uint8_t v___x_3686_; uint8_t v___x_3687_; uint8_t v___x_3688_; 
v___x_3686_ = lean_byte_array_fget(v_array_3667_, v___x_3682_);
v___x_3687_ = 48;
v___x_3688_ = lean_uint8_dec_le(v___x_3687_, v___x_3686_);
if (v___x_3688_ == 0)
{
v_pos_3659_ = v___x_3684_;
v_array_3660_ = v_array_3667_;
v_idx_3661_ = v___x_3682_;
goto v___jp_3658_;
}
else
{
uint8_t v___x_3689_; uint8_t v___x_3690_; 
v___x_3689_ = 57;
v___x_3690_ = lean_uint8_dec_le(v___x_3686_, v___x_3689_);
if (v___x_3690_ == 0)
{
v_pos_3659_ = v___x_3684_;
v_array_3660_ = v_array_3667_;
v_idx_3661_ = v___x_3682_;
goto v___jp_3658_;
}
else
{
lean_object* v___x_3691_; 
lean_dec(v___x_3682_);
lean_dec_ref(v_array_3667_);
v___x_3691_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_3684_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_object* v_pos_3692_; lean_object* v_res_3693_; lean_object* v___x_3694_; uint16_t v___x_3695_; 
v_pos_3692_ = lean_ctor_get(v___x_3691_, 0);
lean_inc(v_pos_3692_);
v_res_3693_ = lean_ctor_get(v___x_3691_, 1);
lean_inc(v_res_3693_);
lean_dec_ref_known(v___x_3691_, 2);
v___x_3694_ = lean_alloc_ctor(2, 0, 2);
v___x_3695_ = lean_unbox(v_res_3693_);
lean_dec(v_res_3693_);
lean_ctor_set_uint16(v___x_3694_, 0, v___x_3695_);
v_port_3641_ = v___x_3694_;
v___y_3642_ = v_pos_3692_;
goto v___jp_3640_;
}
else
{
lean_object* v_pos_3696_; lean_object* v_err_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3704_; 
lean_del_object(v___x_3638_);
lean_dec(v_res_3636_);
v_pos_3696_ = lean_ctor_get(v___x_3691_, 0);
v_err_3697_ = lean_ctor_get(v___x_3691_, 1);
v_isSharedCheck_3704_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3699_ = v___x_3691_;
v_isShared_3700_ = v_isSharedCheck_3704_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_err_3697_);
lean_inc(v_pos_3696_);
lean_dec(v___x_3691_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3704_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v___x_3702_; 
if (v_isShared_3700_ == 0)
{
v___x_3702_ = v___x_3699_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v_pos_3696_);
lean_ctor_set(v_reuseFailAlloc_3703_, 1, v_err_3697_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
return v___x_3702_;
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_3640_:
{
lean_object* v_array_3643_; lean_object* v_idx_3644_; lean_object* v___x_3645_; uint8_t v___x_3646_; 
v_array_3643_ = lean_ctor_get(v___y_3642_, 0);
v_idx_3644_ = lean_ctor_get(v___y_3642_, 1);
v___x_3645_ = lean_byte_array_size(v_array_3643_);
v___x_3646_ = lean_nat_dec_lt(v_idx_3644_, v___x_3645_);
if (v___x_3646_ == 0)
{
lean_object* v___x_3647_; lean_object* v___x_3649_; 
v___x_3647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3647_, 0, v_res_3636_);
lean_ctor_set(v___x_3647_, 1, v_port_3641_);
if (v_isShared_3639_ == 0)
{
lean_ctor_set(v___x_3638_, 1, v___x_3647_);
lean_ctor_set(v___x_3638_, 0, v___y_3642_);
v___x_3649_ = v___x_3638_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___y_3642_);
lean_ctor_set(v_reuseFailAlloc_3650_, 1, v___x_3647_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
else
{
lean_object* v___x_3651_; lean_object* v___x_3653_; 
lean_dec(v_port_3641_);
lean_dec(v_res_3636_);
v___x_3651_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__1));
if (v_isShared_3639_ == 0)
{
lean_ctor_set_tag(v___x_3638_, 1);
lean_ctor_set(v___x_3638_, 1, v___x_3651_);
lean_ctor_set(v___x_3638_, 0, v___y_3642_);
v___x_3653_ = v___x_3638_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v___y_3642_);
lean_ctor_set(v_reuseFailAlloc_3654_, 1, v___x_3651_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
}
v___jp_3655_:
{
lean_object* v___x_3657_; 
v___x_3657_ = lean_box(0);
v_port_3641_ = v___x_3657_;
v___y_3642_ = v_pos_3656_;
goto v___jp_3640_;
}
v___jp_3658_:
{
lean_object* v___x_3662_; uint8_t v___x_3663_; 
v___x_3662_ = lean_byte_array_size(v_array_3660_);
lean_dec_ref(v_array_3660_);
v___x_3663_ = lean_nat_dec_lt(v_idx_3661_, v___x_3662_);
lean_dec(v_idx_3661_);
if (v___x_3663_ == 0)
{
lean_object* v___x_3664_; 
v___x_3664_ = lean_box(1);
v_port_3641_ = v___x_3664_;
v___y_3642_ = v_pos_3659_;
goto v___jp_3640_;
}
else
{
lean_object* v___x_3665_; lean_object* v___x_3666_; 
lean_del_object(v___x_3638_);
lean_dec(v_res_3636_);
v___x_3665_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__3));
v___x_3666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3666_, 0, v_pos_3659_);
lean_ctor_set(v___x_3666_, 1, v___x_3665_);
return v___x_3666_;
}
}
}
}
else
{
lean_object* v_pos_3710_; lean_object* v_err_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
v_pos_3710_ = lean_ctor_get(v___x_3634_, 0);
v_err_3711_ = lean_ctor_get(v___x_3634_, 1);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___x_3634_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_err_3711_);
lean_inc(v_pos_3710_);
lean_dec(v___x_3634_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3714_ == 0)
{
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_pos_3710_);
lean_ctor_set(v_reuseFailAlloc_3717_, 1, v_err_3711_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader___boxed(lean_object* v_config_3719_, lean_object* v_a_3720_){
_start:
{
lean_object* v_res_3721_; 
v_res_3721_ = l_Std_Http_URI_Parser_parseHostHeader(v_config_3719_, v_a_3720_);
lean_dec_ref(v_config_3719_);
return v_res_3721_;
}
}
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec_ByteArray(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_URI_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_URI_Config(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_URI_Parser(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Parsec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Parsec_ByteArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_URI_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_URI_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Data_URI_Parser(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Std_Internal_Parsec(uint8_t builtin);
lean_object* initialize_Std_Internal_Parsec_ByteArray(uint8_t builtin);
lean_object* initialize_Std_Http_Data_URI_Basic(uint8_t builtin);
lean_object* initialize_Std_Http_Data_URI_Config(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Data_URI_Parser(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Parsec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Parsec_ByteArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_URI_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_URI_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_URI_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Data_URI_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Data_URI_Parser(builtin);
}
#ifdef __cplusplus
}
#endif
