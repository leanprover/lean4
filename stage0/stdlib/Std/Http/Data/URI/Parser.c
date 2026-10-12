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
lean_object* l_String_toListImpl(lean_object*);
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
uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0(uint8_t v_c_78_){
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
LEAN_EXPORT void l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_78_ = stack[0].m_num;
uint8_t v_res_100_;
v_res_100_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0(v_c_78_);
stack->m_num = v_res_100_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___boxed(lean_object* v_c_101_){
_start:
{
uint8_t v_c_boxed_102_; uint8_t v_res_103_; lean_object* v_r_104_; 
v_c_boxed_102_ = lean_unbox(v_c_101_);
v_res_103_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0(v_c_boxed_102_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
uint8_t l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(lean_object* v_x_105_){
_start:
{
if (lean_obj_tag(v_x_105_) == 0)
{
uint8_t v___x_106_; 
v___x_106_ = 1;
return v___x_106_;
}
else
{
lean_object* v_head_107_; lean_object* v_tail_108_; uint32_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v_head_107_ = lean_ctor_get(v_x_105_, 0);
v_tail_108_ = lean_ctor_get(v_x_105_, 1);
v___x_138_ = lean_unbox_uint32(v_head_107_);
v___x_139_ = lean_uint32_to_nat(v___x_138_);
v___x_140_ = lean_unsigned_to_nat(128u);
v___x_141_ = lean_nat_dec_lt(v___x_139_, v___x_140_);
lean_dec(v___x_139_);
if (v___x_141_ == 0)
{
goto v___jp_109_;
}
else
{
uint32_t v___x_142_; uint32_t v___x_143_; uint8_t v___x_144_; 
v___x_142_ = 48;
v___x_143_ = lean_unbox_uint32(v_head_107_);
v___x_144_ = lean_uint32_dec_le(v___x_142_, v___x_143_);
if (v___x_144_ == 0)
{
goto v___jp_130_;
}
else
{
uint32_t v___x_145_; uint32_t v___x_146_; uint8_t v___x_147_; 
v___x_145_ = 57;
v___x_146_ = lean_unbox_uint32(v_head_107_);
v___x_147_ = lean_uint32_dec_le(v___x_146_, v___x_145_);
if (v___x_147_ == 0)
{
goto v___jp_130_;
}
else
{
v_x_105_ = v_tail_108_;
goto _start;
}
}
}
v___jp_109_:
{
uint32_t v___x_110_; uint32_t v___x_111_; uint8_t v___x_112_; 
v___x_110_ = 43;
v___x_111_ = lean_unbox_uint32(v_head_107_);
v___x_112_ = lean_uint32_dec_eq(v___x_111_, v___x_110_);
if (v___x_112_ == 0)
{
uint32_t v___x_113_; uint32_t v___x_114_; uint8_t v___x_115_; 
v___x_113_ = 45;
v___x_114_ = lean_unbox_uint32(v_head_107_);
v___x_115_ = lean_uint32_dec_eq(v___x_114_, v___x_113_);
if (v___x_115_ == 0)
{
uint32_t v___x_116_; uint32_t v___x_117_; uint8_t v___x_118_; 
v___x_116_ = 46;
v___x_117_ = lean_unbox_uint32(v_head_107_);
v___x_118_ = lean_uint32_dec_eq(v___x_117_, v___x_116_);
if (v___x_118_ == 0)
{
return v___x_118_;
}
else
{
v_x_105_ = v_tail_108_;
goto _start;
}
}
else
{
v_x_105_ = v_tail_108_;
goto _start;
}
}
else
{
v_x_105_ = v_tail_108_;
goto _start;
}
}
v___jp_122_:
{
uint32_t v___x_123_; uint32_t v___x_124_; uint8_t v___x_125_; 
v___x_123_ = 97;
v___x_124_ = lean_unbox_uint32(v_head_107_);
v___x_125_ = lean_uint32_dec_le(v___x_123_, v___x_124_);
if (v___x_125_ == 0)
{
goto v___jp_109_;
}
else
{
uint32_t v___x_126_; uint32_t v___x_127_; uint8_t v___x_128_; 
v___x_126_ = 122;
v___x_127_ = lean_unbox_uint32(v_head_107_);
v___x_128_ = lean_uint32_dec_le(v___x_127_, v___x_126_);
if (v___x_128_ == 0)
{
goto v___jp_109_;
}
else
{
v_x_105_ = v_tail_108_;
goto _start;
}
}
}
v___jp_130_:
{
uint32_t v___x_131_; uint32_t v___x_132_; uint8_t v___x_133_; 
v___x_131_ = 65;
v___x_132_ = lean_unbox_uint32(v_head_107_);
v___x_133_ = lean_uint32_dec_le(v___x_131_, v___x_132_);
if (v___x_133_ == 0)
{
goto v___jp_122_;
}
else
{
uint32_t v___x_134_; uint32_t v___x_135_; uint8_t v___x_136_; 
v___x_134_ = 90;
v___x_135_ = lean_unbox_uint32(v_head_107_);
v___x_136_ = lean_uint32_dec_le(v___x_135_, v___x_134_);
if (v___x_136_ == 0)
{
goto v___jp_122_;
}
else
{
v_x_105_ = v_tail_108_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_105_ = stack[0].m_obj;
uint8_t v_res_149_;
v_res_149_ = l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(v_x_105_);
stack->m_num = v_res_149_;
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1___boxed(lean_object* v_x_150_){
_start:
{
uint8_t v_res_151_; lean_object* v_r_152_; 
v_res_151_ = l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(v_x_150_);
lean_dec(v_x_150_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(lean_object* v_s_153_, lean_object* v_p_154_){
_start:
{
uint32_t v___y_156_; lean_object* v___x_161_; uint8_t v_decide_162_; 
v___x_161_ = lean_string_utf8_byte_size(v_s_153_);
v_decide_162_ = lean_nat_dec_eq(v_p_154_, v___x_161_);
if (v_decide_162_ == 0)
{
uint32_t v___x_163_; uint32_t v___x_164_; uint8_t v___x_165_; 
v___x_163_ = lean_string_utf8_get_fast(v_s_153_, v_p_154_);
v___x_164_ = 65;
v___x_165_ = lean_uint32_dec_le(v___x_164_, v___x_163_);
if (v___x_165_ == 0)
{
v___y_156_ = v___x_163_;
goto v___jp_155_;
}
else
{
uint32_t v___x_166_; uint8_t v___x_167_; 
v___x_166_ = 90;
v___x_167_ = lean_uint32_dec_le(v___x_163_, v___x_166_);
if (v___x_167_ == 0)
{
v___y_156_ = v___x_163_;
goto v___jp_155_;
}
else
{
uint32_t v___x_168_; uint32_t v___x_169_; 
v___x_168_ = 32;
v___x_169_ = lean_uint32_add(v___x_163_, v___x_168_);
v___y_156_ = v___x_169_;
goto v___jp_155_;
}
}
}
else
{
lean_dec(v_p_154_);
return v_s_153_;
}
v___jp_155_:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
lean_inc(v_p_154_);
v___x_157_ = lean_string_utf8_set(v_s_153_, v_p_154_, v___y_156_);
v___x_158_ = l_Char_utf8Size(v___y_156_);
v___x_159_ = lean_nat_add(v_p_154_, v___x_158_);
lean_dec(v___x_158_);
lean_dec(v_p_154_);
v_s_153_ = v___x_157_;
v_p_154_ = v___x_159_;
goto _start;
}
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_179_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6));
v___x_180_ = lean_unsigned_to_nat(46u);
v___x_181_ = lean_unsigned_to_nat(193u);
v___x_182_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5));
v___x_183_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__4));
v___x_184_ = l_mkPanicMessageWithDecl(v___x_183_, v___x_182_, v___x_181_, v___x_180_, v___x_179_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(lean_object* v_config_189_, lean_object* v_a_190_){
_start:
{
lean_object* v___y_195_; lean_object* v___y_199_; lean_object* v___y_200_; uint8_t v___y_201_; lean_object* v___y_204_; uint32_t v___y_205_; lean_object* v___y_206_; lean_object* v_maxSchemeLength_211_; lean_object* v___x_212_; lean_object* v___y_214_; lean_object* v___y_215_; uint8_t v___x_231_; lean_object* v___y_233_; lean_object* v___y_234_; uint8_t v___y_235_; lean_object* v_lower_236_; lean_object* v_upper_237_; lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_253_; uint8_t v___y_254_; lean_object* v___y_255_; 
v_maxSchemeLength_211_ = lean_ctor_get(v_config_189_, 0);
v___x_212_ = lean_unsigned_to_nat(0u);
v___x_231_ = lean_nat_dec_eq(v_maxSchemeLength_211_, v___x_212_);
if (v___x_231_ == 0)
{
lean_object* v_array_257_; lean_object* v_idx_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v_array_257_ = lean_ctor_get(v_a_190_, 0);
v_idx_258_ = lean_ctor_get(v_a_190_, 1);
v___x_259_ = lean_byte_array_size(v_array_257_);
v___x_260_ = lean_nat_dec_lt(v_idx_258_, v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_box(0);
v___x_262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_262_, 0, v_a_190_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
return v___x_262_;
}
else
{
lean_object* v___f_263_; lean_object* v_pos_265_; uint8_t v_res_266_; uint8_t v_c_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v_it_x27_281_; uint8_t v___x_287_; uint8_t v___x_288_; 
v___f_263_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__8));
v_c_278_ = lean_byte_array_fget(v_array_257_, v_idx_258_);
v___x_279_ = lean_unsigned_to_nat(1u);
v___x_280_ = lean_nat_add(v_idx_258_, v___x_279_);
lean_inc_ref(v_array_257_);
v_it_x27_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_281_, 0, v_array_257_);
lean_ctor_set(v_it_x27_281_, 1, v___x_280_);
v___x_287_ = 65;
v___x_288_ = lean_uint8_dec_le(v___x_287_, v_c_278_);
if (v___x_288_ == 0)
{
goto v___jp_282_;
}
else
{
uint8_t v___x_289_; uint8_t v___x_290_; 
v___x_289_ = 90;
v___x_290_ = lean_uint8_dec_le(v_c_278_, v___x_289_);
if (v___x_290_ == 0)
{
goto v___jp_282_;
}
else
{
lean_dec_ref(v_a_190_);
v_pos_265_ = v_it_x27_281_;
v_res_266_ = v_c_278_;
goto v___jp_264_;
}
}
v___jp_264_:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v_snd_270_; lean_object* v_fst_271_; lean_object* v_fst_272_; lean_object* v_array_273_; lean_object* v_idx_274_; lean_object* v___x_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_267_ = lean_unsigned_to_nat(1u);
v___x_268_ = lean_nat_sub(v_maxSchemeLength_211_, v___x_267_);
lean_inc_ref(v_pos_265_);
v___x_269_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_263_, v___x_268_, v___x_212_, v_pos_265_);
lean_dec(v___x_268_);
v_snd_270_ = lean_ctor_get(v___x_269_, 1);
lean_inc(v_snd_270_);
v_fst_271_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_fst_271_);
lean_dec_ref(v___x_269_);
v_fst_272_ = lean_ctor_get(v_snd_270_, 0);
lean_inc(v_fst_272_);
lean_dec(v_snd_270_);
v_array_273_ = lean_ctor_get(v_pos_265_, 0);
lean_inc_ref(v_array_273_);
v_idx_274_ = lean_ctor_get(v_pos_265_, 1);
lean_inc(v_idx_274_);
lean_dec_ref(v_pos_265_);
v___x_275_ = lean_nat_add(v_idx_274_, v_fst_271_);
lean_dec(v_fst_271_);
v___x_276_ = lean_byte_array_size(v_array_273_);
v___x_277_ = lean_nat_dec_le(v_idx_274_, v___x_212_);
if (v___x_277_ == 0)
{
v___y_250_ = v_fst_272_;
v___y_251_ = v___x_276_;
v___y_252_ = v_array_273_;
v___y_253_ = v___x_275_;
v___y_254_ = v_res_266_;
v___y_255_ = v_idx_274_;
goto v___jp_249_;
}
else
{
lean_dec(v_idx_274_);
v___y_250_ = v_fst_272_;
v___y_251_ = v___x_276_;
v___y_252_ = v_array_273_;
v___y_253_ = v___x_275_;
v___y_254_ = v_res_266_;
v___y_255_ = v___x_212_;
goto v___jp_249_;
}
}
v___jp_282_:
{
uint8_t v___x_283_; uint8_t v___x_284_; 
v___x_283_ = 97;
v___x_284_ = lean_uint8_dec_le(v___x_283_, v_c_278_);
if (v___x_284_ == 0)
{
lean_dec_ref_known(v_it_x27_281_, 2);
goto v___jp_191_;
}
else
{
uint8_t v___x_285_; uint8_t v___x_286_; 
v___x_285_ = 122;
v___x_286_ = lean_uint8_dec_le(v_c_278_, v___x_285_);
if (v___x_286_ == 0)
{
lean_dec_ref_known(v_it_x27_281_, 2);
goto v___jp_191_;
}
else
{
lean_dec_ref(v_a_190_);
v_pos_265_ = v_it_x27_281_;
v_res_266_ = v_c_278_;
goto v___jp_264_;
}
}
}
}
}
else
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10));
v___x_292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_292_, 0, v_a_190_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
return v___x_292_;
}
v___jp_191_:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__1));
v___x_193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_193_, 0, v_a_190_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
return v___x_193_;
}
v___jp_194_:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__3));
v___x_197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_197_, 0, v___y_195_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
return v___x_197_;
}
v___jp_198_:
{
if (v___y_201_ == 0)
{
lean_dec_ref(v___y_200_);
v___y_195_ = v___y_199_;
goto v___jp_194_;
}
else
{
lean_object* v___x_202_; 
v___x_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_202_, 0, v___y_199_);
lean_ctor_set(v___x_202_, 1, v___y_200_);
return v___x_202_;
}
}
v___jp_203_:
{
uint32_t v___x_207_; uint8_t v___x_208_; 
v___x_207_ = 97;
v___x_208_ = lean_uint32_dec_le(v___x_207_, v___y_205_);
if (v___x_208_ == 0)
{
lean_dec_ref(v___y_206_);
v___y_195_ = v___y_204_;
goto v___jp_194_;
}
else
{
uint32_t v___x_209_; uint8_t v___x_210_; 
v___x_209_ = 122;
v___x_210_ = lean_uint32_dec_le(v___y_205_, v___x_209_);
v___y_199_ = v___y_204_;
v___y_200_ = v___y_206_;
v___y_201_ = v___x_210_;
goto v___jp_198_;
}
}
v___jp_213_:
{
lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = l_String_mapAux___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(v___y_215_, v___x_212_);
lean_inc_ref(v___x_216_);
v___x_217_ = l_Std_Http_Internal_instDecidableIsLowerCase(v___x_216_);
if (v___x_217_ == 0)
{
lean_dec_ref(v___x_216_);
v___y_195_ = v___y_214_;
goto v___jp_194_;
}
else
{
lean_object* v___x_218_; uint8_t v___x_219_; 
lean_inc_ref(v___x_216_);
v___x_218_ = l_String_toListImpl(v___x_216_);
v___x_219_ = l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(v___x_218_);
if (v___x_219_ == 0)
{
lean_dec(v___x_218_);
v___y_199_ = v___y_214_;
v___y_200_ = v___x_216_;
v___y_201_ = v___x_219_;
goto v___jp_198_;
}
else
{
lean_object* v___x_220_; 
v___x_220_ = l_List_head_x3f___redArg(v___x_218_);
lean_dec(v___x_218_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_dec_ref(v___x_216_);
v___y_195_ = v___y_214_;
goto v___jp_194_;
}
else
{
lean_object* v_val_221_; uint32_t v___x_222_; uint32_t v___x_223_; uint8_t v___x_224_; 
v_val_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_val_221_);
lean_dec_ref_known(v___x_220_, 1);
v___x_222_ = 65;
v___x_223_ = lean_unbox_uint32(v_val_221_);
v___x_224_ = lean_uint32_dec_le(v___x_222_, v___x_223_);
if (v___x_224_ == 0)
{
uint32_t v___x_225_; 
v___x_225_ = lean_unbox_uint32(v_val_221_);
lean_dec(v_val_221_);
v___y_204_ = v___y_214_;
v___y_205_ = v___x_225_;
v___y_206_ = v___x_216_;
goto v___jp_203_;
}
else
{
uint32_t v___x_226_; uint32_t v___x_227_; uint8_t v___x_228_; 
v___x_226_ = 90;
v___x_227_ = lean_unbox_uint32(v_val_221_);
v___x_228_ = lean_uint32_dec_le(v___x_227_, v___x_226_);
if (v___x_228_ == 0)
{
uint32_t v___x_229_; 
v___x_229_ = lean_unbox_uint32(v_val_221_);
lean_dec(v_val_221_);
v___y_204_ = v___y_214_;
v___y_205_ = v___x_229_;
v___y_206_ = v___x_216_;
goto v___jp_203_;
}
else
{
lean_object* v___x_230_; 
lean_dec(v_val_221_);
v___x_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_230_, 0, v___y_214_);
lean_ctor_set(v___x_230_, 1, v___x_216_);
return v___x_230_;
}
}
}
}
}
}
v___jp_232_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_238_ = l_ByteArray_toByteSlice(v___y_234_, v_lower_236_, v_upper_237_);
v___x_239_ = l_ByteArray_empty;
v___x_240_ = lean_byte_array_push(v___x_239_, v___y_235_);
v___x_241_ = l_ByteSlice_toByteArray(v___x_238_);
v___x_242_ = lean_byte_array_size(v___x_240_);
v___x_243_ = lean_byte_array_size(v___x_241_);
v___x_244_ = lean_byte_array_copy_slice(v___x_241_, v___x_212_, v___x_240_, v___x_242_, v___x_243_, v___x_231_);
lean_dec_ref(v___x_241_);
v___x_245_ = lean_string_validate_utf8(v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; 
lean_dec_ref(v___x_244_);
v___x_246_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_247_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_246_);
v___y_214_ = v___y_233_;
v___y_215_ = v___x_247_;
goto v___jp_213_;
}
else
{
lean_object* v___x_248_; 
v___x_248_ = lean_string_from_utf8_unchecked(v___x_244_);
v___y_214_ = v___y_233_;
v___y_215_ = v___x_248_;
goto v___jp_213_;
}
}
v___jp_249_:
{
uint8_t v___x_256_; 
v___x_256_ = lean_nat_dec_le(v___y_253_, v___y_251_);
if (v___x_256_ == 0)
{
lean_dec(v___y_253_);
v___y_233_ = v___y_250_;
v___y_234_ = v___y_252_;
v___y_235_ = v___y_254_;
v_lower_236_ = v___y_255_;
v_upper_237_ = v___y_251_;
goto v___jp_232_;
}
else
{
lean_dec(v___y_251_);
v___y_233_ = v___y_250_;
v___y_234_ = v___y_252_;
v___y_235_ = v___y_254_;
v_lower_236_ = v___y_255_;
v_upper_237_ = v___y_253_;
goto v___jp_232_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___boxed(lean_object* v_config_293_, lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_293_, v_a_294_);
lean_dec_ref(v_config_293_);
return v_res_295_;
}
}
uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0(uint8_t v___y_296_){
_start:
{
uint8_t v___x_297_; uint8_t v___x_298_; 
v___x_297_ = 48;
v___x_298_ = lean_uint8_dec_le(v___x_297_, v___y_296_);
if (v___x_298_ == 0)
{
return v___x_298_;
}
else
{
uint8_t v___x_299_; uint8_t v___x_300_; 
v___x_299_ = 57;
v___x_300_ = lean_uint8_dec_le(v___y_296_, v___x_299_);
return v___x_300_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_296_ = stack[0].m_num;
uint8_t v_res_301_;
v_res_301_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0(v___y_296_);
stack->m_num = v_res_301_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0___boxed(lean_object* v___y_302_){
_start:
{
uint8_t v___y_560__boxed_303_; uint8_t v_res_304_; lean_object* v_r_305_; 
v___y_560__boxed_303_ = lean_unbox(v___y_302_);
v_res_304_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0(v___y_560__boxed_303_);
v_r_305_ = lean_box(v_res_304_);
return v_r_305_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(lean_object* v_a_309_){
_start:
{
lean_object* v___f_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v_snd_314_; lean_object* v_fst_315_; lean_object* v_fst_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_369_; 
v___f_310_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__0));
v___x_311_ = lean_unsigned_to_nat(5u);
v___x_312_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_309_);
v___x_313_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_310_, v___x_311_, v___x_312_, v_a_309_);
v_snd_314_ = lean_ctor_get(v___x_313_, 1);
lean_inc(v_snd_314_);
v_fst_315_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_fst_315_);
lean_dec_ref(v___x_313_);
v_fst_316_ = lean_ctor_get(v_snd_314_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v_snd_314_);
if (v_isSharedCheck_369_ == 0)
{
lean_object* v_unused_370_; 
v_unused_370_ = lean_ctor_get(v_snd_314_, 1);
lean_dec(v_unused_370_);
v___x_318_ = v_snd_314_;
v_isShared_319_ = v_isSharedCheck_369_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_fst_316_);
lean_dec(v_snd_314_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_369_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___y_321_; lean_object* v_array_352_; lean_object* v_idx_353_; lean_object* v_lower_355_; lean_object* v_upper_356_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___y_366_; uint8_t v___x_368_; 
v_array_352_ = lean_ctor_get(v_a_309_, 0);
lean_inc_ref(v_array_352_);
v_idx_353_ = lean_ctor_get(v_a_309_, 1);
lean_inc(v_idx_353_);
lean_dec_ref(v_a_309_);
v___x_363_ = lean_nat_add(v_idx_353_, v_fst_315_);
lean_dec(v_fst_315_);
v___x_364_ = lean_byte_array_size(v_array_352_);
v___x_368_ = lean_nat_dec_le(v_idx_353_, v___x_312_);
if (v___x_368_ == 0)
{
v___y_366_ = v_idx_353_;
goto v___jp_365_;
}
else
{
lean_dec(v_idx_353_);
v___y_366_ = v___x_312_;
goto v___jp_365_;
}
v___jp_320_:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = lean_string_utf8_byte_size(v___y_321_);
lean_inc_ref(v___y_321_);
v___x_323_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_323_, 0, v___y_321_);
lean_ctor_set(v___x_323_, 1, v___x_312_);
lean_ctor_set(v___x_323_, 2, v___x_322_);
v___x_324_ = l_String_Slice_toNat_x3f(v___x_323_);
lean_dec_ref_known(v___x_323_, 3);
if (lean_obj_tag(v___x_324_) == 1)
{
lean_object* v_val_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_345_; 
lean_dec_ref(v___y_321_);
v_val_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_345_ == 0)
{
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_345_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_val_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_345_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = lean_unsigned_to_nat(65535u);
v___x_330_ = lean_nat_dec_lt(v___x_329_, v_val_325_);
if (v___x_330_ == 0)
{
uint16_t v___x_331_; lean_object* v___x_332_; lean_object* v___x_334_; 
lean_del_object(v___x_327_);
v___x_331_ = lean_uint16_of_nat(v_val_325_);
lean_dec(v_val_325_);
v___x_332_ = lean_box(v___x_331_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 1, v___x_332_);
v___x_334_ = v___x_318_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_fst_316_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v___x_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_336_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__1));
v___x_337_ = l_Nat_reprFast(v_val_325_);
v___x_338_ = lean_string_append(v___x_336_, v___x_337_);
lean_dec_ref(v___x_337_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v___x_338_);
v___x_340_ = v___x_327_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_338_);
v___x_340_ = v_reuseFailAlloc_344_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_342_; 
if (v_isShared_319_ == 0)
{
lean_ctor_set_tag(v___x_318_, 1);
lean_ctor_set(v___x_318_, 1, v___x_340_);
v___x_342_ = v___x_318_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_fst_316_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v___x_340_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_350_; 
lean_dec(v___x_324_);
v___x_346_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__2));
v___x_347_ = lean_string_append(v___x_346_, v___y_321_);
lean_dec_ref(v___y_321_);
v___x_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
if (v_isShared_319_ == 0)
{
lean_ctor_set_tag(v___x_318_, 1);
lean_ctor_set(v___x_318_, 1, v___x_348_);
v___x_350_ = v___x_318_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_fst_316_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v___x_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
v___jp_354_:
{
lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_357_ = l_ByteArray_toByteSlice(v_array_352_, v_lower_355_, v_upper_356_);
v___x_358_ = l_ByteSlice_toByteArray(v___x_357_);
v___x_359_ = lean_string_validate_utf8(v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec_ref(v___x_358_);
v___x_360_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_361_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_360_);
v___y_321_ = v___x_361_;
goto v___jp_320_;
}
else
{
lean_object* v___x_362_; 
v___x_362_ = lean_string_from_utf8_unchecked(v___x_358_);
v___y_321_ = v___x_362_;
goto v___jp_320_;
}
}
v___jp_365_:
{
uint8_t v___x_367_; 
v___x_367_ = lean_nat_dec_le(v___x_363_, v___x_364_);
if (v___x_367_ == 0)
{
lean_dec(v___x_363_);
v_lower_355_ = v___y_366_;
v_upper_356_ = v___x_364_;
goto v___jp_354_;
}
else
{
v_lower_355_ = v___y_366_;
v_upper_356_ = v___x_363_;
goto v___jp_354_;
}
}
}
}
}
uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0(uint8_t v_x_371_){
_start:
{
uint8_t v___x_417_; uint8_t v___x_418_; 
v___x_417_ = 58;
v___x_418_ = lean_uint8_dec_eq(v_x_371_, v___x_417_);
if (v___x_418_ == 0)
{
uint8_t v___x_419_; uint8_t v___x_420_; 
v___x_419_ = 48;
v___x_420_ = lean_uint8_dec_le(v___x_419_, v_x_371_);
if (v___x_420_ == 0)
{
goto v___jp_412_;
}
else
{
uint8_t v___x_421_; uint8_t v___x_422_; 
v___x_421_ = 57;
v___x_422_ = lean_uint8_dec_le(v_x_371_, v___x_421_);
if (v___x_422_ == 0)
{
goto v___jp_412_;
}
else
{
return v___x_422_;
}
}
}
else
{
uint8_t v___x_423_; 
v___x_423_ = 0;
return v___x_423_;
}
v___jp_372_:
{
uint8_t v___x_373_; uint8_t v___x_374_; 
v___x_373_ = 45;
v___x_374_ = lean_uint8_dec_eq(v_x_371_, v___x_373_);
if (v___x_374_ == 0)
{
uint8_t v___x_375_; uint8_t v___x_376_; 
v___x_375_ = 46;
v___x_376_ = lean_uint8_dec_eq(v_x_371_, v___x_375_);
if (v___x_376_ == 0)
{
uint8_t v___x_377_; uint8_t v___x_378_; 
v___x_377_ = 95;
v___x_378_ = lean_uint8_dec_eq(v_x_371_, v___x_377_);
if (v___x_378_ == 0)
{
uint8_t v___x_379_; uint8_t v___x_380_; 
v___x_379_ = 126;
v___x_380_ = lean_uint8_dec_eq(v_x_371_, v___x_379_);
if (v___x_380_ == 0)
{
uint8_t v___x_381_; uint8_t v___x_382_; 
v___x_381_ = 33;
v___x_382_ = lean_uint8_dec_eq(v_x_371_, v___x_381_);
if (v___x_382_ == 0)
{
uint8_t v___x_383_; uint8_t v___x_384_; 
v___x_383_ = 36;
v___x_384_ = lean_uint8_dec_eq(v_x_371_, v___x_383_);
if (v___x_384_ == 0)
{
uint8_t v___x_385_; uint8_t v___x_386_; 
v___x_385_ = 38;
v___x_386_ = lean_uint8_dec_eq(v_x_371_, v___x_385_);
if (v___x_386_ == 0)
{
uint8_t v___x_387_; uint8_t v___x_388_; 
v___x_387_ = 39;
v___x_388_ = lean_uint8_dec_eq(v_x_371_, v___x_387_);
if (v___x_388_ == 0)
{
uint8_t v___x_389_; uint8_t v___x_390_; 
v___x_389_ = 40;
v___x_390_ = lean_uint8_dec_eq(v_x_371_, v___x_389_);
if (v___x_390_ == 0)
{
uint8_t v___x_391_; uint8_t v___x_392_; 
v___x_391_ = 41;
v___x_392_ = lean_uint8_dec_eq(v_x_371_, v___x_391_);
if (v___x_392_ == 0)
{
uint8_t v___x_393_; uint8_t v___x_394_; 
v___x_393_ = 42;
v___x_394_ = lean_uint8_dec_eq(v_x_371_, v___x_393_);
if (v___x_394_ == 0)
{
uint8_t v___x_395_; uint8_t v___x_396_; 
v___x_395_ = 43;
v___x_396_ = lean_uint8_dec_eq(v_x_371_, v___x_395_);
if (v___x_396_ == 0)
{
uint8_t v___x_397_; uint8_t v___x_398_; 
v___x_397_ = 44;
v___x_398_ = lean_uint8_dec_eq(v_x_371_, v___x_397_);
if (v___x_398_ == 0)
{
uint8_t v___x_399_; uint8_t v___x_400_; 
v___x_399_ = 59;
v___x_400_ = lean_uint8_dec_eq(v_x_371_, v___x_399_);
if (v___x_400_ == 0)
{
uint8_t v___x_401_; uint8_t v___x_402_; 
v___x_401_ = 61;
v___x_402_ = lean_uint8_dec_eq(v_x_371_, v___x_401_);
if (v___x_402_ == 0)
{
uint8_t v___x_403_; uint8_t v___x_404_; 
v___x_403_ = 58;
v___x_404_ = lean_uint8_dec_eq(v_x_371_, v___x_403_);
if (v___x_404_ == 0)
{
uint8_t v___x_405_; uint8_t v___x_406_; 
v___x_405_ = 37;
v___x_406_ = lean_uint8_dec_eq(v_x_371_, v___x_405_);
return v___x_406_;
}
else
{
return v___x_404_;
}
}
else
{
return v___x_402_;
}
}
else
{
return v___x_400_;
}
}
else
{
return v___x_398_;
}
}
else
{
return v___x_396_;
}
}
else
{
return v___x_394_;
}
}
else
{
return v___x_392_;
}
}
else
{
return v___x_390_;
}
}
else
{
return v___x_388_;
}
}
else
{
return v___x_386_;
}
}
else
{
return v___x_384_;
}
}
else
{
return v___x_382_;
}
}
else
{
return v___x_380_;
}
}
else
{
return v___x_378_;
}
}
else
{
return v___x_376_;
}
}
else
{
return v___x_374_;
}
}
v___jp_407_:
{
uint8_t v___x_408_; uint8_t v___x_409_; 
v___x_408_ = 65;
v___x_409_ = lean_uint8_dec_le(v___x_408_, v_x_371_);
if (v___x_409_ == 0)
{
goto v___jp_372_;
}
else
{
uint8_t v___x_410_; uint8_t v___x_411_; 
v___x_410_ = 90;
v___x_411_ = lean_uint8_dec_le(v_x_371_, v___x_410_);
if (v___x_411_ == 0)
{
goto v___jp_372_;
}
else
{
return v___x_411_;
}
}
}
v___jp_412_:
{
uint8_t v___x_413_; uint8_t v___x_414_; 
v___x_413_ = 97;
v___x_414_ = lean_uint8_dec_le(v___x_413_, v_x_371_);
if (v___x_414_ == 0)
{
goto v___jp_407_;
}
else
{
uint8_t v___x_415_; uint8_t v___x_416_; 
v___x_415_ = 122;
v___x_416_ = lean_uint8_dec_le(v_x_371_, v___x_415_);
if (v___x_416_ == 0)
{
goto v___jp_407_;
}
else
{
return v___x_416_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_371_ = stack[0].m_num;
uint8_t v_res_424_;
v_res_424_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0(v_x_371_);
stack->m_num = v_res_424_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___boxed(lean_object* v_x_425_){
_start:
{
uint8_t v_x_boxed_426_; uint8_t v_res_427_; lean_object* v_r_428_; 
v_x_boxed_426_ = lean_unbox(v_x_425_);
v_res_427_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0(v_x_boxed_426_);
v_r_428_ = lean_box(v_res_427_);
return v_r_428_;
}
}
uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1(uint8_t v___x_429_, uint8_t v___x_430_, uint8_t v_x_431_){
_start:
{
uint8_t v___x_476_; uint8_t v___x_477_; 
v___x_476_ = 48;
v___x_477_ = lean_uint8_dec_le(v___x_476_, v_x_431_);
if (v___x_477_ == 0)
{
goto v___jp_471_;
}
else
{
uint8_t v___x_478_; uint8_t v___x_479_; 
v___x_478_ = 57;
v___x_479_ = lean_uint8_dec_le(v_x_431_, v___x_478_);
if (v___x_479_ == 0)
{
goto v___jp_471_;
}
else
{
return v___x_430_;
}
}
v___jp_432_:
{
uint8_t v___x_433_; uint8_t v___x_434_; 
v___x_433_ = 45;
v___x_434_ = lean_uint8_dec_eq(v_x_431_, v___x_433_);
if (v___x_434_ == 0)
{
uint8_t v___x_435_; uint8_t v___x_436_; 
v___x_435_ = 46;
v___x_436_ = lean_uint8_dec_eq(v_x_431_, v___x_435_);
if (v___x_436_ == 0)
{
uint8_t v___x_437_; uint8_t v___x_438_; 
v___x_437_ = 95;
v___x_438_ = lean_uint8_dec_eq(v_x_431_, v___x_437_);
if (v___x_438_ == 0)
{
uint8_t v___x_439_; uint8_t v___x_440_; 
v___x_439_ = 126;
v___x_440_ = lean_uint8_dec_eq(v_x_431_, v___x_439_);
if (v___x_440_ == 0)
{
uint8_t v___x_441_; uint8_t v___x_442_; 
v___x_441_ = 33;
v___x_442_ = lean_uint8_dec_eq(v_x_431_, v___x_441_);
if (v___x_442_ == 0)
{
uint8_t v___x_443_; uint8_t v___x_444_; 
v___x_443_ = 36;
v___x_444_ = lean_uint8_dec_eq(v_x_431_, v___x_443_);
if (v___x_444_ == 0)
{
uint8_t v___x_445_; uint8_t v___x_446_; 
v___x_445_ = 38;
v___x_446_ = lean_uint8_dec_eq(v_x_431_, v___x_445_);
if (v___x_446_ == 0)
{
uint8_t v___x_447_; uint8_t v___x_448_; 
v___x_447_ = 39;
v___x_448_ = lean_uint8_dec_eq(v_x_431_, v___x_447_);
if (v___x_448_ == 0)
{
uint8_t v___x_449_; uint8_t v___x_450_; 
v___x_449_ = 40;
v___x_450_ = lean_uint8_dec_eq(v_x_431_, v___x_449_);
if (v___x_450_ == 0)
{
uint8_t v___x_451_; uint8_t v___x_452_; 
v___x_451_ = 41;
v___x_452_ = lean_uint8_dec_eq(v_x_431_, v___x_451_);
if (v___x_452_ == 0)
{
uint8_t v___x_453_; uint8_t v___x_454_; 
v___x_453_ = 42;
v___x_454_ = lean_uint8_dec_eq(v_x_431_, v___x_453_);
if (v___x_454_ == 0)
{
uint8_t v___x_455_; uint8_t v___x_456_; 
v___x_455_ = 43;
v___x_456_ = lean_uint8_dec_eq(v_x_431_, v___x_455_);
if (v___x_456_ == 0)
{
uint8_t v___x_457_; uint8_t v___x_458_; 
v___x_457_ = 44;
v___x_458_ = lean_uint8_dec_eq(v_x_431_, v___x_457_);
if (v___x_458_ == 0)
{
uint8_t v___x_459_; uint8_t v___x_460_; 
v___x_459_ = 59;
v___x_460_ = lean_uint8_dec_eq(v_x_431_, v___x_459_);
if (v___x_460_ == 0)
{
uint8_t v___x_461_; uint8_t v___x_462_; 
v___x_461_ = 61;
v___x_462_ = lean_uint8_dec_eq(v_x_431_, v___x_461_);
if (v___x_462_ == 0)
{
uint8_t v___x_463_; 
v___x_463_ = lean_uint8_dec_eq(v_x_431_, v___x_429_);
if (v___x_463_ == 0)
{
uint8_t v___x_464_; uint8_t v___x_465_; 
v___x_464_ = 37;
v___x_465_ = lean_uint8_dec_eq(v_x_431_, v___x_464_);
return v___x_465_;
}
else
{
return v___x_430_;
}
}
else
{
return v___x_430_;
}
}
else
{
return v___x_430_;
}
}
else
{
return v___x_430_;
}
}
else
{
return v___x_430_;
}
}
else
{
return v___x_430_;
}
}
else
{
return v___x_430_;
}
}
else
{
return v___x_430_;
}
}
else
{
return v___x_430_;
}
}
else
{
return v___x_430_;
}
}
else
{
return v___x_430_;
}
}
else
{
return v___x_430_;
}
}
else
{
return v___x_430_;
}
}
else
{
return v___x_430_;
}
}
else
{
return v___x_430_;
}
}
else
{
return v___x_430_;
}
}
v___jp_466_:
{
uint8_t v___x_467_; uint8_t v___x_468_; 
v___x_467_ = 65;
v___x_468_ = lean_uint8_dec_le(v___x_467_, v_x_431_);
if (v___x_468_ == 0)
{
goto v___jp_432_;
}
else
{
uint8_t v___x_469_; uint8_t v___x_470_; 
v___x_469_ = 90;
v___x_470_ = lean_uint8_dec_le(v_x_431_, v___x_469_);
if (v___x_470_ == 0)
{
goto v___jp_432_;
}
else
{
return v___x_430_;
}
}
}
v___jp_471_:
{
uint8_t v___x_472_; uint8_t v___x_473_; 
v___x_472_ = 97;
v___x_473_ = lean_uint8_dec_le(v___x_472_, v_x_431_);
if (v___x_473_ == 0)
{
goto v___jp_466_;
}
else
{
uint8_t v___x_474_; uint8_t v___x_475_; 
v___x_474_ = 122;
v___x_475_ = lean_uint8_dec_le(v_x_431_, v___x_474_);
if (v___x_475_ == 0)
{
goto v___jp_466_;
}
else
{
return v___x_430_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_429_ = stack[0].m_num;
uint8_t v___x_430_ = stack[1].m_num;
uint8_t v_x_431_ = stack[2].m_num;
uint8_t v_res_480_;
v_res_480_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1(v___x_429_, v___x_430_, v_x_431_);
stack->m_num = v_res_480_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1___boxed(lean_object* v___x_481_, lean_object* v___x_482_, lean_object* v_x_483_){
_start:
{
uint8_t v___x_4678__boxed_484_; uint8_t v___x_4679__boxed_485_; uint8_t v_x_boxed_486_; uint8_t v_res_487_; lean_object* v_r_488_; 
v___x_4678__boxed_484_ = lean_unbox(v___x_481_);
v___x_4679__boxed_485_ = lean_unbox(v___x_482_);
v_x_boxed_486_ = lean_unbox(v_x_483_);
v_res_487_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1(v___x_4678__boxed_484_, v___x_4679__boxed_485_, v_x_boxed_486_);
v_r_488_ = lean_box(v_res_487_);
return v_r_488_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(lean_object* v_config_493_, lean_object* v_a_494_){
_start:
{
lean_object* v___y_496_; lean_object* v_userPassEncoded_497_; lean_object* v___y_498_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v_lower_505_; lean_object* v_upper_506_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_521_; lean_object* v_pos_522_; lean_object* v_maxUserInfoLength_524_; lean_object* v___f_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v_snd_528_; lean_object* v_fst_529_; lean_object* v_fst_530_; lean_object* v_array_531_; lean_object* v_idx_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_584_; 
v_maxUserInfoLength_524_ = lean_ctor_get(v_config_493_, 2);
v___f_525_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__2));
v___x_526_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_494_);
v___x_527_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_525_, v_maxUserInfoLength_524_, v___x_526_, v_a_494_);
v_snd_528_ = lean_ctor_get(v___x_527_, 1);
lean_inc(v_snd_528_);
v_fst_529_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_fst_529_);
lean_dec_ref(v___x_527_);
v_fst_530_ = lean_ctor_get(v_snd_528_, 0);
lean_inc(v_fst_530_);
lean_dec(v_snd_528_);
v_array_531_ = lean_ctor_get(v_a_494_, 0);
v_idx_532_ = lean_ctor_get(v_a_494_, 1);
v_isSharedCheck_584_ = !lean_is_exclusive(v_a_494_);
if (v_isSharedCheck_584_ == 0)
{
v___x_534_ = v_a_494_;
v_isShared_535_ = v_isSharedCheck_584_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_idx_532_);
lean_inc(v_array_531_);
lean_dec(v_a_494_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_584_;
goto v_resetjp_533_;
}
v___jp_495_:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_499_, 0, v___y_496_);
lean_ctor_set(v___x_499_, 1, v_userPassEncoded_497_);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v___y_498_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
return v___x_500_;
}
v___jp_501_:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = l_ByteArray_toByteSlice(v___y_502_, v_lower_505_, v_upper_506_);
v___x_508_ = l_ByteSlice_toByteArray(v___x_507_);
v___x_509_ = l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(v___x_508_);
if (lean_obj_tag(v___x_509_) == 1)
{
v___y_496_ = v___y_504_;
v_userPassEncoded_497_ = v___x_509_;
v___y_498_ = v___y_503_;
goto v___jp_495_;
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; 
lean_dec(v___x_509_);
lean_dec_ref(v___y_504_);
v___x_510_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1));
v___x_511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_511_, 0, v___y_503_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
return v___x_511_;
}
}
v___jp_512_:
{
uint8_t v___x_519_; 
v___x_519_ = lean_nat_dec_le(v___y_514_, v___y_515_);
if (v___x_519_ == 0)
{
lean_dec(v___y_514_);
v___y_502_ = v___y_513_;
v___y_503_ = v___y_516_;
v___y_504_ = v___y_517_;
v_lower_505_ = v___y_518_;
v_upper_506_ = v___y_515_;
goto v___jp_501_;
}
else
{
lean_dec(v___y_515_);
v___y_502_ = v___y_513_;
v___y_503_ = v___y_516_;
v___y_504_ = v___y_517_;
v_lower_505_ = v___y_518_;
v_upper_506_ = v___y_514_;
goto v___jp_501_;
}
}
v___jp_520_:
{
lean_object* v___x_523_; 
v___x_523_ = lean_box(0);
v___y_496_ = v___y_521_;
v_userPassEncoded_497_ = v___x_523_;
v___y_498_ = v_pos_522_;
goto v___jp_495_;
}
v_resetjp_533_:
{
lean_object* v_lower_537_; lean_object* v_upper_538_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___y_581_; uint8_t v___x_583_; 
v___x_578_ = lean_nat_add(v_idx_532_, v_fst_529_);
lean_dec(v_fst_529_);
v___x_579_ = lean_byte_array_size(v_array_531_);
v___x_583_ = lean_nat_dec_le(v_idx_532_, v___x_526_);
if (v___x_583_ == 0)
{
v___y_581_ = v_idx_532_;
goto v___jp_580_;
}
else
{
lean_dec(v_idx_532_);
v___y_581_ = v___x_526_;
goto v___jp_580_;
}
v___jp_536_:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_539_ = l_ByteArray_toByteSlice(v_array_531_, v_lower_537_, v_upper_538_);
v___x_540_ = l_ByteSlice_toByteArray(v___x_539_);
v___x_541_ = l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(v___x_540_);
if (lean_obj_tag(v___x_541_) == 1)
{
lean_object* v_val_542_; lean_object* v_array_543_; lean_object* v_idx_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v_val_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_val_542_);
lean_dec_ref_known(v___x_541_, 1);
v_array_543_ = lean_ctor_get(v_fst_530_, 0);
v_idx_544_ = lean_ctor_get(v_fst_530_, 1);
v___x_545_ = lean_byte_array_size(v_array_543_);
v___x_546_ = lean_nat_dec_lt(v_idx_544_, v___x_545_);
if (v___x_546_ == 0)
{
lean_del_object(v___x_534_);
v___y_521_ = v_val_542_;
v_pos_522_ = v_fst_530_;
goto v___jp_520_;
}
else
{
uint8_t v___x_547_; uint8_t v___x_548_; uint8_t v___x_549_; 
v___x_547_ = lean_byte_array_fget(v_array_543_, v_idx_544_);
v___x_548_ = 58;
v___x_549_ = lean_uint8_dec_eq(v___x_547_, v___x_548_);
if (v___x_549_ == 0)
{
lean_del_object(v___x_534_);
v___y_521_ = v_val_542_;
v_pos_522_ = v_fst_530_;
goto v___jp_520_;
}
else
{
if (v___x_546_ == 0)
{
lean_object* v___x_550_; lean_object* v___x_552_; 
lean_dec(v_val_542_);
v___x_550_ = lean_box(0);
if (v_isShared_535_ == 0)
{
lean_ctor_set_tag(v___x_534_, 1);
lean_ctor_set(v___x_534_, 1, v___x_550_);
lean_ctor_set(v___x_534_, 0, v_fst_530_);
v___x_552_ = v___x_534_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_fst_530_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v___x_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
else
{
lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_571_; 
lean_inc(v_idx_544_);
lean_inc_ref(v_array_543_);
lean_del_object(v___x_534_);
v_isSharedCheck_571_ = !lean_is_exclusive(v_fst_530_);
if (v_isSharedCheck_571_ == 0)
{
lean_object* v_unused_572_; lean_object* v_unused_573_; 
v_unused_572_ = lean_ctor_get(v_fst_530_, 1);
lean_dec(v_unused_572_);
v_unused_573_ = lean_ctor_get(v_fst_530_, 0);
lean_dec(v_unused_573_);
v___x_555_ = v_fst_530_;
v_isShared_556_ = v_isSharedCheck_571_;
goto v_resetjp_554_;
}
else
{
lean_dec(v_fst_530_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_571_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___f_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_557_ = lean_box(v___x_548_);
v___x_558_ = lean_box(v___x_546_);
v___f_559_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1___boxed), 3, 2);
lean_closure_set(v___f_559_, 0, v___x_557_);
lean_closure_set(v___f_559_, 1, v___x_558_);
v___x_560_ = lean_unsigned_to_nat(1u);
v___x_561_ = lean_nat_add(v_idx_544_, v___x_560_);
lean_dec(v_idx_544_);
lean_inc(v___x_561_);
lean_inc_ref(v_array_543_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 1, v___x_561_);
v___x_563_ = v___x_555_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_array_543_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v___x_561_);
v___x_563_ = v_reuseFailAlloc_570_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_564_; lean_object* v_snd_565_; lean_object* v_fst_566_; lean_object* v_fst_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_564_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_559_, v_maxUserInfoLength_524_, v___x_526_, v___x_563_);
v_snd_565_ = lean_ctor_get(v___x_564_, 1);
lean_inc(v_snd_565_);
v_fst_566_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_fst_566_);
lean_dec_ref(v___x_564_);
v_fst_567_ = lean_ctor_get(v_snd_565_, 0);
lean_inc(v_fst_567_);
lean_dec(v_snd_565_);
v___x_568_ = lean_nat_add(v___x_561_, v_fst_566_);
lean_dec(v_fst_566_);
v___x_569_ = lean_nat_dec_le(v___x_561_, v___x_526_);
if (v___x_569_ == 0)
{
v___y_513_ = v_array_543_;
v___y_514_ = v___x_568_;
v___y_515_ = v___x_545_;
v___y_516_ = v_fst_567_;
v___y_517_ = v_val_542_;
v___y_518_ = v___x_561_;
goto v___jp_512_;
}
else
{
lean_dec(v___x_561_);
v___y_513_ = v_array_543_;
v___y_514_ = v___x_568_;
v___y_515_ = v___x_545_;
v___y_516_ = v_fst_567_;
v___y_517_ = v_val_542_;
v___y_518_ = v___x_526_;
goto v___jp_512_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_574_; lean_object* v___x_576_; 
lean_dec(v___x_541_);
v___x_574_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1));
if (v_isShared_535_ == 0)
{
lean_ctor_set_tag(v___x_534_, 1);
lean_ctor_set(v___x_534_, 1, v___x_574_);
lean_ctor_set(v___x_534_, 0, v_fst_530_);
v___x_576_ = v___x_534_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_fst_530_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
v___jp_580_:
{
uint8_t v___x_582_; 
v___x_582_ = lean_nat_dec_le(v___x_578_, v___x_579_);
if (v___x_582_ == 0)
{
lean_dec(v___x_578_);
v_lower_537_ = v___y_581_;
v_upper_538_ = v___x_579_;
goto v___jp_536_;
}
else
{
v_lower_537_ = v___y_581_;
v_upper_538_ = v___x_578_;
goto v___jp_536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___boxed(lean_object* v_config_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(v_config_585_, v_a_586_);
lean_dec_ref(v_config_585_);
return v_res_587_;
}
}
uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(uint8_t v_x_588_){
_start:
{
uint8_t v___x_599_; uint8_t v___x_600_; 
v___x_599_ = 58;
v___x_600_ = lean_uint8_dec_eq(v_x_588_, v___x_599_);
if (v___x_600_ == 0)
{
uint8_t v___x_601_; uint8_t v___x_602_; 
v___x_601_ = 46;
v___x_602_ = lean_uint8_dec_eq(v_x_588_, v___x_601_);
if (v___x_602_ == 0)
{
uint8_t v___x_603_; uint8_t v___x_604_; 
v___x_603_ = 48;
v___x_604_ = lean_uint8_dec_le(v___x_603_, v_x_588_);
if (v___x_604_ == 0)
{
goto v___jp_594_;
}
else
{
uint8_t v___x_605_; uint8_t v___x_606_; 
v___x_605_ = 57;
v___x_606_ = lean_uint8_dec_le(v_x_588_, v___x_605_);
if (v___x_606_ == 0)
{
goto v___jp_594_;
}
else
{
return v___x_606_;
}
}
}
else
{
return v___x_602_;
}
}
else
{
return v___x_600_;
}
v___jp_589_:
{
uint8_t v___x_590_; uint8_t v___x_591_; 
v___x_590_ = 65;
v___x_591_ = lean_uint8_dec_le(v___x_590_, v_x_588_);
if (v___x_591_ == 0)
{
return v___x_591_;
}
else
{
uint8_t v___x_592_; uint8_t v___x_593_; 
v___x_592_ = 70;
v___x_593_ = lean_uint8_dec_le(v_x_588_, v___x_592_);
return v___x_593_;
}
}
v___jp_594_:
{
uint8_t v___x_595_; uint8_t v___x_596_; 
v___x_595_ = 97;
v___x_596_ = lean_uint8_dec_le(v___x_595_, v_x_588_);
if (v___x_596_ == 0)
{
goto v___jp_589_;
}
else
{
uint8_t v___x_597_; uint8_t v___x_598_; 
v___x_597_ = 102;
v___x_598_ = lean_uint8_dec_le(v_x_588_, v___x_597_);
if (v___x_598_ == 0)
{
goto v___jp_589_;
}
else
{
return v___x_598_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_588_ = stack[0].m_num;
uint8_t v_res_607_;
v_res_607_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(v_x_588_);
stack->m_num = v_res_607_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___boxed(lean_object* v_x_608_){
_start:
{
uint8_t v_x_boxed_609_; uint8_t v_res_610_; lean_object* v_r_611_; 
v_x_boxed_609_ = lean_unbox(v_x_608_);
v_res_610_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(v_x_boxed_609_);
v_r_611_ = lean_box(v_res_610_);
return v_r_611_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(lean_object* v_a_623_){
_start:
{
lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v_array_634_; lean_object* v_idx_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v_array_634_ = lean_ctor_get(v_a_623_, 0);
v_idx_635_ = lean_ctor_get(v_a_623_, 1);
v___x_636_ = lean_byte_array_size(v_array_634_);
v___x_637_ = lean_nat_dec_lt(v_idx_635_, v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_box(0);
v___x_639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_639_, 0, v_a_623_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
return v___x_639_;
}
else
{
uint8_t v___x_640_; uint8_t v_got_641_; uint8_t v___x_642_; 
v___x_640_ = 91;
v_got_641_ = lean_byte_array_fget(v_array_634_, v_idx_635_);
v___x_642_ = lean_uint8_dec_eq(v_got_641_, v___x_640_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_644_, 0, v_a_623_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
return v___x_644_;
}
else
{
lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_720_; 
lean_inc(v_idx_635_);
lean_inc_ref(v_array_634_);
v_isSharedCheck_720_ = !lean_is_exclusive(v_a_623_);
if (v_isSharedCheck_720_ == 0)
{
lean_object* v_unused_721_; lean_object* v_unused_722_; 
v_unused_721_ = lean_ctor_get(v_a_623_, 1);
lean_dec(v_unused_721_);
v_unused_722_ = lean_ctor_get(v_a_623_, 0);
lean_dec(v_unused_722_);
v___x_646_ = v_a_623_;
v_isShared_647_ = v_isSharedCheck_720_;
goto v_resetjp_645_;
}
else
{
lean_dec(v_a_623_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_720_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___f_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_652_; 
v___f_648_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3));
v___x_649_ = lean_unsigned_to_nat(1u);
v___x_650_ = lean_nat_add(v_idx_635_, v___x_649_);
lean_dec(v_idx_635_);
lean_inc(v___x_650_);
lean_inc_ref(v_array_634_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 1, v___x_650_);
v___x_652_ = v___x_646_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_array_634_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_650_);
v___x_652_ = v_reuseFailAlloc_719_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v_snd_656_; lean_object* v_fst_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_718_; 
v___x_653_ = lean_unsigned_to_nat(256u);
v___x_654_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___x_652_);
v___x_655_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_648_, v___x_653_, v___x_654_, v___x_652_);
v_snd_656_ = lean_ctor_get(v___x_655_, 1);
v_fst_657_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_718_ == 0)
{
v___x_659_ = v___x_655_;
v_isShared_660_ = v_isSharedCheck_718_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_snd_656_);
lean_inc(v_fst_657_);
lean_dec(v___x_655_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_718_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v_fst_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_716_; 
v_fst_661_ = lean_ctor_get(v_snd_656_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v_snd_656_);
if (v_isSharedCheck_716_ == 0)
{
lean_object* v_unused_717_; 
v_unused_717_ = lean_ctor_get(v_snd_656_, 1);
lean_dec(v_unused_717_);
v___x_663_ = v_snd_656_;
v_isShared_664_ = v_isSharedCheck_716_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_fst_661_);
lean_dec(v_snd_656_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_716_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___y_666_; uint8_t v___x_700_; 
v___x_700_ = lean_nat_dec_eq(v_fst_657_, v___x_654_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; lean_object* v___y_703_; uint8_t v___x_711_; 
lean_dec_ref(v___x_652_);
v___x_701_ = lean_nat_add(v___x_650_, v_fst_657_);
lean_dec(v_fst_657_);
v___x_711_ = lean_nat_dec_le(v___x_650_, v___x_654_);
if (v___x_711_ == 0)
{
v___y_703_ = v___x_650_;
goto v___jp_702_;
}
else
{
lean_dec(v___x_650_);
v___y_703_ = v___x_654_;
goto v___jp_702_;
}
v___jp_702_:
{
uint8_t v___x_704_; 
v___x_704_ = lean_nat_dec_le(v___x_701_, v___x_636_);
if (v___x_704_ == 0)
{
lean_object* v___x_706_; 
lean_dec(v___x_701_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v___x_636_);
lean_ctor_set(v___x_659_, 0, v___y_703_);
v___x_706_ = v___x_659_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___y_703_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v___x_636_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
v___y_666_ = v___x_706_;
goto v___jp_665_;
}
}
else
{
lean_object* v___x_709_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v___x_701_);
lean_ctor_set(v___x_659_, 0, v___y_703_);
v___x_709_ = v___x_659_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___y_703_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___x_701_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
v___y_666_ = v___x_709_;
goto v___jp_665_;
}
}
}
}
else
{
lean_object* v___x_712_; lean_object* v___x_714_; 
lean_del_object(v___x_663_);
lean_dec(v_fst_661_);
lean_dec(v_fst_657_);
lean_dec(v___x_650_);
lean_dec_ref(v_array_634_);
v___x_712_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7));
if (v_isShared_660_ == 0)
{
lean_ctor_set_tag(v___x_659_, 1);
lean_ctor_set(v___x_659_, 1, v___x_712_);
lean_ctor_set(v___x_659_, 0, v___x_652_);
v___x_714_ = v___x_659_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_652_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
v___jp_665_:
{
lean_object* v_array_667_; lean_object* v_idx_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
v_array_667_ = lean_ctor_get(v_fst_661_, 0);
v_idx_668_ = lean_ctor_get(v_fst_661_, 1);
v___x_669_ = lean_byte_array_size(v_array_667_);
v___x_670_ = lean_nat_dec_lt(v_idx_668_, v___x_669_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; lean_object* v___x_673_; 
lean_dec_ref(v___y_666_);
lean_dec_ref(v_array_634_);
v___x_671_ = lean_box(0);
if (v_isShared_664_ == 0)
{
lean_ctor_set_tag(v___x_663_, 1);
lean_ctor_set(v___x_663_, 1, v___x_671_);
v___x_673_ = v___x_663_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_fst_661_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v___x_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
else
{
uint8_t v___x_675_; uint8_t v_got_676_; uint8_t v___x_677_; 
v___x_675_ = 93;
v_got_676_ = lean_byte_array_fget(v_array_667_, v_idx_668_);
v___x_677_ = lean_uint8_dec_eq(v_got_676_, v___x_675_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; lean_object* v___x_680_; 
lean_dec_ref(v___y_666_);
lean_dec_ref(v_array_634_);
v___x_678_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5));
if (v_isShared_664_ == 0)
{
lean_ctor_set_tag(v___x_663_, 1);
lean_ctor_set(v___x_663_, 1, v___x_678_);
v___x_680_ = v___x_663_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_fst_661_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v___x_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
else
{
lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_697_; 
lean_inc(v_idx_668_);
lean_inc_ref(v_array_667_);
lean_del_object(v___x_663_);
v_isSharedCheck_697_ = !lean_is_exclusive(v_fst_661_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; lean_object* v_unused_699_; 
v_unused_698_ = lean_ctor_get(v_fst_661_, 1);
lean_dec(v_unused_698_);
v_unused_699_ = lean_ctor_get(v_fst_661_, 0);
lean_dec(v_unused_699_);
v___x_683_ = v_fst_661_;
v_isShared_684_ = v_isSharedCheck_697_;
goto v_resetjp_682_;
}
else
{
lean_dec(v_fst_661_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_697_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v_lower_685_; lean_object* v_upper_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_690_; 
v_lower_685_ = lean_ctor_get(v___y_666_, 0);
lean_inc(v_lower_685_);
v_upper_686_ = lean_ctor_get(v___y_666_, 1);
lean_inc(v_upper_686_);
lean_dec_ref(v___y_666_);
v___x_687_ = l_ByteArray_toByteSlice(v_array_634_, v_lower_685_, v_upper_686_);
v___x_688_ = lean_nat_add(v_idx_668_, v___x_649_);
lean_dec(v_idx_668_);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 1, v___x_688_);
v___x_690_ = v___x_683_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_array_667_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v___x_688_);
v___x_690_ = v_reuseFailAlloc_696_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_691_ = l_ByteSlice_toByteArray(v___x_687_);
v___x_692_ = lean_string_validate_utf8(v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; 
lean_dec_ref(v___x_691_);
v___x_693_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_694_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_693_);
v___y_625_ = v___x_690_;
v___y_626_ = v___x_694_;
goto v___jp_624_;
}
else
{
lean_object* v___x_695_; 
v___x_695_ = lean_string_from_utf8_unchecked(v___x_691_);
v___y_625_ = v___x_690_;
v___y_626_ = v___x_695_;
goto v___jp_624_;
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
v___jp_624_:
{
lean_object* v___x_627_; 
v___x_627_ = lean_uv_pton_v6(v___y_626_);
if (lean_obj_tag(v___x_627_) == 1)
{
lean_object* v_val_628_; lean_object* v___x_629_; 
lean_dec_ref(v___y_626_);
v_val_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_val_628_);
lean_dec_ref_known(v___x_627_, 1);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v___y_625_);
lean_ctor_set(v___x_629_, 1, v_val_628_);
return v___x_629_;
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec(v___x_627_);
v___x_630_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__0));
v___x_631_ = lean_string_append(v___x_630_, v___y_626_);
lean_dec_ref(v___y_626_);
v___x_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
v___x_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_633_, 0, v___y_625_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
return v___x_633_;
}
}
}
}
uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0(uint8_t v_x_723_){
_start:
{
uint8_t v___x_724_; uint8_t v___x_725_; 
v___x_724_ = 46;
v___x_725_ = lean_uint8_dec_eq(v_x_723_, v___x_724_);
if (v___x_725_ == 0)
{
uint8_t v___x_726_; uint8_t v___x_727_; 
v___x_726_ = 48;
v___x_727_ = lean_uint8_dec_le(v___x_726_, v_x_723_);
if (v___x_727_ == 0)
{
return v___x_727_;
}
else
{
uint8_t v___x_728_; uint8_t v___x_729_; 
v___x_728_ = 57;
v___x_729_ = lean_uint8_dec_le(v_x_723_, v___x_728_);
return v___x_729_;
}
}
else
{
return v___x_725_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_723_ = stack[0].m_num;
uint8_t v_res_730_;
v_res_730_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0(v_x_723_);
stack->m_num = v_res_730_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0___boxed(lean_object* v_x_731_){
_start:
{
uint8_t v_x_boxed_732_; uint8_t v_res_733_; lean_object* v_r_734_; 
v_x_boxed_732_ = lean_unbox(v_x_731_);
v_res_733_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0(v_x_boxed_732_);
v_r_734_ = lean_box(v_res_733_);
return v_r_734_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(lean_object* v_a_737_){
_start:
{
lean_object* v___f_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v_snd_742_; lean_object* v_fst_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_788_; 
v___f_738_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__0));
v___x_739_ = lean_unsigned_to_nat(256u);
v___x_740_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_737_);
v___x_741_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_738_, v___x_739_, v___x_740_, v_a_737_);
v_snd_742_ = lean_ctor_get(v___x_741_, 1);
v_fst_743_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_788_ == 0)
{
v___x_745_ = v___x_741_;
v_isShared_746_ = v_isSharedCheck_788_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_snd_742_);
lean_inc(v_fst_743_);
lean_dec(v___x_741_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_788_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v_fst_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_786_; 
v_fst_747_ = lean_ctor_get(v_snd_742_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v_snd_742_);
if (v_isSharedCheck_786_ == 0)
{
lean_object* v_unused_787_; 
v_unused_787_ = lean_ctor_get(v_snd_742_, 1);
lean_dec(v_unused_787_);
v___x_749_ = v_snd_742_;
v_isShared_750_ = v_isSharedCheck_786_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_fst_747_);
lean_dec(v_snd_742_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_786_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___y_752_; uint8_t v___x_764_; 
v___x_764_ = lean_nat_dec_eq(v_fst_743_, v___x_740_);
if (v___x_764_ == 0)
{
lean_object* v_array_765_; lean_object* v_idx_766_; lean_object* v_lower_768_; lean_object* v_upper_769_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___y_779_; uint8_t v___x_781_; 
lean_del_object(v___x_745_);
v_array_765_ = lean_ctor_get(v_a_737_, 0);
lean_inc_ref(v_array_765_);
v_idx_766_ = lean_ctor_get(v_a_737_, 1);
lean_inc(v_idx_766_);
lean_dec_ref(v_a_737_);
v___x_776_ = lean_nat_add(v_idx_766_, v_fst_743_);
lean_dec(v_fst_743_);
v___x_777_ = lean_byte_array_size(v_array_765_);
v___x_781_ = lean_nat_dec_le(v_idx_766_, v___x_740_);
if (v___x_781_ == 0)
{
v___y_779_ = v_idx_766_;
goto v___jp_778_;
}
else
{
lean_dec(v_idx_766_);
v___y_779_ = v___x_740_;
goto v___jp_778_;
}
v___jp_767_:
{
lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v___x_772_; 
v___x_770_ = l_ByteArray_toByteSlice(v_array_765_, v_lower_768_, v_upper_769_);
v___x_771_ = l_ByteSlice_toByteArray(v___x_770_);
v___x_772_ = lean_string_validate_utf8(v___x_771_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; 
lean_dec_ref(v___x_771_);
v___x_773_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_774_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_773_);
v___y_752_ = v___x_774_;
goto v___jp_751_;
}
else
{
lean_object* v___x_775_; 
v___x_775_ = lean_string_from_utf8_unchecked(v___x_771_);
v___y_752_ = v___x_775_;
goto v___jp_751_;
}
}
v___jp_778_:
{
uint8_t v___x_780_; 
v___x_780_ = lean_nat_dec_le(v___x_776_, v___x_777_);
if (v___x_780_ == 0)
{
lean_dec(v___x_776_);
v_lower_768_ = v___y_779_;
v_upper_769_ = v___x_777_;
goto v___jp_767_;
}
else
{
v_lower_768_ = v___y_779_;
v_upper_769_ = v___x_776_;
goto v___jp_767_;
}
}
}
else
{
lean_object* v___x_782_; lean_object* v___x_784_; 
lean_del_object(v___x_749_);
lean_dec(v_fst_747_);
lean_dec(v_fst_743_);
v___x_782_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7));
if (v_isShared_746_ == 0)
{
lean_ctor_set_tag(v___x_745_, 1);
lean_ctor_set(v___x_745_, 1, v___x_782_);
lean_ctor_set(v___x_745_, 0, v_a_737_);
v___x_784_ = v___x_745_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_737_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
v___jp_751_:
{
lean_object* v___x_753_; 
v___x_753_ = lean_uv_pton_v4(v___y_752_);
if (lean_obj_tag(v___x_753_) == 1)
{
lean_object* v_val_754_; lean_object* v___x_756_; 
lean_dec_ref(v___y_752_);
v_val_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_val_754_);
lean_dec_ref_known(v___x_753_, 1);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v_val_754_);
v___x_756_ = v___x_749_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_fst_747_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_val_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_762_; 
lean_dec(v___x_753_);
v___x_758_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__1));
v___x_759_ = lean_string_append(v___x_758_, v___y_752_);
lean_dec_ref(v___y_752_);
v___x_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
if (v_isShared_750_ == 0)
{
lean_ctor_set_tag(v___x_749_, 1);
lean_ctor_set(v___x_749_, 1, v___x_760_);
v___x_762_ = v___x_749_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_fst_747_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
}
}
}
lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg(){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0));
return v___x_792_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_793_;
v_res_793_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg();
stack->m_obj
 = v_res_793_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___boxed(lean_object* v___dummy_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg();
return v_res_795_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0(void){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg();
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(lean_object* v_s_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___boxed(lean_object* v_s_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(v_s_799_);
lean_dec_ref(v_s_799_);
return v_res_800_;
}
}
uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(uint8_t v___x_801_, uint8_t v_x_802_){
_start:
{
uint8_t v___x_818_; uint8_t v___x_819_; 
v___x_818_ = 48;
v___x_819_ = lean_uint8_dec_le(v___x_818_, v_x_802_);
if (v___x_819_ == 0)
{
goto v___jp_813_;
}
else
{
uint8_t v___x_820_; uint8_t v___x_821_; 
v___x_820_ = 57;
v___x_821_ = lean_uint8_dec_le(v_x_802_, v___x_820_);
if (v___x_821_ == 0)
{
goto v___jp_813_;
}
else
{
return v___x_801_;
}
}
v___jp_803_:
{
uint8_t v___x_804_; uint8_t v___x_805_; 
v___x_804_ = 45;
v___x_805_ = lean_uint8_dec_eq(v_x_802_, v___x_804_);
if (v___x_805_ == 0)
{
uint8_t v___x_806_; uint8_t v___x_807_; 
v___x_806_ = 46;
v___x_807_ = lean_uint8_dec_eq(v_x_802_, v___x_806_);
return v___x_807_;
}
else
{
return v___x_801_;
}
}
v___jp_808_:
{
uint8_t v___x_809_; uint8_t v___x_810_; 
v___x_809_ = 65;
v___x_810_ = lean_uint8_dec_le(v___x_809_, v_x_802_);
if (v___x_810_ == 0)
{
goto v___jp_803_;
}
else
{
uint8_t v___x_811_; uint8_t v___x_812_; 
v___x_811_ = 90;
v___x_812_ = lean_uint8_dec_le(v_x_802_, v___x_811_);
if (v___x_812_ == 0)
{
goto v___jp_803_;
}
else
{
return v___x_801_;
}
}
}
v___jp_813_:
{
uint8_t v___x_814_; uint8_t v___x_815_; 
v___x_814_ = 97;
v___x_815_ = lean_uint8_dec_le(v___x_814_, v_x_802_);
if (v___x_815_ == 0)
{
goto v___jp_808_;
}
else
{
uint8_t v___x_816_; uint8_t v___x_817_; 
v___x_816_ = 122;
v___x_817_ = lean_uint8_dec_le(v_x_802_, v___x_816_);
if (v___x_817_ == 0)
{
goto v___jp_808_;
}
else
{
return v___x_801_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_801_ = stack[0].m_num;
uint8_t v_x_802_ = stack[1].m_num;
uint8_t v_res_822_;
v_res_822_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(v___x_801_, v_x_802_);
stack->m_num = v_res_822_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed(lean_object* v___x_823_, lean_object* v_x_824_){
_start:
{
uint8_t v___x_12911__boxed_825_; uint8_t v_x_boxed_826_; uint8_t v_res_827_; lean_object* v_r_828_; 
v___x_12911__boxed_825_ = lean_unbox(v___x_823_);
v_x_boxed_826_ = lean_unbox(v_x_824_);
v_res_827_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(v___x_12911__boxed_825_, v_x_boxed_826_);
v_r_828_ = lean_box(v_res_827_);
return v_r_828_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(lean_object* v___x_829_, lean_object* v___x_830_, lean_object* v_a_831_, uint8_t v_b_832_){
_start:
{
if (lean_obj_tag(v_a_831_) == 0)
{
lean_object* v_currPos_833_; lean_object* v_searcher_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_848_; 
v_currPos_833_ = lean_ctor_get(v_a_831_, 0);
v_searcher_834_ = lean_ctor_get(v_a_831_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v_a_831_);
if (v_isSharedCheck_848_ == 0)
{
v___x_836_ = v_a_831_;
v_isShared_837_ = v_isSharedCheck_848_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_searcher_834_);
lean_inc(v_currPos_833_);
lean_dec(v_a_831_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_848_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
uint8_t v___x_838_; uint8_t v_decide_839_; 
v___x_838_ = 0;
v_decide_839_ = lean_nat_dec_eq(v_searcher_834_, v___x_830_);
if (v_decide_839_ == 0)
{
uint32_t v___x_840_; uint32_t v___x_841_; uint8_t v___x_842_; 
v___x_840_ = 46;
v___x_841_ = lean_string_utf8_get_fast(v___x_829_, v_searcher_834_);
v___x_842_ = lean_uint32_dec_eq(v___x_841_, v___x_840_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_843_ = lean_string_utf8_next_fast(v___x_829_, v_searcher_834_);
lean_dec(v_searcher_834_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v___x_843_);
v___x_845_ = v___x_836_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_currPos_833_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v___x_843_);
v___x_845_ = v_reuseFailAlloc_847_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
v_a_831_ = v___x_845_;
goto _start;
}
}
else
{
lean_del_object(v___x_836_);
lean_dec(v_searcher_834_);
lean_dec(v_currPos_833_);
return v___x_838_;
}
}
else
{
lean_del_object(v___x_836_);
lean_dec(v_searcher_834_);
lean_dec(v_currPos_833_);
return v___x_838_;
}
}
}
else
{
return v_b_832_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_829_ = stack[0].m_obj;
lean_object* v___x_830_ = stack[1].m_obj;
lean_object* v_a_831_ = stack[2].m_obj;
uint8_t v_b_832_ = stack[3].m_num;
uint8_t v_res_849_;
v_res_849_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_829_, v___x_830_, v_a_831_, v_b_832_);
stack->m_num = v_res_849_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg___boxed(lean_object* v___x_850_, lean_object* v___x_851_, lean_object* v_a_852_, lean_object* v_b_853_){
_start:
{
uint8_t v_b_boxed_854_; uint8_t v_res_855_; lean_object* v_r_856_; 
v_b_boxed_854_ = lean_unbox(v_b_853_);
v_res_855_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_850_, v___x_851_, v_a_852_, v_b_boxed_854_);
lean_dec(v___x_851_);
lean_dec_ref(v___x_850_);
v_r_856_ = lean_box(v_res_855_);
return v_r_856_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(uint8_t v___x_857_, lean_object* v___x_858_, lean_object* v___x_859_, lean_object* v___x_860_, lean_object* v_a_861_, uint8_t v_b_862_){
_start:
{
uint8_t v___y_864_; lean_object* v_it_865_; lean_object* v_startInclusive_866_; lean_object* v_endExclusive_867_; uint8_t v___y_872_; 
if (v___x_857_ == 0)
{
uint8_t v___x_898_; 
v___x_898_ = 1;
v___y_872_ = v___x_898_;
goto v___jp_871_;
}
else
{
uint8_t v___x_899_; 
v___x_899_ = 0;
v___y_872_ = v___x_899_;
goto v___jp_871_;
}
v___jp_863_:
{
lean_object* v___x_868_; uint8_t v___x_869_; 
v___x_868_ = lean_string_utf8_extract_fast(v___x_858_, v_startInclusive_866_, v_endExclusive_867_);
lean_dec(v_endExclusive_867_);
lean_dec(v_startInclusive_866_);
v___x_869_ = l_Std_Http_URI_isValidDomainLabel(v___x_868_);
if (v___x_869_ == 0)
{
lean_dec(v_it_865_);
lean_dec(v___x_860_);
return v___x_869_;
}
else
{
v_a_861_ = v_it_865_;
v_b_862_ = v___y_864_;
goto _start;
}
}
v___jp_871_:
{
if (lean_obj_tag(v_a_861_) == 0)
{
lean_object* v_currPos_873_; lean_object* v_searcher_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_897_; 
v_currPos_873_ = lean_ctor_get(v_a_861_, 0);
v_searcher_874_ = lean_ctor_get(v_a_861_, 1);
v_isSharedCheck_897_ = !lean_is_exclusive(v_a_861_);
if (v_isSharedCheck_897_ == 0)
{
v___x_876_ = v_a_861_;
v_isShared_877_ = v_isSharedCheck_897_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_searcher_874_);
lean_inc(v_currPos_873_);
lean_dec(v_a_861_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_897_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
uint8_t v_decide_878_; 
v_decide_878_ = lean_nat_dec_eq(v_searcher_874_, v___x_860_);
if (v_decide_878_ == 0)
{
uint32_t v___x_879_; uint32_t v___x_880_; uint8_t v___x_881_; 
v___x_879_ = 46;
v___x_880_ = lean_string_utf8_get_fast(v___x_858_, v_searcher_874_);
v___x_881_ = lean_uint32_dec_eq(v___x_880_, v___x_879_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_882_ = lean_string_utf8_next_fast(v___x_858_, v_searcher_874_);
lean_dec(v_searcher_874_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 1, v___x_882_);
v___x_884_ = v___x_876_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_currPos_873_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v___x_882_);
v___x_884_ = v_reuseFailAlloc_886_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
v_a_861_ = v___x_884_;
goto _start;
}
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v_slice_890_; lean_object* v_nextIt_892_; 
v___x_887_ = lean_string_utf8_next_fast(v___x_858_, v_searcher_874_);
v___x_888_ = lean_nat_sub(v___x_887_, v_searcher_874_);
v___x_889_ = lean_nat_add(v_searcher_874_, v___x_888_);
lean_dec(v___x_888_);
v_slice_890_ = l_String_Slice_subslice_x21(v___x_859_, v_currPos_873_, v_searcher_874_);
lean_inc(v___x_889_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 1, v___x_889_);
lean_ctor_set(v___x_876_, 0, v___x_889_);
v_nextIt_892_ = v___x_876_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_889_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v___x_889_);
v_nextIt_892_ = v_reuseFailAlloc_895_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v_startInclusive_893_; lean_object* v_endExclusive_894_; 
v_startInclusive_893_ = lean_ctor_get(v_slice_890_, 0);
lean_inc(v_startInclusive_893_);
v_endExclusive_894_ = lean_ctor_get(v_slice_890_, 1);
lean_inc(v_endExclusive_894_);
lean_dec_ref(v_slice_890_);
v___y_864_ = v___y_872_;
v_it_865_ = v_nextIt_892_;
v_startInclusive_866_ = v_startInclusive_893_;
v_endExclusive_867_ = v_endExclusive_894_;
goto v___jp_863_;
}
}
}
else
{
lean_object* v___x_896_; 
lean_del_object(v___x_876_);
lean_dec(v_searcher_874_);
v___x_896_ = lean_box(1);
lean_inc(v___x_860_);
v___y_864_ = v___y_872_;
v_it_865_ = v___x_896_;
v_startInclusive_866_ = v_currPos_873_;
v_endExclusive_867_ = v___x_860_;
goto v___jp_863_;
}
}
}
else
{
lean_dec(v___x_860_);
return v_b_862_;
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_857_ = stack[0].m_num;
lean_object* v___x_858_ = stack[1].m_obj;
lean_object* v___x_859_ = stack[2].m_obj;
lean_object* v___x_860_ = stack[3].m_obj;
lean_object* v_a_861_ = stack[4].m_obj;
uint8_t v_b_862_ = stack[5].m_num;
uint8_t v_res_900_;
v_res_900_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_857_, v___x_858_, v___x_859_, v___x_860_, v_a_861_, v_b_862_);
stack->m_num = v_res_900_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg___boxed(lean_object* v___x_901_, lean_object* v___x_902_, lean_object* v___x_903_, lean_object* v___x_904_, lean_object* v_a_905_, lean_object* v_b_906_){
_start:
{
uint8_t v___x_13031__boxed_907_; uint8_t v_b_boxed_908_; uint8_t v_res_909_; lean_object* v_r_910_; 
v___x_13031__boxed_907_ = lean_unbox(v___x_901_);
v_b_boxed_908_ = lean_unbox(v_b_906_);
v_res_909_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_13031__boxed_907_, v___x_902_, v___x_903_, v___x_904_, v_a_905_, v_b_boxed_908_);
lean_dec_ref(v___x_903_);
lean_dec_ref(v___x_902_);
v_r_910_ = lean_box(v_res_909_);
return v_r_910_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(lean_object* v_config_918_, lean_object* v_a_919_){
_start:
{
lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; uint8_t v___y_931_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; uint8_t v___y_939_; uint8_t v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; uint8_t v___y_944_; lean_object* v___y_951_; uint8_t v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v_lower_955_; lean_object* v_upper_956_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; uint8_t v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_1002_; lean_object* v_pos_1003_; lean_object* v___y_1027_; lean_object* v_pos_1028_; lean_object* v_res_1029_; lean_object* v_array_1030_; lean_object* v_idx_1031_; lean_object* v_pos_1033_; lean_object* v_res_1034_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v_array_1030_ = lean_ctor_get(v_a_919_, 0);
v_idx_1031_ = lean_ctor_get(v_a_919_, 1);
v___x_1043_ = lean_byte_array_size(v_array_1030_);
v___x_1044_ = lean_nat_dec_lt(v_idx_1031_, v___x_1043_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; 
lean_inc(v_idx_1031_);
lean_inc_ref(v_array_1030_);
v___x_1045_ = lean_box(0);
v_pos_1033_ = v_a_919_;
v_res_1034_ = v___x_1045_;
goto v___jp_1032_;
}
else
{
uint8_t v___x_1046_; uint8_t v___x_1047_; uint8_t v___x_1048_; 
v___x_1046_ = lean_byte_array_fget(v_array_1030_, v_idx_1031_);
v___x_1047_ = 91;
v___x_1048_ = lean_uint8_dec_eq(v___x_1046_, v___x_1047_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; 
lean_inc(v_idx_1031_);
lean_inc_ref(v_array_1030_);
v___x_1049_ = lean_box(0);
v_pos_1033_ = v_a_919_;
v_res_1034_ = v___x_1049_;
goto v___jp_1032_;
}
else
{
lean_object* v___x_1050_; 
v___x_1050_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(v_a_919_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_pos_1051_; lean_object* v_res_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1060_; 
v_pos_1051_ = lean_ctor_get(v___x_1050_, 0);
v_res_1052_ = lean_ctor_get(v___x_1050_, 1);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1054_ = v___x_1050_;
v_isShared_1055_ = v_isSharedCheck_1060_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_res_1052_);
lean_inc(v_pos_1051_);
lean_dec(v___x_1050_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1060_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1058_; 
v___x_1056_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1056_, 0, v_res_1052_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 1, v___x_1056_);
v___x_1058_ = v___x_1054_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_pos_1051_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v___x_1056_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
else
{
lean_object* v_pos_1061_; lean_object* v_err_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
v_pos_1061_ = lean_ctor_get(v___x_1050_, 0);
v_err_1062_ = lean_ctor_get(v___x_1050_, 1);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1050_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_err_1062_);
lean_inc(v_pos_1061_);
lean_dec(v___x_1050_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_pos_1061_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v_err_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
v___jp_920_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_923_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0));
v___x_924_ = lean_string_append(v___x_923_, v___y_921_);
lean_dec_ref(v___y_921_);
v___x_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
v___x_926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_926_, 0, v___y_922_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
return v___x_926_;
}
v___jp_927_:
{
if (v___y_931_ == 0)
{
lean_dec_ref(v___y_928_);
v___y_921_ = v___y_929_;
v___y_922_ = v___y_930_;
goto v___jp_920_;
}
else
{
lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec_ref(v___y_929_);
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v___y_928_);
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v___y_930_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
return v___x_933_;
}
}
v___jp_934_:
{
if (v___y_944_ == 0)
{
lean_dec(v___y_942_);
lean_dec(v___y_941_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec_ref(v___y_935_);
v___y_921_ = v___y_938_;
v___y_922_ = v___y_943_;
goto v___jp_920_;
}
else
{
uint8_t v___x_945_; 
lean_inc(v___y_937_);
v___x_945_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___y_939_, v___y_936_, v___y_935_, v___y_937_, v___y_942_, v___y_944_);
lean_dec_ref(v___y_935_);
if (v___x_945_ == 0)
{
lean_dec(v___y_941_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
v___y_921_ = v___y_938_;
v___y_922_ = v___y_943_;
goto v___jp_920_;
}
else
{
lean_object* v___x_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
v___x_946_ = lean_string_length(v___y_936_);
v___x_947_ = lean_unsigned_to_nat(255u);
v___x_948_ = lean_nat_dec_le(v___x_946_, v___x_947_);
if (v___x_948_ == 0)
{
lean_dec(v___y_941_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
v___y_921_ = v___y_938_;
v___y_922_ = v___y_943_;
goto v___jp_920_;
}
else
{
uint8_t v___x_949_; 
v___x_949_ = lean_nat_dec_eq(v___y_937_, v___y_941_);
lean_dec(v___y_941_);
lean_dec(v___y_937_);
if (v___x_949_ == 0)
{
v___y_928_ = v___y_936_;
v___y_929_ = v___y_938_;
v___y_930_ = v___y_943_;
v___y_931_ = v___x_948_;
goto v___jp_927_;
}
else
{
v___y_928_ = v___y_936_;
v___y_929_ = v___y_938_;
v___y_930_ = v___y_943_;
v___y_931_ = v___y_940_;
goto v___jp_927_;
}
}
}
}
}
v___jp_950_:
{
lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v___x_957_ = l_ByteArray_toByteSlice(v___y_951_, v_lower_955_, v_upper_956_);
v___x_958_ = l_ByteSlice_toByteArray(v___x_957_);
v___x_959_ = lean_string_validate_utf8(v___x_958_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; lean_object* v___x_961_; 
lean_dec_ref(v___x_958_);
lean_dec(v___y_953_);
v___x_960_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2));
v___x_961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_961_, 0, v___y_954_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
return v___x_961_;
}
else
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_962_ = lean_string_from_utf8_unchecked(v___x_958_);
lean_inc_n(v___y_953_, 2);
lean_inc_ref(v___x_962_);
v___x_963_ = l_String_mapAux___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(v___x_962_, v___y_953_);
v___x_964_ = lean_string_utf8_byte_size(v___x_963_);
lean_inc_ref(v___x_963_);
v___x_965_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___y_953_);
lean_ctor_set(v___x_965_, 2, v___x_964_);
v___x_966_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0);
v___x_967_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_963_, v___x_964_, v___x_966_, v___x_959_);
if (v___x_967_ == 0)
{
v___y_935_ = v___x_965_;
v___y_936_ = v___x_963_;
v___y_937_ = v___x_964_;
v___y_938_ = v___x_962_;
v___y_939_ = v___x_967_;
v___y_940_ = v___y_952_;
v___y_941_ = v___y_953_;
v___y_942_ = v___x_966_;
v___y_943_ = v___y_954_;
v___y_944_ = v___x_959_;
goto v___jp_934_;
}
else
{
v___y_935_ = v___x_965_;
v___y_936_ = v___x_963_;
v___y_937_ = v___x_964_;
v___y_938_ = v___x_962_;
v___y_939_ = v___x_967_;
v___y_940_ = v___y_952_;
v___y_941_ = v___y_953_;
v___y_942_ = v___x_966_;
v___y_943_ = v___y_954_;
v___y_944_ = v___y_952_;
goto v___jp_934_;
}
}
}
v___jp_968_:
{
uint8_t v___x_976_; 
v___x_976_ = lean_nat_dec_le(v___y_970_, v___y_969_);
if (v___x_976_ == 0)
{
lean_dec(v___y_970_);
v___y_951_ = v___y_971_;
v___y_952_ = v___y_972_;
v___y_953_ = v___y_973_;
v___y_954_ = v___y_974_;
v_lower_955_ = v___y_975_;
v_upper_956_ = v___y_969_;
goto v___jp_950_;
}
else
{
lean_dec(v___y_969_);
v___y_951_ = v___y_971_;
v___y_952_ = v___y_972_;
v___y_953_ = v___y_973_;
v___y_954_ = v___y_974_;
v_lower_955_ = v___y_975_;
v_upper_956_ = v___y_970_;
goto v___jp_950_;
}
}
v___jp_977_:
{
lean_object* v_maxHostLength_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v_snd_983_; lean_object* v_fst_984_; lean_object* v_fst_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_999_; 
v_maxHostLength_980_ = lean_ctor_get(v_config_918_, 1);
v___x_981_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___y_979_);
lean_inc_ref(v___y_978_);
v___x_982_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___y_978_, v_maxHostLength_980_, v___x_981_, v___y_979_);
v_snd_983_ = lean_ctor_get(v___x_982_, 1);
lean_inc(v_snd_983_);
v_fst_984_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_fst_984_);
lean_dec_ref(v___x_982_);
v_fst_985_ = lean_ctor_get(v_snd_983_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v_snd_983_);
if (v_isSharedCheck_999_ == 0)
{
lean_object* v_unused_1000_; 
v_unused_1000_ = lean_ctor_get(v_snd_983_, 1);
lean_dec(v_unused_1000_);
v___x_987_ = v_snd_983_;
v_isShared_988_ = v_isSharedCheck_999_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_fst_985_);
lean_dec(v_snd_983_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_999_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
uint8_t v___x_989_; 
v___x_989_ = lean_nat_dec_eq(v_fst_984_, v___x_981_);
if (v___x_989_ == 0)
{
lean_object* v_array_990_; lean_object* v_idx_991_; lean_object* v___x_992_; lean_object* v___x_993_; uint8_t v___x_994_; 
lean_del_object(v___x_987_);
v_array_990_ = lean_ctor_get(v___y_979_, 0);
lean_inc_ref(v_array_990_);
v_idx_991_ = lean_ctor_get(v___y_979_, 1);
lean_inc(v_idx_991_);
lean_dec_ref(v___y_979_);
v___x_992_ = lean_nat_add(v_idx_991_, v_fst_984_);
lean_dec(v_fst_984_);
v___x_993_ = lean_byte_array_size(v_array_990_);
v___x_994_ = lean_nat_dec_le(v_idx_991_, v___x_981_);
if (v___x_994_ == 0)
{
v___y_969_ = v___x_993_;
v___y_970_ = v___x_992_;
v___y_971_ = v_array_990_;
v___y_972_ = v___x_989_;
v___y_973_ = v___x_981_;
v___y_974_ = v_fst_985_;
v___y_975_ = v_idx_991_;
goto v___jp_968_;
}
else
{
lean_dec(v_idx_991_);
v___y_969_ = v___x_993_;
v___y_970_ = v___x_992_;
v___y_971_ = v_array_990_;
v___y_972_ = v___x_989_;
v___y_973_ = v___x_981_;
v___y_974_ = v_fst_985_;
v___y_975_ = v___x_981_;
goto v___jp_968_;
}
}
else
{
lean_object* v___x_995_; lean_object* v___x_997_; 
lean_dec(v_fst_985_);
lean_dec(v_fst_984_);
v___x_995_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7));
if (v_isShared_988_ == 0)
{
lean_ctor_set_tag(v___x_987_, 1);
lean_ctor_set(v___x_987_, 1, v___x_995_);
lean_ctor_set(v___x_987_, 0, v___y_979_);
v___x_997_ = v___x_987_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___y_979_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v___x_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
v___jp_1001_:
{
lean_object* v___x_1004_; 
lean_inc_ref(v_pos_1003_);
v___x_1004_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(v_pos_1003_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_pos_1005_; lean_object* v_res_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1014_; 
lean_dec_ref(v_pos_1003_);
v_pos_1005_ = lean_ctor_get(v___x_1004_, 0);
v_res_1006_ = lean_ctor_get(v___x_1004_, 1);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1008_ = v___x_1004_;
v_isShared_1009_ = v_isSharedCheck_1014_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_res_1006_);
lean_inc(v_pos_1005_);
lean_dec(v___x_1004_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1014_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1010_, 0, v_res_1006_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 1, v___x_1010_);
v___x_1012_ = v___x_1008_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_pos_1005_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
else
{
lean_object* v_err_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1024_; 
v_err_1015_ = lean_ctor_get(v___x_1004_, 1);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1024_ == 0)
{
lean_object* v_unused_1025_; 
v_unused_1025_ = lean_ctor_get(v___x_1004_, 0);
lean_dec(v_unused_1025_);
v___x_1017_ = v___x_1004_;
v_isShared_1018_ = v_isSharedCheck_1024_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_err_1015_);
lean_dec(v___x_1004_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1024_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v_idx_1019_; uint8_t v___x_1020_; 
v_idx_1019_ = lean_ctor_get(v_pos_1003_, 1);
v___x_1020_ = lean_nat_dec_eq(v_idx_1019_, v_idx_1019_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1022_; 
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 0, v_pos_1003_);
v___x_1022_ = v___x_1017_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_pos_1003_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_err_1015_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
else
{
lean_del_object(v___x_1017_);
lean_dec(v_err_1015_);
v___y_978_ = v___y_1002_;
v___y_979_ = v_pos_1003_;
goto v___jp_977_;
}
}
}
}
v___jp_1026_:
{
v___y_978_ = v___y_1027_;
v___y_979_ = v_pos_1028_;
goto v___jp_977_;
}
v___jp_1032_:
{
lean_object* v___f_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; 
v___f_1035_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3));
v___x_1036_ = lean_byte_array_size(v_array_1030_);
v___x_1037_ = lean_nat_dec_lt(v_idx_1031_, v___x_1036_);
if (v___x_1037_ == 0)
{
lean_dec(v_idx_1031_);
lean_dec_ref(v_array_1030_);
v___y_1027_ = v___f_1035_;
v_pos_1028_ = v_pos_1033_;
v_res_1029_ = v_res_1034_;
goto v___jp_1026_;
}
else
{
uint8_t v___x_1038_; uint8_t v___x_1039_; uint8_t v___x_1040_; 
v___x_1038_ = lean_byte_array_fget(v_array_1030_, v_idx_1031_);
lean_dec(v_idx_1031_);
lean_dec_ref(v_array_1030_);
v___x_1039_ = 48;
v___x_1040_ = lean_uint8_dec_le(v___x_1039_, v___x_1038_);
if (v___x_1040_ == 0)
{
v___y_1027_ = v___f_1035_;
v_pos_1028_ = v_pos_1033_;
v_res_1029_ = v_res_1034_;
goto v___jp_1026_;
}
else
{
uint8_t v___x_1041_; uint8_t v___x_1042_; 
v___x_1041_ = 57;
v___x_1042_ = lean_uint8_dec_le(v___x_1038_, v___x_1041_);
if (v___x_1042_ == 0)
{
v___y_1027_ = v___f_1035_;
v_pos_1028_ = v_pos_1033_;
v_res_1029_ = v_res_1034_;
goto v___jp_1026_;
}
else
{
v___y_1002_ = v___f_1035_;
v_pos_1003_ = v_pos_1033_;
goto v___jp_1001_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___boxed(lean_object* v_config_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_1070_, v_a_1071_);
lean_dec_ref(v_config_1070_);
return v_res_1072_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(lean_object* v___x_1073_, lean_object* v___x_1074_, lean_object* v___x_1075_, lean_object* v_inst_1076_, lean_object* v_R_1077_, lean_object* v_a_1078_, uint8_t v_b_1079_, lean_object* v_c_1080_){
_start:
{
uint8_t v___x_1081_; 
v___x_1081_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_1073_, v___x_1075_, v_a_1078_, v_b_1079_);
return v___x_1081_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1073_ = stack[0].m_obj;
lean_object* v___x_1074_ = stack[1].m_obj;
lean_object* v___x_1075_ = stack[2].m_obj;
lean_object* v_a_1078_ = stack[5].m_obj;
uint8_t v_b_1079_ = stack[6].m_num;
uint8_t v_res_1082_;
v_res_1082_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(v___x_1073_, v___x_1074_, v___x_1075_, lean_box(0), lean_box(0), v_a_1078_, v_b_1079_, lean_box(0));
stack->m_num = v_res_1082_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___boxed(lean_object* v___x_1083_, lean_object* v___x_1084_, lean_object* v___x_1085_, lean_object* v_inst_1086_, lean_object* v_R_1087_, lean_object* v_a_1088_, lean_object* v_b_1089_, lean_object* v_c_1090_){
_start:
{
uint8_t v_b_boxed_1091_; uint8_t v_res_1092_; lean_object* v_r_1093_; 
v_b_boxed_1091_ = lean_unbox(v_b_1089_);
v_res_1092_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(v___x_1083_, v___x_1084_, v___x_1085_, v_inst_1086_, v_R_1087_, v_a_1088_, v_b_boxed_1091_, v_c_1090_);
lean_dec(v___x_1085_);
lean_dec_ref(v___x_1084_);
lean_dec_ref(v___x_1083_);
v_r_1093_ = lean_box(v_res_1092_);
return v_r_1093_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(uint8_t v___x_1094_, lean_object* v___x_1095_, lean_object* v___x_1096_, lean_object* v___x_1097_, lean_object* v_inst_1098_, lean_object* v_R_1099_, lean_object* v_a_1100_, uint8_t v_b_1101_, lean_object* v_c_1102_){
_start:
{
uint8_t v___x_1103_; 
v___x_1103_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_1094_, v___x_1095_, v___x_1096_, v___x_1097_, v_a_1100_, v_b_1101_);
return v___x_1103_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1094_ = stack[0].m_num;
lean_object* v___x_1095_ = stack[1].m_obj;
lean_object* v___x_1096_ = stack[2].m_obj;
lean_object* v___x_1097_ = stack[3].m_obj;
lean_object* v_a_1100_ = stack[6].m_obj;
uint8_t v_b_1101_ = stack[7].m_num;
uint8_t v_res_1104_;
v_res_1104_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(v___x_1094_, v___x_1095_, v___x_1096_, v___x_1097_, lean_box(0), lean_box(0), v_a_1100_, v_b_1101_, lean_box(0));
stack->m_num = v_res_1104_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___boxed(lean_object* v___x_1105_, lean_object* v___x_1106_, lean_object* v___x_1107_, lean_object* v___x_1108_, lean_object* v_inst_1109_, lean_object* v_R_1110_, lean_object* v_a_1111_, lean_object* v_b_1112_, lean_object* v_c_1113_){
_start:
{
uint8_t v___x_13637__boxed_1114_; uint8_t v_b_boxed_1115_; uint8_t v_res_1116_; lean_object* v_r_1117_; 
v___x_13637__boxed_1114_ = lean_unbox(v___x_1105_);
v_b_boxed_1115_ = lean_unbox(v_b_1112_);
v_res_1116_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(v___x_13637__boxed_1114_, v___x_1106_, v___x_1107_, v___x_1108_, v_inst_1109_, v_R_1110_, v_a_1111_, v_b_boxed_1115_, v_c_1113_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v___x_1106_);
v_r_1117_ = lean_box(v_res_1116_);
return v_r_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(lean_object* v_config_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v_port_1132_; lean_object* v___y_1133_; lean_object* v___y_1137_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1146_; lean_object* v___y_1147_; uint8_t v_val_1148_; lean_object* v___y_1149_; lean_object* v___y_1157_; lean_object* v___y_1158_; uint8_t v___y_1159_; lean_object* v_pos_1160_; lean_object* v_array_1161_; lean_object* v_idx_1162_; lean_object* v_res_1163_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; uint8_t v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v_pos_1178_; lean_object* v_pos_1181_; lean_object* v_res_1182_; lean_object* v_pos_1247_; lean_object* v_res_1248_; lean_object* v_err_1251_; lean_object* v___x_1256_; 
lean_inc_ref(v_a_1128_);
v___x_1256_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(v_config_1127_, v_a_1128_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_pos_1257_; lean_object* v_res_1258_; lean_object* v_array_1259_; lean_object* v_idx_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1276_; 
v_pos_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_pos_1257_);
v_res_1258_ = lean_ctor_get(v___x_1256_, 1);
lean_inc(v_res_1258_);
lean_dec_ref_known(v___x_1256_, 2);
v_array_1259_ = lean_ctor_get(v_pos_1257_, 0);
v_idx_1260_ = lean_ctor_get(v_pos_1257_, 1);
v_isSharedCheck_1276_ = !lean_is_exclusive(v_pos_1257_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1262_ = v_pos_1257_;
v_isShared_1263_ = v_isSharedCheck_1276_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_idx_1260_);
lean_inc(v_array_1259_);
lean_dec(v_pos_1257_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1276_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; uint8_t v___x_1265_; 
v___x_1264_ = lean_byte_array_size(v_array_1259_);
v___x_1265_ = lean_nat_dec_lt(v_idx_1260_, v___x_1264_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; 
lean_del_object(v___x_1262_);
lean_dec(v_idx_1260_);
lean_dec_ref(v_array_1259_);
lean_dec(v_res_1258_);
v___x_1266_ = lean_box(0);
v_err_1251_ = v___x_1266_;
goto v___jp_1250_;
}
else
{
uint8_t v___x_1267_; uint8_t v_got_1268_; uint8_t v___x_1269_; 
v___x_1267_ = 64;
v_got_1268_ = lean_byte_array_fget(v_array_1259_, v_idx_1260_);
v___x_1269_ = lean_uint8_dec_eq(v_got_1268_, v___x_1267_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; 
lean_del_object(v___x_1262_);
lean_dec(v_idx_1260_);
lean_dec_ref(v_array_1259_);
lean_dec(v_res_1258_);
v___x_1270_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5));
v_err_1251_ = v___x_1270_;
goto v___jp_1250_;
}
else
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1274_; 
lean_dec_ref(v_a_1128_);
v___x_1271_ = lean_unsigned_to_nat(1u);
v___x_1272_ = lean_nat_add(v_idx_1260_, v___x_1271_);
lean_dec(v_idx_1260_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 1, v___x_1272_);
v___x_1274_ = v___x_1262_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_array_1259_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v___x_1272_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
v_pos_1247_ = v___x_1274_;
v_res_1248_ = v_res_1258_;
goto v___jp_1246_;
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_pos_1277_; lean_object* v_res_1278_; 
lean_dec_ref(v_a_1128_);
v_pos_1277_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_pos_1277_);
v_res_1278_ = lean_ctor_get(v___x_1256_, 1);
lean_inc(v_res_1278_);
lean_dec_ref_known(v___x_1256_, 2);
v_pos_1247_ = v_pos_1277_;
v_res_1248_ = v_res_1278_;
goto v___jp_1246_;
}
else
{
lean_object* v_err_1279_; 
v_err_1279_ = lean_ctor_get(v___x_1256_, 1);
lean_inc(v_err_1279_);
lean_dec_ref_known(v___x_1256_, 2);
v_err_1251_ = v_err_1279_;
goto v___jp_1250_;
}
}
v___jp_1129_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1134_, 0, v___y_1131_);
lean_ctor_set(v___x_1134_, 1, v___y_1130_);
lean_ctor_set(v___x_1134_, 2, v_port_1132_);
v___x_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___y_1133_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
return v___x_1135_;
}
v___jp_1136_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__1));
v___x_1139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___y_1137_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
return v___x_1139_;
}
v___jp_1140_:
{
lean_object* v___x_1144_; 
v___x_1144_ = lean_box(1);
v___y_1130_ = v___y_1141_;
v___y_1131_ = v___y_1143_;
v_port_1132_ = v___x_1144_;
v___y_1133_ = v___y_1142_;
goto v___jp_1129_;
}
v___jp_1145_:
{
uint8_t v___x_1150_; uint8_t v___x_1151_; 
v___x_1150_ = 47;
v___x_1151_ = lean_uint8_dec_eq(v_val_1148_, v___x_1150_);
if (v___x_1151_ == 0)
{
uint8_t v___x_1152_; uint8_t v___x_1153_; 
v___x_1152_ = 63;
v___x_1153_ = lean_uint8_dec_eq(v_val_1148_, v___x_1152_);
if (v___x_1153_ == 0)
{
uint8_t v___x_1154_; uint8_t v___x_1155_; 
v___x_1154_ = 35;
v___x_1155_ = lean_uint8_dec_eq(v_val_1148_, v___x_1154_);
if (v___x_1155_ == 0)
{
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1146_);
v___y_1137_ = v___y_1147_;
goto v___jp_1136_;
}
else
{
v___y_1141_ = v___y_1146_;
v___y_1142_ = v___y_1147_;
v___y_1143_ = v___y_1149_;
goto v___jp_1140_;
}
}
else
{
v___y_1141_ = v___y_1146_;
v___y_1142_ = v___y_1147_;
v___y_1143_ = v___y_1149_;
goto v___jp_1140_;
}
}
else
{
v___y_1141_ = v___y_1146_;
v___y_1142_ = v___y_1147_;
v___y_1143_ = v___y_1149_;
goto v___jp_1140_;
}
}
v___jp_1156_:
{
lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = lean_byte_array_size(v_array_1161_);
v___x_1165_ = lean_nat_dec_lt(v_idx_1162_, v___x_1164_);
if (v___x_1165_ == 0)
{
lean_dec(v_idx_1162_);
lean_dec_ref(v_array_1161_);
if (v___y_1159_ == 0)
{
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
v___y_1137_ = v_pos_1160_;
goto v___jp_1136_;
}
else
{
v___y_1141_ = v___y_1157_;
v___y_1142_ = v_pos_1160_;
v___y_1143_ = v___y_1158_;
goto v___jp_1140_;
}
}
else
{
uint8_t v___x_1166_; 
v___x_1166_ = lean_byte_array_fget(v_array_1161_, v_idx_1162_);
lean_dec(v_idx_1162_);
lean_dec_ref(v_array_1161_);
v___y_1146_ = v___y_1157_;
v___y_1147_ = v_pos_1160_;
v_val_1148_ = v___x_1166_;
v___y_1149_ = v___y_1158_;
goto v___jp_1145_;
}
}
v___jp_1167_:
{
lean_object* v___x_1174_; 
v___x_1174_ = lean_box(0);
v___y_1157_ = v___y_1169_;
v___y_1158_ = v___y_1170_;
v___y_1159_ = v___y_1172_;
v_pos_1160_ = v___y_1171_;
v_array_1161_ = v___y_1173_;
v_idx_1162_ = v___y_1168_;
v_res_1163_ = v___x_1174_;
goto v___jp_1156_;
}
v___jp_1175_:
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_box(0);
v___y_1130_ = v___y_1176_;
v___y_1131_ = v___y_1177_;
v_port_1132_ = v___x_1179_;
v___y_1133_ = v_pos_1178_;
goto v___jp_1129_;
}
v___jp_1180_:
{
lean_object* v___x_1183_; 
v___x_1183_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_1127_, v_pos_1181_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_pos_1184_; lean_object* v_res_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1236_; 
v_pos_1184_ = lean_ctor_get(v___x_1183_, 0);
v_res_1185_ = lean_ctor_get(v___x_1183_, 1);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1187_ = v___x_1183_;
v_isShared_1188_ = v_isSharedCheck_1236_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_res_1185_);
lean_inc(v_pos_1184_);
lean_dec(v___x_1183_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1236_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v_array_1189_; lean_object* v_idx_1190_; lean_object* v___x_1191_; uint8_t v___x_1192_; 
v_array_1189_ = lean_ctor_get(v_pos_1184_, 0);
v_idx_1190_ = lean_ctor_get(v_pos_1184_, 1);
v___x_1191_ = lean_byte_array_size(v_array_1189_);
v___x_1192_ = lean_nat_dec_lt(v_idx_1190_, v___x_1191_);
if (v___x_1192_ == 0)
{
lean_del_object(v___x_1187_);
v___y_1176_ = v_res_1185_;
v___y_1177_ = v_res_1182_;
v_pos_1178_ = v_pos_1184_;
goto v___jp_1175_;
}
else
{
uint8_t v___x_1193_; uint8_t v___x_1194_; uint8_t v___x_1195_; 
v___x_1193_ = lean_byte_array_fget(v_array_1189_, v_idx_1190_);
v___x_1194_ = 58;
v___x_1195_ = lean_uint8_dec_eq(v___x_1193_, v___x_1194_);
if (v___x_1195_ == 0)
{
lean_del_object(v___x_1187_);
v___y_1176_ = v_res_1185_;
v___y_1177_ = v_res_1182_;
v_pos_1178_ = v_pos_1184_;
goto v___jp_1175_;
}
else
{
if (v___x_1195_ == 0)
{
lean_del_object(v___x_1187_);
v___y_1176_ = v_res_1185_;
v___y_1177_ = v_res_1182_;
v_pos_1178_ = v_pos_1184_;
goto v___jp_1175_;
}
else
{
if (v___x_1192_ == 0)
{
lean_object* v___x_1196_; lean_object* v___x_1198_; 
lean_dec(v_res_1185_);
lean_dec(v_res_1182_);
v___x_1196_ = lean_box(0);
if (v_isShared_1188_ == 0)
{
lean_ctor_set_tag(v___x_1187_, 1);
lean_ctor_set(v___x_1187_, 1, v___x_1196_);
v___x_1198_ = v___x_1187_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_pos_1184_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
else
{
if (v___x_1195_ == 0)
{
lean_object* v___x_1200_; lean_object* v___x_1202_; 
lean_dec(v_res_1185_);
lean_dec(v_res_1182_);
v___x_1200_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_1188_ == 0)
{
lean_ctor_set_tag(v___x_1187_, 1);
lean_ctor_set(v___x_1187_, 1, v___x_1200_);
v___x_1202_ = v___x_1187_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_pos_1184_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
else
{
lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1233_; 
lean_inc(v_idx_1190_);
lean_inc_ref(v_array_1189_);
lean_del_object(v___x_1187_);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_pos_1184_);
if (v_isSharedCheck_1233_ == 0)
{
lean_object* v_unused_1234_; lean_object* v_unused_1235_; 
v_unused_1234_ = lean_ctor_get(v_pos_1184_, 1);
lean_dec(v_unused_1234_);
v_unused_1235_ = lean_ctor_get(v_pos_1184_, 0);
lean_dec(v_unused_1235_);
v___x_1205_ = v_pos_1184_;
v_isShared_1206_ = v_isSharedCheck_1233_;
goto v_resetjp_1204_;
}
else
{
lean_dec(v_pos_1184_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1233_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1210_; 
v___x_1207_ = lean_unsigned_to_nat(1u);
v___x_1208_ = lean_nat_add(v_idx_1190_, v___x_1207_);
lean_dec(v_idx_1190_);
lean_inc(v___x_1208_);
lean_inc_ref(v_array_1189_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 1, v___x_1208_);
v___x_1210_ = v___x_1205_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_array_1189_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
uint8_t v___x_1211_; 
v___x_1211_ = lean_nat_dec_lt(v___x_1208_, v___x_1191_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; 
v___x_1212_ = lean_box(0);
v___y_1157_ = v_res_1185_;
v___y_1158_ = v_res_1182_;
v___y_1159_ = v___x_1195_;
v_pos_1160_ = v___x_1210_;
v_array_1161_ = v_array_1189_;
v_idx_1162_ = v___x_1208_;
v_res_1163_ = v___x_1212_;
goto v___jp_1156_;
}
else
{
uint8_t v___x_1213_; uint8_t v___x_1214_; uint8_t v___x_1215_; 
v___x_1213_ = lean_byte_array_fget(v_array_1189_, v___x_1208_);
v___x_1214_ = 48;
v___x_1215_ = lean_uint8_dec_le(v___x_1214_, v___x_1213_);
if (v___x_1215_ == 0)
{
v___y_1168_ = v___x_1208_;
v___y_1169_ = v_res_1185_;
v___y_1170_ = v_res_1182_;
v___y_1171_ = v___x_1210_;
v___y_1172_ = v___x_1195_;
v___y_1173_ = v_array_1189_;
goto v___jp_1167_;
}
else
{
uint8_t v___x_1216_; uint8_t v___x_1217_; 
v___x_1216_ = 57;
v___x_1217_ = lean_uint8_dec_le(v___x_1213_, v___x_1216_);
if (v___x_1217_ == 0)
{
v___y_1168_ = v___x_1208_;
v___y_1169_ = v_res_1185_;
v___y_1170_ = v_res_1182_;
v___y_1171_ = v___x_1210_;
v___y_1172_ = v___x_1195_;
v___y_1173_ = v_array_1189_;
goto v___jp_1167_;
}
else
{
lean_object* v___x_1218_; 
lean_dec(v___x_1208_);
lean_dec_ref(v_array_1189_);
v___x_1218_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_1210_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_pos_1219_; lean_object* v_res_1220_; lean_object* v___x_1221_; uint16_t v___x_1222_; 
v_pos_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_pos_1219_);
v_res_1220_ = lean_ctor_get(v___x_1218_, 1);
lean_inc(v_res_1220_);
lean_dec_ref_known(v___x_1218_, 2);
v___x_1221_ = lean_alloc_ctor(2, 0, 2);
v___x_1222_ = lean_unbox(v_res_1220_);
lean_dec(v_res_1220_);
lean_ctor_set_uint16(v___x_1221_, 0, v___x_1222_);
v___y_1130_ = v_res_1185_;
v___y_1131_ = v_res_1182_;
v_port_1132_ = v___x_1221_;
v___y_1133_ = v_pos_1219_;
goto v___jp_1129_;
}
else
{
lean_object* v_pos_1223_; lean_object* v_err_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_dec(v_res_1185_);
lean_dec(v_res_1182_);
v_pos_1223_ = lean_ctor_get(v___x_1218_, 0);
v_err_1224_ = lean_ctor_get(v___x_1218_, 1);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1218_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_err_1224_);
lean_inc(v_pos_1223_);
lean_dec(v___x_1218_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_pos_1223_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_err_1224_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
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
lean_object* v_pos_1237_; lean_object* v_err_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
lean_dec(v_res_1182_);
v_pos_1237_ = lean_ctor_get(v___x_1183_, 0);
v_err_1238_ = lean_ctor_get(v___x_1183_, 1);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v___x_1183_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_err_1238_);
lean_inc(v_pos_1237_);
lean_dec(v___x_1183_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_pos_1237_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_err_1238_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
v___jp_1246_:
{
lean_object* v___x_1249_; 
v___x_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1249_, 0, v_res_1248_);
v_pos_1181_ = v_pos_1247_;
v_res_1182_ = v___x_1249_;
goto v___jp_1180_;
}
v___jp_1250_:
{
lean_object* v_idx_1252_; uint8_t v___x_1253_; 
v_idx_1252_ = lean_ctor_get(v_a_1128_, 1);
v___x_1253_ = lean_nat_dec_eq(v_idx_1252_, v_idx_1252_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; 
v___x_1254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1254_, 0, v_a_1128_);
lean_ctor_set(v___x_1254_, 1, v_err_1251_);
return v___x_1254_;
}
else
{
lean_object* v___x_1255_; 
lean_dec(v_err_1251_);
v___x_1255_ = lean_box(0);
v_pos_1181_ = v_a_1128_;
v_res_1182_ = v___x_1255_;
goto v___jp_1180_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___boxed(lean_object* v_config_1280_, lean_object* v_a_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_1280_, v_a_1281_);
lean_dec_ref(v_config_1280_);
return v_res_1282_;
}
}
uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(uint8_t v_c_1283_){
_start:
{
uint8_t v___x_1331_; uint8_t v___x_1332_; 
v___x_1331_ = 48;
v___x_1332_ = lean_uint8_dec_le(v___x_1331_, v_c_1283_);
if (v___x_1332_ == 0)
{
goto v___jp_1326_;
}
else
{
uint8_t v___x_1333_; uint8_t v___x_1334_; 
v___x_1333_ = 57;
v___x_1334_ = lean_uint8_dec_le(v_c_1283_, v___x_1333_);
if (v___x_1334_ == 0)
{
goto v___jp_1326_;
}
else
{
return v___x_1334_;
}
}
v___jp_1284_:
{
uint8_t v___x_1285_; uint8_t v___x_1286_; 
v___x_1285_ = 45;
v___x_1286_ = lean_uint8_dec_eq(v_c_1283_, v___x_1285_);
if (v___x_1286_ == 0)
{
uint8_t v___x_1287_; uint8_t v___x_1288_; 
v___x_1287_ = 46;
v___x_1288_ = lean_uint8_dec_eq(v_c_1283_, v___x_1287_);
if (v___x_1288_ == 0)
{
uint8_t v___x_1289_; uint8_t v___x_1290_; 
v___x_1289_ = 95;
v___x_1290_ = lean_uint8_dec_eq(v_c_1283_, v___x_1289_);
if (v___x_1290_ == 0)
{
uint8_t v___x_1291_; uint8_t v___x_1292_; 
v___x_1291_ = 126;
v___x_1292_ = lean_uint8_dec_eq(v_c_1283_, v___x_1291_);
if (v___x_1292_ == 0)
{
uint8_t v___x_1293_; uint8_t v___x_1294_; 
v___x_1293_ = 33;
v___x_1294_ = lean_uint8_dec_eq(v_c_1283_, v___x_1293_);
if (v___x_1294_ == 0)
{
uint8_t v___x_1295_; uint8_t v___x_1296_; 
v___x_1295_ = 36;
v___x_1296_ = lean_uint8_dec_eq(v_c_1283_, v___x_1295_);
if (v___x_1296_ == 0)
{
uint8_t v___x_1297_; uint8_t v___x_1298_; 
v___x_1297_ = 38;
v___x_1298_ = lean_uint8_dec_eq(v_c_1283_, v___x_1297_);
if (v___x_1298_ == 0)
{
uint8_t v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = 39;
v___x_1300_ = lean_uint8_dec_eq(v_c_1283_, v___x_1299_);
if (v___x_1300_ == 0)
{
uint8_t v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = 40;
v___x_1302_ = lean_uint8_dec_eq(v_c_1283_, v___x_1301_);
if (v___x_1302_ == 0)
{
uint8_t v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = 41;
v___x_1304_ = lean_uint8_dec_eq(v_c_1283_, v___x_1303_);
if (v___x_1304_ == 0)
{
uint8_t v___x_1305_; uint8_t v___x_1306_; 
v___x_1305_ = 42;
v___x_1306_ = lean_uint8_dec_eq(v_c_1283_, v___x_1305_);
if (v___x_1306_ == 0)
{
uint8_t v___x_1307_; uint8_t v___x_1308_; 
v___x_1307_ = 43;
v___x_1308_ = lean_uint8_dec_eq(v_c_1283_, v___x_1307_);
if (v___x_1308_ == 0)
{
uint8_t v___x_1309_; uint8_t v___x_1310_; 
v___x_1309_ = 44;
v___x_1310_ = lean_uint8_dec_eq(v_c_1283_, v___x_1309_);
if (v___x_1310_ == 0)
{
uint8_t v___x_1311_; uint8_t v___x_1312_; 
v___x_1311_ = 59;
v___x_1312_ = lean_uint8_dec_eq(v_c_1283_, v___x_1311_);
if (v___x_1312_ == 0)
{
uint8_t v___x_1313_; uint8_t v___x_1314_; 
v___x_1313_ = 61;
v___x_1314_ = lean_uint8_dec_eq(v_c_1283_, v___x_1313_);
if (v___x_1314_ == 0)
{
uint8_t v___x_1315_; uint8_t v___x_1316_; 
v___x_1315_ = 58;
v___x_1316_ = lean_uint8_dec_eq(v_c_1283_, v___x_1315_);
if (v___x_1316_ == 0)
{
uint8_t v___x_1317_; uint8_t v___x_1318_; 
v___x_1317_ = 64;
v___x_1318_ = lean_uint8_dec_eq(v_c_1283_, v___x_1317_);
if (v___x_1318_ == 0)
{
uint8_t v___x_1319_; uint8_t v___x_1320_; 
v___x_1319_ = 37;
v___x_1320_ = lean_uint8_dec_eq(v_c_1283_, v___x_1319_);
return v___x_1320_;
}
else
{
return v___x_1318_;
}
}
else
{
return v___x_1316_;
}
}
else
{
return v___x_1314_;
}
}
else
{
return v___x_1312_;
}
}
else
{
return v___x_1310_;
}
}
else
{
return v___x_1308_;
}
}
else
{
return v___x_1306_;
}
}
else
{
return v___x_1304_;
}
}
else
{
return v___x_1302_;
}
}
else
{
return v___x_1300_;
}
}
else
{
return v___x_1298_;
}
}
else
{
return v___x_1296_;
}
}
else
{
return v___x_1294_;
}
}
else
{
return v___x_1292_;
}
}
else
{
return v___x_1290_;
}
}
else
{
return v___x_1288_;
}
}
else
{
return v___x_1286_;
}
}
v___jp_1321_:
{
uint8_t v___x_1322_; uint8_t v___x_1323_; 
v___x_1322_ = 65;
v___x_1323_ = lean_uint8_dec_le(v___x_1322_, v_c_1283_);
if (v___x_1323_ == 0)
{
goto v___jp_1284_;
}
else
{
uint8_t v___x_1324_; uint8_t v___x_1325_; 
v___x_1324_ = 90;
v___x_1325_ = lean_uint8_dec_le(v_c_1283_, v___x_1324_);
if (v___x_1325_ == 0)
{
goto v___jp_1284_;
}
else
{
return v___x_1325_;
}
}
}
v___jp_1326_:
{
uint8_t v___x_1327_; uint8_t v___x_1328_; 
v___x_1327_ = 97;
v___x_1328_ = lean_uint8_dec_le(v___x_1327_, v_c_1283_);
if (v___x_1328_ == 0)
{
goto v___jp_1321_;
}
else
{
uint8_t v___x_1329_; uint8_t v___x_1330_; 
v___x_1329_ = 122;
v___x_1330_ = lean_uint8_dec_le(v_c_1283_, v___x_1329_);
if (v___x_1330_ == 0)
{
goto v___jp_1321_;
}
else
{
return v___x_1330_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_1283_ = stack[0].m_num;
uint8_t v_res_1335_;
v_res_1335_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(v_c_1283_);
stack->m_num = v_res_1335_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0___boxed(lean_object* v_c_1336_){
_start:
{
uint8_t v_c_boxed_1337_; uint8_t v_res_1338_; lean_object* v_r_1339_; 
v_c_boxed_1337_ = lean_unbox(v_c_1336_);
v_res_1338_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(v_c_boxed_1337_);
v_r_1339_ = lean_box(v_res_1338_);
return v_r_1339_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(lean_object* v_config_1341_, lean_object* v_a_1342_){
_start:
{
lean_object* v_maxSegmentLength_1343_; lean_object* v___f_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v_snd_1347_; lean_object* v_fst_1348_; lean_object* v_fst_1349_; lean_object* v_array_1350_; lean_object* v_idx_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1368_; 
v_maxSegmentLength_1343_ = lean_ctor_get(v_config_1341_, 3);
v___f_1344_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___closed__0));
v___x_1345_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1342_);
v___x_1346_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1344_, v_maxSegmentLength_1343_, v___x_1345_, v_a_1342_);
v_snd_1347_ = lean_ctor_get(v___x_1346_, 1);
lean_inc(v_snd_1347_);
v_fst_1348_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_fst_1348_);
lean_dec_ref(v___x_1346_);
v_fst_1349_ = lean_ctor_get(v_snd_1347_, 0);
lean_inc(v_fst_1349_);
lean_dec(v_snd_1347_);
v_array_1350_ = lean_ctor_get(v_a_1342_, 0);
v_idx_1351_ = lean_ctor_get(v_a_1342_, 1);
v_isSharedCheck_1368_ = !lean_is_exclusive(v_a_1342_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1353_ = v_a_1342_;
v_isShared_1354_ = v_isSharedCheck_1368_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_idx_1351_);
lean_inc(v_array_1350_);
lean_dec(v_a_1342_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1368_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v_lower_1356_; lean_object* v_upper_1357_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___y_1365_; uint8_t v___x_1367_; 
v___x_1362_ = lean_nat_add(v_idx_1351_, v_fst_1348_);
lean_dec(v_fst_1348_);
v___x_1363_ = lean_byte_array_size(v_array_1350_);
v___x_1367_ = lean_nat_dec_le(v_idx_1351_, v___x_1345_);
if (v___x_1367_ == 0)
{
v___y_1365_ = v_idx_1351_;
goto v___jp_1364_;
}
else
{
lean_dec(v_idx_1351_);
v___y_1365_ = v___x_1345_;
goto v___jp_1364_;
}
v___jp_1355_:
{
lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1358_ = l_ByteArray_toByteSlice(v_array_1350_, v_lower_1356_, v_upper_1357_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 1, v___x_1358_);
lean_ctor_set(v___x_1353_, 0, v_fst_1349_);
v___x_1360_ = v___x_1353_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_fst_1349_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
v___jp_1364_:
{
uint8_t v___x_1366_; 
v___x_1366_ = lean_nat_dec_le(v___x_1362_, v___x_1363_);
if (v___x_1366_ == 0)
{
lean_dec(v___x_1362_);
v_lower_1356_ = v___y_1365_;
v_upper_1357_ = v___x_1363_;
goto v___jp_1355_;
}
else
{
v_lower_1356_ = v___y_1365_;
v_upper_1357_ = v___x_1362_;
goto v___jp_1355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___boxed(lean_object* v_config_1369_, lean_object* v_a_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1369_, v_a_1370_);
lean_dec_ref(v_config_1369_);
return v_res_1371_;
}
}
uint8_t l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(uint8_t v_c_1372_){
_start:
{
uint8_t v___x_1373_; uint8_t v___x_1374_; 
v___x_1373_ = 63;
v___x_1374_ = lean_uint8_dec_eq(v_c_1372_, v___x_1373_);
if (v___x_1374_ == 0)
{
uint8_t v___x_1375_; uint8_t v___x_1376_; 
v___x_1375_ = 35;
v___x_1376_ = lean_uint8_dec_eq(v_c_1372_, v___x_1375_);
return v___x_1376_;
}
else
{
return v___x_1374_;
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_1372_ = stack[0].m_num;
uint8_t v_res_1377_;
v_res_1377_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v_c_1372_);
stack->m_num = v_res_1377_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0___boxed(lean_object* v_c_1378_){
_start:
{
uint8_t v_c_boxed_1379_; uint8_t v_res_1380_; lean_object* v_r_1381_; 
v_c_boxed_1379_ = lean_unbox(v_c_1378_);
v_res_1380_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v_c_boxed_1379_);
v_r_1381_ = lean_box(v_res_1380_);
return v_r_1381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(lean_object* v_config_1389_, lean_object* v_a_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v_array_1416_; lean_object* v_idx_1417_; lean_object* v_fst_1418_; lean_object* v_snd_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1591_; 
v_array_1416_ = lean_ctor_get(v___y_1391_, 0);
v_idx_1417_ = lean_ctor_get(v___y_1391_, 1);
v_fst_1418_ = lean_ctor_get(v_a_1390_, 0);
v_snd_1419_ = lean_ctor_get(v_a_1390_, 1);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_a_1390_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1421_ = v_a_1390_;
v_isShared_1422_ = v_isSharedCheck_1591_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_snd_1419_);
lean_inc(v_fst_1418_);
lean_dec(v_a_1390_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1591_;
goto v_resetjp_1420_;
}
v___jp_1392_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___y_1393_);
lean_ctor_set(v___x_1396_, 1, v___y_1394_);
v___x_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1397_, 0, v___y_1395_);
lean_ctor_set(v___x_1397_, 1, v___x_1396_);
return v___x_1397_;
}
v___jp_1398_:
{
lean_object* v___x_1403_; uint8_t v___x_1404_; 
v___x_1403_ = lean_array_get_size(v___y_1402_);
v___x_1404_ = lean_nat_dec_le(v___y_1401_, v___x_1403_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
lean_dec(v___y_1401_);
v___x_1405_ = l_ByteArray_empty;
v___x_1406_ = lean_array_push(v___y_1402_, v___x_1405_);
v___x_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
lean_ctor_set(v___x_1407_, 1, v___y_1400_);
v_a_1390_ = v___x_1407_;
v___y_1391_ = v___y_1399_;
goto _start;
}
else
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
lean_dec_ref(v___y_1402_);
lean_dec(v___y_1400_);
lean_dec_ref(v_config_1389_);
v___x_1409_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1410_ = l_Nat_reprFast(v___y_1401_);
v___x_1411_ = lean_string_append(v___x_1409_, v___x_1410_);
lean_dec_ref(v___x_1410_);
v___x_1412_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1413_ = lean_string_append(v___x_1411_, v___x_1412_);
v___x_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
v___x_1415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___y_1399_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
return v___x_1415_;
}
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1423_ = lean_byte_array_size(v_array_1416_);
v___x_1424_ = lean_nat_dec_lt(v_idx_1417_, v___x_1423_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1426_; 
lean_dec_ref(v_config_1389_);
if (v_isShared_1422_ == 0)
{
v___x_1426_ = v___x_1421_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_fst_1418_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_snd_1419_);
v___x_1426_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1427_; 
v___x_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___y_1391_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
return v___x_1427_;
}
}
else
{
if (v___x_1424_ == 0)
{
lean_object* v___x_1430_; 
lean_dec_ref(v_config_1389_);
if (v_isShared_1422_ == 0)
{
v___x_1430_ = v___x_1421_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_fst_1418_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_snd_1419_);
v___x_1430_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
lean_object* v___x_1431_; 
v___x_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___y_1391_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
return v___x_1431_;
}
}
else
{
uint8_t v___y_1434_; uint8_t v___x_1534_; uint8_t v___x_1582_; 
v___x_1534_ = lean_byte_array_fget(v_array_1416_, v_idx_1417_);
v___x_1582_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1534_);
if (v___x_1582_ == 0)
{
uint8_t v___x_1583_; uint8_t v___x_1584_; 
v___x_1583_ = 47;
v___x_1584_ = lean_uint8_dec_eq(v___x_1534_, v___x_1583_);
if (v___x_1584_ == 0)
{
uint8_t v___x_1585_; uint8_t v___x_1586_; 
v___x_1585_ = 48;
v___x_1586_ = lean_uint8_dec_le(v___x_1585_, v___x_1534_);
if (v___x_1586_ == 0)
{
goto v___jp_1577_;
}
else
{
uint8_t v___x_1587_; uint8_t v___x_1588_; 
v___x_1587_ = 57;
v___x_1588_ = lean_uint8_dec_le(v___x_1534_, v___x_1587_);
if (v___x_1588_ == 0)
{
goto v___jp_1577_;
}
else
{
v___y_1434_ = v___x_1424_;
goto v___jp_1433_;
}
}
}
else
{
v___y_1434_ = v___x_1424_;
goto v___jp_1433_;
}
}
else
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_del_object(v___x_1421_);
lean_dec_ref(v_config_1389_);
v___x_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1589_, 0, v_fst_1418_);
lean_ctor_set(v___x_1589_, 1, v_snd_1419_);
v___x_1590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___y_1391_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
return v___x_1590_;
}
v___jp_1433_:
{
if (v___y_1434_ == 0)
{
lean_object* v___x_1436_; 
lean_dec_ref(v_config_1389_);
if (v_isShared_1422_ == 0)
{
v___x_1436_ = v___x_1421_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_fst_1418_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_snd_1419_);
v___x_1436_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
lean_object* v___x_1437_; 
v___x_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___y_1391_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
return v___x_1437_;
}
}
else
{
lean_object* v_maxPathSegments_1439_; lean_object* v_maxTotalPathLength_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v_maxPathSegments_1439_ = lean_ctor_get(v_config_1389_, 6);
v_maxTotalPathLength_1440_ = lean_ctor_get(v_config_1389_, 7);
v___x_1441_ = lean_array_get_size(v_fst_1418_);
v___x_1442_ = lean_nat_dec_le(v_maxPathSegments_1439_, v___x_1441_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; 
v___x_1443_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1389_, v___y_1391_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v_pos_1444_; lean_object* v_res_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1517_; 
v_pos_1444_ = lean_ctor_get(v___x_1443_, 0);
v_res_1445_ = lean_ctor_get(v___x_1443_, 1);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1447_ = v___x_1443_;
v_isShared_1448_ = v_isSharedCheck_1517_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_res_1445_);
lean_inc(v_pos_1444_);
lean_dec(v___x_1443_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1517_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
lean_inc(v_res_1445_);
v___x_1449_ = l_ByteSlice_toByteArray(v_res_1445_);
v___x_1450_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_1449_);
if (lean_obj_tag(v___x_1450_) == 1)
{
lean_object* v_val_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1512_; 
v_val_1451_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1453_ = v___x_1450_;
v_isShared_1454_ = v_isSharedCheck_1512_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_val_1451_);
lean_dec(v___x_1450_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1512_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; 
v___x_1455_ = l_ByteSlice_size(v_res_1445_);
lean_dec(v_res_1445_);
v___x_1456_ = lean_nat_add(v_snd_1419_, v___x_1455_);
lean_dec(v___x_1455_);
lean_dec(v_snd_1419_);
v___x_1457_ = lean_nat_dec_lt(v_maxTotalPathLength_1440_, v___x_1456_);
if (v___x_1457_ == 0)
{
lean_object* v_array_1458_; lean_object* v_idx_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; 
v_array_1458_ = lean_ctor_get(v_pos_1444_, 0);
v_idx_1459_ = lean_ctor_get(v_pos_1444_, 1);
v___x_1460_ = lean_array_push(v_fst_1418_, v_val_1451_);
v___x_1461_ = lean_byte_array_size(v_array_1458_);
v___x_1462_ = lean_nat_dec_lt(v_idx_1459_, v___x_1461_);
if (v___x_1462_ == 0)
{
lean_del_object(v___x_1453_);
lean_del_object(v___x_1447_);
lean_del_object(v___x_1421_);
lean_dec_ref(v_config_1389_);
v___y_1393_ = v___x_1460_;
v___y_1394_ = v___x_1456_;
v___y_1395_ = v_pos_1444_;
goto v___jp_1392_;
}
else
{
uint8_t v___x_1463_; uint8_t v___x_1464_; uint8_t v___x_1465_; 
v___x_1463_ = lean_byte_array_fget(v_array_1458_, v_idx_1459_);
v___x_1464_ = 47;
v___x_1465_ = lean_uint8_dec_eq(v___x_1463_, v___x_1464_);
if (v___x_1465_ == 0)
{
lean_del_object(v___x_1453_);
lean_del_object(v___x_1447_);
lean_del_object(v___x_1421_);
lean_dec_ref(v_config_1389_);
v___y_1393_ = v___x_1460_;
v___y_1394_ = v___x_1456_;
v___y_1395_ = v_pos_1444_;
goto v___jp_1392_;
}
else
{
lean_object* v___x_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; 
v___x_1466_ = lean_unsigned_to_nat(1u);
v___x_1467_ = lean_nat_add(v___x_1456_, v___x_1466_);
lean_dec(v___x_1456_);
v___x_1468_ = lean_nat_dec_lt(v_maxTotalPathLength_1440_, v___x_1467_);
if (v___x_1468_ == 0)
{
lean_del_object(v___x_1453_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1469_; lean_object* v___x_1471_; 
lean_dec(v___x_1467_);
lean_dec_ref(v___x_1460_);
lean_del_object(v___x_1421_);
lean_dec_ref(v_config_1389_);
v___x_1469_ = lean_box(0);
if (v_isShared_1448_ == 0)
{
lean_ctor_set_tag(v___x_1447_, 1);
lean_ctor_set(v___x_1447_, 1, v___x_1469_);
v___x_1471_ = v___x_1447_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_pos_1444_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v___x_1469_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
else
{
lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1487_; 
lean_inc(v_idx_1459_);
lean_inc_ref(v_array_1458_);
lean_del_object(v___x_1447_);
v_isSharedCheck_1487_ = !lean_is_exclusive(v_pos_1444_);
if (v_isSharedCheck_1487_ == 0)
{
lean_object* v_unused_1488_; lean_object* v_unused_1489_; 
v_unused_1488_ = lean_ctor_get(v_pos_1444_, 1);
lean_dec(v_unused_1488_);
v_unused_1489_ = lean_ctor_get(v_pos_1444_, 0);
lean_dec(v_unused_1489_);
v___x_1474_ = v_pos_1444_;
v_isShared_1475_ = v_isSharedCheck_1487_;
goto v_resetjp_1473_;
}
else
{
lean_dec(v_pos_1444_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1487_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1476_; lean_object* v___x_1478_; 
v___x_1476_ = lean_nat_add(v_idx_1459_, v___x_1466_);
lean_dec(v_idx_1459_);
lean_inc(v___x_1476_);
lean_inc_ref(v_array_1458_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 1, v___x_1476_);
v___x_1478_ = v___x_1474_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_array_1458_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v___x_1476_);
v___x_1478_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
uint8_t v___x_1479_; 
v___x_1479_ = lean_nat_dec_lt(v___x_1476_, v___x_1461_);
if (v___x_1479_ == 0)
{
lean_dec(v___x_1476_);
lean_dec_ref(v_array_1458_);
lean_del_object(v___x_1421_);
lean_inc(v_maxPathSegments_1439_);
v___y_1399_ = v___x_1478_;
v___y_1400_ = v___x_1467_;
v___y_1401_ = v_maxPathSegments_1439_;
v___y_1402_ = v___x_1460_;
goto v___jp_1398_;
}
else
{
uint8_t v___x_1480_; uint8_t v___x_1481_; 
v___x_1480_ = lean_byte_array_fget(v_array_1458_, v___x_1476_);
lean_dec(v___x_1476_);
lean_dec_ref(v_array_1458_);
v___x_1481_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1480_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1483_; 
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 1, v___x_1467_);
lean_ctor_set(v___x_1421_, 0, v___x_1460_);
v___x_1483_ = v___x_1421_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v___x_1467_);
v___x_1483_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
v_a_1390_ = v___x_1483_;
v___y_1391_ = v___x_1478_;
goto _start;
}
}
else
{
lean_del_object(v___x_1421_);
lean_inc(v_maxPathSegments_1439_);
v___y_1399_ = v___x_1478_;
v___y_1400_ = v___x_1467_;
v___y_1401_ = v_maxPathSegments_1439_;
v___y_1402_ = v___x_1460_;
goto v___jp_1398_;
}
}
}
}
}
}
else
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1496_; 
lean_inc(v_maxTotalPathLength_1440_);
lean_dec(v___x_1467_);
lean_dec_ref(v___x_1460_);
lean_del_object(v___x_1421_);
lean_dec_ref(v_config_1389_);
v___x_1490_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1491_ = l_Nat_reprFast(v_maxTotalPathLength_1440_);
v___x_1492_ = lean_string_append(v___x_1490_, v___x_1491_);
lean_dec_ref(v___x_1491_);
v___x_1493_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1494_ = lean_string_append(v___x_1492_, v___x_1493_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1494_);
v___x_1496_ = v___x_1453_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1494_);
v___x_1496_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1498_; 
if (v_isShared_1448_ == 0)
{
lean_ctor_set_tag(v___x_1447_, 1);
lean_ctor_set(v___x_1447_, 1, v___x_1496_);
v___x_1498_ = v___x_1447_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_pos_1444_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v___x_1496_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
}
}
else
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1507_; 
lean_inc(v_maxTotalPathLength_1440_);
lean_dec(v___x_1456_);
lean_dec(v_val_1451_);
lean_del_object(v___x_1421_);
lean_dec(v_fst_1418_);
lean_dec_ref(v_config_1389_);
v___x_1501_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1502_ = l_Nat_reprFast(v_maxTotalPathLength_1440_);
v___x_1503_ = lean_string_append(v___x_1501_, v___x_1502_);
lean_dec_ref(v___x_1502_);
v___x_1504_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1505_ = lean_string_append(v___x_1503_, v___x_1504_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1505_);
v___x_1507_ = v___x_1453_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1509_; 
if (v_isShared_1448_ == 0)
{
lean_ctor_set_tag(v___x_1447_, 1);
lean_ctor_set(v___x_1447_, 1, v___x_1507_);
v___x_1509_ = v___x_1447_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_pos_1444_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v___x_1507_);
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
}
else
{
lean_object* v___x_1513_; lean_object* v___x_1515_; 
lean_dec(v___x_1450_);
lean_dec(v_res_1445_);
lean_del_object(v___x_1421_);
lean_dec(v_snd_1419_);
lean_dec(v_fst_1418_);
lean_dec_ref(v_config_1389_);
v___x_1513_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5));
if (v_isShared_1448_ == 0)
{
lean_ctor_set_tag(v___x_1447_, 1);
lean_ctor_set(v___x_1447_, 1, v___x_1513_);
v___x_1515_ = v___x_1447_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_pos_1444_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
else
{
lean_object* v_pos_1518_; lean_object* v_err_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_del_object(v___x_1421_);
lean_dec(v_snd_1419_);
lean_dec(v_fst_1418_);
lean_dec_ref(v_config_1389_);
v_pos_1518_ = lean_ctor_get(v___x_1443_, 0);
v_err_1519_ = lean_ctor_get(v___x_1443_, 1);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1443_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_err_1519_);
lean_inc(v_pos_1518_);
lean_dec(v___x_1443_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_pos_1518_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_err_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
else
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
lean_inc(v_maxPathSegments_1439_);
lean_del_object(v___x_1421_);
lean_dec(v_snd_1419_);
lean_dec(v_fst_1418_);
lean_dec_ref(v_config_1389_);
v___x_1527_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1528_ = l_Nat_reprFast(v_maxPathSegments_1439_);
v___x_1529_ = lean_string_append(v___x_1527_, v___x_1528_);
lean_dec_ref(v___x_1528_);
v___x_1530_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1531_ = lean_string_append(v___x_1529_, v___x_1530_);
v___x_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
v___x_1533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___y_1391_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
return v___x_1533_;
}
}
}
v___jp_1535_:
{
uint8_t v___x_1536_; uint8_t v___x_1537_; 
v___x_1536_ = 45;
v___x_1537_ = lean_uint8_dec_eq(v___x_1534_, v___x_1536_);
if (v___x_1537_ == 0)
{
uint8_t v___x_1538_; uint8_t v___x_1539_; 
v___x_1538_ = 46;
v___x_1539_ = lean_uint8_dec_eq(v___x_1534_, v___x_1538_);
if (v___x_1539_ == 0)
{
uint8_t v___x_1540_; uint8_t v___x_1541_; 
v___x_1540_ = 95;
v___x_1541_ = lean_uint8_dec_eq(v___x_1534_, v___x_1540_);
if (v___x_1541_ == 0)
{
uint8_t v___x_1542_; uint8_t v___x_1543_; 
v___x_1542_ = 126;
v___x_1543_ = lean_uint8_dec_eq(v___x_1534_, v___x_1542_);
if (v___x_1543_ == 0)
{
uint8_t v___x_1544_; uint8_t v___x_1545_; 
v___x_1544_ = 33;
v___x_1545_ = lean_uint8_dec_eq(v___x_1534_, v___x_1544_);
if (v___x_1545_ == 0)
{
uint8_t v___x_1546_; uint8_t v___x_1547_; 
v___x_1546_ = 36;
v___x_1547_ = lean_uint8_dec_eq(v___x_1534_, v___x_1546_);
if (v___x_1547_ == 0)
{
uint8_t v___x_1548_; uint8_t v___x_1549_; 
v___x_1548_ = 38;
v___x_1549_ = lean_uint8_dec_eq(v___x_1534_, v___x_1548_);
if (v___x_1549_ == 0)
{
uint8_t v___x_1550_; uint8_t v___x_1551_; 
v___x_1550_ = 39;
v___x_1551_ = lean_uint8_dec_eq(v___x_1534_, v___x_1550_);
if (v___x_1551_ == 0)
{
uint8_t v___x_1552_; uint8_t v___x_1553_; 
v___x_1552_ = 40;
v___x_1553_ = lean_uint8_dec_eq(v___x_1534_, v___x_1552_);
if (v___x_1553_ == 0)
{
uint8_t v___x_1554_; uint8_t v___x_1555_; 
v___x_1554_ = 41;
v___x_1555_ = lean_uint8_dec_eq(v___x_1534_, v___x_1554_);
if (v___x_1555_ == 0)
{
uint8_t v___x_1556_; uint8_t v___x_1557_; 
v___x_1556_ = 42;
v___x_1557_ = lean_uint8_dec_eq(v___x_1534_, v___x_1556_);
if (v___x_1557_ == 0)
{
uint8_t v___x_1558_; uint8_t v___x_1559_; 
v___x_1558_ = 43;
v___x_1559_ = lean_uint8_dec_eq(v___x_1534_, v___x_1558_);
if (v___x_1559_ == 0)
{
uint8_t v___x_1560_; uint8_t v___x_1561_; 
v___x_1560_ = 44;
v___x_1561_ = lean_uint8_dec_eq(v___x_1534_, v___x_1560_);
if (v___x_1561_ == 0)
{
uint8_t v___x_1562_; uint8_t v___x_1563_; 
v___x_1562_ = 59;
v___x_1563_ = lean_uint8_dec_eq(v___x_1534_, v___x_1562_);
if (v___x_1563_ == 0)
{
uint8_t v___x_1564_; uint8_t v___x_1565_; 
v___x_1564_ = 61;
v___x_1565_ = lean_uint8_dec_eq(v___x_1534_, v___x_1564_);
if (v___x_1565_ == 0)
{
uint8_t v___x_1566_; uint8_t v___x_1567_; 
v___x_1566_ = 58;
v___x_1567_ = lean_uint8_dec_eq(v___x_1534_, v___x_1566_);
if (v___x_1567_ == 0)
{
uint8_t v___x_1568_; uint8_t v___x_1569_; 
v___x_1568_ = 64;
v___x_1569_ = lean_uint8_dec_eq(v___x_1534_, v___x_1568_);
if (v___x_1569_ == 0)
{
uint8_t v___x_1570_; uint8_t v___x_1571_; 
v___x_1570_ = 37;
v___x_1571_ = lean_uint8_dec_eq(v___x_1534_, v___x_1570_);
v___y_1434_ = v___x_1571_;
goto v___jp_1433_;
}
else
{
v___y_1434_ = v___x_1424_;
goto v___jp_1433_;
}
}
else
{
v___y_1434_ = v___x_1424_;
goto v___jp_1433_;
}
}
else
{
v___y_1434_ = v___x_1424_;
goto v___jp_1433_;
}
}
else
{
v___y_1434_ = v___x_1424_;
goto v___jp_1433_;
}
}
else
{
v___y_1434_ = v___x_1424_;
goto v___jp_1433_;
}
}
else
{
v___y_1434_ = v___x_1424_;
goto v___jp_1433_;
}
}
else
{
v___y_1434_ = v___x_1424_;
goto v___jp_1433_;
}
}
else
{
v___y_1434_ = v___x_1424_;
goto v___jp_1433_;
}
}
else
{
v___y_1434_ = v___x_1424_;
goto v___jp_1433_;
}
}
else
{
v___y_1434_ = v___x_1424_;
goto v___jp_1433_;
}
}
else
{
v___y_1434_ = v___x_1424_;
goto v___jp_1433_;
}
}
else
{
v___y_1434_ = v___x_1424_;
goto v___jp_1433_;
}
}
else
{
v___y_1434_ = v___x_1424_;
goto v___jp_1433_;
}
}
else
{
v___y_1434_ = v___x_1424_;
goto v___jp_1433_;
}
}
else
{
v___y_1434_ = v___x_1424_;
goto v___jp_1433_;
}
}
else
{
v___y_1434_ = v___x_1424_;
goto v___jp_1433_;
}
}
else
{
v___y_1434_ = v___x_1424_;
goto v___jp_1433_;
}
}
v___jp_1572_:
{
uint8_t v___x_1573_; uint8_t v___x_1574_; 
v___x_1573_ = 65;
v___x_1574_ = lean_uint8_dec_le(v___x_1573_, v___x_1534_);
if (v___x_1574_ == 0)
{
goto v___jp_1535_;
}
else
{
uint8_t v___x_1575_; uint8_t v___x_1576_; 
v___x_1575_ = 90;
v___x_1576_ = lean_uint8_dec_le(v___x_1534_, v___x_1575_);
if (v___x_1576_ == 0)
{
goto v___jp_1535_;
}
else
{
v___y_1434_ = v___x_1424_;
goto v___jp_1433_;
}
}
}
v___jp_1577_:
{
uint8_t v___x_1578_; uint8_t v___x_1579_; 
v___x_1578_ = 97;
v___x_1579_ = lean_uint8_dec_le(v___x_1578_, v___x_1534_);
if (v___x_1579_ == 0)
{
goto v___jp_1572_;
}
else
{
uint8_t v___x_1580_; uint8_t v___x_1581_; 
v___x_1580_ = 122;
v___x_1581_ = lean_uint8_dec_le(v___x_1534_, v___x_1580_);
if (v___x_1581_ == 0)
{
goto v___jp_1572_;
}
else
{
v___y_1434_ = v___x_1424_;
goto v___jp_1433_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(lean_object* v_config_1592_, lean_object* v_a_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v_array_1619_; lean_object* v_idx_1620_; lean_object* v_fst_1621_; lean_object* v_snd_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1794_; 
v_array_1619_ = lean_ctor_get(v___y_1594_, 0);
v_idx_1620_ = lean_ctor_get(v___y_1594_, 1);
v_fst_1621_ = lean_ctor_get(v_a_1593_, 0);
v_snd_1622_ = lean_ctor_get(v_a_1593_, 1);
v_isSharedCheck_1794_ = !lean_is_exclusive(v_a_1593_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1624_ = v_a_1593_;
v_isShared_1625_ = v_isSharedCheck_1794_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_snd_1622_);
lean_inc(v_fst_1621_);
lean_dec(v_a_1593_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1794_;
goto v_resetjp_1623_;
}
v___jp_1595_:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___y_1597_);
lean_ctor_set(v___x_1599_, 1, v___y_1596_);
v___x_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___y_1598_);
lean_ctor_set(v___x_1600_, 1, v___x_1599_);
return v___x_1600_;
}
v___jp_1601_:
{
lean_object* v___x_1606_; uint8_t v___x_1607_; 
v___x_1606_ = lean_array_get_size(v___y_1603_);
v___x_1607_ = lean_nat_dec_le(v___y_1602_, v___x_1606_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_dec(v___y_1602_);
v___x_1608_ = l_ByteArray_empty;
v___x_1609_ = lean_array_push(v___y_1603_, v___x_1608_);
v___x_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set(v___x_1610_, 1, v___y_1604_);
v___x_1611_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_1592_, v___x_1610_, v___y_1605_);
return v___x_1611_;
}
else
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec_ref(v_config_1592_);
v___x_1612_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1613_ = l_Nat_reprFast(v___y_1602_);
v___x_1614_ = lean_string_append(v___x_1612_, v___x_1613_);
lean_dec_ref(v___x_1613_);
v___x_1615_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1616_ = lean_string_append(v___x_1614_, v___x_1615_);
v___x_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
v___x_1618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___y_1605_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
return v___x_1618_;
}
}
v_resetjp_1623_:
{
lean_object* v___x_1626_; uint8_t v___x_1627_; 
v___x_1626_ = lean_byte_array_size(v_array_1619_);
v___x_1627_ = lean_nat_dec_lt(v_idx_1620_, v___x_1626_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1629_; 
lean_dec_ref(v_config_1592_);
if (v_isShared_1625_ == 0)
{
v___x_1629_ = v___x_1624_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_fst_1621_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_snd_1622_);
v___x_1629_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___y_1594_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
return v___x_1630_;
}
}
else
{
if (v___x_1627_ == 0)
{
lean_object* v___x_1633_; 
lean_dec_ref(v_config_1592_);
if (v_isShared_1625_ == 0)
{
v___x_1633_ = v___x_1624_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_fst_1621_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_snd_1622_);
v___x_1633_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
lean_object* v___x_1634_; 
v___x_1634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___y_1594_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
return v___x_1634_;
}
}
else
{
uint8_t v___y_1637_; uint8_t v___x_1737_; uint8_t v___x_1785_; 
v___x_1737_ = lean_byte_array_fget(v_array_1619_, v_idx_1620_);
v___x_1785_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1737_);
if (v___x_1785_ == 0)
{
uint8_t v___x_1786_; uint8_t v___x_1787_; 
v___x_1786_ = 47;
v___x_1787_ = lean_uint8_dec_eq(v___x_1737_, v___x_1786_);
if (v___x_1787_ == 0)
{
uint8_t v___x_1788_; uint8_t v___x_1789_; 
v___x_1788_ = 48;
v___x_1789_ = lean_uint8_dec_le(v___x_1788_, v___x_1737_);
if (v___x_1789_ == 0)
{
goto v___jp_1780_;
}
else
{
uint8_t v___x_1790_; uint8_t v___x_1791_; 
v___x_1790_ = 57;
v___x_1791_ = lean_uint8_dec_le(v___x_1737_, v___x_1790_);
if (v___x_1791_ == 0)
{
goto v___jp_1780_;
}
else
{
v___y_1637_ = v___x_1627_;
goto v___jp_1636_;
}
}
}
else
{
v___y_1637_ = v___x_1627_;
goto v___jp_1636_;
}
}
else
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
lean_del_object(v___x_1624_);
lean_dec_ref(v_config_1592_);
v___x_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1792_, 0, v_fst_1621_);
lean_ctor_set(v___x_1792_, 1, v_snd_1622_);
v___x_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___y_1594_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
return v___x_1793_;
}
v___jp_1636_:
{
if (v___y_1637_ == 0)
{
lean_object* v___x_1639_; 
lean_dec_ref(v_config_1592_);
if (v_isShared_1625_ == 0)
{
v___x_1639_ = v___x_1624_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_fst_1621_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_snd_1622_);
v___x_1639_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
lean_object* v___x_1640_; 
v___x_1640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___y_1594_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
return v___x_1640_;
}
}
else
{
lean_object* v_maxPathSegments_1642_; lean_object* v_maxTotalPathLength_1643_; lean_object* v___x_1644_; uint8_t v___x_1645_; 
v_maxPathSegments_1642_ = lean_ctor_get(v_config_1592_, 6);
v_maxTotalPathLength_1643_ = lean_ctor_get(v_config_1592_, 7);
v___x_1644_ = lean_array_get_size(v_fst_1621_);
v___x_1645_ = lean_nat_dec_le(v_maxPathSegments_1642_, v___x_1644_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; 
v___x_1646_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1592_, v___y_1594_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_pos_1647_; lean_object* v_res_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1720_; 
v_pos_1647_ = lean_ctor_get(v___x_1646_, 0);
v_res_1648_ = lean_ctor_get(v___x_1646_, 1);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1650_ = v___x_1646_;
v_isShared_1651_ = v_isSharedCheck_1720_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_res_1648_);
lean_inc(v_pos_1647_);
lean_dec(v___x_1646_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1720_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
lean_inc(v_res_1648_);
v___x_1652_ = l_ByteSlice_toByteArray(v_res_1648_);
v___x_1653_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_1652_);
if (lean_obj_tag(v___x_1653_) == 1)
{
lean_object* v_val_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1715_; 
v_val_1654_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1656_ = v___x_1653_;
v_isShared_1657_ = v_isSharedCheck_1715_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_val_1654_);
lean_dec(v___x_1653_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1715_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; uint8_t v___x_1660_; 
v___x_1658_ = l_ByteSlice_size(v_res_1648_);
lean_dec(v_res_1648_);
v___x_1659_ = lean_nat_add(v_snd_1622_, v___x_1658_);
lean_dec(v___x_1658_);
lean_dec(v_snd_1622_);
v___x_1660_ = lean_nat_dec_lt(v_maxTotalPathLength_1643_, v___x_1659_);
if (v___x_1660_ == 0)
{
lean_object* v_array_1661_; lean_object* v_idx_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; uint8_t v___x_1665_; 
v_array_1661_ = lean_ctor_get(v_pos_1647_, 0);
v_idx_1662_ = lean_ctor_get(v_pos_1647_, 1);
v___x_1663_ = lean_array_push(v_fst_1621_, v_val_1654_);
v___x_1664_ = lean_byte_array_size(v_array_1661_);
v___x_1665_ = lean_nat_dec_lt(v_idx_1662_, v___x_1664_);
if (v___x_1665_ == 0)
{
lean_del_object(v___x_1656_);
lean_del_object(v___x_1650_);
lean_del_object(v___x_1624_);
lean_dec_ref(v_config_1592_);
v___y_1596_ = v___x_1659_;
v___y_1597_ = v___x_1663_;
v___y_1598_ = v_pos_1647_;
goto v___jp_1595_;
}
else
{
uint8_t v___x_1666_; uint8_t v___x_1667_; uint8_t v___x_1668_; 
v___x_1666_ = lean_byte_array_fget(v_array_1661_, v_idx_1662_);
v___x_1667_ = 47;
v___x_1668_ = lean_uint8_dec_eq(v___x_1666_, v___x_1667_);
if (v___x_1668_ == 0)
{
lean_del_object(v___x_1656_);
lean_del_object(v___x_1650_);
lean_del_object(v___x_1624_);
lean_dec_ref(v_config_1592_);
v___y_1596_ = v___x_1659_;
v___y_1597_ = v___x_1663_;
v___y_1598_ = v_pos_1647_;
goto v___jp_1595_;
}
else
{
lean_object* v___x_1669_; lean_object* v___x_1670_; uint8_t v___x_1671_; 
v___x_1669_ = lean_unsigned_to_nat(1u);
v___x_1670_ = lean_nat_add(v___x_1659_, v___x_1669_);
lean_dec(v___x_1659_);
v___x_1671_ = lean_nat_dec_lt(v_maxTotalPathLength_1643_, v___x_1670_);
if (v___x_1671_ == 0)
{
lean_del_object(v___x_1656_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1672_; lean_object* v___x_1674_; 
lean_dec(v___x_1670_);
lean_dec_ref(v___x_1663_);
lean_del_object(v___x_1624_);
lean_dec_ref(v_config_1592_);
v___x_1672_ = lean_box(0);
if (v_isShared_1651_ == 0)
{
lean_ctor_set_tag(v___x_1650_, 1);
lean_ctor_set(v___x_1650_, 1, v___x_1672_);
v___x_1674_ = v___x_1650_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_pos_1647_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
else
{
lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1690_; 
lean_inc(v_idx_1662_);
lean_inc_ref(v_array_1661_);
lean_del_object(v___x_1650_);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_pos_1647_);
if (v_isSharedCheck_1690_ == 0)
{
lean_object* v_unused_1691_; lean_object* v_unused_1692_; 
v_unused_1691_ = lean_ctor_get(v_pos_1647_, 1);
lean_dec(v_unused_1691_);
v_unused_1692_ = lean_ctor_get(v_pos_1647_, 0);
lean_dec(v_unused_1692_);
v___x_1677_ = v_pos_1647_;
v_isShared_1678_ = v_isSharedCheck_1690_;
goto v_resetjp_1676_;
}
else
{
lean_dec(v_pos_1647_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1690_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1679_ = lean_nat_add(v_idx_1662_, v___x_1669_);
lean_dec(v_idx_1662_);
lean_inc(v___x_1679_);
lean_inc_ref(v_array_1661_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 1, v___x_1679_);
v___x_1681_ = v___x_1677_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_array_1661_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
uint8_t v___x_1682_; 
v___x_1682_ = lean_nat_dec_lt(v___x_1679_, v___x_1664_);
if (v___x_1682_ == 0)
{
lean_dec(v___x_1679_);
lean_dec_ref(v_array_1661_);
lean_del_object(v___x_1624_);
lean_inc(v_maxPathSegments_1642_);
v___y_1602_ = v_maxPathSegments_1642_;
v___y_1603_ = v___x_1663_;
v___y_1604_ = v___x_1670_;
v___y_1605_ = v___x_1681_;
goto v___jp_1601_;
}
else
{
uint8_t v___x_1683_; uint8_t v___x_1684_; 
v___x_1683_ = lean_byte_array_fget(v_array_1661_, v___x_1679_);
lean_dec(v___x_1679_);
lean_dec_ref(v_array_1661_);
v___x_1684_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1683_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1686_; 
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 1, v___x_1670_);
lean_ctor_set(v___x_1624_, 0, v___x_1663_);
v___x_1686_ = v___x_1624_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1663_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v___x_1670_);
v___x_1686_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
lean_object* v___x_1687_; 
v___x_1687_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_1592_, v___x_1686_, v___x_1681_);
return v___x_1687_;
}
}
else
{
lean_del_object(v___x_1624_);
lean_inc(v_maxPathSegments_1642_);
v___y_1602_ = v_maxPathSegments_1642_;
v___y_1603_ = v___x_1663_;
v___y_1604_ = v___x_1670_;
v___y_1605_ = v___x_1681_;
goto v___jp_1601_;
}
}
}
}
}
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1699_; 
lean_inc(v_maxTotalPathLength_1643_);
lean_dec(v___x_1670_);
lean_dec_ref(v___x_1663_);
lean_del_object(v___x_1624_);
lean_dec_ref(v_config_1592_);
v___x_1693_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1694_ = l_Nat_reprFast(v_maxTotalPathLength_1643_);
v___x_1695_ = lean_string_append(v___x_1693_, v___x_1694_);
lean_dec_ref(v___x_1694_);
v___x_1696_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1697_ = lean_string_append(v___x_1695_, v___x_1696_);
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v___x_1697_);
v___x_1699_ = v___x_1656_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
lean_object* v___x_1701_; 
if (v_isShared_1651_ == 0)
{
lean_ctor_set_tag(v___x_1650_, 1);
lean_ctor_set(v___x_1650_, 1, v___x_1699_);
v___x_1701_ = v___x_1650_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_pos_1647_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
}
else
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1710_; 
lean_inc(v_maxTotalPathLength_1643_);
lean_dec(v___x_1659_);
lean_dec(v_val_1654_);
lean_del_object(v___x_1624_);
lean_dec(v_fst_1621_);
lean_dec_ref(v_config_1592_);
v___x_1704_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1705_ = l_Nat_reprFast(v_maxTotalPathLength_1643_);
v___x_1706_ = lean_string_append(v___x_1704_, v___x_1705_);
lean_dec_ref(v___x_1705_);
v___x_1707_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1708_ = lean_string_append(v___x_1706_, v___x_1707_);
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v___x_1708_);
v___x_1710_ = v___x_1656_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1708_);
v___x_1710_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
lean_object* v___x_1712_; 
if (v_isShared_1651_ == 0)
{
lean_ctor_set_tag(v___x_1650_, 1);
lean_ctor_set(v___x_1650_, 1, v___x_1710_);
v___x_1712_ = v___x_1650_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_pos_1647_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v___x_1710_);
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
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1718_; 
lean_dec(v___x_1653_);
lean_dec(v_res_1648_);
lean_del_object(v___x_1624_);
lean_dec(v_snd_1622_);
lean_dec(v_fst_1621_);
lean_dec_ref(v_config_1592_);
v___x_1716_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5));
if (v_isShared_1651_ == 0)
{
lean_ctor_set_tag(v___x_1650_, 1);
lean_ctor_set(v___x_1650_, 1, v___x_1716_);
v___x_1718_ = v___x_1650_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_pos_1647_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v___x_1716_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
else
{
lean_object* v_pos_1721_; lean_object* v_err_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
lean_del_object(v___x_1624_);
lean_dec(v_snd_1622_);
lean_dec(v_fst_1621_);
lean_dec_ref(v_config_1592_);
v_pos_1721_ = lean_ctor_get(v___x_1646_, 0);
v_err_1722_ = lean_ctor_get(v___x_1646_, 1);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1646_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_err_1722_);
lean_inc(v_pos_1721_);
lean_dec(v___x_1646_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_pos_1721_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_err_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
else
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
lean_inc(v_maxPathSegments_1642_);
lean_del_object(v___x_1624_);
lean_dec(v_snd_1622_);
lean_dec(v_fst_1621_);
lean_dec_ref(v_config_1592_);
v___x_1730_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1731_ = l_Nat_reprFast(v_maxPathSegments_1642_);
v___x_1732_ = lean_string_append(v___x_1730_, v___x_1731_);
lean_dec_ref(v___x_1731_);
v___x_1733_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1734_ = lean_string_append(v___x_1732_, v___x_1733_);
v___x_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1734_);
v___x_1736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___y_1594_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
return v___x_1736_;
}
}
}
v___jp_1738_:
{
uint8_t v___x_1739_; uint8_t v___x_1740_; 
v___x_1739_ = 45;
v___x_1740_ = lean_uint8_dec_eq(v___x_1737_, v___x_1739_);
if (v___x_1740_ == 0)
{
uint8_t v___x_1741_; uint8_t v___x_1742_; 
v___x_1741_ = 46;
v___x_1742_ = lean_uint8_dec_eq(v___x_1737_, v___x_1741_);
if (v___x_1742_ == 0)
{
uint8_t v___x_1743_; uint8_t v___x_1744_; 
v___x_1743_ = 95;
v___x_1744_ = lean_uint8_dec_eq(v___x_1737_, v___x_1743_);
if (v___x_1744_ == 0)
{
uint8_t v___x_1745_; uint8_t v___x_1746_; 
v___x_1745_ = 126;
v___x_1746_ = lean_uint8_dec_eq(v___x_1737_, v___x_1745_);
if (v___x_1746_ == 0)
{
uint8_t v___x_1747_; uint8_t v___x_1748_; 
v___x_1747_ = 33;
v___x_1748_ = lean_uint8_dec_eq(v___x_1737_, v___x_1747_);
if (v___x_1748_ == 0)
{
uint8_t v___x_1749_; uint8_t v___x_1750_; 
v___x_1749_ = 36;
v___x_1750_ = lean_uint8_dec_eq(v___x_1737_, v___x_1749_);
if (v___x_1750_ == 0)
{
uint8_t v___x_1751_; uint8_t v___x_1752_; 
v___x_1751_ = 38;
v___x_1752_ = lean_uint8_dec_eq(v___x_1737_, v___x_1751_);
if (v___x_1752_ == 0)
{
uint8_t v___x_1753_; uint8_t v___x_1754_; 
v___x_1753_ = 39;
v___x_1754_ = lean_uint8_dec_eq(v___x_1737_, v___x_1753_);
if (v___x_1754_ == 0)
{
uint8_t v___x_1755_; uint8_t v___x_1756_; 
v___x_1755_ = 40;
v___x_1756_ = lean_uint8_dec_eq(v___x_1737_, v___x_1755_);
if (v___x_1756_ == 0)
{
uint8_t v___x_1757_; uint8_t v___x_1758_; 
v___x_1757_ = 41;
v___x_1758_ = lean_uint8_dec_eq(v___x_1737_, v___x_1757_);
if (v___x_1758_ == 0)
{
uint8_t v___x_1759_; uint8_t v___x_1760_; 
v___x_1759_ = 42;
v___x_1760_ = lean_uint8_dec_eq(v___x_1737_, v___x_1759_);
if (v___x_1760_ == 0)
{
uint8_t v___x_1761_; uint8_t v___x_1762_; 
v___x_1761_ = 43;
v___x_1762_ = lean_uint8_dec_eq(v___x_1737_, v___x_1761_);
if (v___x_1762_ == 0)
{
uint8_t v___x_1763_; uint8_t v___x_1764_; 
v___x_1763_ = 44;
v___x_1764_ = lean_uint8_dec_eq(v___x_1737_, v___x_1763_);
if (v___x_1764_ == 0)
{
uint8_t v___x_1765_; uint8_t v___x_1766_; 
v___x_1765_ = 59;
v___x_1766_ = lean_uint8_dec_eq(v___x_1737_, v___x_1765_);
if (v___x_1766_ == 0)
{
uint8_t v___x_1767_; uint8_t v___x_1768_; 
v___x_1767_ = 61;
v___x_1768_ = lean_uint8_dec_eq(v___x_1737_, v___x_1767_);
if (v___x_1768_ == 0)
{
uint8_t v___x_1769_; uint8_t v___x_1770_; 
v___x_1769_ = 58;
v___x_1770_ = lean_uint8_dec_eq(v___x_1737_, v___x_1769_);
if (v___x_1770_ == 0)
{
uint8_t v___x_1771_; uint8_t v___x_1772_; 
v___x_1771_ = 64;
v___x_1772_ = lean_uint8_dec_eq(v___x_1737_, v___x_1771_);
if (v___x_1772_ == 0)
{
uint8_t v___x_1773_; uint8_t v___x_1774_; 
v___x_1773_ = 37;
v___x_1774_ = lean_uint8_dec_eq(v___x_1737_, v___x_1773_);
v___y_1637_ = v___x_1774_;
goto v___jp_1636_;
}
else
{
v___y_1637_ = v___x_1627_;
goto v___jp_1636_;
}
}
else
{
v___y_1637_ = v___x_1627_;
goto v___jp_1636_;
}
}
else
{
v___y_1637_ = v___x_1627_;
goto v___jp_1636_;
}
}
else
{
v___y_1637_ = v___x_1627_;
goto v___jp_1636_;
}
}
else
{
v___y_1637_ = v___x_1627_;
goto v___jp_1636_;
}
}
else
{
v___y_1637_ = v___x_1627_;
goto v___jp_1636_;
}
}
else
{
v___y_1637_ = v___x_1627_;
goto v___jp_1636_;
}
}
else
{
v___y_1637_ = v___x_1627_;
goto v___jp_1636_;
}
}
else
{
v___y_1637_ = v___x_1627_;
goto v___jp_1636_;
}
}
else
{
v___y_1637_ = v___x_1627_;
goto v___jp_1636_;
}
}
else
{
v___y_1637_ = v___x_1627_;
goto v___jp_1636_;
}
}
else
{
v___y_1637_ = v___x_1627_;
goto v___jp_1636_;
}
}
else
{
v___y_1637_ = v___x_1627_;
goto v___jp_1636_;
}
}
else
{
v___y_1637_ = v___x_1627_;
goto v___jp_1636_;
}
}
else
{
v___y_1637_ = v___x_1627_;
goto v___jp_1636_;
}
}
else
{
v___y_1637_ = v___x_1627_;
goto v___jp_1636_;
}
}
else
{
v___y_1637_ = v___x_1627_;
goto v___jp_1636_;
}
}
v___jp_1775_:
{
uint8_t v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = 65;
v___x_1777_ = lean_uint8_dec_le(v___x_1776_, v___x_1737_);
if (v___x_1777_ == 0)
{
goto v___jp_1738_;
}
else
{
uint8_t v___x_1778_; uint8_t v___x_1779_; 
v___x_1778_ = 90;
v___x_1779_ = lean_uint8_dec_le(v___x_1737_, v___x_1778_);
if (v___x_1779_ == 0)
{
goto v___jp_1738_;
}
else
{
v___y_1637_ = v___x_1627_;
goto v___jp_1636_;
}
}
}
v___jp_1780_:
{
uint8_t v___x_1781_; uint8_t v___x_1782_; 
v___x_1781_ = 97;
v___x_1782_ = lean_uint8_dec_le(v___x_1781_, v___x_1737_);
if (v___x_1782_ == 0)
{
goto v___jp_1775_;
}
else
{
uint8_t v___x_1783_; uint8_t v___x_1784_; 
v___x_1783_ = 122;
v___x_1784_ = lean_uint8_dec_le(v___x_1737_, v___x_1783_);
if (v___x_1784_ == 0)
{
goto v___jp_1775_;
}
else
{
v___y_1637_ = v___x_1627_;
goto v___jp_1636_;
}
}
}
}
}
}
}
}
lean_object* l_Std_Http_URI_Parser_parsePath(lean_object* v_config_1806_, uint8_t v_forceAbsolute_1807_, uint8_t v_allowEmpty_1808_, lean_object* v_a_1809_){
_start:
{
lean_object* v___y_1811_; lean_object* v___y_1815_; lean_object* v_array_1818_; lean_object* v_idx_1819_; uint8_t v_isAbsolute_1820_; lean_object* v___x_1821_; lean_object* v_segments_1822_; uint8_t v_isAbsolute_1824_; lean_object* v_totalLength_1825_; lean_object* v___y_1826_; lean_object* v_pos_1850_; lean_object* v_array_1851_; lean_object* v_idx_1852_; lean_object* v___y_1861_; uint8_t v___y_1865_; lean_object* v_pos_1866_; uint8_t v_res_1867_; uint8_t v___y_1869_; lean_object* v_pos_1870_; uint8_t v_res_1871_; lean_object* v___y_1879_; uint8_t v___y_1880_; uint8_t v___y_1881_; uint8_t v___y_1890_; lean_object* v_pos_1891_; uint8_t v_res_1892_; lean_object* v_pos_1894_; lean_object* v_array_1895_; lean_object* v_idx_1896_; uint8_t v_res_1897_; lean_object* v___x_1901_; uint8_t v___x_1902_; 
v_array_1818_ = lean_ctor_get(v_a_1809_, 0);
lean_inc_ref(v_array_1818_);
v_idx_1819_ = lean_ctor_get(v_a_1809_, 1);
lean_inc(v_idx_1819_);
v_isAbsolute_1820_ = 0;
v___x_1821_ = lean_unsigned_to_nat(0u);
v_segments_1822_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__4));
v___x_1901_ = lean_byte_array_size(v_array_1818_);
v___x_1902_ = lean_nat_dec_lt(v_idx_1819_, v___x_1901_);
if (v___x_1902_ == 0)
{
v_pos_1894_ = v_a_1809_;
v_array_1895_ = v_array_1818_;
v_idx_1896_ = v_idx_1819_;
v_res_1897_ = v_isAbsolute_1820_;
goto v___jp_1893_;
}
else
{
uint8_t v___x_1903_; uint8_t v___x_1953_; uint8_t v___x_1954_; 
v___x_1903_ = lean_byte_array_fget(v_array_1818_, v_idx_1819_);
v___x_1953_ = 48;
v___x_1954_ = lean_uint8_dec_le(v___x_1953_, v___x_1903_);
if (v___x_1954_ == 0)
{
goto v___jp_1948_;
}
else
{
uint8_t v___x_1955_; uint8_t v___x_1956_; 
v___x_1955_ = 57;
v___x_1956_ = lean_uint8_dec_le(v___x_1903_, v___x_1955_);
if (v___x_1956_ == 0)
{
goto v___jp_1948_;
}
else
{
v_pos_1894_ = v_a_1809_;
v_array_1895_ = v_array_1818_;
v_idx_1896_ = v_idx_1819_;
v_res_1897_ = v___x_1956_;
goto v___jp_1893_;
}
}
v___jp_1904_:
{
uint8_t v___x_1905_; uint8_t v___x_1906_; 
v___x_1905_ = 45;
v___x_1906_ = lean_uint8_dec_eq(v___x_1903_, v___x_1905_);
if (v___x_1906_ == 0)
{
uint8_t v___x_1907_; uint8_t v___x_1908_; 
v___x_1907_ = 46;
v___x_1908_ = lean_uint8_dec_eq(v___x_1903_, v___x_1907_);
if (v___x_1908_ == 0)
{
uint8_t v___x_1909_; uint8_t v___x_1910_; 
v___x_1909_ = 95;
v___x_1910_ = lean_uint8_dec_eq(v___x_1903_, v___x_1909_);
if (v___x_1910_ == 0)
{
uint8_t v___x_1911_; uint8_t v___x_1912_; 
v___x_1911_ = 126;
v___x_1912_ = lean_uint8_dec_eq(v___x_1903_, v___x_1911_);
if (v___x_1912_ == 0)
{
uint8_t v___x_1913_; uint8_t v___x_1914_; 
v___x_1913_ = 33;
v___x_1914_ = lean_uint8_dec_eq(v___x_1903_, v___x_1913_);
if (v___x_1914_ == 0)
{
uint8_t v___x_1915_; uint8_t v___x_1916_; 
v___x_1915_ = 36;
v___x_1916_ = lean_uint8_dec_eq(v___x_1903_, v___x_1915_);
if (v___x_1916_ == 0)
{
uint8_t v___x_1917_; uint8_t v___x_1918_; 
v___x_1917_ = 38;
v___x_1918_ = lean_uint8_dec_eq(v___x_1903_, v___x_1917_);
if (v___x_1918_ == 0)
{
uint8_t v___x_1919_; uint8_t v___x_1920_; 
v___x_1919_ = 39;
v___x_1920_ = lean_uint8_dec_eq(v___x_1903_, v___x_1919_);
if (v___x_1920_ == 0)
{
uint8_t v___x_1921_; uint8_t v___x_1922_; 
v___x_1921_ = 40;
v___x_1922_ = lean_uint8_dec_eq(v___x_1903_, v___x_1921_);
if (v___x_1922_ == 0)
{
uint8_t v___x_1923_; uint8_t v___x_1924_; 
v___x_1923_ = 41;
v___x_1924_ = lean_uint8_dec_eq(v___x_1903_, v___x_1923_);
if (v___x_1924_ == 0)
{
uint8_t v___x_1925_; uint8_t v___x_1926_; 
v___x_1925_ = 42;
v___x_1926_ = lean_uint8_dec_eq(v___x_1903_, v___x_1925_);
if (v___x_1926_ == 0)
{
uint8_t v___x_1927_; uint8_t v___x_1928_; 
v___x_1927_ = 43;
v___x_1928_ = lean_uint8_dec_eq(v___x_1903_, v___x_1927_);
if (v___x_1928_ == 0)
{
uint8_t v___x_1929_; uint8_t v___x_1930_; 
v___x_1929_ = 44;
v___x_1930_ = lean_uint8_dec_eq(v___x_1903_, v___x_1929_);
if (v___x_1930_ == 0)
{
uint8_t v___x_1931_; uint8_t v___x_1932_; 
v___x_1931_ = 59;
v___x_1932_ = lean_uint8_dec_eq(v___x_1903_, v___x_1931_);
if (v___x_1932_ == 0)
{
uint8_t v___x_1933_; uint8_t v___x_1934_; 
v___x_1933_ = 61;
v___x_1934_ = lean_uint8_dec_eq(v___x_1903_, v___x_1933_);
if (v___x_1934_ == 0)
{
uint8_t v___x_1935_; uint8_t v___x_1936_; 
v___x_1935_ = 58;
v___x_1936_ = lean_uint8_dec_eq(v___x_1903_, v___x_1935_);
if (v___x_1936_ == 0)
{
uint8_t v___x_1937_; uint8_t v___x_1938_; 
v___x_1937_ = 64;
v___x_1938_ = lean_uint8_dec_eq(v___x_1903_, v___x_1937_);
if (v___x_1938_ == 0)
{
uint8_t v___x_1939_; uint8_t v___x_1940_; 
v___x_1939_ = 37;
v___x_1940_ = lean_uint8_dec_eq(v___x_1903_, v___x_1939_);
if (v___x_1940_ == 0)
{
uint8_t v___x_1941_; uint8_t v___x_1942_; 
v___x_1941_ = 47;
v___x_1942_ = lean_uint8_dec_eq(v___x_1903_, v___x_1941_);
if (v___x_1942_ == 0)
{
v_pos_1894_ = v_a_1809_;
v_array_1895_ = v_array_1818_;
v_idx_1896_ = v_idx_1819_;
v_res_1897_ = v_isAbsolute_1820_;
goto v___jp_1893_;
}
else
{
v_pos_1894_ = v_a_1809_;
v_array_1895_ = v_array_1818_;
v_idx_1896_ = v_idx_1819_;
v_res_1897_ = v___x_1942_;
goto v___jp_1893_;
}
}
else
{
v_pos_1894_ = v_a_1809_;
v_array_1895_ = v_array_1818_;
v_idx_1896_ = v_idx_1819_;
v_res_1897_ = v___x_1940_;
goto v___jp_1893_;
}
}
else
{
v_pos_1894_ = v_a_1809_;
v_array_1895_ = v_array_1818_;
v_idx_1896_ = v_idx_1819_;
v_res_1897_ = v___x_1938_;
goto v___jp_1893_;
}
}
else
{
v_pos_1894_ = v_a_1809_;
v_array_1895_ = v_array_1818_;
v_idx_1896_ = v_idx_1819_;
v_res_1897_ = v___x_1936_;
goto v___jp_1893_;
}
}
else
{
v_pos_1894_ = v_a_1809_;
v_array_1895_ = v_array_1818_;
v_idx_1896_ = v_idx_1819_;
v_res_1897_ = v___x_1934_;
goto v___jp_1893_;
}
}
else
{
v_pos_1894_ = v_a_1809_;
v_array_1895_ = v_array_1818_;
v_idx_1896_ = v_idx_1819_;
v_res_1897_ = v___x_1932_;
goto v___jp_1893_;
}
}
else
{
v_pos_1894_ = v_a_1809_;
v_array_1895_ = v_array_1818_;
v_idx_1896_ = v_idx_1819_;
v_res_1897_ = v___x_1930_;
goto v___jp_1893_;
}
}
else
{
v_pos_1894_ = v_a_1809_;
v_array_1895_ = v_array_1818_;
v_idx_1896_ = v_idx_1819_;
v_res_1897_ = v___x_1928_;
goto v___jp_1893_;
}
}
else
{
v_pos_1894_ = v_a_1809_;
v_array_1895_ = v_array_1818_;
v_idx_1896_ = v_idx_1819_;
v_res_1897_ = v___x_1926_;
goto v___jp_1893_;
}
}
else
{
v_pos_1894_ = v_a_1809_;
v_array_1895_ = v_array_1818_;
v_idx_1896_ = v_idx_1819_;
v_res_1897_ = v___x_1924_;
goto v___jp_1893_;
}
}
else
{
v_pos_1894_ = v_a_1809_;
v_array_1895_ = v_array_1818_;
v_idx_1896_ = v_idx_1819_;
v_res_1897_ = v___x_1922_;
goto v___jp_1893_;
}
}
else
{
v_pos_1894_ = v_a_1809_;
v_array_1895_ = v_array_1818_;
v_idx_1896_ = v_idx_1819_;
v_res_1897_ = v___x_1920_;
goto v___jp_1893_;
}
}
else
{
v_pos_1894_ = v_a_1809_;
v_array_1895_ = v_array_1818_;
v_idx_1896_ = v_idx_1819_;
v_res_1897_ = v___x_1918_;
goto v___jp_1893_;
}
}
else
{
v_pos_1894_ = v_a_1809_;
v_array_1895_ = v_array_1818_;
v_idx_1896_ = v_idx_1819_;
v_res_1897_ = v___x_1916_;
goto v___jp_1893_;
}
}
else
{
v_pos_1894_ = v_a_1809_;
v_array_1895_ = v_array_1818_;
v_idx_1896_ = v_idx_1819_;
v_res_1897_ = v___x_1914_;
goto v___jp_1893_;
}
}
else
{
v_pos_1894_ = v_a_1809_;
v_array_1895_ = v_array_1818_;
v_idx_1896_ = v_idx_1819_;
v_res_1897_ = v___x_1912_;
goto v___jp_1893_;
}
}
else
{
v_pos_1894_ = v_a_1809_;
v_array_1895_ = v_array_1818_;
v_idx_1896_ = v_idx_1819_;
v_res_1897_ = v___x_1910_;
goto v___jp_1893_;
}
}
else
{
v_pos_1894_ = v_a_1809_;
v_array_1895_ = v_array_1818_;
v_idx_1896_ = v_idx_1819_;
v_res_1897_ = v___x_1908_;
goto v___jp_1893_;
}
}
else
{
v_pos_1894_ = v_a_1809_;
v_array_1895_ = v_array_1818_;
v_idx_1896_ = v_idx_1819_;
v_res_1897_ = v___x_1906_;
goto v___jp_1893_;
}
}
v___jp_1943_:
{
uint8_t v___x_1944_; uint8_t v___x_1945_; 
v___x_1944_ = 65;
v___x_1945_ = lean_uint8_dec_le(v___x_1944_, v___x_1903_);
if (v___x_1945_ == 0)
{
goto v___jp_1904_;
}
else
{
uint8_t v___x_1946_; uint8_t v___x_1947_; 
v___x_1946_ = 90;
v___x_1947_ = lean_uint8_dec_le(v___x_1903_, v___x_1946_);
if (v___x_1947_ == 0)
{
goto v___jp_1904_;
}
else
{
v_pos_1894_ = v_a_1809_;
v_array_1895_ = v_array_1818_;
v_idx_1896_ = v_idx_1819_;
v_res_1897_ = v___x_1947_;
goto v___jp_1893_;
}
}
}
v___jp_1948_:
{
uint8_t v___x_1949_; uint8_t v___x_1950_; 
v___x_1949_ = 97;
v___x_1950_ = lean_uint8_dec_le(v___x_1949_, v___x_1903_);
if (v___x_1950_ == 0)
{
goto v___jp_1943_;
}
else
{
uint8_t v___x_1951_; uint8_t v___x_1952_; 
v___x_1951_ = 122;
v___x_1952_ = lean_uint8_dec_le(v___x_1903_, v___x_1951_);
if (v___x_1952_ == 0)
{
goto v___jp_1943_;
}
else
{
v_pos_1894_ = v_a_1809_;
v_array_1895_ = v_array_1818_;
v_idx_1896_ = v_idx_1819_;
v_res_1897_ = v___x_1952_;
goto v___jp_1893_;
}
}
}
}
v___jp_1810_:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__1));
v___x_1813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___y_1811_);
lean_ctor_set(v___x_1813_, 1, v___x_1812_);
return v___x_1813_;
}
v___jp_1814_:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1816_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__3));
v___x_1817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___y_1815_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
return v___x_1817_;
}
v___jp_1823_:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1827_, 0, v_segments_1822_);
lean_ctor_set(v___x_1827_, 1, v_totalLength_1825_);
v___x_1828_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(v_config_1806_, v___x_1827_, v___y_1826_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_res_1829_; lean_object* v_pos_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1839_; 
v_res_1829_ = lean_ctor_get(v___x_1828_, 1);
v_pos_1830_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1832_ = v___x_1828_;
v_isShared_1833_ = v_isSharedCheck_1839_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_res_1829_);
lean_inc(v_pos_1830_);
lean_dec(v___x_1828_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1839_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v_fst_1834_; lean_object* v___x_1835_; lean_object* v___x_1837_; 
v_fst_1834_ = lean_ctor_get(v_res_1829_, 0);
lean_inc(v_fst_1834_);
lean_dec(v_res_1829_);
v___x_1835_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1835_, 0, v_fst_1834_);
lean_ctor_set_uint8(v___x_1835_, sizeof(void*)*1, v_isAbsolute_1824_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 1, v___x_1835_);
v___x_1837_ = v___x_1832_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_pos_1830_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
else
{
lean_object* v_pos_1840_; lean_object* v_err_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
v_pos_1840_ = lean_ctor_get(v___x_1828_, 0);
v_err_1841_ = lean_ctor_get(v___x_1828_, 1);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1828_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_err_1841_);
lean_inc(v_pos_1840_);
lean_dec(v___x_1828_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_pos_1840_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_err_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
v___jp_1849_:
{
lean_object* v___x_1853_; uint8_t v___x_1854_; 
v___x_1853_ = lean_byte_array_size(v_array_1851_);
v___x_1854_ = lean_nat_dec_lt(v_idx_1852_, v___x_1853_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
lean_dec(v_idx_1852_);
lean_dec_ref(v_array_1851_);
lean_dec_ref(v_config_1806_);
v___x_1855_ = lean_box(0);
v___x_1856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1856_, 0, v_pos_1850_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
return v___x_1856_;
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
lean_dec_ref(v_pos_1850_);
v___x_1857_ = lean_unsigned_to_nat(1u);
v___x_1858_ = lean_nat_add(v_idx_1852_, v___x_1857_);
lean_dec(v_idx_1852_);
v___x_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1859_, 0, v_array_1851_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v_isAbsolute_1824_ = v___x_1854_;
v_totalLength_1825_ = v___x_1857_;
v___y_1826_ = v___x_1859_;
goto v___jp_1823_;
}
}
v___jp_1860_:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__5));
v___x_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___y_1861_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
return v___x_1863_;
}
v___jp_1864_:
{
if (v_allowEmpty_1808_ == 0)
{
v___y_1811_ = v_pos_1866_;
goto v___jp_1810_;
}
else
{
if (v_res_1867_ == 0)
{
if (v___y_1865_ == 0)
{
v___y_1861_ = v_pos_1866_;
goto v___jp_1860_;
}
else
{
v___y_1811_ = v_pos_1866_;
goto v___jp_1810_;
}
}
else
{
v___y_1861_ = v_pos_1866_;
goto v___jp_1860_;
}
}
}
v___jp_1868_:
{
if (v_res_1871_ == 0)
{
if (v_forceAbsolute_1807_ == 0)
{
v_isAbsolute_1824_ = v_isAbsolute_1820_;
v_totalLength_1825_ = v___x_1821_;
v___y_1826_ = v_pos_1870_;
goto v___jp_1823_;
}
else
{
lean_object* v_array_1872_; lean_object* v_idx_1873_; lean_object* v___x_1874_; uint8_t v___x_1875_; 
lean_dec_ref(v_config_1806_);
v_array_1872_ = lean_ctor_get(v_pos_1870_, 0);
v_idx_1873_ = lean_ctor_get(v_pos_1870_, 1);
v___x_1874_ = lean_byte_array_size(v_array_1872_);
v___x_1875_ = lean_nat_dec_lt(v_idx_1873_, v___x_1874_);
if (v___x_1875_ == 0)
{
v___y_1865_ = v___y_1869_;
v_pos_1866_ = v_pos_1870_;
v_res_1867_ = v_forceAbsolute_1807_;
goto v___jp_1864_;
}
else
{
v___y_1865_ = v___y_1869_;
v_pos_1866_ = v_pos_1870_;
v_res_1867_ = v_res_1871_;
goto v___jp_1864_;
}
}
}
else
{
lean_object* v_array_1876_; lean_object* v_idx_1877_; 
v_array_1876_ = lean_ctor_get(v_pos_1870_, 0);
lean_inc_ref(v_array_1876_);
v_idx_1877_ = lean_ctor_get(v_pos_1870_, 1);
lean_inc(v_idx_1877_);
v_pos_1850_ = v_pos_1870_;
v_array_1851_ = v_array_1876_;
v_idx_1852_ = v_idx_1877_;
goto v___jp_1849_;
}
}
v___jp_1878_:
{
lean_object* v_array_1882_; lean_object* v_idx_1883_; lean_object* v___x_1884_; uint8_t v___x_1885_; 
v_array_1882_ = lean_ctor_get(v___y_1879_, 0);
v_idx_1883_ = lean_ctor_get(v___y_1879_, 1);
v___x_1884_ = lean_byte_array_size(v_array_1882_);
v___x_1885_ = lean_nat_dec_lt(v_idx_1883_, v___x_1884_);
if (v___x_1885_ == 0)
{
v___y_1869_ = v___y_1880_;
v_pos_1870_ = v___y_1879_;
v_res_1871_ = v___y_1881_;
goto v___jp_1868_;
}
else
{
uint8_t v___x_1886_; uint8_t v___x_1887_; uint8_t v___x_1888_; 
v___x_1886_ = lean_byte_array_fget(v_array_1882_, v_idx_1883_);
v___x_1887_ = 47;
v___x_1888_ = lean_uint8_dec_eq(v___x_1886_, v___x_1887_);
if (v___x_1888_ == 0)
{
v___y_1869_ = v___y_1880_;
v_pos_1870_ = v___y_1879_;
v_res_1871_ = v___y_1881_;
goto v___jp_1868_;
}
else
{
lean_inc(v_idx_1883_);
lean_inc_ref(v_array_1882_);
v_pos_1850_ = v___y_1879_;
v_array_1851_ = v_array_1882_;
v_idx_1852_ = v_idx_1883_;
goto v___jp_1849_;
}
}
}
v___jp_1889_:
{
if (v_allowEmpty_1808_ == 0)
{
if (v_res_1892_ == 0)
{
if (v___y_1890_ == 0)
{
lean_dec_ref(v_config_1806_);
v___y_1815_ = v_pos_1891_;
goto v___jp_1814_;
}
else
{
v___y_1879_ = v_pos_1891_;
v___y_1880_ = v___y_1890_;
v___y_1881_ = v_res_1892_;
goto v___jp_1878_;
}
}
else
{
lean_dec_ref(v_config_1806_);
v___y_1815_ = v_pos_1891_;
goto v___jp_1814_;
}
}
else
{
v___y_1879_ = v_pos_1891_;
v___y_1880_ = v___y_1890_;
v___y_1881_ = v_isAbsolute_1820_;
goto v___jp_1878_;
}
}
v___jp_1893_:
{
lean_object* v___x_1898_; uint8_t v___x_1899_; 
v___x_1898_ = lean_byte_array_size(v_array_1895_);
lean_dec_ref(v_array_1895_);
v___x_1899_ = lean_nat_dec_lt(v_idx_1896_, v___x_1898_);
lean_dec(v_idx_1896_);
if (v___x_1899_ == 0)
{
uint8_t v___x_1900_; 
v___x_1900_ = 1;
v___y_1890_ = v_res_1897_;
v_pos_1891_ = v_pos_1894_;
v_res_1892_ = v___x_1900_;
goto v___jp_1889_;
}
else
{
v___y_1890_ = v_res_1897_;
v_pos_1891_ = v_pos_1894_;
v_res_1892_ = v_isAbsolute_1820_;
goto v___jp_1889_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_URI_Parser_parsePath_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_1806_ = stack[0].m_obj;
uint8_t v_forceAbsolute_1807_ = stack[1].m_num;
uint8_t v_allowEmpty_1808_ = stack[2].m_num;
lean_object* v_a_1809_ = stack[3].m_obj;
lean_object* v_res_1957_;
v_res_1957_ = l_Std_Http_URI_Parser_parsePath(v_config_1806_, v_forceAbsolute_1807_, v_allowEmpty_1808_, v_a_1809_);
stack->m_obj
 = v_res_1957_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath___boxed(lean_object* v_config_1958_, lean_object* v_forceAbsolute_1959_, lean_object* v_allowEmpty_1960_, lean_object* v_a_1961_){
_start:
{
uint8_t v_forceAbsolute_boxed_1962_; uint8_t v_allowEmpty_boxed_1963_; lean_object* v_res_1964_; 
v_forceAbsolute_boxed_1962_ = lean_unbox(v_forceAbsolute_1959_);
v_allowEmpty_boxed_1963_ = lean_unbox(v_allowEmpty_1960_);
v_res_1964_ = l_Std_Http_URI_Parser_parsePath(v_config_1958_, v_forceAbsolute_boxed_1962_, v_allowEmpty_boxed_1963_, v_a_1961_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0(lean_object* v_config_1965_, lean_object* v_inst_1966_, lean_object* v_a_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v___x_1969_; 
v___x_1969_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(v_config_1965_, v_a_1967_, v___y_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0(lean_object* v_config_1970_, lean_object* v_inst_1971_, lean_object* v_a_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_1970_, v_a_1972_, v___y_1973_);
return v___x_1974_;
}
}
lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg(){
_start:
{
lean_object* v___x_1976_; 
v___x_1976_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0));
return v___x_1976_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1977_;
v_res_1977_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg();
stack->m_obj
 = v_res_1977_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg___boxed(lean_object* v___dummy_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg();
return v_res_1979_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg();
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(lean_object* v_s_1981_){
_start:
{
lean_object* v___x_1982_; 
v___x_1982_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___boxed(lean_object* v_s_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(v_s_1983_);
lean_dec_ref(v_s_1983_);
return v_res_1984_;
}
}
lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg(){
_start:
{
lean_object* v___x_1986_; 
v___x_1986_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0));
return v___x_1986_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1987_;
v_res_1987_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg();
stack->m_obj
 = v_res_1987_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg___boxed(lean_object* v___dummy_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg();
return v_res_1989_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1990_; 
v___x_1990_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg();
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(lean_object* v_s_1991_){
_start:
{
lean_object* v___x_1992_; 
v___x_1992_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___boxed(lean_object* v_s_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(v_s_1993_);
lean_dec_ref(v_s_1993_);
return v_res_1994_;
}
}
uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(uint8_t v_c_1995_){
_start:
{
uint8_t v___x_2047_; uint8_t v___x_2048_; 
v___x_2047_ = 48;
v___x_2048_ = lean_uint8_dec_le(v___x_2047_, v_c_1995_);
if (v___x_2048_ == 0)
{
goto v___jp_2042_;
}
else
{
uint8_t v___x_2049_; uint8_t v___x_2050_; 
v___x_2049_ = 57;
v___x_2050_ = lean_uint8_dec_le(v_c_1995_, v___x_2049_);
if (v___x_2050_ == 0)
{
goto v___jp_2042_;
}
else
{
return v___x_2050_;
}
}
v___jp_1996_:
{
uint8_t v___x_1997_; uint8_t v___x_1998_; 
v___x_1997_ = 45;
v___x_1998_ = lean_uint8_dec_eq(v_c_1995_, v___x_1997_);
if (v___x_1998_ == 0)
{
uint8_t v___x_1999_; uint8_t v___x_2000_; 
v___x_1999_ = 46;
v___x_2000_ = lean_uint8_dec_eq(v_c_1995_, v___x_1999_);
if (v___x_2000_ == 0)
{
uint8_t v___x_2001_; uint8_t v___x_2002_; 
v___x_2001_ = 95;
v___x_2002_ = lean_uint8_dec_eq(v_c_1995_, v___x_2001_);
if (v___x_2002_ == 0)
{
uint8_t v___x_2003_; uint8_t v___x_2004_; 
v___x_2003_ = 126;
v___x_2004_ = lean_uint8_dec_eq(v_c_1995_, v___x_2003_);
if (v___x_2004_ == 0)
{
uint8_t v___x_2005_; uint8_t v___x_2006_; 
v___x_2005_ = 33;
v___x_2006_ = lean_uint8_dec_eq(v_c_1995_, v___x_2005_);
if (v___x_2006_ == 0)
{
uint8_t v___x_2007_; uint8_t v___x_2008_; 
v___x_2007_ = 36;
v___x_2008_ = lean_uint8_dec_eq(v_c_1995_, v___x_2007_);
if (v___x_2008_ == 0)
{
uint8_t v___x_2009_; uint8_t v___x_2010_; 
v___x_2009_ = 38;
v___x_2010_ = lean_uint8_dec_eq(v_c_1995_, v___x_2009_);
if (v___x_2010_ == 0)
{
uint8_t v___x_2011_; uint8_t v___x_2012_; 
v___x_2011_ = 39;
v___x_2012_ = lean_uint8_dec_eq(v_c_1995_, v___x_2011_);
if (v___x_2012_ == 0)
{
uint8_t v___x_2013_; uint8_t v___x_2014_; 
v___x_2013_ = 40;
v___x_2014_ = lean_uint8_dec_eq(v_c_1995_, v___x_2013_);
if (v___x_2014_ == 0)
{
uint8_t v___x_2015_; uint8_t v___x_2016_; 
v___x_2015_ = 41;
v___x_2016_ = lean_uint8_dec_eq(v_c_1995_, v___x_2015_);
if (v___x_2016_ == 0)
{
uint8_t v___x_2017_; uint8_t v___x_2018_; 
v___x_2017_ = 42;
v___x_2018_ = lean_uint8_dec_eq(v_c_1995_, v___x_2017_);
if (v___x_2018_ == 0)
{
uint8_t v___x_2019_; uint8_t v___x_2020_; 
v___x_2019_ = 43;
v___x_2020_ = lean_uint8_dec_eq(v_c_1995_, v___x_2019_);
if (v___x_2020_ == 0)
{
uint8_t v___x_2021_; uint8_t v___x_2022_; 
v___x_2021_ = 44;
v___x_2022_ = lean_uint8_dec_eq(v_c_1995_, v___x_2021_);
if (v___x_2022_ == 0)
{
uint8_t v___x_2023_; uint8_t v___x_2024_; 
v___x_2023_ = 59;
v___x_2024_ = lean_uint8_dec_eq(v_c_1995_, v___x_2023_);
if (v___x_2024_ == 0)
{
uint8_t v___x_2025_; uint8_t v___x_2026_; 
v___x_2025_ = 61;
v___x_2026_ = lean_uint8_dec_eq(v_c_1995_, v___x_2025_);
if (v___x_2026_ == 0)
{
uint8_t v___x_2027_; uint8_t v___x_2028_; 
v___x_2027_ = 58;
v___x_2028_ = lean_uint8_dec_eq(v_c_1995_, v___x_2027_);
if (v___x_2028_ == 0)
{
uint8_t v___x_2029_; uint8_t v___x_2030_; 
v___x_2029_ = 64;
v___x_2030_ = lean_uint8_dec_eq(v_c_1995_, v___x_2029_);
if (v___x_2030_ == 0)
{
uint8_t v___x_2031_; uint8_t v___x_2032_; 
v___x_2031_ = 47;
v___x_2032_ = lean_uint8_dec_eq(v_c_1995_, v___x_2031_);
if (v___x_2032_ == 0)
{
uint8_t v___x_2033_; uint8_t v___x_2034_; 
v___x_2033_ = 63;
v___x_2034_ = lean_uint8_dec_eq(v_c_1995_, v___x_2033_);
if (v___x_2034_ == 0)
{
uint8_t v___x_2035_; uint8_t v___x_2036_; 
v___x_2035_ = 37;
v___x_2036_ = lean_uint8_dec_eq(v_c_1995_, v___x_2035_);
return v___x_2036_;
}
else
{
return v___x_2034_;
}
}
else
{
return v___x_2032_;
}
}
else
{
return v___x_2030_;
}
}
else
{
return v___x_2028_;
}
}
else
{
return v___x_2026_;
}
}
else
{
return v___x_2024_;
}
}
else
{
return v___x_2022_;
}
}
else
{
return v___x_2020_;
}
}
else
{
return v___x_2018_;
}
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
v___jp_2037_:
{
uint8_t v___x_2038_; uint8_t v___x_2039_; 
v___x_2038_ = 65;
v___x_2039_ = lean_uint8_dec_le(v___x_2038_, v_c_1995_);
if (v___x_2039_ == 0)
{
goto v___jp_1996_;
}
else
{
uint8_t v___x_2040_; uint8_t v___x_2041_; 
v___x_2040_ = 90;
v___x_2041_ = lean_uint8_dec_le(v_c_1995_, v___x_2040_);
if (v___x_2041_ == 0)
{
goto v___jp_1996_;
}
else
{
return v___x_2041_;
}
}
}
v___jp_2042_:
{
uint8_t v___x_2043_; uint8_t v___x_2044_; 
v___x_2043_ = 97;
v___x_2044_ = lean_uint8_dec_le(v___x_2043_, v_c_1995_);
if (v___x_2044_ == 0)
{
goto v___jp_2037_;
}
else
{
uint8_t v___x_2045_; uint8_t v___x_2046_; 
v___x_2045_ = 122;
v___x_2046_ = lean_uint8_dec_le(v_c_1995_, v___x_2045_);
if (v___x_2046_ == 0)
{
goto v___jp_2037_;
}
else
{
return v___x_2046_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_1995_ = stack[0].m_num;
uint8_t v_res_2051_;
v_res_2051_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(v_c_1995_);
stack->m_num = v_res_2051_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0___boxed(lean_object* v_c_2052_){
_start:
{
uint8_t v_c_boxed_2053_; uint8_t v_res_2054_; lean_object* v_r_2055_; 
v_c_boxed_2053_ = lean_unbox(v_c_2052_);
v_res_2054_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(v_c_boxed_2053_);
v_r_2055_ = lean_box(v_res_2054_);
return v_r_2055_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(lean_object* v___x_2056_, lean_object* v___x_2057_, lean_object* v_a_2058_, lean_object* v_b_2059_){
_start:
{
lean_object* v_it_2061_; 
if (lean_obj_tag(v_a_2058_) == 0)
{
lean_object* v_currPos_2065_; lean_object* v_searcher_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2092_; 
v_currPos_2065_ = lean_ctor_get(v_a_2058_, 0);
v_searcher_2066_ = lean_ctor_get(v_a_2058_, 1);
v_isSharedCheck_2092_ = !lean_is_exclusive(v_a_2058_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2068_ = v_a_2058_;
v_isShared_2069_ = v_isSharedCheck_2092_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_searcher_2066_);
lean_inc(v_currPos_2065_);
lean_dec(v_a_2058_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2092_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v_str_2070_; lean_object* v_startInclusive_2071_; lean_object* v_endExclusive_2072_; lean_object* v___x_2073_; uint8_t v_decide_2074_; 
v_str_2070_ = lean_ctor_get(v___x_2056_, 0);
v_startInclusive_2071_ = lean_ctor_get(v___x_2056_, 1);
v_endExclusive_2072_ = lean_ctor_get(v___x_2056_, 2);
v___x_2073_ = lean_nat_sub(v_endExclusive_2072_, v_startInclusive_2071_);
v_decide_2074_ = lean_nat_dec_eq(v_searcher_2066_, v___x_2073_);
lean_dec(v___x_2073_);
if (v_decide_2074_ == 0)
{
uint32_t v___x_2075_; lean_object* v___x_2076_; uint32_t v___x_2077_; uint8_t v___x_2078_; 
v___x_2075_ = 38;
v___x_2076_ = lean_nat_add(v_startInclusive_2071_, v_searcher_2066_);
v___x_2077_ = lean_string_utf8_get_fast(v_str_2070_, v___x_2076_);
v___x_2078_ = lean_uint32_dec_eq(v___x_2077_, v___x_2075_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2082_; 
lean_dec(v_searcher_2066_);
v___x_2079_ = lean_string_utf8_next_fast(v_str_2070_, v___x_2076_);
lean_dec(v___x_2076_);
v___x_2080_ = lean_nat_sub(v___x_2079_, v_startInclusive_2071_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 1, v___x_2080_);
v___x_2082_ = v___x_2068_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_currPos_2065_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
v_a_2058_ = v___x_2082_;
goto _start;
}
}
else
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v_nextIt_2089_; 
lean_dec(v_currPos_2065_);
v___x_2085_ = lean_string_utf8_next_fast(v_str_2070_, v___x_2076_);
v___x_2086_ = lean_nat_sub(v___x_2085_, v___x_2076_);
lean_dec(v___x_2076_);
v___x_2087_ = lean_nat_add(v_searcher_2066_, v___x_2086_);
lean_dec(v___x_2086_);
lean_dec(v_searcher_2066_);
lean_inc(v___x_2087_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 1, v___x_2087_);
lean_ctor_set(v___x_2068_, 0, v___x_2087_);
v_nextIt_2089_ = v___x_2068_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2087_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v___x_2087_);
v_nextIt_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
v_it_2061_ = v_nextIt_2089_;
goto v___jp_2060_;
}
}
}
else
{
lean_object* v___x_2091_; 
lean_del_object(v___x_2068_);
lean_dec(v_searcher_2066_);
lean_dec(v_currPos_2065_);
v___x_2091_ = lean_box(1);
v_it_2061_ = v___x_2091_;
goto v___jp_2060_;
}
}
}
else
{
return v_b_2059_;
}
v___jp_2060_:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2062_ = lean_unsigned_to_nat(1u);
v___x_2063_ = lean_nat_add(v_b_2059_, v___x_2062_);
lean_dec(v_b_2059_);
v_a_2058_ = v_it_2061_;
v_b_2059_ = v___x_2063_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg___boxed(lean_object* v___x_2093_, lean_object* v___x_2094_, lean_object* v_a_2095_, lean_object* v_b_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2093_, v___x_2094_, v_a_2095_, v_b_2096_);
lean_dec(v___x_2094_);
lean_dec_ref(v___x_2093_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(lean_object* v___x_2098_, lean_object* v___x_2099_, lean_object* v___x_2100_, lean_object* v_a_2101_, lean_object* v_b_2102_){
_start:
{
lean_object* v_it_2104_; 
if (lean_obj_tag(v_a_2101_) == 0)
{
lean_object* v_currPos_2108_; lean_object* v_searcher_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2135_; 
v_currPos_2108_ = lean_ctor_get(v_a_2101_, 0);
v_searcher_2109_ = lean_ctor_get(v_a_2101_, 1);
v_isSharedCheck_2135_ = !lean_is_exclusive(v_a_2101_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2111_ = v_a_2101_;
v_isShared_2112_ = v_isSharedCheck_2135_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_searcher_2109_);
lean_inc(v_currPos_2108_);
lean_dec(v_a_2101_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2135_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v_str_2113_; lean_object* v_startInclusive_2114_; lean_object* v_endExclusive_2115_; lean_object* v___x_2116_; uint8_t v_decide_2117_; 
v_str_2113_ = lean_ctor_get(v___x_2099_, 0);
v_startInclusive_2114_ = lean_ctor_get(v___x_2099_, 1);
v_endExclusive_2115_ = lean_ctor_get(v___x_2099_, 2);
v___x_2116_ = lean_nat_sub(v_endExclusive_2115_, v_startInclusive_2114_);
v_decide_2117_ = lean_nat_dec_eq(v_searcher_2109_, v___x_2116_);
lean_dec(v___x_2116_);
if (v_decide_2117_ == 0)
{
lean_object* v___x_2118_; uint32_t v___x_2119_; uint32_t v___x_2120_; uint8_t v___x_2121_; 
v___x_2118_ = lean_nat_add(v_startInclusive_2114_, v_searcher_2109_);
v___x_2119_ = lean_string_utf8_get_fast(v_str_2113_, v___x_2118_);
v___x_2120_ = 38;
v___x_2121_ = lean_uint32_dec_eq(v___x_2119_, v___x_2120_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2125_; 
lean_dec(v_searcher_2109_);
v___x_2122_ = lean_string_utf8_next_fast(v_str_2113_, v___x_2118_);
lean_dec(v___x_2118_);
v___x_2123_ = lean_nat_sub(v___x_2122_, v_startInclusive_2114_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 1, v___x_2123_);
v___x_2125_ = v___x_2111_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_currPos_2108_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v___x_2123_);
v___x_2125_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2099_, v___x_2100_, v___x_2125_, v_b_2102_);
return v___x_2126_;
}
}
else
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v_nextIt_2132_; 
lean_dec(v_currPos_2108_);
v___x_2128_ = lean_string_utf8_next_fast(v_str_2113_, v___x_2118_);
v___x_2129_ = lean_nat_sub(v___x_2128_, v___x_2118_);
lean_dec(v___x_2118_);
v___x_2130_ = lean_nat_add(v_searcher_2109_, v___x_2129_);
lean_dec(v___x_2129_);
lean_dec(v_searcher_2109_);
lean_inc(v___x_2130_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 1, v___x_2130_);
lean_ctor_set(v___x_2111_, 0, v___x_2130_);
v_nextIt_2132_ = v___x_2111_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v___x_2130_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v___x_2130_);
v_nextIt_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
v_it_2104_ = v_nextIt_2132_;
goto v___jp_2103_;
}
}
}
else
{
lean_object* v___x_2134_; 
lean_del_object(v___x_2111_);
lean_dec(v_searcher_2109_);
lean_dec(v_currPos_2108_);
v___x_2134_ = lean_box(1);
v_it_2104_ = v___x_2134_;
goto v___jp_2103_;
}
}
}
else
{
return v_b_2102_;
}
v___jp_2103_:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2105_ = lean_unsigned_to_nat(1u);
v___x_2106_ = lean_nat_add(v_b_2102_, v___x_2105_);
lean_dec(v_b_2102_);
v___x_2107_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2099_, v___x_2100_, v_it_2104_, v___x_2106_);
return v___x_2107_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg___boxed(lean_object* v___x_2136_, lean_object* v___x_2137_, lean_object* v___x_2138_, lean_object* v_a_2139_, lean_object* v_b_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2136_, v___x_2137_, v___x_2138_, v_a_2139_, v_b_2140_);
lean_dec(v___x_2138_);
lean_dec_ref(v___x_2137_);
lean_dec_ref(v___x_2136_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(lean_object* v_out_2142_, lean_object* v_a_2143_, lean_object* v_b_2144_){
_start:
{
if (lean_obj_tag(v_a_2143_) == 0)
{
lean_object* v_currPos_2145_; lean_object* v_searcher_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2185_; 
v_currPos_2145_ = lean_ctor_get(v_a_2143_, 0);
v_searcher_2146_ = lean_ctor_get(v_a_2143_, 1);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_a_2143_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2148_ = v_a_2143_;
v_isShared_2149_ = v_isSharedCheck_2185_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_searcher_2146_);
lean_inc(v_currPos_2145_);
lean_dec(v_a_2143_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2185_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v_str_2150_; lean_object* v_startInclusive_2151_; lean_object* v_endExclusive_2152_; lean_object* v_it_2154_; lean_object* v_startInclusive_2155_; lean_object* v_endExclusive_2156_; lean_object* v___x_2163_; uint8_t v_decide_2164_; 
v_str_2150_ = lean_ctor_get(v_out_2142_, 0);
v_startInclusive_2151_ = lean_ctor_get(v_out_2142_, 1);
v_endExclusive_2152_ = lean_ctor_get(v_out_2142_, 2);
v___x_2163_ = lean_nat_sub(v_endExclusive_2152_, v_startInclusive_2151_);
v_decide_2164_ = lean_nat_dec_eq(v_searcher_2146_, v___x_2163_);
if (v_decide_2164_ == 0)
{
uint32_t v___x_2165_; lean_object* v___x_2166_; uint32_t v___x_2167_; uint8_t v___x_2168_; 
lean_dec(v___x_2163_);
v___x_2165_ = 61;
v___x_2166_ = lean_nat_add(v_startInclusive_2151_, v_searcher_2146_);
v___x_2167_ = lean_string_utf8_get_fast(v_str_2150_, v___x_2166_);
v___x_2168_ = lean_uint32_dec_eq(v___x_2167_, v___x_2165_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2172_; 
lean_dec(v_searcher_2146_);
v___x_2169_ = lean_string_utf8_next_fast(v_str_2150_, v___x_2166_);
lean_dec(v___x_2166_);
v___x_2170_ = lean_nat_sub(v___x_2169_, v_startInclusive_2151_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 1, v___x_2170_);
v___x_2172_ = v___x_2148_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_currPos_2145_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v___x_2170_);
v___x_2172_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
v_a_2143_ = v___x_2172_;
goto _start;
}
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v_slice_2178_; lean_object* v_nextIt_2180_; 
v___x_2175_ = lean_string_utf8_next_fast(v_str_2150_, v___x_2166_);
v___x_2176_ = lean_nat_sub(v___x_2175_, v___x_2166_);
lean_dec(v___x_2166_);
v___x_2177_ = lean_nat_add(v_searcher_2146_, v___x_2176_);
lean_dec(v___x_2176_);
v_slice_2178_ = l_String_Slice_subslice_x21(v_out_2142_, v_currPos_2145_, v_searcher_2146_);
lean_inc(v___x_2177_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 1, v___x_2177_);
lean_ctor_set(v___x_2148_, 0, v___x_2177_);
v_nextIt_2180_ = v___x_2148_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v___x_2177_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v___x_2177_);
v_nextIt_2180_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
lean_object* v_startInclusive_2181_; lean_object* v_endExclusive_2182_; 
v_startInclusive_2181_ = lean_ctor_get(v_slice_2178_, 0);
lean_inc(v_startInclusive_2181_);
v_endExclusive_2182_ = lean_ctor_get(v_slice_2178_, 1);
lean_inc(v_endExclusive_2182_);
lean_dec_ref(v_slice_2178_);
v_it_2154_ = v_nextIt_2180_;
v_startInclusive_2155_ = v_startInclusive_2181_;
v_endExclusive_2156_ = v_endExclusive_2182_;
goto v___jp_2153_;
}
}
}
else
{
lean_object* v___x_2184_; 
lean_del_object(v___x_2148_);
lean_dec(v_searcher_2146_);
v___x_2184_ = lean_box(1);
v_it_2154_ = v___x_2184_;
v_startInclusive_2155_ = v_currPos_2145_;
v_endExclusive_2156_ = v___x_2163_;
goto v___jp_2153_;
}
v___jp_2153_:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2157_ = lean_nat_add(v_startInclusive_2151_, v_startInclusive_2155_);
lean_dec(v_startInclusive_2155_);
v___x_2158_ = lean_nat_add(v_startInclusive_2151_, v_endExclusive_2156_);
lean_dec(v_endExclusive_2156_);
lean_inc_ref(v_str_2150_);
v___x_2159_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2159_, 0, v_str_2150_);
lean_ctor_set(v___x_2159_, 1, v___x_2157_);
lean_ctor_set(v___x_2159_, 2, v___x_2158_);
v___x_2160_ = l_String_Slice_toString(v___x_2159_);
lean_dec_ref_known(v___x_2159_, 3);
v___x_2161_ = lean_array_push(v_b_2144_, v___x_2160_);
v_a_2143_ = v_it_2154_;
v_b_2144_ = v___x_2161_;
goto _start;
}
}
}
else
{
return v_b_2144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg___boxed(lean_object* v_out_2186_, lean_object* v_a_2187_, lean_object* v_b_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_2186_, v_a_2187_, v_b_2188_);
lean_dec_ref(v_out_2186_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(lean_object* v___x_2193_, lean_object* v___x_2194_, lean_object* v___x_2195_, lean_object* v_a_2196_, lean_object* v_b_2197_){
_start:
{
lean_object* v_it_2199_; lean_object* v_startInclusive_2200_; lean_object* v_endExclusive_2201_; 
if (lean_obj_tag(v_a_2196_) == 0)
{
lean_object* v_currPos_2226_; lean_object* v_searcher_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2256_; 
v_currPos_2226_ = lean_ctor_get(v_a_2196_, 0);
v_searcher_2227_ = lean_ctor_get(v_a_2196_, 1);
v_isSharedCheck_2256_ = !lean_is_exclusive(v_a_2196_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2229_ = v_a_2196_;
v_isShared_2230_ = v_isSharedCheck_2256_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_searcher_2227_);
lean_inc(v_currPos_2226_);
lean_dec(v_a_2196_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2256_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v_str_2231_; lean_object* v_startInclusive_2232_; lean_object* v_endExclusive_2233_; lean_object* v___x_2234_; uint8_t v_decide_2235_; 
v_str_2231_ = lean_ctor_get(v___x_2194_, 0);
v_startInclusive_2232_ = lean_ctor_get(v___x_2194_, 1);
v_endExclusive_2233_ = lean_ctor_get(v___x_2194_, 2);
v___x_2234_ = lean_nat_sub(v_endExclusive_2233_, v_startInclusive_2232_);
v_decide_2235_ = lean_nat_dec_eq(v_searcher_2227_, v___x_2234_);
lean_dec(v___x_2234_);
if (v_decide_2235_ == 0)
{
uint32_t v___x_2236_; lean_object* v___x_2237_; uint32_t v___x_2238_; uint8_t v___x_2239_; 
v___x_2236_ = 38;
v___x_2237_ = lean_nat_add(v_startInclusive_2232_, v_searcher_2227_);
v___x_2238_ = lean_string_utf8_get_fast(v_str_2231_, v___x_2237_);
v___x_2239_ = lean_uint32_dec_eq(v___x_2238_, v___x_2236_);
if (v___x_2239_ == 0)
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2243_; 
lean_dec(v_searcher_2227_);
v___x_2240_ = lean_string_utf8_next_fast(v_str_2231_, v___x_2237_);
lean_dec(v___x_2237_);
v___x_2241_ = lean_nat_sub(v___x_2240_, v_startInclusive_2232_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 1, v___x_2241_);
v___x_2243_ = v___x_2229_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_currPos_2226_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v___x_2241_);
v___x_2243_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
v_a_2196_ = v___x_2243_;
goto _start;
}
}
else
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v_slice_2249_; lean_object* v_nextIt_2251_; 
v___x_2246_ = lean_string_utf8_next_fast(v_str_2231_, v___x_2237_);
v___x_2247_ = lean_nat_sub(v___x_2246_, v___x_2237_);
lean_dec(v___x_2237_);
v___x_2248_ = lean_nat_add(v_searcher_2227_, v___x_2247_);
lean_dec(v___x_2247_);
v_slice_2249_ = l_String_Slice_subslice_x21(v___x_2194_, v_currPos_2226_, v_searcher_2227_);
lean_inc(v___x_2248_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 1, v___x_2248_);
lean_ctor_set(v___x_2229_, 0, v___x_2248_);
v_nextIt_2251_ = v___x_2229_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2248_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v___x_2248_);
v_nextIt_2251_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
lean_object* v_startInclusive_2252_; lean_object* v_endExclusive_2253_; 
v_startInclusive_2252_ = lean_ctor_get(v_slice_2249_, 0);
lean_inc(v_startInclusive_2252_);
v_endExclusive_2253_ = lean_ctor_get(v_slice_2249_, 1);
lean_inc(v_endExclusive_2253_);
lean_dec_ref(v_slice_2249_);
v_it_2199_ = v_nextIt_2251_;
v_startInclusive_2200_ = v_startInclusive_2252_;
v_endExclusive_2201_ = v_endExclusive_2253_;
goto v___jp_2198_;
}
}
}
else
{
lean_object* v___x_2255_; 
lean_del_object(v___x_2229_);
lean_dec(v_searcher_2227_);
v___x_2255_ = lean_box(1);
lean_inc(v___x_2195_);
v_it_2199_ = v___x_2255_;
v_startInclusive_2200_ = v_currPos_2226_;
v_endExclusive_2201_ = v___x_2195_;
goto v___jp_2198_;
}
}
}
else
{
lean_object* v___x_2257_; 
lean_dec(v___x_2195_);
lean_dec_ref(v___x_2193_);
v___x_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2257_, 0, v_b_2197_);
return v___x_2257_;
}
v___jp_2198_:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
lean_inc_ref(v___x_2193_);
v___x_2202_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2193_);
lean_ctor_set(v___x_2202_, 1, v_startInclusive_2200_);
lean_ctor_set(v___x_2202_, 2, v_endExclusive_2201_);
v___x_2203_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
v___x_2204_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0));
v___x_2205_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_2202_, v___x_2203_, v___x_2204_);
lean_dec_ref_known(v___x_2202_, 3);
v___x_2206_ = lean_array_to_list(v___x_2205_);
if (lean_obj_tag(v___x_2206_) == 0)
{
v_a_2196_ = v_it_2199_;
goto _start;
}
else
{
lean_object* v_tail_2208_; 
v_tail_2208_ = lean_ctor_get(v___x_2206_, 1);
if (lean_obj_tag(v_tail_2208_) == 0)
{
lean_object* v_head_2209_; lean_object* v___x_2210_; 
v_head_2209_ = lean_ctor_get(v___x_2206_, 0);
lean_inc(v_head_2209_);
lean_dec_ref_known(v___x_2206_, 2);
v___x_2210_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2209_);
lean_dec(v_head_2209_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v___x_2211_; 
lean_dec(v_it_2199_);
lean_dec_ref(v_b_2197_);
lean_dec(v___x_2195_);
lean_dec_ref(v___x_2193_);
v___x_2211_ = lean_box(0);
return v___x_2211_;
}
else
{
lean_object* v_val_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v_val_2212_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_val_2212_);
lean_dec_ref_known(v___x_2210_, 1);
v___x_2213_ = lean_box(0);
v___x_2214_ = l_Std_Http_URI_Query_insertEncoded(v_b_2197_, v_val_2212_, v___x_2213_);
v_a_2196_ = v_it_2199_;
v_b_2197_ = v___x_2214_;
goto _start;
}
}
else
{
lean_object* v_head_2216_; lean_object* v___x_2217_; 
lean_inc(v_tail_2208_);
v_head_2216_ = lean_ctor_get(v___x_2206_, 0);
lean_inc(v_head_2216_);
lean_dec_ref_known(v___x_2206_, 2);
v___x_2217_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2216_);
lean_dec(v_head_2216_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v___x_2218_; 
lean_dec(v_tail_2208_);
lean_dec(v_it_2199_);
lean_dec_ref(v_b_2197_);
lean_dec(v___x_2195_);
lean_dec_ref(v___x_2193_);
v___x_2218_ = lean_box(0);
return v___x_2218_;
}
else
{
lean_object* v_val_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v_val_2219_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_val_2219_);
lean_dec_ref_known(v___x_2217_, 1);
v___x_2220_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1));
v___x_2221_ = l_String_intercalate(v___x_2220_, v_tail_2208_);
v___x_2222_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2221_);
lean_dec_ref(v___x_2221_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v___x_2223_; 
lean_dec(v_val_2219_);
lean_dec(v_it_2199_);
lean_dec_ref(v_b_2197_);
lean_dec(v___x_2195_);
lean_dec_ref(v___x_2193_);
v___x_2223_ = lean_box(0);
return v___x_2223_;
}
else
{
lean_object* v___x_2224_; 
v___x_2224_ = l_Std_Http_URI_Query_insertEncoded(v_b_2197_, v_val_2219_, v___x_2222_);
v_a_2196_ = v_it_2199_;
v_b_2197_ = v___x_2224_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___boxed(lean_object* v___x_2258_, lean_object* v___x_2259_, lean_object* v___x_2260_, lean_object* v_a_2261_, lean_object* v_b_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2258_, v___x_2259_, v___x_2260_, v_a_2261_, v_b_2262_);
lean_dec_ref(v___x_2259_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(lean_object* v___x_2264_, lean_object* v___x_2265_, lean_object* v___x_2266_, lean_object* v_a_2267_, lean_object* v_b_2268_){
_start:
{
lean_object* v_it_2270_; lean_object* v_startInclusive_2271_; lean_object* v_endExclusive_2272_; 
if (lean_obj_tag(v_a_2267_) == 0)
{
lean_object* v_currPos_2297_; lean_object* v_searcher_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2327_; 
v_currPos_2297_ = lean_ctor_get(v_a_2267_, 0);
v_searcher_2298_ = lean_ctor_get(v_a_2267_, 1);
v_isSharedCheck_2327_ = !lean_is_exclusive(v_a_2267_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2300_ = v_a_2267_;
v_isShared_2301_ = v_isSharedCheck_2327_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_searcher_2298_);
lean_inc(v_currPos_2297_);
lean_dec(v_a_2267_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2327_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v_str_2302_; lean_object* v_startInclusive_2303_; lean_object* v_endExclusive_2304_; lean_object* v___x_2305_; uint8_t v_decide_2306_; 
v_str_2302_ = lean_ctor_get(v___x_2265_, 0);
v_startInclusive_2303_ = lean_ctor_get(v___x_2265_, 1);
v_endExclusive_2304_ = lean_ctor_get(v___x_2265_, 2);
v___x_2305_ = lean_nat_sub(v_endExclusive_2304_, v_startInclusive_2303_);
v_decide_2306_ = lean_nat_dec_eq(v_searcher_2298_, v___x_2305_);
lean_dec(v___x_2305_);
if (v_decide_2306_ == 0)
{
lean_object* v___x_2307_; uint32_t v___x_2308_; uint32_t v___x_2309_; uint8_t v___x_2310_; 
v___x_2307_ = lean_nat_add(v_startInclusive_2303_, v_searcher_2298_);
v___x_2308_ = lean_string_utf8_get_fast(v_str_2302_, v___x_2307_);
v___x_2309_ = 38;
v___x_2310_ = lean_uint32_dec_eq(v___x_2308_, v___x_2309_);
if (v___x_2310_ == 0)
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2314_; 
lean_dec(v_searcher_2298_);
v___x_2311_ = lean_string_utf8_next_fast(v_str_2302_, v___x_2307_);
lean_dec(v___x_2307_);
v___x_2312_ = lean_nat_sub(v___x_2311_, v_startInclusive_2303_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 1, v___x_2312_);
v___x_2314_ = v___x_2300_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_currPos_2297_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v___x_2312_);
v___x_2314_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
lean_object* v___x_2315_; 
v___x_2315_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2264_, v___x_2265_, v___x_2266_, v___x_2314_, v_b_2268_);
return v___x_2315_;
}
}
else
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v_slice_2320_; lean_object* v_nextIt_2322_; 
v___x_2317_ = lean_string_utf8_next_fast(v_str_2302_, v___x_2307_);
v___x_2318_ = lean_nat_sub(v___x_2317_, v___x_2307_);
lean_dec(v___x_2307_);
v___x_2319_ = lean_nat_add(v_searcher_2298_, v___x_2318_);
lean_dec(v___x_2318_);
v_slice_2320_ = l_String_Slice_subslice_x21(v___x_2265_, v_currPos_2297_, v_searcher_2298_);
lean_inc(v___x_2319_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 1, v___x_2319_);
lean_ctor_set(v___x_2300_, 0, v___x_2319_);
v_nextIt_2322_ = v___x_2300_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v___x_2319_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v___x_2319_);
v_nextIt_2322_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
lean_object* v_startInclusive_2323_; lean_object* v_endExclusive_2324_; 
v_startInclusive_2323_ = lean_ctor_get(v_slice_2320_, 0);
lean_inc(v_startInclusive_2323_);
v_endExclusive_2324_ = lean_ctor_get(v_slice_2320_, 1);
lean_inc(v_endExclusive_2324_);
lean_dec_ref(v_slice_2320_);
v_it_2270_ = v_nextIt_2322_;
v_startInclusive_2271_ = v_startInclusive_2323_;
v_endExclusive_2272_ = v_endExclusive_2324_;
goto v___jp_2269_;
}
}
}
else
{
lean_object* v___x_2326_; 
lean_del_object(v___x_2300_);
lean_dec(v_searcher_2298_);
v___x_2326_ = lean_box(1);
lean_inc(v___x_2266_);
v_it_2270_ = v___x_2326_;
v_startInclusive_2271_ = v_currPos_2297_;
v_endExclusive_2272_ = v___x_2266_;
goto v___jp_2269_;
}
}
}
else
{
lean_object* v___x_2328_; 
lean_dec(v___x_2266_);
lean_dec_ref(v___x_2264_);
v___x_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2328_, 0, v_b_2268_);
return v___x_2328_;
}
v___jp_2269_:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
lean_inc_ref(v___x_2264_);
v___x_2273_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2264_);
lean_ctor_set(v___x_2273_, 1, v_startInclusive_2271_);
lean_ctor_set(v___x_2273_, 2, v_endExclusive_2272_);
v___x_2274_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
v___x_2275_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0));
v___x_2276_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_2273_, v___x_2274_, v___x_2275_);
lean_dec_ref_known(v___x_2273_, 3);
v___x_2277_ = lean_array_to_list(v___x_2276_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v___x_2278_; 
v___x_2278_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2264_, v___x_2265_, v___x_2266_, v_it_2270_, v_b_2268_);
return v___x_2278_;
}
else
{
lean_object* v_tail_2279_; 
v_tail_2279_ = lean_ctor_get(v___x_2277_, 1);
if (lean_obj_tag(v_tail_2279_) == 0)
{
lean_object* v_head_2280_; lean_object* v___x_2281_; 
v_head_2280_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_head_2280_);
lean_dec_ref_known(v___x_2277_, 2);
v___x_2281_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2280_);
lean_dec(v_head_2280_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v___x_2282_; 
lean_dec(v_it_2270_);
lean_dec_ref(v_b_2268_);
lean_dec(v___x_2266_);
lean_dec_ref(v___x_2264_);
v___x_2282_ = lean_box(0);
return v___x_2282_;
}
else
{
lean_object* v_val_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v_val_2283_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_val_2283_);
lean_dec_ref_known(v___x_2281_, 1);
v___x_2284_ = lean_box(0);
v___x_2285_ = l_Std_Http_URI_Query_insertEncoded(v_b_2268_, v_val_2283_, v___x_2284_);
v___x_2286_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2264_, v___x_2265_, v___x_2266_, v_it_2270_, v___x_2285_);
return v___x_2286_;
}
}
else
{
lean_object* v_head_2287_; lean_object* v___x_2288_; 
lean_inc(v_tail_2279_);
v_head_2287_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_head_2287_);
lean_dec_ref_known(v___x_2277_, 2);
v___x_2288_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2287_);
lean_dec(v_head_2287_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v___x_2289_; 
lean_dec(v_tail_2279_);
lean_dec(v_it_2270_);
lean_dec_ref(v_b_2268_);
lean_dec(v___x_2266_);
lean_dec_ref(v___x_2264_);
v___x_2289_ = lean_box(0);
return v___x_2289_;
}
else
{
lean_object* v_val_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v_val_2290_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_val_2290_);
lean_dec_ref_known(v___x_2288_, 1);
v___x_2291_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1));
v___x_2292_ = l_String_intercalate(v___x_2291_, v_tail_2279_);
v___x_2293_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2292_);
lean_dec_ref(v___x_2292_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v___x_2294_; 
lean_dec(v_val_2290_);
lean_dec(v_it_2270_);
lean_dec_ref(v_b_2268_);
lean_dec(v___x_2266_);
lean_dec_ref(v___x_2264_);
v___x_2294_ = lean_box(0);
return v___x_2294_;
}
else
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = l_Std_Http_URI_Query_insertEncoded(v_b_2268_, v_val_2290_, v___x_2293_);
v___x_2296_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2264_, v___x_2265_, v___x_2266_, v_it_2270_, v___x_2295_);
return v___x_2296_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg___boxed(lean_object* v___x_2329_, lean_object* v___x_2330_, lean_object* v___x_2331_, lean_object* v_a_2332_, lean_object* v_b_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2329_, v___x_2330_, v___x_2331_, v_a_2332_, v_b_2333_);
lean_dec_ref(v___x_2330_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(lean_object* v_config_2340_, lean_object* v_a_2341_){
_start:
{
lean_object* v_maxQueryLength_2342_; lean_object* v_maxQueryParams_2343_; lean_object* v___f_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v_snd_2347_; lean_object* v_fst_2348_; lean_object* v_fst_2349_; lean_object* v_array_2350_; lean_object* v_idx_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2401_; 
v_maxQueryLength_2342_ = lean_ctor_get(v_config_2340_, 4);
lean_inc(v_maxQueryLength_2342_);
v_maxQueryParams_2343_ = lean_ctor_get(v_config_2340_, 8);
lean_inc(v_maxQueryParams_2343_);
lean_dec_ref(v_config_2340_);
v___f_2344_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2345_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2341_);
v___x_2346_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2344_, v_maxQueryLength_2342_, v___x_2345_, v_a_2341_);
lean_dec(v_maxQueryLength_2342_);
v_snd_2347_ = lean_ctor_get(v___x_2346_, 1);
lean_inc(v_snd_2347_);
v_fst_2348_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_fst_2348_);
lean_dec_ref(v___x_2346_);
v_fst_2349_ = lean_ctor_get(v_snd_2347_, 0);
lean_inc(v_fst_2349_);
lean_dec(v_snd_2347_);
v_array_2350_ = lean_ctor_get(v_a_2341_, 0);
v_idx_2351_ = lean_ctor_get(v_a_2341_, 1);
v_isSharedCheck_2401_ = !lean_is_exclusive(v_a_2341_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2353_ = v_a_2341_;
v_isShared_2354_ = v_isSharedCheck_2401_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_idx_2351_);
lean_inc(v_array_2350_);
lean_dec(v_a_2341_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2401_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v_lower_2356_; lean_object* v_upper_2357_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___y_2398_; uint8_t v___x_2400_; 
v___x_2395_ = lean_nat_add(v_idx_2351_, v_fst_2348_);
lean_dec(v_fst_2348_);
v___x_2396_ = lean_byte_array_size(v_array_2350_);
v___x_2400_ = lean_nat_dec_le(v_idx_2351_, v___x_2345_);
if (v___x_2400_ == 0)
{
v___y_2398_ = v_idx_2351_;
goto v___jp_2397_;
}
else
{
lean_dec(v_idx_2351_);
v___y_2398_ = v___x_2345_;
goto v___jp_2397_;
}
v___jp_2355_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; uint8_t v___x_2360_; 
v___x_2358_ = l_ByteArray_toByteSlice(v_array_2350_, v_lower_2356_, v_upper_2357_);
v___x_2359_ = l_ByteSlice_toByteArray(v___x_2358_);
v___x_2360_ = lean_string_validate_utf8(v___x_2359_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2361_; lean_object* v___x_2363_; 
lean_dec_ref(v___x_2359_);
lean_dec(v_maxQueryParams_2343_);
v___x_2361_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2354_ == 0)
{
lean_ctor_set_tag(v___x_2353_, 1);
lean_ctor_set(v___x_2353_, 1, v___x_2361_);
lean_ctor_set(v___x_2353_, 0, v_fst_2349_);
v___x_2363_ = v___x_2353_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_fst_2349_);
lean_ctor_set(v_reuseFailAlloc_2364_, 1, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
else
{
lean_object* v___x_2365_; lean_object* v___x_2366_; uint8_t v___x_2367_; 
v___x_2365_ = lean_string_from_utf8_unchecked(v___x_2359_);
v___x_2366_ = lean_string_utf8_byte_size(v___x_2365_);
v___x_2367_ = lean_nat_dec_eq(v___x_2366_, v___x_2345_);
if (v___x_2367_ == 0)
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; uint8_t v___x_2371_; 
lean_inc_ref(v___x_2365_);
v___x_2368_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2365_);
lean_ctor_set(v___x_2368_, 1, v___x_2345_);
lean_ctor_set(v___x_2368_, 2, v___x_2366_);
v___x_2369_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0);
v___x_2370_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2365_, v___x_2368_, v___x_2366_, v___x_2369_, v___x_2345_);
v___x_2371_ = lean_nat_dec_lt(v_maxQueryParams_2343_, v___x_2370_);
lean_dec(v___x_2370_);
if (v___x_2371_ == 0)
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
lean_dec(v_maxQueryParams_2343_);
v___x_2372_ = l_Std_Http_URI_Query_empty;
v___x_2373_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2365_, v___x_2368_, v___x_2366_, v___x_2369_, v___x_2372_);
lean_dec_ref_known(v___x_2368_, 3);
if (lean_obj_tag(v___x_2373_) == 1)
{
lean_object* v_val_2374_; lean_object* v___x_2376_; 
v_val_2374_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_val_2374_);
lean_dec_ref_known(v___x_2373_, 1);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 1, v_val_2374_);
lean_ctor_set(v___x_2353_, 0, v_fst_2349_);
v___x_2376_ = v___x_2353_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_fst_2349_);
lean_ctor_set(v_reuseFailAlloc_2377_, 1, v_val_2374_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
else
{
lean_object* v___x_2378_; lean_object* v___x_2380_; 
lean_dec(v___x_2373_);
v___x_2378_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2354_ == 0)
{
lean_ctor_set_tag(v___x_2353_, 1);
lean_ctor_set(v___x_2353_, 1, v___x_2378_);
lean_ctor_set(v___x_2353_, 0, v_fst_2349_);
v___x_2380_ = v___x_2353_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_fst_2349_);
lean_ctor_set(v_reuseFailAlloc_2381_, 1, v___x_2378_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
else
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2389_; 
lean_dec_ref_known(v___x_2368_, 3);
lean_dec_ref(v___x_2365_);
v___x_2382_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3));
v___x_2383_ = l_Nat_reprFast(v_maxQueryParams_2343_);
v___x_2384_ = lean_string_append(v___x_2382_, v___x_2383_);
lean_dec_ref(v___x_2383_);
v___x_2385_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_2386_ = lean_string_append(v___x_2384_, v___x_2385_);
v___x_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set_tag(v___x_2353_, 1);
lean_ctor_set(v___x_2353_, 1, v___x_2387_);
lean_ctor_set(v___x_2353_, 0, v_fst_2349_);
v___x_2389_ = v___x_2353_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_fst_2349_);
lean_ctor_set(v_reuseFailAlloc_2390_, 1, v___x_2387_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
else
{
lean_object* v___x_2391_; lean_object* v___x_2393_; 
lean_dec_ref(v___x_2365_);
lean_dec(v_maxQueryParams_2343_);
v___x_2391_ = l_Std_Http_URI_Query_empty;
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 1, v___x_2391_);
lean_ctor_set(v___x_2353_, 0, v_fst_2349_);
v___x_2393_ = v___x_2353_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_fst_2349_);
lean_ctor_set(v_reuseFailAlloc_2394_, 1, v___x_2391_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
v___jp_2397_:
{
uint8_t v___x_2399_; 
v___x_2399_ = lean_nat_dec_le(v___x_2395_, v___x_2396_);
if (v___x_2399_ == 0)
{
lean_dec(v___x_2395_);
v_lower_2356_ = v___y_2398_;
v_upper_2357_ = v___x_2396_;
goto v___jp_2355_;
}
else
{
v_lower_2356_ = v___y_2398_;
v_upper_2357_ = v___x_2395_;
goto v___jp_2355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(lean_object* v___x_2402_, lean_object* v___x_2403_, lean_object* v___x_2404_, lean_object* v_inst_2405_, lean_object* v_R_2406_, lean_object* v_a_2407_, lean_object* v_b_2408_, lean_object* v_c_2409_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2402_, v___x_2403_, v___x_2404_, v_a_2407_, v_b_2408_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___boxed(lean_object* v___x_2411_, lean_object* v___x_2412_, lean_object* v___x_2413_, lean_object* v_inst_2414_, lean_object* v_R_2415_, lean_object* v_a_2416_, lean_object* v_b_2417_, lean_object* v_c_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(v___x_2411_, v___x_2412_, v___x_2413_, v_inst_2414_, v_R_2415_, v_a_2416_, v_b_2417_, v_c_2418_);
lean_dec(v___x_2413_);
lean_dec_ref(v___x_2412_);
lean_dec_ref(v___x_2411_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(lean_object* v_out_2420_, lean_object* v_inst_2421_, lean_object* v_R_2422_, lean_object* v_a_2423_, lean_object* v_b_2424_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_2420_, v_a_2423_, v_b_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___boxed(lean_object* v_out_2426_, lean_object* v_inst_2427_, lean_object* v_R_2428_, lean_object* v_a_2429_, lean_object* v_b_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(v_out_2426_, v_inst_2427_, v_R_2428_, v_a_2429_, v_b_2430_);
lean_dec_ref(v_out_2426_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(lean_object* v___x_2432_, lean_object* v___x_2433_, lean_object* v___x_2434_, lean_object* v_inst_2435_, lean_object* v_R_2436_, lean_object* v_a_2437_, lean_object* v_b_2438_, lean_object* v_c_2439_){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2432_, v___x_2433_, v___x_2434_, v_a_2437_, v_b_2438_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___boxed(lean_object* v___x_2441_, lean_object* v___x_2442_, lean_object* v___x_2443_, lean_object* v_inst_2444_, lean_object* v_R_2445_, lean_object* v_a_2446_, lean_object* v_b_2447_, lean_object* v_c_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(v___x_2441_, v___x_2442_, v___x_2443_, v_inst_2444_, v_R_2445_, v_a_2446_, v_b_2447_, v_c_2448_);
lean_dec_ref(v___x_2442_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(lean_object* v___x_2450_, lean_object* v___x_2451_, lean_object* v___x_2452_, lean_object* v_inst_2453_, lean_object* v_R_2454_, lean_object* v_a_2455_, lean_object* v_b_2456_, lean_object* v_c_2457_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2451_, v___x_2452_, v_a_2455_, v_b_2456_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___boxed(lean_object* v___x_2459_, lean_object* v___x_2460_, lean_object* v___x_2461_, lean_object* v_inst_2462_, lean_object* v_R_2463_, lean_object* v_a_2464_, lean_object* v_b_2465_, lean_object* v_c_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(v___x_2459_, v___x_2460_, v___x_2461_, v_inst_2462_, v_R_2463_, v_a_2464_, v_b_2465_, v_c_2466_);
lean_dec(v___x_2461_);
lean_dec_ref(v___x_2460_);
lean_dec_ref(v___x_2459_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(lean_object* v___x_2468_, lean_object* v___x_2469_, lean_object* v___x_2470_, lean_object* v_inst_2471_, lean_object* v_R_2472_, lean_object* v_a_2473_, lean_object* v_b_2474_, lean_object* v_c_2475_){
_start:
{
lean_object* v___x_2476_; 
v___x_2476_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2468_, v___x_2469_, v___x_2470_, v_a_2473_, v_b_2474_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___boxed(lean_object* v___x_2477_, lean_object* v___x_2478_, lean_object* v___x_2479_, lean_object* v_inst_2480_, lean_object* v_R_2481_, lean_object* v_a_2482_, lean_object* v_b_2483_, lean_object* v_c_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(v___x_2477_, v___x_2478_, v___x_2479_, v_inst_2480_, v_R_2481_, v_a_2482_, v_b_2483_, v_c_2484_);
lean_dec_ref(v___x_2478_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(lean_object* v_config_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v_maxFragmentLength_2491_; lean_object* v___f_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v_snd_2495_; lean_object* v_fst_2496_; lean_object* v_fst_2497_; lean_object* v_array_2498_; lean_object* v_idx_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2523_; 
v_maxFragmentLength_2491_ = lean_ctor_get(v_config_2489_, 5);
v___f_2492_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2493_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2490_);
v___x_2494_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2492_, v_maxFragmentLength_2491_, v___x_2493_, v_a_2490_);
v_snd_2495_ = lean_ctor_get(v___x_2494_, 1);
lean_inc(v_snd_2495_);
v_fst_2496_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_fst_2496_);
lean_dec_ref(v___x_2494_);
v_fst_2497_ = lean_ctor_get(v_snd_2495_, 0);
lean_inc(v_fst_2497_);
lean_dec(v_snd_2495_);
v_array_2498_ = lean_ctor_get(v_a_2490_, 0);
v_idx_2499_ = lean_ctor_get(v_a_2490_, 1);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_a_2490_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2501_ = v_a_2490_;
v_isShared_2502_ = v_isSharedCheck_2523_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_idx_2499_);
lean_inc(v_array_2498_);
lean_dec(v_a_2490_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2523_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v_lower_2504_; lean_object* v_upper_2505_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___y_2520_; uint8_t v___x_2522_; 
v___x_2517_ = lean_nat_add(v_idx_2499_, v_fst_2496_);
lean_dec(v_fst_2496_);
v___x_2518_ = lean_byte_array_size(v_array_2498_);
v___x_2522_ = lean_nat_dec_le(v_idx_2499_, v___x_2493_);
if (v___x_2522_ == 0)
{
v___y_2520_ = v_idx_2499_;
goto v___jp_2519_;
}
else
{
lean_dec(v_idx_2499_);
v___y_2520_ = v___x_2493_;
goto v___jp_2519_;
}
v___jp_2503_:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2506_ = l_ByteArray_toByteSlice(v_array_2498_, v_lower_2504_, v_upper_2505_);
v___x_2507_ = l_ByteSlice_toByteArray(v___x_2506_);
v___x_2508_ = l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(v___x_2507_);
if (lean_obj_tag(v___x_2508_) == 1)
{
lean_object* v_val_2509_; lean_object* v___x_2511_; 
v_val_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_val_2509_);
lean_dec_ref_known(v___x_2508_, 1);
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 1, v_val_2509_);
lean_ctor_set(v___x_2501_, 0, v_fst_2497_);
v___x_2511_ = v___x_2501_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_fst_2497_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v_val_2509_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
else
{
lean_object* v___x_2513_; lean_object* v___x_2515_; 
lean_dec(v___x_2508_);
v___x_2513_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1));
if (v_isShared_2502_ == 0)
{
lean_ctor_set_tag(v___x_2501_, 1);
lean_ctor_set(v___x_2501_, 1, v___x_2513_);
lean_ctor_set(v___x_2501_, 0, v_fst_2497_);
v___x_2515_ = v___x_2501_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_fst_2497_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v___x_2513_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
v___jp_2519_:
{
uint8_t v___x_2521_; 
v___x_2521_ = lean_nat_dec_le(v___x_2517_, v___x_2518_);
if (v___x_2521_ == 0)
{
lean_dec(v___x_2517_);
v_lower_2504_ = v___y_2520_;
v_upper_2505_ = v___x_2518_;
goto v___jp_2503_;
}
else
{
v_lower_2504_ = v___y_2520_;
v_upper_2505_ = v___x_2517_;
goto v___jp_2503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___boxed(lean_object* v_config_2524_, lean_object* v_a_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2524_, v_a_2525_);
lean_dec_ref(v_config_2524_);
return v_res_2526_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1(void){
_start:
{
lean_object* v___x_2528_; lean_object* v_utf8_2529_; 
v___x_2528_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0));
v_utf8_2529_ = lean_string_to_utf8(v___x_2528_);
return v_utf8_2529_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(lean_object* v_config_2530_, lean_object* v_a_2531_){
_start:
{
uint8_t v___y_2533_; lean_object* v_pos_2534_; lean_object* v_res_2535_; uint8_t v___y_2557_; lean_object* v___y_2558_; lean_object* v_err_2559_; lean_object* v_pos_2565_; lean_object* v_utf8_2573_; lean_object* v___x_2574_; 
v_utf8_2573_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1);
lean_inc_ref(v_a_2531_);
v___x_2574_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_2573_, v_a_2531_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_pos_2575_; 
lean_dec_ref(v_a_2531_);
v_pos_2575_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_pos_2575_);
lean_dec_ref_known(v___x_2574_, 2);
v_pos_2565_ = v_pos_2575_;
goto v___jp_2564_;
}
else
{
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_pos_2576_; 
lean_dec_ref(v_a_2531_);
v_pos_2576_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_pos_2576_);
lean_dec_ref_known(v___x_2574_, 2);
v_pos_2565_ = v_pos_2576_;
goto v___jp_2564_;
}
else
{
lean_object* v_err_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2608_; 
v_err_2577_ = lean_ctor_get(v___x_2574_, 1);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2608_ == 0)
{
lean_object* v_unused_2609_; 
v_unused_2609_ = lean_ctor_get(v___x_2574_, 0);
lean_dec(v_unused_2609_);
v___x_2579_ = v___x_2574_;
v_isShared_2580_ = v_isSharedCheck_2608_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_err_2577_);
lean_dec(v___x_2574_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2608_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v_idx_2581_; uint8_t v___x_2582_; 
v_idx_2581_ = lean_ctor_get(v_a_2531_, 1);
v___x_2582_ = lean_nat_dec_eq(v_idx_2581_, v_idx_2581_);
if (v___x_2582_ == 0)
{
lean_object* v___x_2584_; 
lean_dec_ref(v_config_2530_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v_a_2531_);
v___x_2584_ = v___x_2579_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2531_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v_err_2577_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
else
{
uint8_t v___x_2586_; lean_object* v___x_2587_; 
lean_del_object(v___x_2579_);
lean_dec(v_err_2577_);
v___x_2586_ = 0;
v___x_2587_ = l_Std_Http_URI_Parser_parsePath(v_config_2530_, v___x_2586_, v___x_2582_, v_a_2531_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_pos_2588_; lean_object* v_res_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2598_; 
v_pos_2588_ = lean_ctor_get(v___x_2587_, 0);
v_res_2589_ = lean_ctor_get(v___x_2587_, 1);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2591_ = v___x_2587_;
v_isShared_2592_ = v_isSharedCheck_2598_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_res_2589_);
lean_inc(v_pos_2588_);
lean_dec(v___x_2587_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2598_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2596_; 
v___x_2593_ = lean_box(0);
v___x_2594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
lean_ctor_set(v___x_2594_, 1, v_res_2589_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 1, v___x_2594_);
v___x_2596_ = v___x_2591_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_pos_2588_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
else
{
lean_object* v_pos_2599_; lean_object* v_err_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
v_pos_2599_ = lean_ctor_get(v___x_2587_, 0);
v_err_2600_ = lean_ctor_get(v___x_2587_, 1);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2587_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_err_2600_);
lean_inc(v_pos_2599_);
lean_dec(v___x_2587_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_pos_2599_);
lean_ctor_set(v_reuseFailAlloc_2606_, 1, v_err_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
}
}
}
v___jp_2532_:
{
lean_object* v___x_2536_; 
v___x_2536_ = l_Std_Http_URI_Parser_parsePath(v_config_2530_, v___y_2533_, v___y_2533_, v_pos_2534_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_pos_2537_; lean_object* v_res_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2546_; 
v_pos_2537_ = lean_ctor_get(v___x_2536_, 0);
v_res_2538_ = lean_ctor_get(v___x_2536_, 1);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2540_ = v___x_2536_;
v_isShared_2541_ = v_isSharedCheck_2546_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_res_2538_);
lean_inc(v_pos_2537_);
lean_dec(v___x_2536_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2546_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2542_; lean_object* v___x_2544_; 
v___x_2542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2542_, 0, v_res_2535_);
lean_ctor_set(v___x_2542_, 1, v_res_2538_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 1, v___x_2542_);
v___x_2544_ = v___x_2540_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_pos_2537_);
lean_ctor_set(v_reuseFailAlloc_2545_, 1, v___x_2542_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
else
{
lean_object* v_pos_2547_; lean_object* v_err_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2555_; 
lean_dec(v_res_2535_);
v_pos_2547_ = lean_ctor_get(v___x_2536_, 0);
v_err_2548_ = lean_ctor_get(v___x_2536_, 1);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2550_ = v___x_2536_;
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_err_2548_);
lean_inc(v_pos_2547_);
lean_dec(v___x_2536_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2553_; 
if (v_isShared_2551_ == 0)
{
v___x_2553_ = v___x_2550_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_pos_2547_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v_err_2548_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
}
v___jp_2556_:
{
lean_object* v_idx_2560_; uint8_t v___x_2561_; 
v_idx_2560_ = lean_ctor_get(v___y_2558_, 1);
v___x_2561_ = lean_nat_dec_eq(v_idx_2560_, v_idx_2560_);
if (v___x_2561_ == 0)
{
lean_object* v___x_2562_; 
lean_dec_ref(v_config_2530_);
v___x_2562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___y_2558_);
lean_ctor_set(v___x_2562_, 1, v_err_2559_);
return v___x_2562_;
}
else
{
lean_object* v___x_2563_; 
lean_dec(v_err_2559_);
v___x_2563_ = lean_box(0);
v___y_2533_ = v___y_2557_;
v_pos_2534_ = v___y_2558_;
v_res_2535_ = v___x_2563_;
goto v___jp_2532_;
}
}
v___jp_2564_:
{
uint8_t v___x_2566_; lean_object* v___x_2567_; 
v___x_2566_ = 1;
lean_inc_ref(v_pos_2565_);
v___x_2567_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_2530_, v_pos_2565_);
if (lean_obj_tag(v___x_2567_) == 0)
{
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_pos_2568_; lean_object* v_res_2569_; lean_object* v___x_2570_; 
lean_dec_ref(v_pos_2565_);
v_pos_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc(v_pos_2568_);
v_res_2569_ = lean_ctor_get(v___x_2567_, 1);
lean_inc(v_res_2569_);
lean_dec_ref_known(v___x_2567_, 2);
v___x_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2570_, 0, v_res_2569_);
v___y_2533_ = v___x_2566_;
v_pos_2534_ = v_pos_2568_;
v_res_2535_ = v___x_2570_;
goto v___jp_2532_;
}
else
{
lean_object* v_err_2571_; 
v_err_2571_ = lean_ctor_get(v___x_2567_, 1);
lean_inc(v_err_2571_);
lean_dec_ref_known(v___x_2567_, 2);
v___y_2557_ = v___x_2566_;
v___y_2558_ = v_pos_2565_;
v_err_2559_ = v_err_2571_;
goto v___jp_2556_;
}
}
else
{
lean_object* v_err_2572_; 
v_err_2572_ = lean_ctor_get(v___x_2567_, 1);
lean_inc(v_err_2572_);
lean_dec_ref_known(v___x_2567_, 2);
v___y_2557_ = v___x_2566_;
v___y_2558_ = v_pos_2565_;
v_err_2559_ = v_err_2572_;
goto v___jp_2556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURI(lean_object* v_config_2619_, lean_object* v_a_2620_){
_start:
{
lean_object* v___x_2621_; 
v___x_2621_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_2619_, v_a_2620_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_pos_2622_; lean_object* v_res_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2754_; 
v_pos_2622_ = lean_ctor_get(v___x_2621_, 0);
v_res_2623_ = lean_ctor_get(v___x_2621_, 1);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2625_ = v___x_2621_;
v_isShared_2626_ = v_isSharedCheck_2754_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_res_2623_);
lean_inc(v_pos_2622_);
lean_dec(v___x_2621_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2754_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v_array_2627_; lean_object* v_idx_2628_; lean_object* v___x_2629_; uint8_t v___x_2630_; 
v_array_2627_ = lean_ctor_get(v_pos_2622_, 0);
v_idx_2628_ = lean_ctor_get(v_pos_2622_, 1);
v___x_2629_ = lean_byte_array_size(v_array_2627_);
v___x_2630_ = lean_nat_dec_lt(v_idx_2628_, v___x_2629_);
if (v___x_2630_ == 0)
{
lean_object* v___x_2631_; lean_object* v___x_2633_; 
lean_dec(v_res_2623_);
lean_dec_ref(v_config_2619_);
v___x_2631_ = lean_box(0);
if (v_isShared_2626_ == 0)
{
lean_ctor_set_tag(v___x_2625_, 1);
lean_ctor_set(v___x_2625_, 1, v___x_2631_);
v___x_2633_ = v___x_2625_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_pos_2622_);
lean_ctor_set(v_reuseFailAlloc_2634_, 1, v___x_2631_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
else
{
uint8_t v___x_2635_; uint8_t v_got_2636_; uint8_t v___x_2637_; 
v___x_2635_ = 58;
v_got_2636_ = lean_byte_array_fget(v_array_2627_, v_idx_2628_);
v___x_2637_ = lean_uint8_dec_eq(v_got_2636_, v___x_2635_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2638_; lean_object* v___x_2640_; 
lean_dec(v_res_2623_);
lean_dec_ref(v_config_2619_);
v___x_2638_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_2626_ == 0)
{
lean_ctor_set_tag(v___x_2625_, 1);
lean_ctor_set(v___x_2625_, 1, v___x_2638_);
v___x_2640_ = v___x_2625_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_pos_2622_);
lean_ctor_set(v_reuseFailAlloc_2641_, 1, v___x_2638_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
else
{
lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2751_; 
lean_inc(v_idx_2628_);
lean_inc_ref(v_array_2627_);
v_isSharedCheck_2751_ = !lean_is_exclusive(v_pos_2622_);
if (v_isSharedCheck_2751_ == 0)
{
lean_object* v_unused_2752_; lean_object* v_unused_2753_; 
v_unused_2752_ = lean_ctor_get(v_pos_2622_, 1);
lean_dec(v_unused_2752_);
v_unused_2753_ = lean_ctor_get(v_pos_2622_, 0);
lean_dec(v_unused_2753_);
v___x_2643_ = v_pos_2622_;
v_isShared_2644_ = v_isSharedCheck_2751_;
goto v_resetjp_2642_;
}
else
{
lean_dec(v_pos_2622_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2751_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2648_; 
v___x_2645_ = lean_unsigned_to_nat(1u);
v___x_2646_ = lean_nat_add(v_idx_2628_, v___x_2645_);
lean_dec(v_idx_2628_);
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 1, v___x_2646_);
v___x_2648_ = v___x_2643_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_array_2627_);
lean_ctor_set(v_reuseFailAlloc_2750_, 1, v___x_2646_);
v___x_2648_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
lean_object* v___x_2649_; 
lean_inc_ref(v_config_2619_);
v___x_2649_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2619_, v___x_2648_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_res_2650_; lean_object* v_pos_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2740_; 
v_res_2650_ = lean_ctor_get(v___x_2649_, 1);
v_pos_2651_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2653_ = v___x_2649_;
v_isShared_2654_ = v_isSharedCheck_2740_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_res_2650_);
lean_inc(v_pos_2651_);
lean_dec(v___x_2649_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2740_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v_fst_2655_; lean_object* v_snd_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2739_; 
v_fst_2655_ = lean_ctor_get(v_res_2650_, 0);
v_snd_2656_ = lean_ctor_get(v_res_2650_, 1);
v_isSharedCheck_2739_ = !lean_is_exclusive(v_res_2650_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2658_ = v_res_2650_;
v_isShared_2659_ = v_isSharedCheck_2739_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_snd_2656_);
lean_inc(v_fst_2655_);
lean_dec(v_res_2650_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2739_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___y_2661_; lean_object* v_pos_2662_; lean_object* v_res_2663_; lean_object* v_idx_2669_; lean_object* v___y_2670_; lean_object* v_pos_2671_; lean_object* v_err_2672_; lean_object* v_pos_2680_; lean_object* v_array_2681_; lean_object* v_idx_2682_; lean_object* v_res_2683_; lean_object* v_array_2702_; lean_object* v_idx_2703_; lean_object* v_pos_2705_; lean_object* v_array_2706_; lean_object* v_idx_2707_; lean_object* v_err_2708_; lean_object* v___x_2712_; uint8_t v___x_2713_; 
v_array_2702_ = lean_ctor_get(v_pos_2651_, 0);
lean_inc_ref(v_array_2702_);
v_idx_2703_ = lean_ctor_get(v_pos_2651_, 1);
lean_inc(v_idx_2703_);
v___x_2712_ = lean_byte_array_size(v_array_2702_);
v___x_2713_ = lean_nat_dec_lt(v_idx_2703_, v___x_2712_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2714_; 
v___x_2714_ = lean_box(0);
lean_inc(v_idx_2703_);
v_pos_2705_ = v_pos_2651_;
v_array_2706_ = v_array_2702_;
v_idx_2707_ = v_idx_2703_;
v_err_2708_ = v___x_2714_;
goto v___jp_2704_;
}
else
{
uint8_t v___x_2715_; uint8_t v_got_2716_; uint8_t v___x_2717_; 
v___x_2715_ = 63;
v_got_2716_ = lean_byte_array_fget(v_array_2702_, v_idx_2703_);
v___x_2717_ = lean_uint8_dec_eq(v_got_2716_, v___x_2715_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2718_; 
v___x_2718_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_2703_);
v_pos_2705_ = v_pos_2651_;
v_array_2706_ = v_array_2702_;
v_idx_2707_ = v_idx_2703_;
v_err_2708_ = v___x_2718_;
goto v___jp_2704_;
}
else
{
lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2736_; 
v_isSharedCheck_2736_ = !lean_is_exclusive(v_pos_2651_);
if (v_isSharedCheck_2736_ == 0)
{
lean_object* v_unused_2737_; lean_object* v_unused_2738_; 
v_unused_2737_ = lean_ctor_get(v_pos_2651_, 1);
lean_dec(v_unused_2737_);
v_unused_2738_ = lean_ctor_get(v_pos_2651_, 0);
lean_dec(v_unused_2738_);
v___x_2720_ = v_pos_2651_;
v_isShared_2721_ = v_isSharedCheck_2736_;
goto v_resetjp_2719_;
}
else
{
lean_dec(v_pos_2651_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2736_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2722_; lean_object* v___x_2724_; 
v___x_2722_ = lean_nat_add(v_idx_2703_, v___x_2645_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 1, v___x_2722_);
v___x_2724_ = v___x_2720_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_array_2702_);
lean_ctor_set(v_reuseFailAlloc_2735_, 1, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
lean_object* v___x_2725_; 
lean_inc_ref(v_config_2619_);
v___x_2725_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2619_, v___x_2724_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_pos_2726_; lean_object* v_res_2727_; lean_object* v_array_2728_; lean_object* v_idx_2729_; lean_object* v___x_2730_; 
lean_dec(v_idx_2703_);
v_pos_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_pos_2726_);
v_res_2727_ = lean_ctor_get(v___x_2725_, 1);
lean_inc(v_res_2727_);
lean_dec_ref_known(v___x_2725_, 2);
v_array_2728_ = lean_ctor_get(v_pos_2726_, 0);
lean_inc_ref(v_array_2728_);
v_idx_2729_ = lean_ctor_get(v_pos_2726_, 1);
lean_inc(v_idx_2729_);
v___x_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2730_, 0, v_res_2727_);
v_pos_2680_ = v_pos_2726_;
v_array_2681_ = v_array_2728_;
v_idx_2682_ = v_idx_2729_;
v_res_2683_ = v___x_2730_;
goto v___jp_2679_;
}
else
{
lean_object* v_pos_2731_; lean_object* v_err_2732_; lean_object* v_array_2733_; lean_object* v_idx_2734_; 
v_pos_2731_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_pos_2731_);
v_err_2732_ = lean_ctor_get(v___x_2725_, 1);
lean_inc(v_err_2732_);
lean_dec_ref_known(v___x_2725_, 2);
v_array_2733_ = lean_ctor_get(v_pos_2731_, 0);
lean_inc_ref(v_array_2733_);
v_idx_2734_ = lean_ctor_get(v_pos_2731_, 1);
lean_inc(v_idx_2734_);
v_pos_2705_ = v_pos_2731_;
v_array_2706_ = v_array_2733_;
v_idx_2707_ = v_idx_2734_;
v_err_2708_ = v_err_2732_;
goto v___jp_2704_;
}
}
}
}
}
v___jp_2660_:
{
lean_object* v___x_2664_; lean_object* v___x_2666_; 
v___x_2664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2664_, 0, v_res_2623_);
lean_ctor_set(v___x_2664_, 1, v_fst_2655_);
lean_ctor_set(v___x_2664_, 2, v_snd_2656_);
lean_ctor_set(v___x_2664_, 3, v___y_2661_);
lean_ctor_set(v___x_2664_, 4, v_res_2663_);
if (v_isShared_2654_ == 0)
{
lean_ctor_set(v___x_2653_, 1, v___x_2664_);
lean_ctor_set(v___x_2653_, 0, v_pos_2662_);
v___x_2666_ = v___x_2653_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_pos_2662_);
lean_ctor_set(v_reuseFailAlloc_2667_, 1, v___x_2664_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
v___jp_2668_:
{
lean_object* v_idx_2673_; uint8_t v___x_2674_; 
v_idx_2673_ = lean_ctor_get(v_pos_2671_, 1);
v___x_2674_ = lean_nat_dec_eq(v_idx_2669_, v_idx_2673_);
lean_dec(v_idx_2669_);
if (v___x_2674_ == 0)
{
lean_object* v___x_2676_; 
lean_dec(v___y_2670_);
lean_dec(v_snd_2656_);
lean_dec(v_fst_2655_);
lean_del_object(v___x_2653_);
lean_dec(v_res_2623_);
if (v_isShared_2626_ == 0)
{
lean_ctor_set_tag(v___x_2625_, 1);
lean_ctor_set(v___x_2625_, 1, v_err_2672_);
lean_ctor_set(v___x_2625_, 0, v_pos_2671_);
v___x_2676_ = v___x_2625_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_pos_2671_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_err_2672_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
else
{
lean_object* v___x_2678_; 
lean_dec(v_err_2672_);
lean_del_object(v___x_2625_);
v___x_2678_ = lean_box(0);
v___y_2661_ = v___y_2670_;
v_pos_2662_ = v_pos_2671_;
v_res_2663_ = v___x_2678_;
goto v___jp_2660_;
}
}
v___jp_2679_:
{
lean_object* v___x_2684_; uint8_t v___x_2685_; 
v___x_2684_ = lean_byte_array_size(v_array_2681_);
v___x_2685_ = lean_nat_dec_lt(v_idx_2682_, v___x_2684_);
if (v___x_2685_ == 0)
{
lean_object* v___x_2686_; 
lean_dec_ref(v_array_2681_);
lean_del_object(v___x_2658_);
lean_dec_ref(v_config_2619_);
v___x_2686_ = lean_box(0);
v_idx_2669_ = v_idx_2682_;
v___y_2670_ = v_res_2683_;
v_pos_2671_ = v_pos_2680_;
v_err_2672_ = v___x_2686_;
goto v___jp_2668_;
}
else
{
uint8_t v___x_2687_; uint8_t v_got_2688_; uint8_t v___x_2689_; 
v___x_2687_ = 35;
v_got_2688_ = lean_byte_array_fget(v_array_2681_, v_idx_2682_);
v___x_2689_ = lean_uint8_dec_eq(v_got_2688_, v___x_2687_);
if (v___x_2689_ == 0)
{
lean_object* v___x_2690_; 
lean_dec_ref(v_array_2681_);
lean_del_object(v___x_2658_);
lean_dec_ref(v_config_2619_);
v___x_2690_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v_idx_2669_ = v_idx_2682_;
v___y_2670_ = v_res_2683_;
v_pos_2671_ = v_pos_2680_;
v_err_2672_ = v___x_2690_;
goto v___jp_2668_;
}
else
{
lean_object* v___x_2691_; lean_object* v___x_2693_; 
lean_dec_ref(v_pos_2680_);
v___x_2691_ = lean_nat_add(v_idx_2682_, v___x_2645_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 1, v___x_2691_);
lean_ctor_set(v___x_2658_, 0, v_array_2681_);
v___x_2693_ = v___x_2658_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_array_2681_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v___x_2691_);
v___x_2693_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
lean_object* v___x_2694_; 
v___x_2694_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2619_, v___x_2693_);
lean_dec_ref(v_config_2619_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_pos_2695_; lean_object* v_res_2696_; lean_object* v___x_2697_; 
v_pos_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_pos_2695_);
v_res_2696_ = lean_ctor_get(v___x_2694_, 1);
lean_inc(v_res_2696_);
lean_dec_ref_known(v___x_2694_, 2);
v___x_2697_ = l_Std_Http_URI_EncodedFragment_decode(v_res_2696_);
lean_dec(v_res_2696_);
if (lean_obj_tag(v___x_2697_) == 1)
{
lean_dec(v_idx_2682_);
lean_del_object(v___x_2625_);
v___y_2661_ = v_res_2683_;
v_pos_2662_ = v_pos_2695_;
v_res_2663_ = v___x_2697_;
goto v___jp_2660_;
}
else
{
lean_object* v___x_2698_; 
lean_dec(v___x_2697_);
v___x_2698_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__3));
v_idx_2669_ = v_idx_2682_;
v___y_2670_ = v_res_2683_;
v_pos_2671_ = v_pos_2695_;
v_err_2672_ = v___x_2698_;
goto v___jp_2668_;
}
}
else
{
lean_object* v_pos_2699_; lean_object* v_err_2700_; 
v_pos_2699_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_pos_2699_);
v_err_2700_ = lean_ctor_get(v___x_2694_, 1);
lean_inc(v_err_2700_);
lean_dec_ref_known(v___x_2694_, 2);
v_idx_2669_ = v_idx_2682_;
v___y_2670_ = v_res_2683_;
v_pos_2671_ = v_pos_2699_;
v_err_2672_ = v_err_2700_;
goto v___jp_2668_;
}
}
}
}
}
v___jp_2704_:
{
uint8_t v___x_2709_; 
v___x_2709_ = lean_nat_dec_eq(v_idx_2703_, v_idx_2707_);
lean_dec(v_idx_2703_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2710_; 
lean_dec(v_idx_2707_);
lean_dec_ref(v_array_2706_);
lean_del_object(v___x_2658_);
lean_dec(v_snd_2656_);
lean_dec(v_fst_2655_);
lean_del_object(v___x_2653_);
lean_del_object(v___x_2625_);
lean_dec(v_res_2623_);
lean_dec_ref(v_config_2619_);
v___x_2710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2710_, 0, v_pos_2705_);
lean_ctor_set(v___x_2710_, 1, v_err_2708_);
return v___x_2710_;
}
else
{
lean_object* v___x_2711_; 
lean_dec(v_err_2708_);
v___x_2711_ = lean_box(0);
v_pos_2680_ = v_pos_2705_;
v_array_2681_ = v_array_2706_;
v_idx_2682_ = v_idx_2707_;
v_res_2683_ = v___x_2711_;
goto v___jp_2679_;
}
}
}
}
}
else
{
lean_object* v_pos_2741_; lean_object* v_err_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
lean_del_object(v___x_2625_);
lean_dec(v_res_2623_);
lean_dec_ref(v_config_2619_);
v_pos_2741_ = lean_ctor_get(v___x_2649_, 0);
v_err_2742_ = lean_ctor_get(v___x_2649_, 1);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2744_ = v___x_2649_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_err_2742_);
lean_inc(v_pos_2741_);
lean_dec(v___x_2649_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2747_; 
if (v_isShared_2745_ == 0)
{
v___x_2747_ = v___x_2744_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_pos_2741_);
lean_ctor_set(v_reuseFailAlloc_2748_, 1, v_err_2742_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
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
lean_object* v_pos_2755_; lean_object* v_err_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
lean_dec_ref(v_config_2619_);
v_pos_2755_ = lean_ctor_get(v___x_2621_, 0);
v_err_2756_ = lean_ctor_get(v___x_2621_, 1);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2621_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_err_2756_);
lean_inc(v_pos_2755_);
lean_dec(v___x_2621_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_pos_2755_);
lean_ctor_set(v_reuseFailAlloc_2762_, 1, v_err_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(lean_object* v_a_2767_){
_start:
{
lean_object* v_array_2768_; lean_object* v_idx_2769_; lean_object* v___x_2770_; uint8_t v___x_2771_; 
v_array_2768_ = lean_ctor_get(v_a_2767_, 0);
v_idx_2769_ = lean_ctor_get(v_a_2767_, 1);
v___x_2770_ = lean_byte_array_size(v_array_2768_);
v___x_2771_ = lean_nat_dec_lt(v_idx_2769_, v___x_2770_);
if (v___x_2771_ == 0)
{
lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2772_ = lean_box(0);
v___x_2773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2773_, 0, v_a_2767_);
lean_ctor_set(v___x_2773_, 1, v___x_2772_);
return v___x_2773_;
}
else
{
uint8_t v___x_2774_; uint8_t v_got_2775_; uint8_t v___x_2776_; 
v___x_2774_ = 42;
v_got_2775_ = lean_byte_array_fget(v_array_2768_, v_idx_2769_);
v___x_2776_ = lean_uint8_dec_eq(v_got_2775_, v___x_2774_);
if (v___x_2776_ == 0)
{
lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2777_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1));
v___x_2778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2778_, 0, v_a_2767_);
lean_ctor_set(v___x_2778_, 1, v___x_2777_);
return v___x_2778_;
}
else
{
lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2789_; 
lean_inc(v_idx_2769_);
lean_inc_ref(v_array_2768_);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_a_2767_);
if (v_isSharedCheck_2789_ == 0)
{
lean_object* v_unused_2790_; lean_object* v_unused_2791_; 
v_unused_2790_ = lean_ctor_get(v_a_2767_, 1);
lean_dec(v_unused_2790_);
v_unused_2791_ = lean_ctor_get(v_a_2767_, 0);
lean_dec(v_unused_2791_);
v___x_2780_ = v_a_2767_;
v_isShared_2781_ = v_isSharedCheck_2789_;
goto v_resetjp_2779_;
}
else
{
lean_dec(v_a_2767_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2789_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2785_; 
v___x_2782_ = lean_unsigned_to_nat(1u);
v___x_2783_ = lean_nat_add(v_idx_2769_, v___x_2782_);
lean_dec(v_idx_2769_);
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 1, v___x_2783_);
v___x_2785_ = v___x_2780_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_array_2768_);
lean_ctor_set(v_reuseFailAlloc_2788_, 1, v___x_2783_);
v___x_2785_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2786_ = lean_box(3);
v___x_2787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2785_);
lean_ctor_set(v___x_2787_, 1, v___x_2786_);
return v___x_2787_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(lean_object* v_config_2795_, lean_object* v_a_2796_){
_start:
{
lean_object* v_array_2800_; lean_object* v_idx_2801_; lean_object* v___x_2802_; uint8_t v___x_2803_; 
v_array_2800_ = lean_ctor_get(v_a_2796_, 0);
v_idx_2801_ = lean_ctor_get(v_a_2796_, 1);
v___x_2802_ = lean_byte_array_size(v_array_2800_);
v___x_2803_ = lean_nat_dec_lt(v_idx_2801_, v___x_2802_);
if (v___x_2803_ == 0)
{
lean_dec_ref(v_config_2795_);
goto v___jp_2797_;
}
else
{
uint8_t v___x_2804_; uint8_t v___x_2805_; uint8_t v___x_2806_; 
v___x_2804_ = lean_byte_array_fget(v_array_2800_, v_idx_2801_);
v___x_2805_ = 47;
v___x_2806_ = lean_uint8_dec_eq(v___x_2804_, v___x_2805_);
if (v___x_2806_ == 0)
{
lean_dec_ref(v_config_2795_);
goto v___jp_2797_;
}
else
{
lean_object* v___x_2807_; 
lean_inc_ref(v_a_2796_);
lean_inc_ref(v_config_2795_);
v___x_2807_ = l_Std_Http_URI_Parser_parsePath(v_config_2795_, v___x_2806_, v___x_2806_, v_a_2796_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_pos_2808_; lean_object* v_res_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2854_; 
v_pos_2808_ = lean_ctor_get(v___x_2807_, 0);
v_res_2809_ = lean_ctor_get(v___x_2807_, 1);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2811_ = v___x_2807_;
v_isShared_2812_ = v_isSharedCheck_2854_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_res_2809_);
lean_inc(v_pos_2808_);
lean_dec(v___x_2807_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2854_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v_pos_2814_; lean_object* v_res_2815_; lean_object* v_array_2820_; lean_object* v_idx_2821_; lean_object* v_pos_2823_; lean_object* v_idx_2824_; lean_object* v_err_2825_; lean_object* v___x_2829_; uint8_t v___x_2830_; 
v_array_2820_ = lean_ctor_get(v_pos_2808_, 0);
v_idx_2821_ = lean_ctor_get(v_pos_2808_, 1);
lean_inc(v_idx_2821_);
v___x_2829_ = lean_byte_array_size(v_array_2820_);
v___x_2830_ = lean_nat_dec_lt(v_idx_2821_, v___x_2829_);
if (v___x_2830_ == 0)
{
lean_object* v___x_2831_; 
lean_dec_ref(v_config_2795_);
v___x_2831_ = lean_box(0);
lean_inc(v_idx_2821_);
v_pos_2823_ = v_pos_2808_;
v_idx_2824_ = v_idx_2821_;
v_err_2825_ = v___x_2831_;
goto v___jp_2822_;
}
else
{
uint8_t v___x_2832_; uint8_t v_got_2833_; uint8_t v___x_2834_; 
v___x_2832_ = 63;
v_got_2833_ = lean_byte_array_fget(v_array_2820_, v_idx_2821_);
v___x_2834_ = lean_uint8_dec_eq(v_got_2833_, v___x_2832_);
if (v___x_2834_ == 0)
{
lean_object* v___x_2835_; 
lean_dec_ref(v_config_2795_);
v___x_2835_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_2821_);
v_pos_2823_ = v_pos_2808_;
v_idx_2824_ = v_idx_2821_;
v_err_2825_ = v___x_2835_;
goto v___jp_2822_;
}
else
{
lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2851_; 
lean_inc_ref(v_array_2820_);
v_isSharedCheck_2851_ = !lean_is_exclusive(v_pos_2808_);
if (v_isSharedCheck_2851_ == 0)
{
lean_object* v_unused_2852_; lean_object* v_unused_2853_; 
v_unused_2852_ = lean_ctor_get(v_pos_2808_, 1);
lean_dec(v_unused_2852_);
v_unused_2853_ = lean_ctor_get(v_pos_2808_, 0);
lean_dec(v_unused_2853_);
v___x_2837_ = v_pos_2808_;
v_isShared_2838_ = v_isSharedCheck_2851_;
goto v_resetjp_2836_;
}
else
{
lean_dec(v_pos_2808_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2851_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2842_; 
v___x_2839_ = lean_unsigned_to_nat(1u);
v___x_2840_ = lean_nat_add(v_idx_2821_, v___x_2839_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 1, v___x_2840_);
v___x_2842_ = v___x_2837_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_array_2820_);
lean_ctor_set(v_reuseFailAlloc_2850_, 1, v___x_2840_);
v___x_2842_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
lean_object* v___x_2843_; 
v___x_2843_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2795_, v___x_2842_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_pos_2844_; lean_object* v_res_2845_; lean_object* v___x_2846_; 
lean_dec(v_idx_2821_);
lean_dec_ref(v_a_2796_);
v_pos_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_pos_2844_);
v_res_2845_ = lean_ctor_get(v___x_2843_, 1);
lean_inc(v_res_2845_);
lean_dec_ref_known(v___x_2843_, 2);
v___x_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2846_, 0, v_res_2845_);
v_pos_2814_ = v_pos_2844_;
v_res_2815_ = v___x_2846_;
goto v___jp_2813_;
}
else
{
lean_object* v_pos_2847_; lean_object* v_err_2848_; lean_object* v_idx_2849_; 
v_pos_2847_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_pos_2847_);
v_err_2848_ = lean_ctor_get(v___x_2843_, 1);
lean_inc(v_err_2848_);
lean_dec_ref_known(v___x_2843_, 2);
v_idx_2849_ = lean_ctor_get(v_pos_2847_, 1);
lean_inc(v_idx_2849_);
v_pos_2823_ = v_pos_2847_;
v_idx_2824_ = v_idx_2849_;
v_err_2825_ = v_err_2848_;
goto v___jp_2822_;
}
}
}
}
}
v___jp_2813_:
{
lean_object* v___x_2816_; lean_object* v___x_2818_; 
v___x_2816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2816_, 0, v_res_2809_);
lean_ctor_set(v___x_2816_, 1, v_res_2815_);
if (v_isShared_2812_ == 0)
{
lean_ctor_set(v___x_2811_, 1, v___x_2816_);
lean_ctor_set(v___x_2811_, 0, v_pos_2814_);
v___x_2818_ = v___x_2811_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_pos_2814_);
lean_ctor_set(v_reuseFailAlloc_2819_, 1, v___x_2816_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
v___jp_2822_:
{
uint8_t v___x_2826_; 
v___x_2826_ = lean_nat_dec_eq(v_idx_2821_, v_idx_2824_);
lean_dec(v_idx_2824_);
lean_dec(v_idx_2821_);
if (v___x_2826_ == 0)
{
lean_object* v___x_2827_; 
lean_dec_ref(v_pos_2823_);
lean_del_object(v___x_2811_);
lean_dec(v_res_2809_);
v___x_2827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2827_, 0, v_a_2796_);
lean_ctor_set(v___x_2827_, 1, v_err_2825_);
return v___x_2827_;
}
else
{
lean_object* v___x_2828_; 
lean_dec(v_err_2825_);
lean_dec_ref(v_a_2796_);
v___x_2828_ = lean_box(0);
v_pos_2814_ = v_pos_2823_;
v_res_2815_ = v___x_2828_;
goto v___jp_2813_;
}
}
}
}
else
{
lean_object* v_err_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
lean_dec_ref(v_config_2795_);
v_err_2855_ = lean_ctor_get(v___x_2807_, 1);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2862_ == 0)
{
lean_object* v_unused_2863_; 
v_unused_2863_ = lean_ctor_get(v___x_2807_, 0);
lean_dec(v_unused_2863_);
v___x_2857_ = v___x_2807_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_err_2855_);
lean_dec(v___x_2807_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 0, v_a_2796_);
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2796_);
lean_ctor_set(v_reuseFailAlloc_2861_, 1, v_err_2855_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
}
v___jp_2797_:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2798_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1));
v___x_2799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2799_, 0, v_a_2796_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
return v___x_2799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(lean_object* v_config_2864_, lean_object* v_scheme_2865_, lean_object* v_a_2866_){
_start:
{
lean_object* v_array_2867_; lean_object* v_idx_2868_; lean_object* v___x_2869_; uint8_t v___x_2870_; 
v_array_2867_ = lean_ctor_get(v_a_2866_, 0);
v_idx_2868_ = lean_ctor_get(v_a_2866_, 1);
v___x_2869_ = lean_byte_array_size(v_array_2867_);
v___x_2870_ = lean_nat_dec_lt(v_idx_2868_, v___x_2869_);
if (v___x_2870_ == 0)
{
lean_object* v___x_2871_; lean_object* v___x_2872_; 
lean_dec_ref(v_scheme_2865_);
lean_dec_ref(v_config_2864_);
v___x_2871_ = lean_box(0);
v___x_2872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2872_, 0, v_a_2866_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
return v___x_2872_;
}
else
{
uint8_t v___x_2873_; uint8_t v_got_2874_; uint8_t v___x_2875_; 
v___x_2873_ = 58;
v_got_2874_ = lean_byte_array_fget(v_array_2867_, v_idx_2868_);
v___x_2875_ = lean_uint8_dec_eq(v_got_2874_, v___x_2873_);
if (v___x_2875_ == 0)
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
lean_dec_ref(v_scheme_2865_);
lean_dec_ref(v_config_2864_);
v___x_2876_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
v___x_2877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2877_, 0, v_a_2866_);
lean_ctor_set(v___x_2877_, 1, v___x_2876_);
return v___x_2877_;
}
else
{
lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2952_; 
lean_inc(v_idx_2868_);
lean_inc_ref(v_array_2867_);
v_isSharedCheck_2952_ = !lean_is_exclusive(v_a_2866_);
if (v_isSharedCheck_2952_ == 0)
{
lean_object* v_unused_2953_; lean_object* v_unused_2954_; 
v_unused_2953_ = lean_ctor_get(v_a_2866_, 1);
lean_dec(v_unused_2953_);
v_unused_2954_ = lean_ctor_get(v_a_2866_, 0);
lean_dec(v_unused_2954_);
v___x_2879_ = v_a_2866_;
v_isShared_2880_ = v_isSharedCheck_2952_;
goto v_resetjp_2878_;
}
else
{
lean_dec(v_a_2866_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2952_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2884_; 
v___x_2881_ = lean_unsigned_to_nat(1u);
v___x_2882_ = lean_nat_add(v_idx_2868_, v___x_2881_);
lean_dec(v_idx_2868_);
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 1, v___x_2882_);
v___x_2884_ = v___x_2879_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_array_2867_);
lean_ctor_set(v_reuseFailAlloc_2951_, 1, v___x_2882_);
v___x_2884_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
lean_object* v___x_2885_; 
lean_inc_ref(v_config_2864_);
v___x_2885_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2864_, v___x_2884_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_res_2886_; lean_object* v_pos_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2941_; 
v_res_2886_ = lean_ctor_get(v___x_2885_, 1);
v_pos_2887_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2889_ = v___x_2885_;
v_isShared_2890_ = v_isSharedCheck_2941_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_res_2886_);
lean_inc(v_pos_2887_);
lean_dec(v___x_2885_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2941_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v_fst_2891_; lean_object* v_snd_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2940_; 
v_fst_2891_ = lean_ctor_get(v_res_2886_, 0);
v_snd_2892_ = lean_ctor_get(v_res_2886_, 1);
v_isSharedCheck_2940_ = !lean_is_exclusive(v_res_2886_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2894_ = v_res_2886_;
v_isShared_2895_ = v_isSharedCheck_2940_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_snd_2892_);
lean_inc(v_fst_2891_);
lean_dec(v_res_2886_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2940_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v_pos_2897_; lean_object* v_res_2898_; lean_object* v_array_2905_; lean_object* v_idx_2906_; lean_object* v_pos_2908_; lean_object* v_idx_2909_; lean_object* v_err_2910_; lean_object* v___x_2916_; uint8_t v___x_2917_; 
v_array_2905_ = lean_ctor_get(v_pos_2887_, 0);
v_idx_2906_ = lean_ctor_get(v_pos_2887_, 1);
lean_inc(v_idx_2906_);
v___x_2916_ = lean_byte_array_size(v_array_2905_);
v___x_2917_ = lean_nat_dec_lt(v_idx_2906_, v___x_2916_);
if (v___x_2917_ == 0)
{
lean_object* v___x_2918_; 
lean_dec_ref(v_config_2864_);
v___x_2918_ = lean_box(0);
lean_inc(v_idx_2906_);
v_pos_2908_ = v_pos_2887_;
v_idx_2909_ = v_idx_2906_;
v_err_2910_ = v___x_2918_;
goto v___jp_2907_;
}
else
{
uint8_t v___x_2919_; uint8_t v_got_2920_; uint8_t v___x_2921_; 
v___x_2919_ = 63;
v_got_2920_ = lean_byte_array_fget(v_array_2905_, v_idx_2906_);
v___x_2921_ = lean_uint8_dec_eq(v_got_2920_, v___x_2919_);
if (v___x_2921_ == 0)
{
lean_object* v___x_2922_; 
lean_dec_ref(v_config_2864_);
v___x_2922_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_2906_);
v_pos_2908_ = v_pos_2887_;
v_idx_2909_ = v_idx_2906_;
v_err_2910_ = v___x_2922_;
goto v___jp_2907_;
}
else
{
lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2937_; 
lean_inc_ref(v_array_2905_);
v_isSharedCheck_2937_ = !lean_is_exclusive(v_pos_2887_);
if (v_isSharedCheck_2937_ == 0)
{
lean_object* v_unused_2938_; lean_object* v_unused_2939_; 
v_unused_2938_ = lean_ctor_get(v_pos_2887_, 1);
lean_dec(v_unused_2938_);
v_unused_2939_ = lean_ctor_get(v_pos_2887_, 0);
lean_dec(v_unused_2939_);
v___x_2924_ = v_pos_2887_;
v_isShared_2925_ = v_isSharedCheck_2937_;
goto v_resetjp_2923_;
}
else
{
lean_dec(v_pos_2887_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2937_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2926_; lean_object* v___x_2928_; 
v___x_2926_ = lean_nat_add(v_idx_2906_, v___x_2881_);
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 1, v___x_2926_);
v___x_2928_ = v___x_2924_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_array_2905_);
lean_ctor_set(v_reuseFailAlloc_2936_, 1, v___x_2926_);
v___x_2928_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
lean_object* v___x_2929_; 
v___x_2929_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2864_, v___x_2928_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v_pos_2930_; lean_object* v_res_2931_; lean_object* v___x_2932_; 
lean_dec(v_idx_2906_);
lean_del_object(v___x_2894_);
v_pos_2930_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_pos_2930_);
v_res_2931_ = lean_ctor_get(v___x_2929_, 1);
lean_inc(v_res_2931_);
lean_dec_ref_known(v___x_2929_, 2);
v___x_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2932_, 0, v_res_2931_);
v_pos_2897_ = v_pos_2930_;
v_res_2898_ = v___x_2932_;
goto v___jp_2896_;
}
else
{
lean_object* v_pos_2933_; lean_object* v_err_2934_; lean_object* v_idx_2935_; 
v_pos_2933_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_pos_2933_);
v_err_2934_ = lean_ctor_get(v___x_2929_, 1);
lean_inc(v_err_2934_);
lean_dec_ref_known(v___x_2929_, 2);
v_idx_2935_ = lean_ctor_get(v_pos_2933_, 1);
lean_inc(v_idx_2935_);
v_pos_2908_ = v_pos_2933_;
v_idx_2909_ = v_idx_2935_;
v_err_2910_ = v_err_2934_;
goto v___jp_2907_;
}
}
}
}
}
v___jp_2896_:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2903_; 
v___x_2899_ = lean_box(0);
v___x_2900_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2900_, 0, v_scheme_2865_);
lean_ctor_set(v___x_2900_, 1, v_fst_2891_);
lean_ctor_set(v___x_2900_, 2, v_snd_2892_);
lean_ctor_set(v___x_2900_, 3, v_res_2898_);
lean_ctor_set(v___x_2900_, 4, v___x_2899_);
v___x_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2900_);
if (v_isShared_2890_ == 0)
{
lean_ctor_set(v___x_2889_, 1, v___x_2901_);
lean_ctor_set(v___x_2889_, 0, v_pos_2897_);
v___x_2903_ = v___x_2889_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_pos_2897_);
lean_ctor_set(v_reuseFailAlloc_2904_, 1, v___x_2901_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
v___jp_2907_:
{
uint8_t v___x_2911_; 
v___x_2911_ = lean_nat_dec_eq(v_idx_2906_, v_idx_2909_);
lean_dec(v_idx_2909_);
lean_dec(v_idx_2906_);
if (v___x_2911_ == 0)
{
lean_object* v___x_2913_; 
lean_dec(v_snd_2892_);
lean_dec(v_fst_2891_);
lean_del_object(v___x_2889_);
lean_dec_ref(v_scheme_2865_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set_tag(v___x_2894_, 1);
lean_ctor_set(v___x_2894_, 1, v_err_2910_);
lean_ctor_set(v___x_2894_, 0, v_pos_2908_);
v___x_2913_ = v___x_2894_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_pos_2908_);
lean_ctor_set(v_reuseFailAlloc_2914_, 1, v_err_2910_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
else
{
lean_object* v___x_2915_; 
lean_dec(v_err_2910_);
lean_del_object(v___x_2894_);
v___x_2915_ = lean_box(0);
v_pos_2897_ = v_pos_2908_;
v_res_2898_ = v___x_2915_;
goto v___jp_2896_;
}
}
}
}
}
else
{
lean_object* v_pos_2942_; lean_object* v_err_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
lean_dec_ref(v_scheme_2865_);
lean_dec_ref(v_config_2864_);
v_pos_2942_ = lean_ctor_get(v___x_2885_, 0);
v_err_2943_ = lean_ctor_get(v___x_2885_, 1);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2945_ = v___x_2885_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_err_2943_);
lean_inc(v_pos_2942_);
lean_dec(v___x_2885_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_pos_2942_);
lean_ctor_set(v_reuseFailAlloc_2949_, 1, v_err_2943_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(lean_object* v_config_2963_, lean_object* v_a_2964_){
_start:
{
lean_object* v___x_2968_; 
lean_inc_ref(v_a_2964_);
v___x_2968_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_2963_, v_a_2964_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_pos_2969_; lean_object* v_res_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_3066_; 
v_pos_2969_ = lean_ctor_get(v___x_2968_, 0);
v_res_2970_ = lean_ctor_get(v___x_2968_, 1);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_2972_ = v___x_2968_;
v_isShared_2973_ = v_isSharedCheck_3066_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_res_2970_);
lean_inc(v_pos_2969_);
lean_dec(v___x_2968_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_3066_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v_pos_2977_; lean_object* v_res_2978_; lean_object* v_idx_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v_pos_2989_; lean_object* v_idx_2990_; lean_object* v_err_2991_; lean_object* v___x_3060_; uint8_t v___x_3061_; 
v___x_3060_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2));
v___x_3061_ = lean_string_dec_eq(v_res_2970_, v___x_3060_);
if (v___x_3061_ == 0)
{
lean_object* v___x_3062_; uint8_t v___x_3063_; 
v___x_3062_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3));
v___x_3063_ = lean_string_dec_eq(v_res_2970_, v___x_3062_);
if (v___x_3063_ == 0)
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
lean_del_object(v___x_2972_);
lean_dec(v_res_2970_);
lean_dec(v_pos_2969_);
lean_dec_ref(v_config_2963_);
v___x_3064_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5));
v___x_3065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3065_, 0, v_a_2964_);
lean_ctor_set(v___x_3065_, 1, v___x_3064_);
return v___x_3065_;
}
else
{
goto v___jp_2995_;
}
}
else
{
goto v___jp_2995_;
}
v___jp_2974_:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2983_; 
v___x_2979_ = lean_box(0);
v___x_2980_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2980_, 0, v_res_2970_);
lean_ctor_set(v___x_2980_, 1, v___y_2976_);
lean_ctor_set(v___x_2980_, 2, v___y_2975_);
lean_ctor_set(v___x_2980_, 3, v_res_2978_);
lean_ctor_set(v___x_2980_, 4, v___x_2979_);
v___x_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2980_);
if (v_isShared_2973_ == 0)
{
lean_ctor_set(v___x_2972_, 1, v___x_2981_);
lean_ctor_set(v___x_2972_, 0, v_pos_2977_);
v___x_2983_ = v___x_2972_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_pos_2977_);
lean_ctor_set(v_reuseFailAlloc_2984_, 1, v___x_2981_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
v___jp_2985_:
{
uint8_t v___x_2992_; 
v___x_2992_ = lean_nat_dec_eq(v_idx_2986_, v_idx_2990_);
lean_dec(v_idx_2990_);
lean_dec(v_idx_2986_);
if (v___x_2992_ == 0)
{
lean_object* v___x_2993_; 
lean_dec_ref(v_pos_2989_);
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_del_object(v___x_2972_);
lean_dec(v_res_2970_);
v___x_2993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2993_, 0, v_a_2964_);
lean_ctor_set(v___x_2993_, 1, v_err_2991_);
return v___x_2993_;
}
else
{
lean_object* v___x_2994_; 
lean_dec(v_err_2991_);
lean_dec_ref(v_a_2964_);
v___x_2994_ = lean_box(0);
v___y_2975_ = v___y_2987_;
v___y_2976_ = v___y_2988_;
v_pos_2977_ = v_pos_2989_;
v_res_2978_ = v___x_2994_;
goto v___jp_2974_;
}
}
v___jp_2995_:
{
lean_object* v_array_2996_; lean_object* v_idx_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3059_; 
v_array_2996_ = lean_ctor_get(v_pos_2969_, 0);
v_idx_2997_ = lean_ctor_get(v_pos_2969_, 1);
v_isSharedCheck_3059_ = !lean_is_exclusive(v_pos_2969_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_2999_ = v_pos_2969_;
v_isShared_3000_ = v_isSharedCheck_3059_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_idx_2997_);
lean_inc(v_array_2996_);
lean_dec(v_pos_2969_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3059_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3001_; uint8_t v___x_3002_; 
v___x_3001_ = lean_byte_array_size(v_array_2996_);
v___x_3002_ = lean_nat_dec_lt(v_idx_2997_, v___x_3001_);
if (v___x_3002_ == 0)
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
lean_del_object(v___x_2999_);
lean_dec(v_idx_2997_);
lean_dec_ref(v_array_2996_);
lean_del_object(v___x_2972_);
lean_dec(v_res_2970_);
lean_dec_ref(v_config_2963_);
v___x_3003_ = lean_box(0);
v___x_3004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3004_, 0, v_a_2964_);
lean_ctor_set(v___x_3004_, 1, v___x_3003_);
return v___x_3004_;
}
else
{
uint8_t v___x_3005_; uint8_t v_got_3006_; uint8_t v___x_3007_; 
v___x_3005_ = 58;
v_got_3006_ = lean_byte_array_fget(v_array_2996_, v_idx_2997_);
v___x_3007_ = lean_uint8_dec_eq(v_got_3006_, v___x_3005_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; lean_object* v___x_3009_; 
lean_del_object(v___x_2999_);
lean_dec(v_idx_2997_);
lean_dec_ref(v_array_2996_);
lean_del_object(v___x_2972_);
lean_dec(v_res_2970_);
lean_dec_ref(v_config_2963_);
v___x_3008_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
v___x_3009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3009_, 0, v_a_2964_);
lean_ctor_set(v___x_3009_, 1, v___x_3008_);
return v___x_3009_;
}
else
{
lean_object* v___x_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; 
v___x_3010_ = lean_unsigned_to_nat(1u);
v___x_3011_ = lean_nat_add(v_idx_2997_, v___x_3010_);
lean_dec(v_idx_2997_);
v___x_3012_ = lean_nat_dec_lt(v___x_3011_, v___x_3001_);
if (v___x_3012_ == 0)
{
lean_dec(v___x_3011_);
lean_del_object(v___x_2999_);
lean_dec_ref(v_array_2996_);
lean_del_object(v___x_2972_);
lean_dec(v_res_2970_);
lean_dec_ref(v_config_2963_);
goto v___jp_2965_;
}
else
{
uint8_t v___x_3013_; uint8_t v___x_3014_; uint8_t v___x_3015_; 
v___x_3013_ = lean_byte_array_fget(v_array_2996_, v___x_3011_);
v___x_3014_ = 47;
v___x_3015_ = lean_uint8_dec_eq(v___x_3013_, v___x_3014_);
if (v___x_3015_ == 0)
{
lean_dec(v___x_3011_);
lean_del_object(v___x_2999_);
lean_dec_ref(v_array_2996_);
lean_del_object(v___x_2972_);
lean_dec(v_res_2970_);
lean_dec_ref(v_config_2963_);
goto v___jp_2965_;
}
else
{
lean_object* v___x_3017_; 
if (v_isShared_3000_ == 0)
{
lean_ctor_set(v___x_2999_, 1, v___x_3011_);
v___x_3017_ = v___x_2999_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_array_2996_);
lean_ctor_set(v_reuseFailAlloc_3058_, 1, v___x_3011_);
v___x_3017_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
lean_object* v___x_3018_; 
lean_inc_ref(v_config_2963_);
v___x_3018_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2963_, v___x_3017_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_res_3019_; lean_object* v_pos_3020_; lean_object* v_fst_3021_; lean_object* v_snd_3022_; lean_object* v_array_3023_; lean_object* v_idx_3024_; lean_object* v___x_3025_; uint8_t v___x_3026_; 
v_res_3019_ = lean_ctor_get(v___x_3018_, 1);
lean_inc(v_res_3019_);
v_pos_3020_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_pos_3020_);
lean_dec_ref_known(v___x_3018_, 2);
v_fst_3021_ = lean_ctor_get(v_res_3019_, 0);
lean_inc(v_fst_3021_);
v_snd_3022_ = lean_ctor_get(v_res_3019_, 1);
lean_inc(v_snd_3022_);
lean_dec(v_res_3019_);
v_array_3023_ = lean_ctor_get(v_pos_3020_, 0);
v_idx_3024_ = lean_ctor_get(v_pos_3020_, 1);
lean_inc(v_idx_3024_);
v___x_3025_ = lean_byte_array_size(v_array_3023_);
v___x_3026_ = lean_nat_dec_lt(v_idx_3024_, v___x_3025_);
if (v___x_3026_ == 0)
{
lean_object* v___x_3027_; 
lean_dec_ref(v_config_2963_);
v___x_3027_ = lean_box(0);
lean_inc(v_idx_3024_);
v_idx_2986_ = v_idx_3024_;
v___y_2987_ = v_snd_3022_;
v___y_2988_ = v_fst_3021_;
v_pos_2989_ = v_pos_3020_;
v_idx_2990_ = v_idx_3024_;
v_err_2991_ = v___x_3027_;
goto v___jp_2985_;
}
else
{
uint8_t v___x_3028_; uint8_t v_got_3029_; uint8_t v___x_3030_; 
v___x_3028_ = 63;
v_got_3029_ = lean_byte_array_fget(v_array_3023_, v_idx_3024_);
v___x_3030_ = lean_uint8_dec_eq(v_got_3029_, v___x_3028_);
if (v___x_3030_ == 0)
{
lean_object* v___x_3031_; 
lean_dec_ref(v_config_2963_);
v___x_3031_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_3024_);
v_idx_2986_ = v_idx_3024_;
v___y_2987_ = v_snd_3022_;
v___y_2988_ = v_fst_3021_;
v_pos_2989_ = v_pos_3020_;
v_idx_2990_ = v_idx_3024_;
v_err_2991_ = v___x_3031_;
goto v___jp_2985_;
}
else
{
lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3046_; 
lean_inc_ref(v_array_3023_);
v_isSharedCheck_3046_ = !lean_is_exclusive(v_pos_3020_);
if (v_isSharedCheck_3046_ == 0)
{
lean_object* v_unused_3047_; lean_object* v_unused_3048_; 
v_unused_3047_ = lean_ctor_get(v_pos_3020_, 1);
lean_dec(v_unused_3047_);
v_unused_3048_ = lean_ctor_get(v_pos_3020_, 0);
lean_dec(v_unused_3048_);
v___x_3033_ = v_pos_3020_;
v_isShared_3034_ = v_isSharedCheck_3046_;
goto v_resetjp_3032_;
}
else
{
lean_dec(v_pos_3020_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3046_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3035_; lean_object* v___x_3037_; 
v___x_3035_ = lean_nat_add(v_idx_3024_, v___x_3010_);
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 1, v___x_3035_);
v___x_3037_ = v___x_3033_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_array_3023_);
lean_ctor_set(v_reuseFailAlloc_3045_, 1, v___x_3035_);
v___x_3037_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
lean_object* v___x_3038_; 
v___x_3038_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2963_, v___x_3037_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_pos_3039_; lean_object* v_res_3040_; lean_object* v___x_3041_; 
lean_dec(v_idx_3024_);
lean_dec_ref(v_a_2964_);
v_pos_3039_ = lean_ctor_get(v___x_3038_, 0);
lean_inc(v_pos_3039_);
v_res_3040_ = lean_ctor_get(v___x_3038_, 1);
lean_inc(v_res_3040_);
lean_dec_ref_known(v___x_3038_, 2);
v___x_3041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3041_, 0, v_res_3040_);
v___y_2975_ = v_snd_3022_;
v___y_2976_ = v_fst_3021_;
v_pos_2977_ = v_pos_3039_;
v_res_2978_ = v___x_3041_;
goto v___jp_2974_;
}
else
{
lean_object* v_pos_3042_; lean_object* v_err_3043_; lean_object* v_idx_3044_; 
v_pos_3042_ = lean_ctor_get(v___x_3038_, 0);
lean_inc(v_pos_3042_);
v_err_3043_ = lean_ctor_get(v___x_3038_, 1);
lean_inc(v_err_3043_);
lean_dec_ref_known(v___x_3038_, 2);
v_idx_3044_ = lean_ctor_get(v_pos_3042_, 1);
lean_inc(v_idx_3044_);
v_idx_2986_ = v_idx_3024_;
v___y_2987_ = v_snd_3022_;
v___y_2988_ = v_fst_3021_;
v_pos_2989_ = v_pos_3042_;
v_idx_2990_ = v_idx_3044_;
v_err_2991_ = v_err_3043_;
goto v___jp_2985_;
}
}
}
}
}
}
else
{
lean_object* v_err_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
lean_del_object(v___x_2972_);
lean_dec(v_res_2970_);
lean_dec_ref(v_config_2963_);
v_err_3049_ = lean_ctor_get(v___x_3018_, 1);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3056_ == 0)
{
lean_object* v_unused_3057_; 
v_unused_3057_ = lean_ctor_get(v___x_3018_, 0);
lean_dec(v_unused_3057_);
v___x_3051_ = v___x_3018_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_err_3049_);
lean_dec(v___x_3018_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 0, v_a_2964_);
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_2964_);
lean_ctor_set(v_reuseFailAlloc_3055_, 1, v_err_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
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
lean_object* v_err_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
lean_dec_ref(v_config_2963_);
v_err_3067_ = lean_ctor_get(v___x_2968_, 1);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_3074_ == 0)
{
lean_object* v_unused_3075_; 
v_unused_3075_ = lean_ctor_get(v___x_2968_, 0);
lean_dec(v_unused_3075_);
v___x_3069_ = v___x_2968_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_err_3067_);
lean_dec(v___x_2968_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 0, v_a_2964_);
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_2964_);
lean_ctor_set(v_reuseFailAlloc_3073_, 1, v_err_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
v___jp_2965_:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2966_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1));
v___x_2967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2967_, 0, v_a_2964_);
lean_ctor_set(v___x_2967_, 1, v___x_2966_);
return v___x_2967_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(lean_object* v_config_3076_, lean_object* v_a_3077_){
_start:
{
lean_object* v___x_3078_; 
lean_inc_ref(v_a_3077_);
v___x_3078_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3076_, v_a_3077_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v_pos_3079_; lean_object* v_res_3080_; lean_object* v___x_3081_; 
v_pos_3079_ = lean_ctor_get(v___x_3078_, 0);
lean_inc(v_pos_3079_);
v_res_3080_ = lean_ctor_get(v___x_3078_, 1);
lean_inc(v_res_3080_);
lean_dec_ref_known(v___x_3078_, 2);
v___x_3081_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(v_config_3076_, v_res_3080_, v_pos_3079_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_dec_ref(v_a_3077_);
return v___x_3081_;
}
else
{
lean_object* v_err_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3089_; 
v_err_3082_ = lean_ctor_get(v___x_3081_, 1);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3089_ == 0)
{
lean_object* v_unused_3090_; 
v_unused_3090_ = lean_ctor_get(v___x_3081_, 0);
lean_dec(v_unused_3090_);
v___x_3084_ = v___x_3081_;
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_err_3082_);
lean_dec(v___x_3081_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3087_; 
if (v_isShared_3085_ == 0)
{
lean_ctor_set(v___x_3084_, 0, v_a_3077_);
v___x_3087_ = v___x_3084_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_a_3077_);
lean_ctor_set(v_reuseFailAlloc_3088_, 1, v_err_3082_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
}
else
{
lean_object* v_err_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
lean_dec_ref(v_config_3076_);
v_err_3091_ = lean_ctor_get(v___x_3078_, 1);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3098_ == 0)
{
lean_object* v_unused_3099_; 
v_unused_3099_ = lean_ctor_get(v___x_3078_, 0);
lean_dec(v_unused_3099_);
v___x_3093_ = v___x_3078_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_err_3091_);
lean_dec(v___x_3078_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 0, v_a_3077_);
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3077_);
lean_ctor_set(v_reuseFailAlloc_3097_, 1, v_err_3091_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(lean_object* v_config_3100_, lean_object* v_a_3101_){
_start:
{
lean_object* v___x_3102_; 
lean_inc_ref(v_a_3101_);
v___x_3102_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_3100_, v_a_3101_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_pos_3103_; lean_object* v_res_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3156_; 
v_pos_3103_ = lean_ctor_get(v___x_3102_, 0);
v_res_3104_ = lean_ctor_get(v___x_3102_, 1);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3106_ = v___x_3102_;
v_isShared_3107_ = v_isSharedCheck_3156_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_res_3104_);
lean_inc(v_pos_3103_);
lean_dec(v___x_3102_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3156_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v_array_3108_; lean_object* v_idx_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3155_; 
v_array_3108_ = lean_ctor_get(v_pos_3103_, 0);
v_idx_3109_ = lean_ctor_get(v_pos_3103_, 1);
v_isSharedCheck_3155_ = !lean_is_exclusive(v_pos_3103_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3111_ = v_pos_3103_;
v_isShared_3112_ = v_isSharedCheck_3155_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_idx_3109_);
lean_inc(v_array_3108_);
lean_dec(v_pos_3103_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3155_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3113_; uint8_t v___x_3114_; 
v___x_3113_ = lean_byte_array_size(v_array_3108_);
v___x_3114_ = lean_nat_dec_lt(v_idx_3109_, v___x_3113_);
if (v___x_3114_ == 0)
{
lean_object* v___x_3115_; lean_object* v___x_3117_; 
lean_del_object(v___x_3111_);
lean_dec(v_idx_3109_);
lean_dec_ref(v_array_3108_);
lean_dec(v_res_3104_);
v___x_3115_ = lean_box(0);
if (v_isShared_3107_ == 0)
{
lean_ctor_set_tag(v___x_3106_, 1);
lean_ctor_set(v___x_3106_, 1, v___x_3115_);
lean_ctor_set(v___x_3106_, 0, v_a_3101_);
v___x_3117_ = v___x_3106_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3101_);
lean_ctor_set(v_reuseFailAlloc_3118_, 1, v___x_3115_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
else
{
uint8_t v___x_3119_; uint8_t v_got_3120_; uint8_t v___x_3121_; 
v___x_3119_ = 58;
v_got_3120_ = lean_byte_array_fget(v_array_3108_, v_idx_3109_);
v___x_3121_ = lean_uint8_dec_eq(v_got_3120_, v___x_3119_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; lean_object* v___x_3124_; 
lean_del_object(v___x_3111_);
lean_dec(v_idx_3109_);
lean_dec_ref(v_array_3108_);
lean_dec(v_res_3104_);
v___x_3122_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_3107_ == 0)
{
lean_ctor_set_tag(v___x_3106_, 1);
lean_ctor_set(v___x_3106_, 1, v___x_3122_);
lean_ctor_set(v___x_3106_, 0, v_a_3101_);
v___x_3124_ = v___x_3106_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3101_);
lean_ctor_set(v_reuseFailAlloc_3125_, 1, v___x_3122_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
else
{
lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3129_; 
lean_del_object(v___x_3106_);
v___x_3126_ = lean_unsigned_to_nat(1u);
v___x_3127_ = lean_nat_add(v_idx_3109_, v___x_3126_);
lean_dec(v_idx_3109_);
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 1, v___x_3127_);
v___x_3129_ = v___x_3111_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_array_3108_);
lean_ctor_set(v_reuseFailAlloc_3154_, 1, v___x_3127_);
v___x_3129_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
lean_object* v___x_3130_; 
v___x_3130_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_3129_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_pos_3131_; lean_object* v_res_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3144_; 
lean_dec_ref(v_a_3101_);
v_pos_3131_ = lean_ctor_get(v___x_3130_, 0);
v_res_3132_ = lean_ctor_get(v___x_3130_, 1);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3134_ = v___x_3130_;
v_isShared_3135_ = v_isSharedCheck_3144_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_res_3132_);
lean_inc(v_pos_3131_);
lean_dec(v___x_3130_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3144_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; uint16_t v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3142_; 
v___x_3136_ = lean_box(0);
v___x_3137_ = lean_alloc_ctor(2, 0, 2);
v___x_3138_ = lean_unbox(v_res_3132_);
lean_dec(v_res_3132_);
lean_ctor_set_uint16(v___x_3137_, 0, v___x_3138_);
v___x_3139_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3136_);
lean_ctor_set(v___x_3139_, 1, v_res_3104_);
lean_ctor_set(v___x_3139_, 2, v___x_3137_);
v___x_3140_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3139_);
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 1, v___x_3140_);
v___x_3142_ = v___x_3134_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_pos_3131_);
lean_ctor_set(v_reuseFailAlloc_3143_, 1, v___x_3140_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
else
{
lean_object* v_err_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
lean_dec(v_res_3104_);
v_err_3145_ = lean_ctor_get(v___x_3130_, 1);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3152_ == 0)
{
lean_object* v_unused_3153_; 
v_unused_3153_ = lean_ctor_get(v___x_3130_, 0);
lean_dec(v_unused_3153_);
v___x_3147_ = v___x_3130_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_err_3145_);
lean_dec(v___x_3130_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 0, v_a_3101_);
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3101_);
lean_ctor_set(v_reuseFailAlloc_3151_, 1, v_err_3145_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
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
lean_object* v_err_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3164_; 
v_err_3157_ = lean_ctor_get(v___x_3102_, 1);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3164_ == 0)
{
lean_object* v_unused_3165_; 
v_unused_3165_ = lean_ctor_get(v___x_3102_, 0);
lean_dec(v_unused_3165_);
v___x_3159_ = v___x_3102_;
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_err_3157_);
lean_dec(v___x_3102_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3162_; 
if (v_isShared_3160_ == 0)
{
lean_ctor_set(v___x_3159_, 0, v_a_3101_);
v___x_3162_ = v___x_3159_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_a_3101_);
lean_ctor_set(v_reuseFailAlloc_3163_, 1, v_err_3157_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority___boxed(lean_object* v_config_3166_, lean_object* v_a_3167_){
_start:
{
lean_object* v_res_3168_; 
v_res_3168_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3166_, v_a_3167_);
lean_dec_ref(v_config_3166_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object* v_config_3169_, lean_object* v_a_3170_){
_start:
{
lean_object* v___x_3171_; 
lean_inc_ref(v_a_3170_);
v___x_3171_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(v_a_3170_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_dec_ref(v_a_3170_);
lean_dec_ref(v_config_3169_);
return v___x_3171_;
}
else
{
lean_object* v_pos_3172_; lean_object* v_idx_3173_; lean_object* v_idx_3174_; uint8_t v___x_3175_; 
v_pos_3172_ = lean_ctor_get(v___x_3171_, 0);
v_idx_3173_ = lean_ctor_get(v_a_3170_, 1);
lean_inc(v_idx_3173_);
lean_dec_ref(v_a_3170_);
v_idx_3174_ = lean_ctor_get(v_pos_3172_, 1);
v___x_3175_ = lean_nat_dec_eq(v_idx_3173_, v_idx_3174_);
lean_dec(v_idx_3173_);
if (v___x_3175_ == 0)
{
lean_dec_ref(v_config_3169_);
return v___x_3171_;
}
else
{
lean_object* v___x_3176_; 
lean_inc(v_idx_3174_);
lean_inc(v_pos_3172_);
lean_dec_ref_known(v___x_3171_, 2);
lean_inc_ref(v_config_3169_);
v___x_3176_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(v_config_3169_, v_pos_3172_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_dec(v_idx_3174_);
lean_dec_ref(v_config_3169_);
return v___x_3176_;
}
else
{
lean_object* v_pos_3177_; lean_object* v_idx_3178_; uint8_t v___x_3179_; 
v_pos_3177_ = lean_ctor_get(v___x_3176_, 0);
v_idx_3178_ = lean_ctor_get(v_pos_3177_, 1);
v___x_3179_ = lean_nat_dec_eq(v_idx_3174_, v_idx_3178_);
lean_dec(v_idx_3174_);
if (v___x_3179_ == 0)
{
lean_dec_ref(v_config_3169_);
return v___x_3176_;
}
else
{
lean_object* v___x_3180_; 
lean_inc(v_idx_3178_);
lean_inc(v_pos_3177_);
lean_dec_ref_known(v___x_3176_, 2);
lean_inc_ref(v_config_3169_);
v___x_3180_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(v_config_3169_, v_pos_3177_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_dec(v_idx_3178_);
lean_dec_ref(v_config_3169_);
return v___x_3180_;
}
else
{
lean_object* v_pos_3181_; lean_object* v_idx_3182_; uint8_t v___x_3183_; 
v_pos_3181_ = lean_ctor_get(v___x_3180_, 0);
v_idx_3182_ = lean_ctor_get(v_pos_3181_, 1);
v___x_3183_ = lean_nat_dec_eq(v_idx_3178_, v_idx_3182_);
lean_dec(v_idx_3178_);
if (v___x_3183_ == 0)
{
lean_dec_ref(v_config_3169_);
return v___x_3180_;
}
else
{
lean_object* v___x_3184_; 
lean_inc(v_idx_3182_);
lean_inc(v_pos_3181_);
lean_dec_ref_known(v___x_3180_, 2);
v___x_3184_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3169_, v_pos_3181_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_dec(v_idx_3182_);
lean_dec_ref(v_config_3169_);
return v___x_3184_;
}
else
{
lean_object* v_pos_3185_; lean_object* v_idx_3186_; uint8_t v___x_3187_; 
v_pos_3185_ = lean_ctor_get(v___x_3184_, 0);
v_idx_3186_ = lean_ctor_get(v_pos_3185_, 1);
v___x_3187_ = lean_nat_dec_eq(v_idx_3182_, v_idx_3186_);
lean_dec(v_idx_3182_);
if (v___x_3187_ == 0)
{
lean_dec_ref(v_config_3169_);
return v___x_3184_;
}
else
{
lean_object* v___x_3188_; 
lean_inc(v_pos_3185_);
lean_dec_ref_known(v___x_3184_, 2);
v___x_3188_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(v_config_3169_, v_pos_3185_);
return v___x_3188_;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(lean_object* v_config_3192_, lean_object* v_a_3193_){
_start:
{
lean_object* v___x_3194_; 
v___x_3194_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_3192_, v_a_3193_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_object* v_pos_3195_; lean_object* v_res_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3209_; 
v_pos_3195_ = lean_ctor_get(v___x_3194_, 0);
v_res_3196_ = lean_ctor_get(v___x_3194_, 1);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3198_ = v___x_3194_;
v_isShared_3199_ = v_isSharedCheck_3209_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_res_3196_);
lean_inc(v_pos_3195_);
lean_dec(v___x_3194_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3209_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Std_Http_URI_EncodedFragment_decode(v_res_3196_);
lean_dec(v_res_3196_);
if (lean_obj_tag(v___x_3200_) == 1)
{
lean_object* v_val_3201_; lean_object* v___x_3203_; 
v_val_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc(v_val_3201_);
lean_dec_ref_known(v___x_3200_, 1);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 1, v_val_3201_);
v___x_3203_ = v___x_3198_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_pos_3195_);
lean_ctor_set(v_reuseFailAlloc_3204_, 1, v_val_3201_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
else
{
lean_object* v___x_3205_; lean_object* v___x_3207_; 
lean_dec(v___x_3200_);
v___x_3205_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___closed__1));
if (v_isShared_3199_ == 0)
{
lean_ctor_set_tag(v___x_3198_, 1);
lean_ctor_set(v___x_3198_, 1, v___x_3205_);
v___x_3207_ = v___x_3198_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_pos_3195_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v___x_3205_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
else
{
lean_object* v_pos_3210_; lean_object* v_err_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
v_pos_3210_ = lean_ctor_get(v___x_3194_, 0);
v_err_3211_ = lean_ctor_get(v___x_3194_, 1);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3194_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_err_3211_);
lean_inc(v_pos_3210_);
lean_dec(v___x_3194_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_pos_3210_);
lean_ctor_set(v_reuseFailAlloc_3217_, 1, v_err_3211_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___boxed(lean_object* v_config_3219_, lean_object* v_a_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3219_, v_a_3220_);
lean_dec_ref(v_config_3219_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_uri(lean_object* v_config_3222_, lean_object* v_a_3223_){
_start:
{
lean_object* v___x_3224_; 
lean_inc_ref(v_a_3223_);
v___x_3224_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3222_, v_a_3223_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v_pos_3225_; lean_object* v_res_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3355_; 
v_pos_3225_ = lean_ctor_get(v___x_3224_, 0);
v_res_3226_ = lean_ctor_get(v___x_3224_, 1);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3228_ = v___x_3224_;
v_isShared_3229_ = v_isSharedCheck_3355_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_res_3226_);
lean_inc(v_pos_3225_);
lean_dec(v___x_3224_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3355_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v_array_3230_; lean_object* v_idx_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3354_; 
v_array_3230_ = lean_ctor_get(v_pos_3225_, 0);
v_idx_3231_ = lean_ctor_get(v_pos_3225_, 1);
v_isSharedCheck_3354_ = !lean_is_exclusive(v_pos_3225_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3233_ = v_pos_3225_;
v_isShared_3234_ = v_isSharedCheck_3354_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_idx_3231_);
lean_inc(v_array_3230_);
lean_dec(v_pos_3225_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3354_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3235_; uint8_t v___x_3236_; 
v___x_3235_ = lean_byte_array_size(v_array_3230_);
v___x_3236_ = lean_nat_dec_lt(v_idx_3231_, v___x_3235_);
if (v___x_3236_ == 0)
{
lean_object* v___x_3237_; lean_object* v___x_3239_; 
lean_del_object(v___x_3233_);
lean_dec(v_idx_3231_);
lean_dec_ref(v_array_3230_);
lean_dec(v_res_3226_);
lean_dec_ref(v_config_3222_);
v___x_3237_ = lean_box(0);
if (v_isShared_3229_ == 0)
{
lean_ctor_set_tag(v___x_3228_, 1);
lean_ctor_set(v___x_3228_, 1, v___x_3237_);
lean_ctor_set(v___x_3228_, 0, v_a_3223_);
v___x_3239_ = v___x_3228_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3223_);
lean_ctor_set(v_reuseFailAlloc_3240_, 1, v___x_3237_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
else
{
uint8_t v___x_3241_; uint8_t v_got_3242_; uint8_t v___x_3243_; 
v___x_3241_ = 58;
v_got_3242_ = lean_byte_array_fget(v_array_3230_, v_idx_3231_);
v___x_3243_ = lean_uint8_dec_eq(v_got_3242_, v___x_3241_);
if (v___x_3243_ == 0)
{
lean_object* v___x_3244_; lean_object* v___x_3246_; 
lean_del_object(v___x_3233_);
lean_dec(v_idx_3231_);
lean_dec_ref(v_array_3230_);
lean_dec(v_res_3226_);
lean_dec_ref(v_config_3222_);
v___x_3244_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_3229_ == 0)
{
lean_ctor_set_tag(v___x_3228_, 1);
lean_ctor_set(v___x_3228_, 1, v___x_3244_);
lean_ctor_set(v___x_3228_, 0, v_a_3223_);
v___x_3246_ = v___x_3228_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_a_3223_);
lean_ctor_set(v_reuseFailAlloc_3247_, 1, v___x_3244_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
else
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3251_; 
v___x_3248_ = lean_unsigned_to_nat(1u);
v___x_3249_ = lean_nat_add(v_idx_3231_, v___x_3248_);
lean_dec(v_idx_3231_);
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 1, v___x_3249_);
v___x_3251_ = v___x_3233_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_array_3230_);
lean_ctor_set(v_reuseFailAlloc_3353_, 1, v___x_3249_);
v___x_3251_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
lean_object* v___x_3252_; 
lean_inc_ref(v_config_3222_);
v___x_3252_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_3222_, v___x_3251_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_res_3253_; lean_object* v_pos_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3343_; 
v_res_3253_ = lean_ctor_get(v___x_3252_, 1);
v_pos_3254_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3256_ = v___x_3252_;
v_isShared_3257_ = v_isSharedCheck_3343_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_res_3253_);
lean_inc(v_pos_3254_);
lean_dec(v___x_3252_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3343_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v_fst_3258_; lean_object* v_snd_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3342_; 
v_fst_3258_ = lean_ctor_get(v_res_3253_, 0);
v_snd_3259_ = lean_ctor_get(v_res_3253_, 1);
v_isSharedCheck_3342_ = !lean_is_exclusive(v_res_3253_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3261_ = v_res_3253_;
v_isShared_3262_ = v_isSharedCheck_3342_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_snd_3259_);
lean_inc(v_fst_3258_);
lean_dec(v_res_3253_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3342_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___y_3264_; lean_object* v_pos_3265_; lean_object* v_res_3266_; lean_object* v___y_3273_; lean_object* v_idx_3274_; lean_object* v_pos_3275_; lean_object* v_err_3276_; lean_object* v_pos_3284_; lean_object* v_array_3285_; lean_object* v_idx_3286_; lean_object* v_res_3287_; lean_object* v_array_3305_; lean_object* v_idx_3306_; lean_object* v_pos_3308_; lean_object* v_array_3309_; lean_object* v_idx_3310_; lean_object* v_err_3311_; lean_object* v___x_3315_; uint8_t v___x_3316_; 
v_array_3305_ = lean_ctor_get(v_pos_3254_, 0);
lean_inc_ref(v_array_3305_);
v_idx_3306_ = lean_ctor_get(v_pos_3254_, 1);
lean_inc(v_idx_3306_);
v___x_3315_ = lean_byte_array_size(v_array_3305_);
v___x_3316_ = lean_nat_dec_lt(v_idx_3306_, v___x_3315_);
if (v___x_3316_ == 0)
{
lean_object* v___x_3317_; 
v___x_3317_ = lean_box(0);
lean_inc(v_idx_3306_);
v_pos_3308_ = v_pos_3254_;
v_array_3309_ = v_array_3305_;
v_idx_3310_ = v_idx_3306_;
v_err_3311_ = v___x_3317_;
goto v___jp_3307_;
}
else
{
uint8_t v___x_3318_; uint8_t v_got_3319_; uint8_t v___x_3320_; 
v___x_3318_ = 63;
v_got_3319_ = lean_byte_array_fget(v_array_3305_, v_idx_3306_);
v___x_3320_ = lean_uint8_dec_eq(v_got_3319_, v___x_3318_);
if (v___x_3320_ == 0)
{
lean_object* v___x_3321_; 
v___x_3321_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_3306_);
v_pos_3308_ = v_pos_3254_;
v_array_3309_ = v_array_3305_;
v_idx_3310_ = v_idx_3306_;
v_err_3311_ = v___x_3321_;
goto v___jp_3307_;
}
else
{
lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3339_; 
v_isSharedCheck_3339_ = !lean_is_exclusive(v_pos_3254_);
if (v_isSharedCheck_3339_ == 0)
{
lean_object* v_unused_3340_; lean_object* v_unused_3341_; 
v_unused_3340_ = lean_ctor_get(v_pos_3254_, 1);
lean_dec(v_unused_3340_);
v_unused_3341_ = lean_ctor_get(v_pos_3254_, 0);
lean_dec(v_unused_3341_);
v___x_3323_ = v_pos_3254_;
v_isShared_3324_ = v_isSharedCheck_3339_;
goto v_resetjp_3322_;
}
else
{
lean_dec(v_pos_3254_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3339_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3325_; lean_object* v___x_3327_; 
v___x_3325_ = lean_nat_add(v_idx_3306_, v___x_3248_);
if (v_isShared_3324_ == 0)
{
lean_ctor_set(v___x_3323_, 1, v___x_3325_);
v___x_3327_ = v___x_3323_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_array_3305_);
lean_ctor_set(v_reuseFailAlloc_3338_, 1, v___x_3325_);
v___x_3327_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
lean_object* v___x_3328_; 
lean_inc_ref(v_config_3222_);
v___x_3328_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3222_, v___x_3327_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_pos_3329_; lean_object* v_res_3330_; lean_object* v_array_3331_; lean_object* v_idx_3332_; lean_object* v___x_3333_; 
lean_dec(v_idx_3306_);
v_pos_3329_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_pos_3329_);
v_res_3330_ = lean_ctor_get(v___x_3328_, 1);
lean_inc(v_res_3330_);
lean_dec_ref_known(v___x_3328_, 2);
v_array_3331_ = lean_ctor_get(v_pos_3329_, 0);
lean_inc_ref(v_array_3331_);
v_idx_3332_ = lean_ctor_get(v_pos_3329_, 1);
lean_inc(v_idx_3332_);
v___x_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3333_, 0, v_res_3330_);
v_pos_3284_ = v_pos_3329_;
v_array_3285_ = v_array_3331_;
v_idx_3286_ = v_idx_3332_;
v_res_3287_ = v___x_3333_;
goto v___jp_3283_;
}
else
{
lean_object* v_pos_3334_; lean_object* v_err_3335_; lean_object* v_array_3336_; lean_object* v_idx_3337_; 
v_pos_3334_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_pos_3334_);
v_err_3335_ = lean_ctor_get(v___x_3328_, 1);
lean_inc(v_err_3335_);
lean_dec_ref_known(v___x_3328_, 2);
v_array_3336_ = lean_ctor_get(v_pos_3334_, 0);
lean_inc_ref(v_array_3336_);
v_idx_3337_ = lean_ctor_get(v_pos_3334_, 1);
lean_inc(v_idx_3337_);
v_pos_3308_ = v_pos_3334_;
v_array_3309_ = v_array_3336_;
v_idx_3310_ = v_idx_3337_;
v_err_3311_ = v_err_3335_;
goto v___jp_3307_;
}
}
}
}
}
v___jp_3263_:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3270_; 
v___x_3267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3267_, 0, v_res_3226_);
lean_ctor_set(v___x_3267_, 1, v_fst_3258_);
lean_ctor_set(v___x_3267_, 2, v_snd_3259_);
lean_ctor_set(v___x_3267_, 3, v___y_3264_);
lean_ctor_set(v___x_3267_, 4, v_res_3266_);
v___x_3268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3267_);
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 1, v___x_3268_);
lean_ctor_set(v___x_3256_, 0, v_pos_3265_);
v___x_3270_ = v___x_3256_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_pos_3265_);
lean_ctor_set(v_reuseFailAlloc_3271_, 1, v___x_3268_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
v___jp_3272_:
{
lean_object* v_idx_3277_; uint8_t v___x_3278_; 
v_idx_3277_ = lean_ctor_get(v_pos_3275_, 1);
v___x_3278_ = lean_nat_dec_eq(v_idx_3274_, v_idx_3277_);
lean_dec(v_idx_3274_);
if (v___x_3278_ == 0)
{
lean_object* v___x_3280_; 
lean_dec_ref(v_pos_3275_);
lean_dec(v___y_3273_);
lean_dec(v_snd_3259_);
lean_dec(v_fst_3258_);
lean_del_object(v___x_3256_);
lean_dec(v_res_3226_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set_tag(v___x_3228_, 1);
lean_ctor_set(v___x_3228_, 1, v_err_3276_);
lean_ctor_set(v___x_3228_, 0, v_a_3223_);
v___x_3280_ = v___x_3228_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_a_3223_);
lean_ctor_set(v_reuseFailAlloc_3281_, 1, v_err_3276_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
else
{
lean_object* v___x_3282_; 
lean_dec(v_err_3276_);
lean_del_object(v___x_3228_);
lean_dec_ref(v_a_3223_);
v___x_3282_ = lean_box(0);
v___y_3264_ = v___y_3273_;
v_pos_3265_ = v_pos_3275_;
v_res_3266_ = v___x_3282_;
goto v___jp_3263_;
}
}
v___jp_3283_:
{
lean_object* v___x_3288_; uint8_t v___x_3289_; 
v___x_3288_ = lean_byte_array_size(v_array_3285_);
v___x_3289_ = lean_nat_dec_lt(v_idx_3286_, v___x_3288_);
if (v___x_3289_ == 0)
{
lean_object* v___x_3290_; 
lean_dec_ref(v_array_3285_);
lean_del_object(v___x_3261_);
lean_dec_ref(v_config_3222_);
v___x_3290_ = lean_box(0);
v___y_3273_ = v_res_3287_;
v_idx_3274_ = v_idx_3286_;
v_pos_3275_ = v_pos_3284_;
v_err_3276_ = v___x_3290_;
goto v___jp_3272_;
}
else
{
uint8_t v___x_3291_; uint8_t v_got_3292_; uint8_t v___x_3293_; 
v___x_3291_ = 35;
v_got_3292_ = lean_byte_array_fget(v_array_3285_, v_idx_3286_);
v___x_3293_ = lean_uint8_dec_eq(v_got_3292_, v___x_3291_);
if (v___x_3293_ == 0)
{
lean_object* v___x_3294_; 
lean_dec_ref(v_array_3285_);
lean_del_object(v___x_3261_);
lean_dec_ref(v_config_3222_);
v___x_3294_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v___y_3273_ = v_res_3287_;
v_idx_3274_ = v_idx_3286_;
v_pos_3275_ = v_pos_3284_;
v_err_3276_ = v___x_3294_;
goto v___jp_3272_;
}
else
{
lean_object* v___x_3295_; lean_object* v___x_3297_; 
lean_dec_ref(v_pos_3284_);
v___x_3295_ = lean_nat_add(v_idx_3286_, v___x_3248_);
if (v_isShared_3262_ == 0)
{
lean_ctor_set(v___x_3261_, 1, v___x_3295_);
lean_ctor_set(v___x_3261_, 0, v_array_3285_);
v___x_3297_ = v___x_3261_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_array_3285_);
lean_ctor_set(v_reuseFailAlloc_3304_, 1, v___x_3295_);
v___x_3297_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
lean_object* v___x_3298_; 
v___x_3298_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3222_, v___x_3297_);
lean_dec_ref(v_config_3222_);
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_object* v_pos_3299_; lean_object* v_res_3300_; lean_object* v___x_3301_; 
lean_dec(v_idx_3286_);
lean_del_object(v___x_3228_);
lean_dec_ref(v_a_3223_);
v_pos_3299_ = lean_ctor_get(v___x_3298_, 0);
lean_inc(v_pos_3299_);
v_res_3300_ = lean_ctor_get(v___x_3298_, 1);
lean_inc(v_res_3300_);
lean_dec_ref_known(v___x_3298_, 2);
v___x_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3301_, 0, v_res_3300_);
v___y_3264_ = v_res_3287_;
v_pos_3265_ = v_pos_3299_;
v_res_3266_ = v___x_3301_;
goto v___jp_3263_;
}
else
{
lean_object* v_pos_3302_; lean_object* v_err_3303_; 
v_pos_3302_ = lean_ctor_get(v___x_3298_, 0);
lean_inc(v_pos_3302_);
v_err_3303_ = lean_ctor_get(v___x_3298_, 1);
lean_inc(v_err_3303_);
lean_dec_ref_known(v___x_3298_, 2);
v___y_3273_ = v_res_3287_;
v_idx_3274_ = v_idx_3286_;
v_pos_3275_ = v_pos_3302_;
v_err_3276_ = v_err_3303_;
goto v___jp_3272_;
}
}
}
}
}
v___jp_3307_:
{
uint8_t v___x_3312_; 
v___x_3312_ = lean_nat_dec_eq(v_idx_3306_, v_idx_3310_);
lean_dec(v_idx_3306_);
if (v___x_3312_ == 0)
{
lean_object* v___x_3313_; 
lean_dec(v_idx_3310_);
lean_dec_ref(v_array_3309_);
lean_dec_ref(v_pos_3308_);
lean_del_object(v___x_3261_);
lean_dec(v_snd_3259_);
lean_dec(v_fst_3258_);
lean_del_object(v___x_3256_);
lean_del_object(v___x_3228_);
lean_dec(v_res_3226_);
lean_dec_ref(v_config_3222_);
v___x_3313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3313_, 0, v_a_3223_);
lean_ctor_set(v___x_3313_, 1, v_err_3311_);
return v___x_3313_;
}
else
{
lean_object* v___x_3314_; 
lean_dec(v_err_3311_);
v___x_3314_ = lean_box(0);
v_pos_3284_ = v_pos_3308_;
v_array_3285_ = v_array_3309_;
v_idx_3286_ = v_idx_3310_;
v_res_3287_ = v___x_3314_;
goto v___jp_3283_;
}
}
}
}
}
else
{
lean_object* v_err_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3351_; 
lean_del_object(v___x_3228_);
lean_dec(v_res_3226_);
lean_dec_ref(v_config_3222_);
v_err_3344_ = lean_ctor_get(v___x_3252_, 1);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3351_ == 0)
{
lean_object* v_unused_3352_; 
v_unused_3352_ = lean_ctor_get(v___x_3252_, 0);
lean_dec(v_unused_3352_);
v___x_3346_ = v___x_3252_;
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_err_3344_);
lean_dec(v___x_3252_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3349_; 
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 0, v_a_3223_);
v___x_3349_ = v___x_3346_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_a_3223_);
lean_ctor_set(v_reuseFailAlloc_3350_, 1, v_err_3344_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
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
lean_object* v_err_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3363_; 
lean_dec_ref(v_config_3222_);
v_err_3356_ = lean_ctor_get(v___x_3224_, 1);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3363_ == 0)
{
lean_object* v_unused_3364_; 
v_unused_3364_ = lean_ctor_get(v___x_3224_, 0);
lean_dec(v_unused_3364_);
v___x_3358_ = v___x_3224_;
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_err_3356_);
lean_dec(v___x_3224_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3361_; 
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 0, v_a_3223_);
v___x_3361_ = v___x_3358_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_a_3223_);
lean_ctor_set(v_reuseFailAlloc_3362_, 1, v_err_3356_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withAuthority(lean_object* v_config_3365_, lean_object* v_a_3366_){
_start:
{
lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v_pos_3371_; lean_object* v_res_3372_; lean_object* v_idx_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v_pos_3381_; lean_object* v_err_3382_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v_pos_3398_; lean_object* v_array_3399_; lean_object* v_idx_3400_; lean_object* v_res_3401_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v_idx_3421_; lean_object* v_pos_3422_; lean_object* v_array_3423_; lean_object* v_idx_3424_; lean_object* v_err_3425_; lean_object* v_pos_3430_; lean_object* v_utf8_3486_; lean_object* v___x_3487_; 
v_utf8_3486_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1);
lean_inc_ref(v_a_3366_);
v___x_3487_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_3486_, v_a_3366_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_pos_3488_; 
v_pos_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_pos_3488_);
lean_dec_ref_known(v___x_3487_, 2);
v_pos_3430_ = v_pos_3488_;
goto v___jp_3429_;
}
else
{
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_pos_3489_; 
v_pos_3489_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_pos_3489_);
lean_dec_ref_known(v___x_3487_, 2);
v_pos_3430_ = v_pos_3489_;
goto v___jp_3429_;
}
else
{
lean_object* v_err_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3497_; 
lean_dec_ref(v_config_3365_);
v_err_3490_ = lean_ctor_get(v___x_3487_, 1);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3497_ == 0)
{
lean_object* v_unused_3498_; 
v_unused_3498_ = lean_ctor_get(v___x_3487_, 0);
lean_dec(v_unused_3498_);
v___x_3492_ = v___x_3487_;
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_err_3490_);
lean_dec(v___x_3487_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3495_; 
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 0, v_a_3366_);
v___x_3495_ = v___x_3492_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3366_);
lean_ctor_set(v_reuseFailAlloc_3496_, 1, v_err_3490_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
}
v___jp_3367_:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3373_, 0, v___y_3368_);
v___x_3374_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3373_);
lean_ctor_set(v___x_3374_, 1, v___y_3370_);
lean_ctor_set(v___x_3374_, 2, v___y_3369_);
lean_ctor_set(v___x_3374_, 3, v_res_3372_);
v___x_3375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3375_, 0, v_pos_3371_);
lean_ctor_set(v___x_3375_, 1, v___x_3374_);
return v___x_3375_;
}
v___jp_3376_:
{
lean_object* v_idx_3383_; uint8_t v___x_3384_; 
v_idx_3383_ = lean_ctor_get(v_pos_3381_, 1);
v___x_3384_ = lean_nat_dec_eq(v_idx_3377_, v_idx_3383_);
lean_dec(v_idx_3377_);
if (v___x_3384_ == 0)
{
lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3391_; 
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
v_isSharedCheck_3391_ = !lean_is_exclusive(v_pos_3381_);
if (v_isSharedCheck_3391_ == 0)
{
lean_object* v_unused_3392_; lean_object* v_unused_3393_; 
v_unused_3392_ = lean_ctor_get(v_pos_3381_, 1);
lean_dec(v_unused_3392_);
v_unused_3393_ = lean_ctor_get(v_pos_3381_, 0);
lean_dec(v_unused_3393_);
v___x_3386_ = v_pos_3381_;
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
else
{
lean_dec(v_pos_3381_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3389_; 
if (v_isShared_3387_ == 0)
{
lean_ctor_set_tag(v___x_3386_, 1);
lean_ctor_set(v___x_3386_, 1, v_err_3382_);
lean_ctor_set(v___x_3386_, 0, v_a_3366_);
v___x_3389_ = v___x_3386_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_a_3366_);
lean_ctor_set(v_reuseFailAlloc_3390_, 1, v_err_3382_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
}
else
{
lean_object* v___x_3394_; 
lean_dec(v_err_3382_);
lean_dec_ref(v_a_3366_);
v___x_3394_ = lean_box(0);
v___y_3368_ = v___y_3378_;
v___y_3369_ = v___y_3379_;
v___y_3370_ = v___y_3380_;
v_pos_3371_ = v_pos_3381_;
v_res_3372_ = v___x_3394_;
goto v___jp_3367_;
}
}
v___jp_3395_:
{
lean_object* v___x_3402_; uint8_t v___x_3403_; 
v___x_3402_ = lean_byte_array_size(v_array_3399_);
v___x_3403_ = lean_nat_dec_lt(v_idx_3400_, v___x_3402_);
if (v___x_3403_ == 0)
{
lean_object* v___x_3404_; 
lean_dec_ref(v_array_3399_);
lean_dec_ref(v_config_3365_);
v___x_3404_ = lean_box(0);
v_idx_3377_ = v_idx_3400_;
v___y_3378_ = v___y_3396_;
v___y_3379_ = v_res_3401_;
v___y_3380_ = v___y_3397_;
v_pos_3381_ = v_pos_3398_;
v_err_3382_ = v___x_3404_;
goto v___jp_3376_;
}
else
{
uint8_t v___x_3405_; uint8_t v_got_3406_; uint8_t v___x_3407_; 
v___x_3405_ = 35;
v_got_3406_ = lean_byte_array_fget(v_array_3399_, v_idx_3400_);
v___x_3407_ = lean_uint8_dec_eq(v_got_3406_, v___x_3405_);
if (v___x_3407_ == 0)
{
lean_object* v___x_3408_; 
lean_dec_ref(v_array_3399_);
lean_dec_ref(v_config_3365_);
v___x_3408_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v_idx_3377_ = v_idx_3400_;
v___y_3378_ = v___y_3396_;
v___y_3379_ = v_res_3401_;
v___y_3380_ = v___y_3397_;
v_pos_3381_ = v_pos_3398_;
v_err_3382_ = v___x_3408_;
goto v___jp_3376_;
}
else
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
lean_dec_ref(v_pos_3398_);
v___x_3409_ = lean_unsigned_to_nat(1u);
v___x_3410_ = lean_nat_add(v_idx_3400_, v___x_3409_);
v___x_3411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3411_, 0, v_array_3399_);
lean_ctor_set(v___x_3411_, 1, v___x_3410_);
v___x_3412_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3365_, v___x_3411_);
lean_dec_ref(v_config_3365_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v_pos_3413_; lean_object* v_res_3414_; lean_object* v___x_3415_; 
lean_dec(v_idx_3400_);
lean_dec_ref(v_a_3366_);
v_pos_3413_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_pos_3413_);
v_res_3414_ = lean_ctor_get(v___x_3412_, 1);
lean_inc(v_res_3414_);
lean_dec_ref_known(v___x_3412_, 2);
v___x_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3415_, 0, v_res_3414_);
v___y_3368_ = v___y_3396_;
v___y_3369_ = v_res_3401_;
v___y_3370_ = v___y_3397_;
v_pos_3371_ = v_pos_3413_;
v_res_3372_ = v___x_3415_;
goto v___jp_3367_;
}
else
{
lean_object* v_pos_3416_; lean_object* v_err_3417_; 
v_pos_3416_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_pos_3416_);
v_err_3417_ = lean_ctor_get(v___x_3412_, 1);
lean_inc(v_err_3417_);
lean_dec_ref_known(v___x_3412_, 2);
v_idx_3377_ = v_idx_3400_;
v___y_3378_ = v___y_3396_;
v___y_3379_ = v_res_3401_;
v___y_3380_ = v___y_3397_;
v_pos_3381_ = v_pos_3416_;
v_err_3382_ = v_err_3417_;
goto v___jp_3376_;
}
}
}
}
v___jp_3418_:
{
uint8_t v___x_3426_; 
v___x_3426_ = lean_nat_dec_eq(v_idx_3421_, v_idx_3424_);
lean_dec(v_idx_3421_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; 
lean_dec(v_idx_3424_);
lean_dec_ref(v_array_3423_);
lean_dec_ref(v_pos_3422_);
lean_dec_ref(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec_ref(v_config_3365_);
v___x_3427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3427_, 0, v_a_3366_);
lean_ctor_set(v___x_3427_, 1, v_err_3425_);
return v___x_3427_;
}
else
{
lean_object* v___x_3428_; 
lean_dec(v_err_3425_);
v___x_3428_ = lean_box(0);
v___y_3396_ = v___y_3419_;
v___y_3397_ = v___y_3420_;
v_pos_3398_ = v_pos_3422_;
v_array_3399_ = v_array_3423_;
v_idx_3400_ = v_idx_3424_;
v_res_3401_ = v___x_3428_;
goto v___jp_3395_;
}
}
v___jp_3429_:
{
lean_object* v___x_3431_; 
v___x_3431_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_3365_, v_pos_3430_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_pos_3432_; lean_object* v_res_3433_; uint8_t v___x_3434_; lean_object* v___x_3435_; 
v_pos_3432_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_pos_3432_);
v_res_3433_ = lean_ctor_get(v___x_3431_, 1);
lean_inc(v_res_3433_);
lean_dec_ref_known(v___x_3431_, 2);
v___x_3434_ = 1;
lean_inc_ref(v_config_3365_);
v___x_3435_ = l_Std_Http_URI_Parser_parsePath(v_config_3365_, v___x_3434_, v___x_3434_, v_pos_3432_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v_pos_3436_; lean_object* v_res_3437_; lean_object* v_array_3438_; lean_object* v_idx_3439_; lean_object* v___x_3440_; uint8_t v___x_3441_; 
v_pos_3436_ = lean_ctor_get(v___x_3435_, 0);
lean_inc(v_pos_3436_);
v_res_3437_ = lean_ctor_get(v___x_3435_, 1);
lean_inc(v_res_3437_);
lean_dec_ref_known(v___x_3435_, 2);
v_array_3438_ = lean_ctor_get(v_pos_3436_, 0);
lean_inc_ref(v_array_3438_);
v_idx_3439_ = lean_ctor_get(v_pos_3436_, 1);
lean_inc(v_idx_3439_);
v___x_3440_ = lean_byte_array_size(v_array_3438_);
v___x_3441_ = lean_nat_dec_lt(v_idx_3439_, v___x_3440_);
if (v___x_3441_ == 0)
{
lean_object* v___x_3442_; 
v___x_3442_ = lean_box(0);
lean_inc(v_idx_3439_);
v___y_3419_ = v_res_3433_;
v___y_3420_ = v_res_3437_;
v_idx_3421_ = v_idx_3439_;
v_pos_3422_ = v_pos_3436_;
v_array_3423_ = v_array_3438_;
v_idx_3424_ = v_idx_3439_;
v_err_3425_ = v___x_3442_;
goto v___jp_3418_;
}
else
{
uint8_t v___x_3443_; uint8_t v_got_3444_; uint8_t v___x_3445_; 
v___x_3443_ = 63;
v_got_3444_ = lean_byte_array_fget(v_array_3438_, v_idx_3439_);
v___x_3445_ = lean_uint8_dec_eq(v_got_3444_, v___x_3443_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3446_; 
v___x_3446_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_3439_);
v___y_3419_ = v_res_3433_;
v___y_3420_ = v_res_3437_;
v_idx_3421_ = v_idx_3439_;
v_pos_3422_ = v_pos_3436_;
v_array_3423_ = v_array_3438_;
v_idx_3424_ = v_idx_3439_;
v_err_3425_ = v___x_3446_;
goto v___jp_3418_;
}
else
{
lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3465_; 
v_isSharedCheck_3465_ = !lean_is_exclusive(v_pos_3436_);
if (v_isSharedCheck_3465_ == 0)
{
lean_object* v_unused_3466_; lean_object* v_unused_3467_; 
v_unused_3466_ = lean_ctor_get(v_pos_3436_, 1);
lean_dec(v_unused_3466_);
v_unused_3467_ = lean_ctor_get(v_pos_3436_, 0);
lean_dec(v_unused_3467_);
v___x_3448_ = v_pos_3436_;
v_isShared_3449_ = v_isSharedCheck_3465_;
goto v_resetjp_3447_;
}
else
{
lean_dec(v_pos_3436_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3465_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3453_; 
v___x_3450_ = lean_unsigned_to_nat(1u);
v___x_3451_ = lean_nat_add(v_idx_3439_, v___x_3450_);
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 1, v___x_3451_);
v___x_3453_ = v___x_3448_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_array_3438_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v___x_3451_);
v___x_3453_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
lean_object* v___x_3454_; 
lean_inc_ref(v_config_3365_);
v___x_3454_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3365_, v___x_3453_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_pos_3455_; lean_object* v_res_3456_; lean_object* v_array_3457_; lean_object* v_idx_3458_; lean_object* v___x_3459_; 
lean_dec(v_idx_3439_);
v_pos_3455_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_pos_3455_);
v_res_3456_ = lean_ctor_get(v___x_3454_, 1);
lean_inc(v_res_3456_);
lean_dec_ref_known(v___x_3454_, 2);
v_array_3457_ = lean_ctor_get(v_pos_3455_, 0);
lean_inc_ref(v_array_3457_);
v_idx_3458_ = lean_ctor_get(v_pos_3455_, 1);
lean_inc(v_idx_3458_);
v___x_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3459_, 0, v_res_3456_);
v___y_3396_ = v_res_3433_;
v___y_3397_ = v_res_3437_;
v_pos_3398_ = v_pos_3455_;
v_array_3399_ = v_array_3457_;
v_idx_3400_ = v_idx_3458_;
v_res_3401_ = v___x_3459_;
goto v___jp_3395_;
}
else
{
lean_object* v_pos_3460_; lean_object* v_err_3461_; lean_object* v_array_3462_; lean_object* v_idx_3463_; 
v_pos_3460_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_pos_3460_);
v_err_3461_ = lean_ctor_get(v___x_3454_, 1);
lean_inc(v_err_3461_);
lean_dec_ref_known(v___x_3454_, 2);
v_array_3462_ = lean_ctor_get(v_pos_3460_, 0);
lean_inc_ref(v_array_3462_);
v_idx_3463_ = lean_ctor_get(v_pos_3460_, 1);
lean_inc(v_idx_3463_);
v___y_3419_ = v_res_3433_;
v___y_3420_ = v_res_3437_;
v_idx_3421_ = v_idx_3439_;
v_pos_3422_ = v_pos_3460_;
v_array_3423_ = v_array_3462_;
v_idx_3424_ = v_idx_3463_;
v_err_3425_ = v_err_3461_;
goto v___jp_3418_;
}
}
}
}
}
}
else
{
lean_object* v_err_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3475_; 
lean_dec(v_res_3433_);
lean_dec_ref(v_config_3365_);
v_err_3468_ = lean_ctor_get(v___x_3435_, 1);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3475_ == 0)
{
lean_object* v_unused_3476_; 
v_unused_3476_ = lean_ctor_get(v___x_3435_, 0);
lean_dec(v_unused_3476_);
v___x_3470_ = v___x_3435_;
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_err_3468_);
lean_dec(v___x_3435_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3473_; 
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 0, v_a_3366_);
v___x_3473_ = v___x_3470_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_a_3366_);
lean_ctor_set(v_reuseFailAlloc_3474_, 1, v_err_3468_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
else
{
lean_object* v_err_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3484_; 
lean_dec_ref(v_config_3365_);
v_err_3477_ = lean_ctor_get(v___x_3431_, 1);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3484_ == 0)
{
lean_object* v_unused_3485_; 
v_unused_3485_ = lean_ctor_get(v___x_3431_, 0);
lean_dec(v_unused_3485_);
v___x_3479_ = v___x_3431_;
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_err_3477_);
lean_dec(v___x_3431_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 0, v_a_3366_);
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3366_);
lean_ctor_set(v_reuseFailAlloc_3483_, 1, v_err_3477_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath(lean_object* v_config_3499_, lean_object* v_a_3500_){
_start:
{
uint8_t v___x_3501_; uint8_t v___x_3502_; lean_object* v___x_3503_; 
v___x_3501_ = 0;
v___x_3502_ = 1;
lean_inc_ref(v_config_3499_);
v___x_3503_ = l_Std_Http_URI_Parser_parsePath(v_config_3499_, v___x_3501_, v___x_3502_, v_a_3500_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_pos_3504_; lean_object* v_res_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3586_; 
v_pos_3504_ = lean_ctor_get(v___x_3503_, 0);
v_res_3505_ = lean_ctor_get(v___x_3503_, 1);
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3507_ = v___x_3503_;
v_isShared_3508_ = v_isSharedCheck_3586_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_res_3505_);
lean_inc(v_pos_3504_);
lean_dec(v___x_3503_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3586_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___y_3510_; lean_object* v_pos_3511_; lean_object* v_res_3512_; lean_object* v_idx_3519_; lean_object* v___y_3520_; lean_object* v_pos_3521_; lean_object* v_err_3522_; lean_object* v_pos_3528_; lean_object* v_array_3529_; lean_object* v_idx_3530_; lean_object* v_res_3531_; lean_object* v_array_3548_; lean_object* v_idx_3549_; lean_object* v_pos_3551_; lean_object* v_array_3552_; lean_object* v_idx_3553_; lean_object* v_err_3554_; lean_object* v___x_3558_; uint8_t v___x_3559_; 
v_array_3548_ = lean_ctor_get(v_pos_3504_, 0);
lean_inc_ref(v_array_3548_);
v_idx_3549_ = lean_ctor_get(v_pos_3504_, 1);
lean_inc(v_idx_3549_);
v___x_3558_ = lean_byte_array_size(v_array_3548_);
v___x_3559_ = lean_nat_dec_lt(v_idx_3549_, v___x_3558_);
if (v___x_3559_ == 0)
{
lean_object* v___x_3560_; 
v___x_3560_ = lean_box(0);
lean_inc(v_idx_3549_);
v_pos_3551_ = v_pos_3504_;
v_array_3552_ = v_array_3548_;
v_idx_3553_ = v_idx_3549_;
v_err_3554_ = v___x_3560_;
goto v___jp_3550_;
}
else
{
uint8_t v___x_3561_; uint8_t v_got_3562_; uint8_t v___x_3563_; 
v___x_3561_ = 63;
v_got_3562_ = lean_byte_array_fget(v_array_3548_, v_idx_3549_);
v___x_3563_ = lean_uint8_dec_eq(v_got_3562_, v___x_3561_);
if (v___x_3563_ == 0)
{
lean_object* v___x_3564_; 
v___x_3564_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_3549_);
v_pos_3551_ = v_pos_3504_;
v_array_3552_ = v_array_3548_;
v_idx_3553_ = v_idx_3549_;
v_err_3554_ = v___x_3564_;
goto v___jp_3550_;
}
else
{
lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3583_; 
v_isSharedCheck_3583_ = !lean_is_exclusive(v_pos_3504_);
if (v_isSharedCheck_3583_ == 0)
{
lean_object* v_unused_3584_; lean_object* v_unused_3585_; 
v_unused_3584_ = lean_ctor_get(v_pos_3504_, 1);
lean_dec(v_unused_3584_);
v_unused_3585_ = lean_ctor_get(v_pos_3504_, 0);
lean_dec(v_unused_3585_);
v___x_3566_ = v_pos_3504_;
v_isShared_3567_ = v_isSharedCheck_3583_;
goto v_resetjp_3565_;
}
else
{
lean_dec(v_pos_3504_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3583_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3571_; 
v___x_3568_ = lean_unsigned_to_nat(1u);
v___x_3569_ = lean_nat_add(v_idx_3549_, v___x_3568_);
if (v_isShared_3567_ == 0)
{
lean_ctor_set(v___x_3566_, 1, v___x_3569_);
v___x_3571_ = v___x_3566_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_array_3548_);
lean_ctor_set(v_reuseFailAlloc_3582_, 1, v___x_3569_);
v___x_3571_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
lean_object* v___x_3572_; 
lean_inc_ref(v_config_3499_);
v___x_3572_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3499_, v___x_3571_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v_pos_3573_; lean_object* v_res_3574_; lean_object* v_array_3575_; lean_object* v_idx_3576_; lean_object* v___x_3577_; 
lean_dec(v_idx_3549_);
v_pos_3573_ = lean_ctor_get(v___x_3572_, 0);
lean_inc(v_pos_3573_);
v_res_3574_ = lean_ctor_get(v___x_3572_, 1);
lean_inc(v_res_3574_);
lean_dec_ref_known(v___x_3572_, 2);
v_array_3575_ = lean_ctor_get(v_pos_3573_, 0);
lean_inc_ref(v_array_3575_);
v_idx_3576_ = lean_ctor_get(v_pos_3573_, 1);
lean_inc(v_idx_3576_);
v___x_3577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3577_, 0, v_res_3574_);
v_pos_3528_ = v_pos_3573_;
v_array_3529_ = v_array_3575_;
v_idx_3530_ = v_idx_3576_;
v_res_3531_ = v___x_3577_;
goto v___jp_3527_;
}
else
{
lean_object* v_pos_3578_; lean_object* v_err_3579_; lean_object* v_array_3580_; lean_object* v_idx_3581_; 
v_pos_3578_ = lean_ctor_get(v___x_3572_, 0);
lean_inc(v_pos_3578_);
v_err_3579_ = lean_ctor_get(v___x_3572_, 1);
lean_inc(v_err_3579_);
lean_dec_ref_known(v___x_3572_, 2);
v_array_3580_ = lean_ctor_get(v_pos_3578_, 0);
lean_inc_ref(v_array_3580_);
v_idx_3581_ = lean_ctor_get(v_pos_3578_, 1);
lean_inc(v_idx_3581_);
v_pos_3551_ = v_pos_3578_;
v_array_3552_ = v_array_3580_;
v_idx_3553_ = v_idx_3581_;
v_err_3554_ = v_err_3579_;
goto v___jp_3550_;
}
}
}
}
}
v___jp_3509_:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3516_; 
v___x_3513_ = lean_box(0);
v___x_3514_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3513_);
lean_ctor_set(v___x_3514_, 1, v_res_3505_);
lean_ctor_set(v___x_3514_, 2, v___y_3510_);
lean_ctor_set(v___x_3514_, 3, v_res_3512_);
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 1, v___x_3514_);
lean_ctor_set(v___x_3507_, 0, v_pos_3511_);
v___x_3516_ = v___x_3507_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_pos_3511_);
lean_ctor_set(v_reuseFailAlloc_3517_, 1, v___x_3514_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
v___jp_3518_:
{
lean_object* v_idx_3523_; uint8_t v___x_3524_; 
v_idx_3523_ = lean_ctor_get(v_pos_3521_, 1);
v___x_3524_ = lean_nat_dec_eq(v_idx_3519_, v_idx_3523_);
lean_dec(v_idx_3519_);
if (v___x_3524_ == 0)
{
lean_object* v___x_3525_; 
lean_dec(v___y_3520_);
lean_del_object(v___x_3507_);
lean_dec(v_res_3505_);
v___x_3525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3525_, 0, v_pos_3521_);
lean_ctor_set(v___x_3525_, 1, v_err_3522_);
return v___x_3525_;
}
else
{
lean_object* v___x_3526_; 
lean_dec(v_err_3522_);
v___x_3526_ = lean_box(0);
v___y_3510_ = v___y_3520_;
v_pos_3511_ = v_pos_3521_;
v_res_3512_ = v___x_3526_;
goto v___jp_3509_;
}
}
v___jp_3527_:
{
lean_object* v___x_3532_; uint8_t v___x_3533_; 
v___x_3532_ = lean_byte_array_size(v_array_3529_);
v___x_3533_ = lean_nat_dec_lt(v_idx_3530_, v___x_3532_);
if (v___x_3533_ == 0)
{
lean_object* v___x_3534_; 
lean_dec_ref(v_array_3529_);
lean_dec_ref(v_config_3499_);
v___x_3534_ = lean_box(0);
v_idx_3519_ = v_idx_3530_;
v___y_3520_ = v_res_3531_;
v_pos_3521_ = v_pos_3528_;
v_err_3522_ = v___x_3534_;
goto v___jp_3518_;
}
else
{
uint8_t v___x_3535_; uint8_t v_got_3536_; uint8_t v___x_3537_; 
v___x_3535_ = 35;
v_got_3536_ = lean_byte_array_fget(v_array_3529_, v_idx_3530_);
v___x_3537_ = lean_uint8_dec_eq(v_got_3536_, v___x_3535_);
if (v___x_3537_ == 0)
{
lean_object* v___x_3538_; 
lean_dec_ref(v_array_3529_);
lean_dec_ref(v_config_3499_);
v___x_3538_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v_idx_3519_ = v_idx_3530_;
v___y_3520_ = v_res_3531_;
v_pos_3521_ = v_pos_3528_;
v_err_3522_ = v___x_3538_;
goto v___jp_3518_;
}
else
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; 
lean_dec_ref(v_pos_3528_);
v___x_3539_ = lean_unsigned_to_nat(1u);
v___x_3540_ = lean_nat_add(v_idx_3530_, v___x_3539_);
v___x_3541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3541_, 0, v_array_3529_);
lean_ctor_set(v___x_3541_, 1, v___x_3540_);
v___x_3542_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3499_, v___x_3541_);
lean_dec_ref(v_config_3499_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_object* v_pos_3543_; lean_object* v_res_3544_; lean_object* v___x_3545_; 
lean_dec(v_idx_3530_);
v_pos_3543_ = lean_ctor_get(v___x_3542_, 0);
lean_inc(v_pos_3543_);
v_res_3544_ = lean_ctor_get(v___x_3542_, 1);
lean_inc(v_res_3544_);
lean_dec_ref_known(v___x_3542_, 2);
v___x_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3545_, 0, v_res_3544_);
v___y_3510_ = v_res_3531_;
v_pos_3511_ = v_pos_3543_;
v_res_3512_ = v___x_3545_;
goto v___jp_3509_;
}
else
{
lean_object* v_pos_3546_; lean_object* v_err_3547_; 
v_pos_3546_ = lean_ctor_get(v___x_3542_, 0);
lean_inc(v_pos_3546_);
v_err_3547_ = lean_ctor_get(v___x_3542_, 1);
lean_inc(v_err_3547_);
lean_dec_ref_known(v___x_3542_, 2);
v_idx_3519_ = v_idx_3530_;
v___y_3520_ = v_res_3531_;
v_pos_3521_ = v_pos_3546_;
v_err_3522_ = v_err_3547_;
goto v___jp_3518_;
}
}
}
}
v___jp_3550_:
{
uint8_t v___x_3555_; 
v___x_3555_ = lean_nat_dec_eq(v_idx_3549_, v_idx_3553_);
lean_dec(v_idx_3549_);
if (v___x_3555_ == 0)
{
lean_object* v___x_3556_; 
lean_dec(v_idx_3553_);
lean_dec_ref(v_array_3552_);
lean_del_object(v___x_3507_);
lean_dec(v_res_3505_);
lean_dec_ref(v_config_3499_);
v___x_3556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3556_, 0, v_pos_3551_);
lean_ctor_set(v___x_3556_, 1, v_err_3554_);
return v___x_3556_;
}
else
{
lean_object* v___x_3557_; 
lean_dec(v_err_3554_);
v___x_3557_ = lean_box(0);
v_pos_3528_ = v_pos_3551_;
v_array_3529_ = v_array_3552_;
v_idx_3530_ = v_idx_3553_;
v_res_3531_ = v___x_3557_;
goto v___jp_3527_;
}
}
}
}
else
{
lean_object* v_pos_3587_; lean_object* v_err_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
lean_dec_ref(v_config_3499_);
v_pos_3587_ = lean_ctor_get(v___x_3503_, 0);
v_err_3588_ = lean_ctor_get(v___x_3503_, 1);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3503_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_err_3588_);
lean_inc(v_pos_3587_);
lean_dec(v___x_3503_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3593_; 
if (v_isShared_3591_ == 0)
{
v___x_3593_ = v___x_3590_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_pos_3587_);
lean_ctor_set(v_reuseFailAlloc_3594_, 1, v_err_3588_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_relative(lean_object* v_config_3596_, lean_object* v_a_3597_){
_start:
{
lean_object* v___y_3599_; lean_object* v___x_3619_; 
lean_inc_ref(v_a_3597_);
lean_inc_ref(v_config_3596_);
v___x_3619_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withAuthority(v_config_3596_, v_a_3597_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_dec_ref(v_a_3597_);
lean_dec_ref(v_config_3596_);
v___y_3599_ = v___x_3619_;
goto v___jp_3598_;
}
else
{
lean_object* v_pos_3620_; lean_object* v_idx_3621_; lean_object* v_idx_3622_; uint8_t v___x_3623_; 
v_pos_3620_ = lean_ctor_get(v___x_3619_, 0);
v_idx_3621_ = lean_ctor_get(v_a_3597_, 1);
lean_inc(v_idx_3621_);
lean_dec_ref(v_a_3597_);
v_idx_3622_ = lean_ctor_get(v_pos_3620_, 1);
v___x_3623_ = lean_nat_dec_eq(v_idx_3621_, v_idx_3622_);
lean_dec(v_idx_3621_);
if (v___x_3623_ == 0)
{
lean_dec_ref(v_config_3596_);
v___y_3599_ = v___x_3619_;
goto v___jp_3598_;
}
else
{
lean_object* v___x_3624_; 
lean_inc(v_pos_3620_);
lean_dec_ref_known(v___x_3619_, 2);
v___x_3624_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath(v_config_3596_, v_pos_3620_);
v___y_3599_ = v___x_3624_;
goto v___jp_3598_;
}
}
v___jp_3598_:
{
if (lean_obj_tag(v___y_3599_) == 0)
{
lean_object* v_pos_3600_; lean_object* v_res_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3609_; 
v_pos_3600_ = lean_ctor_get(v___y_3599_, 0);
v_res_3601_ = lean_ctor_get(v___y_3599_, 1);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___y_3599_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3603_ = v___y_3599_;
v_isShared_3604_ = v_isSharedCheck_3609_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_res_3601_);
lean_inc(v_pos_3600_);
lean_dec(v___y_3599_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3609_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3605_; lean_object* v___x_3607_; 
v___x_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3605_, 0, v_res_3601_);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 1, v___x_3605_);
v___x_3607_ = v___x_3603_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_pos_3600_);
lean_ctor_set(v_reuseFailAlloc_3608_, 1, v___x_3605_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
else
{
lean_object* v_pos_3610_; lean_object* v_err_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
v_pos_3610_ = lean_ctor_get(v___y_3599_, 0);
v_err_3611_ = lean_ctor_get(v___y_3599_, 1);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___y_3599_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___y_3599_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_err_3611_);
lean_inc(v_pos_3610_);
lean_dec(v___y_3599_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_pos_3610_);
lean_ctor_set(v_reuseFailAlloc_3617_, 1, v_err_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURIReference(lean_object* v_config_3625_, lean_object* v_a_3626_){
_start:
{
lean_object* v___y_3628_; lean_object* v_pos_3629_; lean_object* v___x_3634_; 
lean_inc_ref(v_a_3626_);
lean_inc_ref(v_config_3625_);
v___x_3634_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_uri(v_config_3625_, v_a_3626_);
if (lean_obj_tag(v___x_3634_) == 0)
{
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_dec_ref(v_a_3626_);
lean_dec_ref(v_config_3625_);
return v___x_3634_;
}
else
{
lean_object* v_pos_3635_; 
v_pos_3635_ = lean_ctor_get(v___x_3634_, 0);
lean_inc(v_pos_3635_);
v___y_3628_ = v___x_3634_;
v_pos_3629_ = v_pos_3635_;
goto v___jp_3627_;
}
}
else
{
lean_object* v_err_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3643_; 
v_err_3636_ = lean_ctor_get(v___x_3634_, 1);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3643_ == 0)
{
lean_object* v_unused_3644_; 
v_unused_3644_ = lean_ctor_get(v___x_3634_, 0);
lean_dec(v_unused_3644_);
v___x_3638_ = v___x_3634_;
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_err_3636_);
lean_dec(v___x_3634_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3641_; 
lean_inc_ref(v_a_3626_);
if (v_isShared_3639_ == 0)
{
lean_ctor_set(v___x_3638_, 0, v_a_3626_);
v___x_3641_ = v___x_3638_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_a_3626_);
lean_ctor_set(v_reuseFailAlloc_3642_, 1, v_err_3636_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
lean_inc_ref(v_a_3626_);
v___y_3628_ = v___x_3641_;
v_pos_3629_ = v_a_3626_;
goto v___jp_3627_;
}
}
}
v___jp_3627_:
{
lean_object* v_idx_3630_; lean_object* v_idx_3631_; uint8_t v___x_3632_; 
v_idx_3630_ = lean_ctor_get(v_a_3626_, 1);
lean_inc(v_idx_3630_);
lean_dec_ref(v_a_3626_);
v_idx_3631_ = lean_ctor_get(v_pos_3629_, 1);
v___x_3632_ = lean_nat_dec_eq(v_idx_3630_, v_idx_3631_);
lean_dec(v_idx_3630_);
if (v___x_3632_ == 0)
{
lean_dec_ref(v_pos_3629_);
lean_dec_ref(v_config_3625_);
return v___y_3628_;
}
else
{
lean_object* v___x_3633_; 
lean_dec_ref(v___y_3628_);
v___x_3633_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_relative(v_config_3625_, v_pos_3629_);
return v___x_3633_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader(lean_object* v_config_3651_, lean_object* v_a_3652_){
_start:
{
lean_object* v___x_3653_; 
v___x_3653_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_3651_, v_a_3652_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v_pos_3654_; lean_object* v_res_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3728_; 
v_pos_3654_ = lean_ctor_get(v___x_3653_, 0);
v_res_3655_ = lean_ctor_get(v___x_3653_, 1);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3657_ = v___x_3653_;
v_isShared_3658_ = v_isSharedCheck_3728_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_res_3655_);
lean_inc(v_pos_3654_);
lean_dec(v___x_3653_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3728_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v_port_3660_; lean_object* v___y_3661_; lean_object* v_pos_3675_; lean_object* v_pos_3678_; lean_object* v_array_3679_; lean_object* v_idx_3680_; lean_object* v_array_3686_; lean_object* v_idx_3687_; lean_object* v___x_3688_; uint8_t v___x_3689_; 
v_array_3686_ = lean_ctor_get(v_pos_3654_, 0);
v_idx_3687_ = lean_ctor_get(v_pos_3654_, 1);
v___x_3688_ = lean_byte_array_size(v_array_3686_);
v___x_3689_ = lean_nat_dec_lt(v_idx_3687_, v___x_3688_);
if (v___x_3689_ == 0)
{
v_pos_3675_ = v_pos_3654_;
goto v___jp_3674_;
}
else
{
uint8_t v___x_3690_; uint8_t v___x_3691_; uint8_t v___x_3692_; 
v___x_3690_ = lean_byte_array_fget(v_array_3686_, v_idx_3687_);
v___x_3691_ = 58;
v___x_3692_ = lean_uint8_dec_eq(v___x_3690_, v___x_3691_);
if (v___x_3692_ == 0)
{
v_pos_3675_ = v_pos_3654_;
goto v___jp_3674_;
}
else
{
if (v___x_3689_ == 0)
{
lean_object* v___x_3693_; lean_object* v___x_3694_; 
lean_del_object(v___x_3657_);
lean_dec(v_res_3655_);
v___x_3693_ = lean_box(0);
v___x_3694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3694_, 0, v_pos_3654_);
lean_ctor_set(v___x_3694_, 1, v___x_3693_);
return v___x_3694_;
}
else
{
if (v___x_3692_ == 0)
{
lean_object* v___x_3695_; lean_object* v___x_3696_; 
lean_del_object(v___x_3657_);
lean_dec(v_res_3655_);
v___x_3695_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
v___x_3696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3696_, 0, v_pos_3654_);
lean_ctor_set(v___x_3696_, 1, v___x_3695_);
return v___x_3696_;
}
else
{
lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3725_; 
lean_inc(v_idx_3687_);
lean_inc_ref(v_array_3686_);
v_isSharedCheck_3725_ = !lean_is_exclusive(v_pos_3654_);
if (v_isSharedCheck_3725_ == 0)
{
lean_object* v_unused_3726_; lean_object* v_unused_3727_; 
v_unused_3726_ = lean_ctor_get(v_pos_3654_, 1);
lean_dec(v_unused_3726_);
v_unused_3727_ = lean_ctor_get(v_pos_3654_, 0);
lean_dec(v_unused_3727_);
v___x_3698_ = v_pos_3654_;
v_isShared_3699_ = v_isSharedCheck_3725_;
goto v_resetjp_3697_;
}
else
{
lean_dec(v_pos_3654_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3725_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3703_; 
v___x_3700_ = lean_unsigned_to_nat(1u);
v___x_3701_ = lean_nat_add(v_idx_3687_, v___x_3700_);
lean_dec(v_idx_3687_);
lean_inc(v___x_3701_);
lean_inc_ref(v_array_3686_);
if (v_isShared_3699_ == 0)
{
lean_ctor_set(v___x_3698_, 1, v___x_3701_);
v___x_3703_ = v___x_3698_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_array_3686_);
lean_ctor_set(v_reuseFailAlloc_3724_, 1, v___x_3701_);
v___x_3703_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
uint8_t v___x_3704_; 
v___x_3704_ = lean_nat_dec_lt(v___x_3701_, v___x_3688_);
if (v___x_3704_ == 0)
{
v_pos_3678_ = v___x_3703_;
v_array_3679_ = v_array_3686_;
v_idx_3680_ = v___x_3701_;
goto v___jp_3677_;
}
else
{
uint8_t v___x_3705_; uint8_t v___x_3706_; uint8_t v___x_3707_; 
v___x_3705_ = lean_byte_array_fget(v_array_3686_, v___x_3701_);
v___x_3706_ = 48;
v___x_3707_ = lean_uint8_dec_le(v___x_3706_, v___x_3705_);
if (v___x_3707_ == 0)
{
v_pos_3678_ = v___x_3703_;
v_array_3679_ = v_array_3686_;
v_idx_3680_ = v___x_3701_;
goto v___jp_3677_;
}
else
{
uint8_t v___x_3708_; uint8_t v___x_3709_; 
v___x_3708_ = 57;
v___x_3709_ = lean_uint8_dec_le(v___x_3705_, v___x_3708_);
if (v___x_3709_ == 0)
{
v_pos_3678_ = v___x_3703_;
v_array_3679_ = v_array_3686_;
v_idx_3680_ = v___x_3701_;
goto v___jp_3677_;
}
else
{
lean_object* v___x_3710_; 
lean_dec(v___x_3701_);
lean_dec_ref(v_array_3686_);
v___x_3710_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_3703_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v_pos_3711_; lean_object* v_res_3712_; lean_object* v___x_3713_; uint16_t v___x_3714_; 
v_pos_3711_ = lean_ctor_get(v___x_3710_, 0);
lean_inc(v_pos_3711_);
v_res_3712_ = lean_ctor_get(v___x_3710_, 1);
lean_inc(v_res_3712_);
lean_dec_ref_known(v___x_3710_, 2);
v___x_3713_ = lean_alloc_ctor(2, 0, 2);
v___x_3714_ = lean_unbox(v_res_3712_);
lean_dec(v_res_3712_);
lean_ctor_set_uint16(v___x_3713_, 0, v___x_3714_);
v_port_3660_ = v___x_3713_;
v___y_3661_ = v_pos_3711_;
goto v___jp_3659_;
}
else
{
lean_object* v_pos_3715_; lean_object* v_err_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3723_; 
lean_del_object(v___x_3657_);
lean_dec(v_res_3655_);
v_pos_3715_ = lean_ctor_get(v___x_3710_, 0);
v_err_3716_ = lean_ctor_get(v___x_3710_, 1);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3718_ = v___x_3710_;
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_err_3716_);
lean_inc(v_pos_3715_);
lean_dec(v___x_3710_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3721_; 
if (v_isShared_3719_ == 0)
{
v___x_3721_ = v___x_3718_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_pos_3715_);
lean_ctor_set(v_reuseFailAlloc_3722_, 1, v_err_3716_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
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
v___jp_3659_:
{
lean_object* v_array_3662_; lean_object* v_idx_3663_; lean_object* v___x_3664_; uint8_t v___x_3665_; 
v_array_3662_ = lean_ctor_get(v___y_3661_, 0);
v_idx_3663_ = lean_ctor_get(v___y_3661_, 1);
v___x_3664_ = lean_byte_array_size(v_array_3662_);
v___x_3665_ = lean_nat_dec_lt(v_idx_3663_, v___x_3664_);
if (v___x_3665_ == 0)
{
lean_object* v___x_3666_; lean_object* v___x_3668_; 
v___x_3666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3666_, 0, v_res_3655_);
lean_ctor_set(v___x_3666_, 1, v_port_3660_);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 1, v___x_3666_);
lean_ctor_set(v___x_3657_, 0, v___y_3661_);
v___x_3668_ = v___x_3657_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___y_3661_);
lean_ctor_set(v_reuseFailAlloc_3669_, 1, v___x_3666_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
else
{
lean_object* v___x_3670_; lean_object* v___x_3672_; 
lean_dec(v_port_3660_);
lean_dec(v_res_3655_);
v___x_3670_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__1));
if (v_isShared_3658_ == 0)
{
lean_ctor_set_tag(v___x_3657_, 1);
lean_ctor_set(v___x_3657_, 1, v___x_3670_);
lean_ctor_set(v___x_3657_, 0, v___y_3661_);
v___x_3672_ = v___x_3657_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___y_3661_);
lean_ctor_set(v_reuseFailAlloc_3673_, 1, v___x_3670_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
v___jp_3674_:
{
lean_object* v___x_3676_; 
v___x_3676_ = lean_box(0);
v_port_3660_ = v___x_3676_;
v___y_3661_ = v_pos_3675_;
goto v___jp_3659_;
}
v___jp_3677_:
{
lean_object* v___x_3681_; uint8_t v___x_3682_; 
v___x_3681_ = lean_byte_array_size(v_array_3679_);
lean_dec_ref(v_array_3679_);
v___x_3682_ = lean_nat_dec_lt(v_idx_3680_, v___x_3681_);
lean_dec(v_idx_3680_);
if (v___x_3682_ == 0)
{
lean_object* v___x_3683_; 
v___x_3683_ = lean_box(1);
v_port_3660_ = v___x_3683_;
v___y_3661_ = v_pos_3678_;
goto v___jp_3659_;
}
else
{
lean_object* v___x_3684_; lean_object* v___x_3685_; 
lean_del_object(v___x_3657_);
lean_dec(v_res_3655_);
v___x_3684_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__3));
v___x_3685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3685_, 0, v_pos_3678_);
lean_ctor_set(v___x_3685_, 1, v___x_3684_);
return v___x_3685_;
}
}
}
}
else
{
lean_object* v_pos_3729_; lean_object* v_err_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
v_pos_3729_ = lean_ctor_get(v___x_3653_, 0);
v_err_3730_ = lean_ctor_get(v___x_3653_, 1);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3653_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_err_3730_);
lean_inc(v_pos_3729_);
lean_dec(v___x_3653_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_pos_3729_);
lean_ctor_set(v_reuseFailAlloc_3736_, 1, v_err_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader___boxed(lean_object* v_config_3738_, lean_object* v_a_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l_Std_Http_URI_Parser_parseHostHeader(v_config_3738_, v_a_3739_);
lean_dec_ref(v_config_3738_);
return v_res_3740_;
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
