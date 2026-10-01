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
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ByteArray_toByteSlice(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_ByteSlice_toByteArray(lean_object*);
lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(lean_object*);
lean_object* l_ByteSlice_size(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Http_URI_isValidDomainLabel(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
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
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1___boxed(lean_object*);
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "invalid percent encoding in user info"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1_value;
static const lean_closure_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__2 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__2_value;
static const lean_closure_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__3 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__3_value;
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
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "invalid domain name: "};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "invalid host"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2_value;
static const lean_closure_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l_Std_Http_URI_Parser_parsePath___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_URI_Parser_parsePath___closed__2 = (const lean_object*)&l_Std_Http_URI_Parser_parsePath___closed__2_value;
static const lean_ctor_object l_Std_Http_URI_Parser_parsePath___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_URI_Parser_parsePath___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Http_URI_Parser_parsePath___closed__3 = (const lean_object*)&l_Std_Http_URI_Parser_parsePath___closed__3_value;
static const lean_string_object l_Std_Http_URI_Parser_parsePath___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "need a path"};
static const lean_object* l_Std_Http_URI_Parser_parsePath___closed__4 = (const lean_object*)&l_Std_Http_URI_Parser_parsePath___closed__4_value;
static const lean_ctor_object l_Std_Http_URI_Parser_parsePath___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_URI_Parser_parsePath___closed__4_value)}};
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
uint8_t v___y_80_; uint8_t v___y_81_; uint8_t v___y_82_; uint8_t v___y_84_; uint8_t v___x_101_; uint8_t v___x_102_; 
v___x_101_ = 48;
v___x_102_ = lean_uint8_dec_le(v___x_101_, v_c_78_);
if (v___x_102_ == 0)
{
goto v___jp_96_;
}
else
{
uint8_t v___x_103_; uint8_t v___x_104_; 
v___x_103_ = 57;
v___x_104_ = lean_uint8_dec_le(v_c_78_, v___x_103_);
if (v___x_104_ == 0)
{
goto v___jp_96_;
}
else
{
v___y_84_ = v___x_104_;
goto v___jp_83_;
}
}
v___jp_79_:
{
if (v___y_81_ == 0)
{
if (v___y_80_ == 0)
{
return v___y_82_;
}
else
{
return v___y_80_;
}
}
else
{
if (v___y_80_ == 0)
{
return v___y_81_;
}
else
{
return v___y_80_;
}
}
}
v___jp_83_:
{
uint8_t v___x_85_; uint8_t v___x_86_; uint8_t v___x_87_; uint8_t v___x_88_; 
v___x_85_ = 43;
v___x_86_ = lean_uint8_dec_eq(v_c_78_, v___x_85_);
v___x_87_ = 45;
v___x_88_ = lean_uint8_dec_eq(v_c_78_, v___x_87_);
if (v___x_88_ == 0)
{
uint8_t v___x_89_; uint8_t v___x_90_; 
v___x_89_ = 46;
v___x_90_ = lean_uint8_dec_eq(v_c_78_, v___x_89_);
v___y_80_ = v___y_84_;
v___y_81_ = v___x_86_;
v___y_82_ = v___x_90_;
goto v___jp_79_;
}
else
{
v___y_80_ = v___y_84_;
v___y_81_ = v___x_86_;
v___y_82_ = v___x_88_;
goto v___jp_79_;
}
}
v___jp_91_:
{
uint8_t v___x_92_; uint8_t v___x_93_; 
v___x_92_ = 65;
v___x_93_ = lean_uint8_dec_le(v___x_92_, v_c_78_);
if (v___x_93_ == 0)
{
v___y_84_ = v___x_93_;
goto v___jp_83_;
}
else
{
uint8_t v___x_94_; uint8_t v___x_95_; 
v___x_94_ = 90;
v___x_95_ = lean_uint8_dec_le(v_c_78_, v___x_94_);
v___y_84_ = v___x_95_;
goto v___jp_83_;
}
}
v___jp_96_:
{
uint8_t v___x_97_; uint8_t v___x_98_; 
v___x_97_ = 97;
v___x_98_ = lean_uint8_dec_le(v___x_97_, v_c_78_);
if (v___x_98_ == 0)
{
goto v___jp_91_;
}
else
{
uint8_t v___x_99_; uint8_t v___x_100_; 
v___x_99_ = 122;
v___x_100_ = lean_uint8_dec_le(v_c_78_, v___x_99_);
if (v___x_100_ == 0)
{
goto v___jp_91_;
}
else
{
v___y_84_ = v___x_100_;
goto v___jp_83_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___boxed(lean_object* v_c_105_){
_start:
{
uint8_t v_c_boxed_106_; uint8_t v_res_107_; lean_object* v_r_108_; 
v_c_boxed_106_ = lean_unbox(v_c_105_);
v_res_107_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0(v_c_boxed_106_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(lean_object* v_x_109_){
_start:
{
if (lean_obj_tag(v_x_109_) == 0)
{
uint8_t v___x_110_; 
v___x_110_ = 1;
return v___x_110_;
}
else
{
lean_object* v_head_111_; lean_object* v_tail_112_; uint8_t v___y_127_; uint32_t v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v___x_146_; 
v_head_111_ = lean_ctor_get(v_x_109_, 0);
v_tail_112_ = lean_ctor_get(v_x_109_, 1);
v___x_143_ = lean_unbox_uint32(v_head_111_);
v___x_144_ = lean_uint32_to_nat(v___x_143_);
v___x_145_ = lean_unsigned_to_nat(128u);
v___x_146_ = lean_nat_dec_lt(v___x_144_, v___x_145_);
lean_dec(v___x_144_);
if (v___x_146_ == 0)
{
goto v___jp_113_;
}
else
{
uint32_t v___x_147_; uint32_t v___x_148_; uint8_t v___x_149_; 
v___x_147_ = 48;
v___x_148_ = lean_unbox_uint32(v_head_111_);
v___x_149_ = lean_uint32_dec_le(v___x_147_, v___x_148_);
if (v___x_149_ == 0)
{
goto v___jp_136_;
}
else
{
uint32_t v___x_150_; uint32_t v___x_151_; uint8_t v___x_152_; 
v___x_150_ = 57;
v___x_151_ = lean_unbox_uint32(v_head_111_);
v___x_152_ = lean_uint32_dec_le(v___x_151_, v___x_150_);
if (v___x_152_ == 0)
{
goto v___jp_136_;
}
else
{
v_x_109_ = v_tail_112_;
goto _start;
}
}
}
v___jp_113_:
{
uint32_t v___x_114_; uint32_t v___x_115_; uint8_t v___x_116_; 
v___x_114_ = 43;
v___x_115_ = lean_unbox_uint32(v_head_111_);
v___x_116_ = lean_uint32_dec_eq(v___x_115_, v___x_114_);
if (v___x_116_ == 0)
{
uint32_t v___x_117_; uint32_t v___x_118_; uint8_t v___x_119_; 
v___x_117_ = 45;
v___x_118_ = lean_unbox_uint32(v_head_111_);
v___x_119_ = lean_uint32_dec_eq(v___x_118_, v___x_117_);
if (v___x_119_ == 0)
{
uint32_t v___x_120_; uint32_t v___x_121_; uint8_t v___x_122_; 
v___x_120_ = 46;
v___x_121_ = lean_unbox_uint32(v_head_111_);
v___x_122_ = lean_uint32_dec_eq(v___x_121_, v___x_120_);
if (v___x_122_ == 0)
{
return v___x_122_;
}
else
{
v_x_109_ = v_tail_112_;
goto _start;
}
}
else
{
v_x_109_ = v_tail_112_;
goto _start;
}
}
else
{
v_x_109_ = v_tail_112_;
goto _start;
}
}
v___jp_126_:
{
if (v___y_127_ == 0)
{
uint32_t v___x_128_; uint32_t v___x_129_; uint8_t v___x_130_; 
v___x_128_ = 97;
v___x_129_ = lean_unbox_uint32(v_head_111_);
v___x_130_ = lean_uint32_dec_le(v___x_128_, v___x_129_);
if (v___x_130_ == 0)
{
goto v___jp_113_;
}
else
{
uint32_t v___x_131_; uint32_t v___x_132_; uint8_t v___x_133_; 
v___x_131_ = 122;
v___x_132_ = lean_unbox_uint32(v_head_111_);
v___x_133_ = lean_uint32_dec_le(v___x_132_, v___x_131_);
if (v___x_133_ == 0)
{
goto v___jp_113_;
}
else
{
v_x_109_ = v_tail_112_;
goto _start;
}
}
}
else
{
v_x_109_ = v_tail_112_;
goto _start;
}
}
v___jp_136_:
{
uint32_t v___x_137_; uint32_t v___x_138_; uint8_t v___x_139_; 
v___x_137_ = 65;
v___x_138_ = lean_unbox_uint32(v_head_111_);
v___x_139_ = lean_uint32_dec_le(v___x_137_, v___x_138_);
if (v___x_139_ == 0)
{
v___y_127_ = v___x_139_;
goto v___jp_126_;
}
else
{
uint32_t v___x_140_; uint32_t v___x_141_; uint8_t v___x_142_; 
v___x_140_ = 90;
v___x_141_ = lean_unbox_uint32(v_head_111_);
v___x_142_ = lean_uint32_dec_le(v___x_141_, v___x_140_);
v___y_127_ = v___x_142_;
goto v___jp_126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1___boxed(lean_object* v_x_154_){
_start:
{
uint8_t v_res_155_; lean_object* v_r_156_; 
v_res_155_ = l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(v_x_154_);
lean_dec(v_x_154_);
v_r_156_ = lean_box(v_res_155_);
return v_r_156_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(lean_object* v_s_157_, lean_object* v_p_158_){
_start:
{
uint32_t v___y_160_; lean_object* v___x_165_; uint8_t v_decide_166_; 
v___x_165_ = lean_string_utf8_byte_size(v_s_157_);
v_decide_166_ = lean_nat_dec_eq(v_p_158_, v___x_165_);
if (v_decide_166_ == 0)
{
uint32_t v___x_167_; uint8_t v___y_169_; uint32_t v___x_172_; uint8_t v___x_173_; 
v___x_167_ = lean_string_utf8_get_fast(v_s_157_, v_p_158_);
v___x_172_ = 65;
v___x_173_ = lean_uint32_dec_le(v___x_172_, v___x_167_);
if (v___x_173_ == 0)
{
v___y_169_ = v___x_173_;
goto v___jp_168_;
}
else
{
uint32_t v___x_174_; uint8_t v___x_175_; 
v___x_174_ = 90;
v___x_175_ = lean_uint32_dec_le(v___x_167_, v___x_174_);
v___y_169_ = v___x_175_;
goto v___jp_168_;
}
v___jp_168_:
{
if (v___y_169_ == 0)
{
v___y_160_ = v___x_167_;
goto v___jp_159_;
}
else
{
uint32_t v___x_170_; uint32_t v___x_171_; 
v___x_170_ = 32;
v___x_171_ = lean_uint32_add(v___x_167_, v___x_170_);
v___y_160_ = v___x_171_;
goto v___jp_159_;
}
}
}
else
{
lean_dec(v_p_158_);
return v_s_157_;
}
v___jp_159_:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
lean_inc(v_p_158_);
v___x_161_ = lean_string_utf8_set(v_s_157_, v_p_158_, v___y_160_);
v___x_162_ = l_Char_utf8Size(v___y_160_);
v___x_163_ = lean_nat_add(v_p_158_, v___x_162_);
lean_dec(v___x_162_);
lean_dec(v_p_158_);
v_s_157_ = v___x_161_;
v_p_158_ = v___x_163_;
goto _start;
}
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_185_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6));
v___x_186_ = lean_unsigned_to_nat(46u);
v___x_187_ = lean_unsigned_to_nat(193u);
v___x_188_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5));
v___x_189_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__4));
v___x_190_ = l_mkPanicMessageWithDecl(v___x_189_, v___x_188_, v___x_187_, v___x_186_, v___x_185_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(lean_object* v_config_195_, lean_object* v_a_196_){
_start:
{
lean_object* v___y_201_; lean_object* v___y_205_; lean_object* v___y_206_; uint8_t v___y_207_; uint8_t v___y_208_; lean_object* v___y_211_; lean_object* v___y_212_; uint8_t v___y_213_; uint8_t v___y_214_; uint8_t v___y_215_; lean_object* v___y_217_; lean_object* v___y_218_; uint8_t v___y_219_; uint32_t v___y_220_; uint8_t v___y_221_; uint8_t v___y_222_; lean_object* v_maxSchemeLength_227_; lean_object* v___x_228_; uint8_t v___x_229_; lean_object* v___y_231_; lean_object* v___y_232_; lean_object* v___y_248_; uint8_t v___y_249_; lean_object* v___y_250_; lean_object* v_lower_251_; lean_object* v_upper_252_; uint8_t v___y_265_; lean_object* v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; 
v_maxSchemeLength_227_ = lean_ctor_get(v_config_195_, 0);
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = lean_nat_dec_eq(v_maxSchemeLength_227_, v___x_228_);
if (v___x_229_ == 0)
{
lean_object* v_array_272_; lean_object* v_idx_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v_array_272_ = lean_ctor_get(v_a_196_, 0);
v_idx_273_ = lean_ctor_get(v_a_196_, 1);
v___x_274_ = lean_byte_array_size(v_array_272_);
v___x_275_ = lean_nat_dec_lt(v_idx_273_, v___x_274_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_box(0);
v___x_277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_277_, 0, v_a_196_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
return v___x_277_;
}
else
{
lean_object* v___f_278_; lean_object* v_pos_280_; uint8_t v_res_281_; uint8_t v_c_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v_it_x27_296_; uint8_t v___x_302_; uint8_t v___x_303_; 
v___f_278_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__8));
v_c_293_ = lean_byte_array_fget(v_array_272_, v_idx_273_);
v___x_294_ = lean_unsigned_to_nat(1u);
v___x_295_ = lean_nat_add(v_idx_273_, v___x_294_);
lean_inc_ref(v_array_272_);
v_it_x27_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_296_, 0, v_array_272_);
lean_ctor_set(v_it_x27_296_, 1, v___x_295_);
v___x_302_ = 65;
v___x_303_ = lean_uint8_dec_le(v___x_302_, v_c_293_);
if (v___x_303_ == 0)
{
goto v___jp_297_;
}
else
{
uint8_t v___x_304_; uint8_t v___x_305_; 
v___x_304_ = 90;
v___x_305_ = lean_uint8_dec_le(v_c_293_, v___x_304_);
if (v___x_305_ == 0)
{
goto v___jp_297_;
}
else
{
lean_dec_ref(v_a_196_);
v_pos_280_ = v_it_x27_296_;
v_res_281_ = v_c_293_;
goto v___jp_279_;
}
}
v___jp_279_:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v_snd_285_; lean_object* v_fst_286_; lean_object* v_fst_287_; lean_object* v_array_288_; lean_object* v_idx_289_; lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_282_ = lean_unsigned_to_nat(1u);
v___x_283_ = lean_nat_sub(v_maxSchemeLength_227_, v___x_282_);
lean_inc_ref(v_pos_280_);
v___x_284_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_278_, v___x_283_, v___x_228_, v_pos_280_);
lean_dec(v___x_283_);
v_snd_285_ = lean_ctor_get(v___x_284_, 1);
lean_inc(v_snd_285_);
v_fst_286_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_fst_286_);
lean_dec_ref(v___x_284_);
v_fst_287_ = lean_ctor_get(v_snd_285_, 0);
lean_inc(v_fst_287_);
lean_dec(v_snd_285_);
v_array_288_ = lean_ctor_get(v_pos_280_, 0);
lean_inc_ref(v_array_288_);
v_idx_289_ = lean_ctor_get(v_pos_280_, 1);
lean_inc(v_idx_289_);
lean_dec_ref(v_pos_280_);
v___x_290_ = lean_nat_add(v_idx_289_, v_fst_286_);
lean_dec(v_fst_286_);
v___x_291_ = lean_byte_array_size(v_array_288_);
v___x_292_ = lean_nat_dec_le(v_idx_289_, v___x_228_);
if (v___x_292_ == 0)
{
v___y_265_ = v_res_281_;
v___y_266_ = v_fst_287_;
v___y_267_ = v___x_291_;
v___y_268_ = v_array_288_;
v___y_269_ = v___x_290_;
v___y_270_ = v_idx_289_;
goto v___jp_264_;
}
else
{
lean_dec(v_idx_289_);
v___y_265_ = v_res_281_;
v___y_266_ = v_fst_287_;
v___y_267_ = v___x_291_;
v___y_268_ = v_array_288_;
v___y_269_ = v___x_290_;
v___y_270_ = v___x_228_;
goto v___jp_264_;
}
}
v___jp_297_:
{
uint8_t v___x_298_; uint8_t v___x_299_; 
v___x_298_ = 97;
v___x_299_ = lean_uint8_dec_le(v___x_298_, v_c_293_);
if (v___x_299_ == 0)
{
lean_dec_ref_known(v_it_x27_296_, 2);
goto v___jp_197_;
}
else
{
uint8_t v___x_300_; uint8_t v___x_301_; 
v___x_300_ = 122;
v___x_301_ = lean_uint8_dec_le(v_c_293_, v___x_300_);
if (v___x_301_ == 0)
{
lean_dec_ref_known(v_it_x27_296_, 2);
goto v___jp_197_;
}
else
{
lean_dec_ref(v_a_196_);
v_pos_280_ = v_it_x27_296_;
v_res_281_ = v_c_293_;
goto v___jp_279_;
}
}
}
}
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10));
v___x_307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_307_, 0, v_a_196_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
return v___x_307_;
}
v___jp_197_:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__1));
v___x_199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_199_, 0, v_a_196_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
return v___x_199_;
}
v___jp_200_:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__3));
v___x_203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_203_, 0, v___y_201_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
return v___x_203_;
}
v___jp_204_:
{
if (v___y_207_ == 0)
{
lean_dec_ref(v___y_205_);
v___y_201_ = v___y_206_;
goto v___jp_200_;
}
else
{
if (v___y_208_ == 0)
{
lean_dec_ref(v___y_205_);
v___y_201_ = v___y_206_;
goto v___jp_200_;
}
else
{
lean_object* v___x_209_; 
v___x_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_209_, 0, v___y_206_);
lean_ctor_set(v___x_209_, 1, v___y_205_);
return v___x_209_;
}
}
}
v___jp_210_:
{
if (v___y_213_ == 0)
{
v___y_205_ = v___y_211_;
v___y_206_ = v___y_212_;
v___y_207_ = v___y_214_;
v___y_208_ = v___y_213_;
goto v___jp_204_;
}
else
{
v___y_205_ = v___y_211_;
v___y_206_ = v___y_212_;
v___y_207_ = v___y_214_;
v___y_208_ = v___y_215_;
goto v___jp_204_;
}
}
v___jp_216_:
{
if (v___y_222_ == 0)
{
uint32_t v___x_223_; uint8_t v___x_224_; 
v___x_223_ = 97;
v___x_224_ = lean_uint32_dec_le(v___x_223_, v___y_220_);
if (v___x_224_ == 0)
{
v___y_211_ = v___y_217_;
v___y_212_ = v___y_218_;
v___y_213_ = v___y_219_;
v___y_214_ = v___y_221_;
v___y_215_ = v___x_224_;
goto v___jp_210_;
}
else
{
uint32_t v___x_225_; uint8_t v___x_226_; 
v___x_225_ = 122;
v___x_226_ = lean_uint32_dec_le(v___y_220_, v___x_225_);
v___y_211_ = v___y_217_;
v___y_212_ = v___y_218_;
v___y_213_ = v___y_219_;
v___y_214_ = v___y_221_;
v___y_215_ = v___x_226_;
goto v___jp_210_;
}
}
else
{
v___y_211_ = v___y_217_;
v___y_212_ = v___y_218_;
v___y_213_ = v___y_219_;
v___y_214_ = v___y_221_;
v___y_215_ = v___y_222_;
goto v___jp_210_;
}
}
v___jp_230_:
{
lean_object* v___x_233_; uint8_t v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; lean_object* v___x_237_; 
v___x_233_ = l_String_mapAux___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(v___y_232_, v___x_228_);
lean_inc_ref_n(v___x_233_, 2);
v___x_234_ = l_Std_Http_Internal_instDecidableIsLowerCase(v___x_233_);
v___x_235_ = lean_string_data(v___x_233_);
v___x_236_ = l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(v___x_235_);
v___x_237_ = l_List_head_x3f___redArg(v___x_235_);
lean_dec(v___x_235_);
if (lean_obj_tag(v___x_237_) == 0)
{
v___y_211_ = v___x_233_;
v___y_212_ = v___y_231_;
v___y_213_ = v___x_236_;
v___y_214_ = v___x_234_;
v___y_215_ = v___x_229_;
goto v___jp_210_;
}
else
{
lean_object* v_val_238_; uint32_t v___x_239_; uint32_t v___x_240_; uint8_t v___x_241_; 
v_val_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_val_238_);
lean_dec_ref_known(v___x_237_, 1);
v___x_239_ = 65;
v___x_240_ = lean_unbox_uint32(v_val_238_);
v___x_241_ = lean_uint32_dec_le(v___x_239_, v___x_240_);
if (v___x_241_ == 0)
{
uint32_t v___x_242_; 
v___x_242_ = lean_unbox_uint32(v_val_238_);
lean_dec(v_val_238_);
v___y_217_ = v___x_233_;
v___y_218_ = v___y_231_;
v___y_219_ = v___x_236_;
v___y_220_ = v___x_242_;
v___y_221_ = v___x_234_;
v___y_222_ = v___x_241_;
goto v___jp_216_;
}
else
{
uint32_t v___x_243_; uint32_t v___x_244_; uint8_t v___x_245_; uint32_t v___x_246_; 
v___x_243_ = 90;
v___x_244_ = lean_unbox_uint32(v_val_238_);
v___x_245_ = lean_uint32_dec_le(v___x_244_, v___x_243_);
v___x_246_ = lean_unbox_uint32(v_val_238_);
lean_dec(v_val_238_);
v___y_217_ = v___x_233_;
v___y_218_ = v___y_231_;
v___y_219_ = v___x_236_;
v___y_220_ = v___x_246_;
v___y_221_ = v___x_234_;
v___y_222_ = v___x_245_;
goto v___jp_216_;
}
}
}
v___jp_247_:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_253_ = l_ByteArray_toByteSlice(v___y_250_, v_lower_251_, v_upper_252_);
v___x_254_ = l_ByteArray_empty;
v___x_255_ = lean_byte_array_push(v___x_254_, v___y_249_);
v___x_256_ = l_ByteSlice_toByteArray(v___x_253_);
v___x_257_ = lean_byte_array_size(v___x_255_);
v___x_258_ = lean_byte_array_size(v___x_256_);
v___x_259_ = lean_byte_array_copy_slice(v___x_256_, v___x_228_, v___x_255_, v___x_257_, v___x_258_, v___x_229_);
lean_dec_ref(v___x_256_);
v___x_260_ = lean_string_validate_utf8(v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; 
lean_dec_ref(v___x_259_);
v___x_261_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_262_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_261_);
v___y_231_ = v___y_248_;
v___y_232_ = v___x_262_;
goto v___jp_230_;
}
else
{
lean_object* v___x_263_; 
v___x_263_ = lean_string_from_utf8_unchecked(v___x_259_);
v___y_231_ = v___y_248_;
v___y_232_ = v___x_263_;
goto v___jp_230_;
}
}
v___jp_264_:
{
uint8_t v___x_271_; 
v___x_271_ = lean_nat_dec_le(v___y_269_, v___y_267_);
if (v___x_271_ == 0)
{
lean_dec(v___y_269_);
v___y_248_ = v___y_266_;
v___y_249_ = v___y_265_;
v___y_250_ = v___y_268_;
v_lower_251_ = v___y_270_;
v_upper_252_ = v___y_267_;
goto v___jp_247_;
}
else
{
lean_dec(v___y_267_);
v___y_248_ = v___y_266_;
v___y_249_ = v___y_265_;
v___y_250_ = v___y_268_;
v_lower_251_ = v___y_270_;
v_upper_252_ = v___y_269_;
goto v___jp_247_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___boxed(lean_object* v_config_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_308_, v_a_309_);
lean_dec_ref(v_config_308_);
return v_res_310_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0(uint8_t v___y_311_){
_start:
{
uint8_t v___x_312_; uint8_t v___x_313_; 
v___x_312_ = 48;
v___x_313_ = lean_uint8_dec_le(v___x_312_, v___y_311_);
if (v___x_313_ == 0)
{
return v___x_313_;
}
else
{
uint8_t v___x_314_; uint8_t v___x_315_; 
v___x_314_ = 57;
v___x_315_ = lean_uint8_dec_le(v___y_311_, v___x_314_);
return v___x_315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0___boxed(lean_object* v___y_316_){
_start:
{
uint8_t v___y_560__boxed_317_; uint8_t v_res_318_; lean_object* v_r_319_; 
v___y_560__boxed_317_ = lean_unbox(v___y_316_);
v_res_318_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0(v___y_560__boxed_317_);
v_r_319_ = lean_box(v_res_318_);
return v_r_319_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(lean_object* v_a_323_){
_start:
{
lean_object* v___f_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v_snd_328_; lean_object* v_fst_329_; lean_object* v_fst_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_383_; 
v___f_324_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__0));
v___x_325_ = lean_unsigned_to_nat(5u);
v___x_326_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_323_);
v___x_327_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_324_, v___x_325_, v___x_326_, v_a_323_);
v_snd_328_ = lean_ctor_get(v___x_327_, 1);
lean_inc(v_snd_328_);
v_fst_329_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_fst_329_);
lean_dec_ref(v___x_327_);
v_fst_330_ = lean_ctor_get(v_snd_328_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v_snd_328_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; 
v_unused_384_ = lean_ctor_get(v_snd_328_, 1);
lean_dec(v_unused_384_);
v___x_332_ = v_snd_328_;
v_isShared_333_ = v_isSharedCheck_383_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_fst_330_);
lean_dec(v_snd_328_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_383_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___y_335_; lean_object* v_array_366_; lean_object* v_idx_367_; lean_object* v_lower_369_; lean_object* v_upper_370_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___y_380_; uint8_t v___x_382_; 
v_array_366_ = lean_ctor_get(v_a_323_, 0);
lean_inc_ref(v_array_366_);
v_idx_367_ = lean_ctor_get(v_a_323_, 1);
lean_inc(v_idx_367_);
lean_dec_ref(v_a_323_);
v___x_377_ = lean_nat_add(v_idx_367_, v_fst_329_);
lean_dec(v_fst_329_);
v___x_378_ = lean_byte_array_size(v_array_366_);
v___x_382_ = lean_nat_dec_le(v_idx_367_, v___x_326_);
if (v___x_382_ == 0)
{
v___y_380_ = v_idx_367_;
goto v___jp_379_;
}
else
{
lean_dec(v_idx_367_);
v___y_380_ = v___x_326_;
goto v___jp_379_;
}
v___jp_334_:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_336_ = lean_string_utf8_byte_size(v___y_335_);
lean_inc_ref(v___y_335_);
v___x_337_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_337_, 0, v___y_335_);
lean_ctor_set(v___x_337_, 1, v___x_326_);
lean_ctor_set(v___x_337_, 2, v___x_336_);
v___x_338_ = l_String_Slice_toNat_x3f(v___x_337_);
lean_dec_ref_known(v___x_337_, 3);
if (lean_obj_tag(v___x_338_) == 1)
{
lean_object* v_val_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_359_; 
lean_dec_ref(v___y_335_);
v_val_339_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_359_ == 0)
{
v___x_341_ = v___x_338_;
v_isShared_342_ = v_isSharedCheck_359_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_val_339_);
lean_dec(v___x_338_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_359_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = lean_unsigned_to_nat(65535u);
v___x_344_ = lean_nat_dec_lt(v___x_343_, v_val_339_);
if (v___x_344_ == 0)
{
uint16_t v___x_345_; lean_object* v___x_346_; lean_object* v___x_348_; 
lean_del_object(v___x_341_);
v___x_345_ = lean_uint16_of_nat(v_val_339_);
lean_dec(v_val_339_);
v___x_346_ = lean_box(v___x_345_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v___x_346_);
v___x_348_ = v___x_332_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_fst_330_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v___x_346_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
else
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_350_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__1));
v___x_351_ = l_Nat_reprFast(v_val_339_);
v___x_352_ = lean_string_append(v___x_350_, v___x_351_);
lean_dec_ref(v___x_351_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v___x_352_);
v___x_354_ = v___x_341_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_358_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_356_; 
if (v_isShared_333_ == 0)
{
lean_ctor_set_tag(v___x_332_, 1);
lean_ctor_set(v___x_332_, 1, v___x_354_);
v___x_356_ = v___x_332_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_fst_330_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v___x_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_364_; 
lean_dec(v___x_338_);
v___x_360_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__2));
v___x_361_ = lean_string_append(v___x_360_, v___y_335_);
lean_dec_ref(v___y_335_);
v___x_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
if (v_isShared_333_ == 0)
{
lean_ctor_set_tag(v___x_332_, 1);
lean_ctor_set(v___x_332_, 1, v___x_362_);
v___x_364_ = v___x_332_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_fst_330_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v___x_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
v___jp_368_:
{
lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_371_ = l_ByteArray_toByteSlice(v_array_366_, v_lower_369_, v_upper_370_);
v___x_372_ = l_ByteSlice_toByteArray(v___x_371_);
v___x_373_ = lean_string_validate_utf8(v___x_372_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; lean_object* v___x_375_; 
lean_dec_ref(v___x_372_);
v___x_374_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_375_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_374_);
v___y_335_ = v___x_375_;
goto v___jp_334_;
}
else
{
lean_object* v___x_376_; 
v___x_376_ = lean_string_from_utf8_unchecked(v___x_372_);
v___y_335_ = v___x_376_;
goto v___jp_334_;
}
}
v___jp_379_:
{
uint8_t v___x_381_; 
v___x_381_ = lean_nat_dec_le(v___x_377_, v___x_378_);
if (v___x_381_ == 0)
{
lean_dec(v___x_377_);
v_lower_369_ = v___y_380_;
v_upper_370_ = v___x_378_;
goto v___jp_368_;
}
else
{
v_lower_369_ = v___y_380_;
v_upper_370_ = v___x_377_;
goto v___jp_368_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0(uint8_t v_x_385_){
_start:
{
uint8_t v___y_387_; uint8_t v___y_388_; uint8_t v___x_391_; uint8_t v___x_392_; uint8_t v___y_394_; uint8_t v___y_426_; uint8_t v___y_432_; uint8_t v___y_438_; 
v___x_391_ = 58;
v___x_392_ = lean_uint8_dec_eq(v_x_385_, v___x_391_);
if (v___x_392_ == 0)
{
uint8_t v___x_443_; 
v___x_443_ = 1;
v___y_438_ = v___x_443_;
goto v___jp_437_;
}
else
{
uint8_t v___x_444_; 
v___x_444_ = 0;
v___y_438_ = v___x_444_;
goto v___jp_437_;
}
v___jp_386_:
{
if (v___y_388_ == 0)
{
if (v___y_387_ == 0)
{
return v___y_387_;
}
else
{
uint8_t v___x_389_; uint8_t v___x_390_; 
v___x_389_ = 37;
v___x_390_ = lean_uint8_dec_eq(v_x_385_, v___x_389_);
return v___x_390_;
}
}
else
{
if (v___y_387_ == 0)
{
return v___y_387_;
}
else
{
return v___y_388_;
}
}
}
v___jp_393_:
{
uint8_t v___x_395_; uint8_t v___x_396_; 
v___x_395_ = 45;
v___x_396_ = lean_uint8_dec_eq(v_x_385_, v___x_395_);
if (v___x_396_ == 0)
{
uint8_t v___x_397_; uint8_t v___x_398_; 
v___x_397_ = 46;
v___x_398_ = lean_uint8_dec_eq(v_x_385_, v___x_397_);
if (v___x_398_ == 0)
{
uint8_t v___x_399_; uint8_t v___x_400_; 
v___x_399_ = 95;
v___x_400_ = lean_uint8_dec_eq(v_x_385_, v___x_399_);
if (v___x_400_ == 0)
{
uint8_t v___x_401_; uint8_t v___x_402_; 
v___x_401_ = 126;
v___x_402_ = lean_uint8_dec_eq(v_x_385_, v___x_401_);
if (v___x_402_ == 0)
{
uint8_t v___x_403_; uint8_t v___x_404_; 
v___x_403_ = 33;
v___x_404_ = lean_uint8_dec_eq(v_x_385_, v___x_403_);
if (v___x_404_ == 0)
{
uint8_t v___x_405_; uint8_t v___x_406_; 
v___x_405_ = 36;
v___x_406_ = lean_uint8_dec_eq(v_x_385_, v___x_405_);
if (v___x_406_ == 0)
{
uint8_t v___x_407_; uint8_t v___x_408_; 
v___x_407_ = 38;
v___x_408_ = lean_uint8_dec_eq(v_x_385_, v___x_407_);
if (v___x_408_ == 0)
{
uint8_t v___x_409_; uint8_t v___x_410_; 
v___x_409_ = 39;
v___x_410_ = lean_uint8_dec_eq(v_x_385_, v___x_409_);
if (v___x_410_ == 0)
{
uint8_t v___x_411_; uint8_t v___x_412_; 
v___x_411_ = 40;
v___x_412_ = lean_uint8_dec_eq(v_x_385_, v___x_411_);
if (v___x_412_ == 0)
{
uint8_t v___x_413_; uint8_t v___x_414_; 
v___x_413_ = 41;
v___x_414_ = lean_uint8_dec_eq(v_x_385_, v___x_413_);
if (v___x_414_ == 0)
{
uint8_t v___x_415_; uint8_t v___x_416_; 
v___x_415_ = 42;
v___x_416_ = lean_uint8_dec_eq(v_x_385_, v___x_415_);
if (v___x_416_ == 0)
{
uint8_t v___x_417_; uint8_t v___x_418_; 
v___x_417_ = 43;
v___x_418_ = lean_uint8_dec_eq(v_x_385_, v___x_417_);
if (v___x_418_ == 0)
{
uint8_t v___x_419_; uint8_t v___x_420_; 
v___x_419_ = 44;
v___x_420_ = lean_uint8_dec_eq(v_x_385_, v___x_419_);
if (v___x_420_ == 0)
{
uint8_t v___x_421_; uint8_t v___x_422_; 
v___x_421_ = 59;
v___x_422_ = lean_uint8_dec_eq(v_x_385_, v___x_421_);
if (v___x_422_ == 0)
{
uint8_t v___x_423_; uint8_t v___x_424_; 
v___x_423_ = 61;
v___x_424_ = lean_uint8_dec_eq(v_x_385_, v___x_423_);
if (v___x_424_ == 0)
{
v___y_387_ = v___y_394_;
v___y_388_ = v___x_392_;
goto v___jp_386_;
}
else
{
v___y_387_ = v___y_394_;
v___y_388_ = v___x_424_;
goto v___jp_386_;
}
}
else
{
v___y_387_ = v___y_394_;
v___y_388_ = v___x_422_;
goto v___jp_386_;
}
}
else
{
v___y_387_ = v___y_394_;
v___y_388_ = v___x_420_;
goto v___jp_386_;
}
}
else
{
v___y_387_ = v___y_394_;
v___y_388_ = v___x_418_;
goto v___jp_386_;
}
}
else
{
v___y_387_ = v___y_394_;
v___y_388_ = v___x_416_;
goto v___jp_386_;
}
}
else
{
v___y_387_ = v___y_394_;
v___y_388_ = v___x_414_;
goto v___jp_386_;
}
}
else
{
v___y_387_ = v___y_394_;
v___y_388_ = v___x_412_;
goto v___jp_386_;
}
}
else
{
v___y_387_ = v___y_394_;
v___y_388_ = v___x_410_;
goto v___jp_386_;
}
}
else
{
v___y_387_ = v___y_394_;
v___y_388_ = v___x_408_;
goto v___jp_386_;
}
}
else
{
v___y_387_ = v___y_394_;
v___y_388_ = v___x_406_;
goto v___jp_386_;
}
}
else
{
v___y_387_ = v___y_394_;
v___y_388_ = v___x_404_;
goto v___jp_386_;
}
}
else
{
v___y_387_ = v___y_394_;
v___y_388_ = v___x_402_;
goto v___jp_386_;
}
}
else
{
v___y_387_ = v___y_394_;
v___y_388_ = v___x_400_;
goto v___jp_386_;
}
}
else
{
v___y_387_ = v___y_394_;
v___y_388_ = v___x_398_;
goto v___jp_386_;
}
}
else
{
v___y_387_ = v___y_394_;
v___y_388_ = v___x_396_;
goto v___jp_386_;
}
}
v___jp_425_:
{
uint8_t v___x_427_; uint8_t v___x_428_; 
v___x_427_ = 65;
v___x_428_ = lean_uint8_dec_le(v___x_427_, v_x_385_);
if (v___x_428_ == 0)
{
v___y_394_ = v___y_426_;
goto v___jp_393_;
}
else
{
uint8_t v___x_429_; uint8_t v___x_430_; 
v___x_429_ = 90;
v___x_430_ = lean_uint8_dec_le(v_x_385_, v___x_429_);
if (v___x_430_ == 0)
{
v___y_394_ = v___y_426_;
goto v___jp_393_;
}
else
{
v___y_387_ = v___y_426_;
v___y_388_ = v___x_430_;
goto v___jp_386_;
}
}
}
v___jp_431_:
{
uint8_t v___x_433_; uint8_t v___x_434_; 
v___x_433_ = 97;
v___x_434_ = lean_uint8_dec_le(v___x_433_, v_x_385_);
if (v___x_434_ == 0)
{
v___y_426_ = v___y_432_;
goto v___jp_425_;
}
else
{
uint8_t v___x_435_; uint8_t v___x_436_; 
v___x_435_ = 122;
v___x_436_ = lean_uint8_dec_le(v_x_385_, v___x_435_);
if (v___x_436_ == 0)
{
v___y_426_ = v___y_432_;
goto v___jp_425_;
}
else
{
v___y_387_ = v___y_432_;
v___y_388_ = v___x_436_;
goto v___jp_386_;
}
}
}
v___jp_437_:
{
uint8_t v___x_439_; uint8_t v___x_440_; 
v___x_439_ = 48;
v___x_440_ = lean_uint8_dec_le(v___x_439_, v_x_385_);
if (v___x_440_ == 0)
{
v___y_432_ = v___y_438_;
goto v___jp_431_;
}
else
{
uint8_t v___x_441_; uint8_t v___x_442_; 
v___x_441_ = 57;
v___x_442_ = lean_uint8_dec_le(v_x_385_, v___x_441_);
if (v___x_442_ == 0)
{
v___y_432_ = v___y_438_;
goto v___jp_431_;
}
else
{
v___y_387_ = v___y_438_;
v___y_388_ = v___x_442_;
goto v___jp_386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___boxed(lean_object* v_x_445_){
_start:
{
uint8_t v_x_boxed_446_; uint8_t v_res_447_; lean_object* v_r_448_; 
v_x_boxed_446_ = lean_unbox(v_x_445_);
v_res_447_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0(v_x_boxed_446_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1(uint8_t v_x_449_){
_start:
{
uint8_t v___y_451_; uint8_t v___x_497_; uint8_t v___x_498_; 
v___x_497_ = 48;
v___x_498_ = lean_uint8_dec_le(v___x_497_, v_x_449_);
if (v___x_498_ == 0)
{
goto v___jp_492_;
}
else
{
uint8_t v___x_499_; uint8_t v___x_500_; 
v___x_499_ = 57;
v___x_500_ = lean_uint8_dec_le(v_x_449_, v___x_499_);
if (v___x_500_ == 0)
{
goto v___jp_492_;
}
else
{
v___y_451_ = v___x_500_;
goto v___jp_450_;
}
}
v___jp_450_:
{
if (v___y_451_ == 0)
{
uint8_t v___x_452_; uint8_t v___x_453_; 
v___x_452_ = 37;
v___x_453_ = lean_uint8_dec_eq(v_x_449_, v___x_452_);
return v___x_453_;
}
else
{
return v___y_451_;
}
}
v___jp_454_:
{
uint8_t v___x_455_; uint8_t v___x_456_; 
v___x_455_ = 45;
v___x_456_ = lean_uint8_dec_eq(v_x_449_, v___x_455_);
if (v___x_456_ == 0)
{
uint8_t v___x_457_; uint8_t v___x_458_; 
v___x_457_ = 46;
v___x_458_ = lean_uint8_dec_eq(v_x_449_, v___x_457_);
if (v___x_458_ == 0)
{
uint8_t v___x_459_; uint8_t v___x_460_; 
v___x_459_ = 95;
v___x_460_ = lean_uint8_dec_eq(v_x_449_, v___x_459_);
if (v___x_460_ == 0)
{
uint8_t v___x_461_; uint8_t v___x_462_; 
v___x_461_ = 126;
v___x_462_ = lean_uint8_dec_eq(v_x_449_, v___x_461_);
if (v___x_462_ == 0)
{
uint8_t v___x_463_; uint8_t v___x_464_; 
v___x_463_ = 33;
v___x_464_ = lean_uint8_dec_eq(v_x_449_, v___x_463_);
if (v___x_464_ == 0)
{
uint8_t v___x_465_; uint8_t v___x_466_; 
v___x_465_ = 36;
v___x_466_ = lean_uint8_dec_eq(v_x_449_, v___x_465_);
if (v___x_466_ == 0)
{
uint8_t v___x_467_; uint8_t v___x_468_; 
v___x_467_ = 38;
v___x_468_ = lean_uint8_dec_eq(v_x_449_, v___x_467_);
if (v___x_468_ == 0)
{
uint8_t v___x_469_; uint8_t v___x_470_; 
v___x_469_ = 39;
v___x_470_ = lean_uint8_dec_eq(v_x_449_, v___x_469_);
if (v___x_470_ == 0)
{
uint8_t v___x_471_; uint8_t v___x_472_; 
v___x_471_ = 40;
v___x_472_ = lean_uint8_dec_eq(v_x_449_, v___x_471_);
if (v___x_472_ == 0)
{
uint8_t v___x_473_; uint8_t v___x_474_; 
v___x_473_ = 41;
v___x_474_ = lean_uint8_dec_eq(v_x_449_, v___x_473_);
if (v___x_474_ == 0)
{
uint8_t v___x_475_; uint8_t v___x_476_; 
v___x_475_ = 42;
v___x_476_ = lean_uint8_dec_eq(v_x_449_, v___x_475_);
if (v___x_476_ == 0)
{
uint8_t v___x_477_; uint8_t v___x_478_; 
v___x_477_ = 43;
v___x_478_ = lean_uint8_dec_eq(v_x_449_, v___x_477_);
if (v___x_478_ == 0)
{
uint8_t v___x_479_; uint8_t v___x_480_; 
v___x_479_ = 44;
v___x_480_ = lean_uint8_dec_eq(v_x_449_, v___x_479_);
if (v___x_480_ == 0)
{
uint8_t v___x_481_; uint8_t v___x_482_; 
v___x_481_ = 59;
v___x_482_ = lean_uint8_dec_eq(v_x_449_, v___x_481_);
if (v___x_482_ == 0)
{
uint8_t v___x_483_; uint8_t v___x_484_; 
v___x_483_ = 61;
v___x_484_ = lean_uint8_dec_eq(v_x_449_, v___x_483_);
if (v___x_484_ == 0)
{
uint8_t v___x_485_; uint8_t v___x_486_; 
v___x_485_ = 58;
v___x_486_ = lean_uint8_dec_eq(v_x_449_, v___x_485_);
v___y_451_ = v___x_486_;
goto v___jp_450_;
}
else
{
v___y_451_ = v___x_484_;
goto v___jp_450_;
}
}
else
{
v___y_451_ = v___x_482_;
goto v___jp_450_;
}
}
else
{
v___y_451_ = v___x_480_;
goto v___jp_450_;
}
}
else
{
v___y_451_ = v___x_478_;
goto v___jp_450_;
}
}
else
{
v___y_451_ = v___x_476_;
goto v___jp_450_;
}
}
else
{
v___y_451_ = v___x_474_;
goto v___jp_450_;
}
}
else
{
v___y_451_ = v___x_472_;
goto v___jp_450_;
}
}
else
{
v___y_451_ = v___x_470_;
goto v___jp_450_;
}
}
else
{
v___y_451_ = v___x_468_;
goto v___jp_450_;
}
}
else
{
v___y_451_ = v___x_466_;
goto v___jp_450_;
}
}
else
{
v___y_451_ = v___x_464_;
goto v___jp_450_;
}
}
else
{
v___y_451_ = v___x_462_;
goto v___jp_450_;
}
}
else
{
v___y_451_ = v___x_460_;
goto v___jp_450_;
}
}
else
{
v___y_451_ = v___x_458_;
goto v___jp_450_;
}
}
else
{
v___y_451_ = v___x_456_;
goto v___jp_450_;
}
}
v___jp_487_:
{
uint8_t v___x_488_; uint8_t v___x_489_; 
v___x_488_ = 65;
v___x_489_ = lean_uint8_dec_le(v___x_488_, v_x_449_);
if (v___x_489_ == 0)
{
goto v___jp_454_;
}
else
{
uint8_t v___x_490_; uint8_t v___x_491_; 
v___x_490_ = 90;
v___x_491_ = lean_uint8_dec_le(v_x_449_, v___x_490_);
if (v___x_491_ == 0)
{
goto v___jp_454_;
}
else
{
v___y_451_ = v___x_491_;
goto v___jp_450_;
}
}
}
v___jp_492_:
{
uint8_t v___x_493_; uint8_t v___x_494_; 
v___x_493_ = 97;
v___x_494_ = lean_uint8_dec_le(v___x_493_, v_x_449_);
if (v___x_494_ == 0)
{
goto v___jp_487_;
}
else
{
uint8_t v___x_495_; uint8_t v___x_496_; 
v___x_495_ = 122;
v___x_496_ = lean_uint8_dec_le(v_x_449_, v___x_495_);
if (v___x_496_ == 0)
{
goto v___jp_487_;
}
else
{
v___y_451_ = v___x_496_;
goto v___jp_450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1___boxed(lean_object* v_x_501_){
_start:
{
uint8_t v_x_boxed_502_; uint8_t v_res_503_; lean_object* v_r_504_; 
v_x_boxed_502_ = lean_unbox(v_x_501_);
v_res_503_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1(v_x_boxed_502_);
v_r_504_ = lean_box(v_res_503_);
return v_r_504_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(lean_object* v_config_510_, lean_object* v_a_511_){
_start:
{
lean_object* v___y_513_; lean_object* v_userPassEncoded_514_; lean_object* v___y_515_; lean_object* v___y_519_; lean_object* v_pos_520_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v_lower_526_; lean_object* v_upper_527_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v_maxUserInfoLength_541_; lean_object* v___f_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v_snd_545_; lean_object* v_fst_546_; lean_object* v_fst_547_; lean_object* v_array_548_; lean_object* v_idx_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_599_; 
v_maxUserInfoLength_541_ = lean_ctor_get(v_config_510_, 2);
v___f_542_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__2));
v___x_543_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_511_);
v___x_544_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_542_, v_maxUserInfoLength_541_, v___x_543_, v_a_511_);
v_snd_545_ = lean_ctor_get(v___x_544_, 1);
lean_inc(v_snd_545_);
v_fst_546_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_fst_546_);
lean_dec_ref(v___x_544_);
v_fst_547_ = lean_ctor_get(v_snd_545_, 0);
lean_inc(v_fst_547_);
lean_dec(v_snd_545_);
v_array_548_ = lean_ctor_get(v_a_511_, 0);
v_idx_549_ = lean_ctor_get(v_a_511_, 1);
v_isSharedCheck_599_ = !lean_is_exclusive(v_a_511_);
if (v_isSharedCheck_599_ == 0)
{
v___x_551_ = v_a_511_;
v_isShared_552_ = v_isSharedCheck_599_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_idx_549_);
lean_inc(v_array_548_);
lean_dec(v_a_511_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_599_;
goto v_resetjp_550_;
}
v___jp_512_:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v___y_513_);
lean_ctor_set(v___x_516_, 1, v_userPassEncoded_514_);
v___x_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_517_, 0, v___y_515_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
return v___x_517_;
}
v___jp_518_:
{
lean_object* v___x_521_; 
v___x_521_ = lean_box(0);
v___y_513_ = v___y_519_;
v_userPassEncoded_514_ = v___x_521_;
v___y_515_ = v_pos_520_;
goto v___jp_512_;
}
v___jp_522_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_528_ = l_ByteArray_toByteSlice(v___y_524_, v_lower_526_, v_upper_527_);
v___x_529_ = l_ByteSlice_toByteArray(v___x_528_);
v___x_530_ = l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(v___x_529_);
if (lean_obj_tag(v___x_530_) == 1)
{
v___y_513_ = v___y_523_;
v_userPassEncoded_514_ = v___x_530_;
v___y_515_ = v___y_525_;
goto v___jp_512_;
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; 
lean_dec(v___x_530_);
lean_dec_ref(v___y_523_);
v___x_531_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1));
v___x_532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_532_, 0, v___y_525_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
return v___x_532_;
}
}
v___jp_533_:
{
uint8_t v___x_540_; 
v___x_540_ = lean_nat_dec_le(v___y_535_, v___y_537_);
if (v___x_540_ == 0)
{
lean_dec(v___y_535_);
v___y_523_ = v___y_534_;
v___y_524_ = v___y_536_;
v___y_525_ = v___y_538_;
v_lower_526_ = v___y_539_;
v_upper_527_ = v___y_537_;
goto v___jp_522_;
}
else
{
lean_dec(v___y_537_);
v___y_523_ = v___y_534_;
v___y_524_ = v___y_536_;
v___y_525_ = v___y_538_;
v_lower_526_ = v___y_539_;
v_upper_527_ = v___y_535_;
goto v___jp_522_;
}
}
v_resetjp_550_:
{
lean_object* v___f_553_; lean_object* v_lower_555_; lean_object* v_upper_556_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___y_596_; uint8_t v___x_598_; 
v___f_553_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__3));
v___x_593_ = lean_nat_add(v_idx_549_, v_fst_546_);
lean_dec(v_fst_546_);
v___x_594_ = lean_byte_array_size(v_array_548_);
v___x_598_ = lean_nat_dec_le(v_idx_549_, v___x_543_);
if (v___x_598_ == 0)
{
v___y_596_ = v_idx_549_;
goto v___jp_595_;
}
else
{
lean_dec(v_idx_549_);
v___y_596_ = v___x_543_;
goto v___jp_595_;
}
v___jp_554_:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_557_ = l_ByteArray_toByteSlice(v_array_548_, v_lower_555_, v_upper_556_);
v___x_558_ = l_ByteSlice_toByteArray(v___x_557_);
v___x_559_ = l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(v___x_558_);
if (lean_obj_tag(v___x_559_) == 1)
{
lean_object* v_val_560_; lean_object* v_array_561_; lean_object* v_idx_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v_val_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_val_560_);
lean_dec_ref_known(v___x_559_, 1);
v_array_561_ = lean_ctor_get(v_fst_547_, 0);
v_idx_562_ = lean_ctor_get(v_fst_547_, 1);
v___x_563_ = lean_byte_array_size(v_array_561_);
v___x_564_ = lean_nat_dec_lt(v_idx_562_, v___x_563_);
if (v___x_564_ == 0)
{
lean_del_object(v___x_551_);
v___y_519_ = v_val_560_;
v_pos_520_ = v_fst_547_;
goto v___jp_518_;
}
else
{
uint8_t v___x_565_; uint8_t v___x_566_; uint8_t v___x_567_; 
v___x_565_ = lean_byte_array_fget(v_array_561_, v_idx_562_);
v___x_566_ = 58;
v___x_567_ = lean_uint8_dec_eq(v___x_565_, v___x_566_);
if (v___x_567_ == 0)
{
lean_del_object(v___x_551_);
v___y_519_ = v_val_560_;
v_pos_520_ = v_fst_547_;
goto v___jp_518_;
}
else
{
if (v___x_564_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_570_; 
lean_dec(v_val_560_);
v___x_568_ = lean_box(0);
if (v_isShared_552_ == 0)
{
lean_ctor_set_tag(v___x_551_, 1);
lean_ctor_set(v___x_551_, 1, v___x_568_);
lean_ctor_set(v___x_551_, 0, v_fst_547_);
v___x_570_ = v___x_551_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_fst_547_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
else
{
lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_586_; 
lean_inc(v_idx_562_);
lean_inc_ref(v_array_561_);
lean_del_object(v___x_551_);
v_isSharedCheck_586_ = !lean_is_exclusive(v_fst_547_);
if (v_isSharedCheck_586_ == 0)
{
lean_object* v_unused_587_; lean_object* v_unused_588_; 
v_unused_587_ = lean_ctor_get(v_fst_547_, 1);
lean_dec(v_unused_587_);
v_unused_588_ = lean_ctor_get(v_fst_547_, 0);
lean_dec(v_unused_588_);
v___x_573_ = v_fst_547_;
v_isShared_574_ = v_isSharedCheck_586_;
goto v_resetjp_572_;
}
else
{
lean_dec(v_fst_547_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_586_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
v___x_575_ = lean_unsigned_to_nat(1u);
v___x_576_ = lean_nat_add(v_idx_562_, v___x_575_);
lean_dec(v_idx_562_);
lean_inc(v___x_576_);
lean_inc_ref(v_array_561_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 1, v___x_576_);
v___x_578_ = v___x_573_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_array_561_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v___x_576_);
v___x_578_ = v_reuseFailAlloc_585_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_579_; lean_object* v_snd_580_; lean_object* v_fst_581_; lean_object* v_fst_582_; lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_579_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_553_, v_maxUserInfoLength_541_, v___x_543_, v___x_578_);
v_snd_580_ = lean_ctor_get(v___x_579_, 1);
lean_inc(v_snd_580_);
v_fst_581_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_fst_581_);
lean_dec_ref(v___x_579_);
v_fst_582_ = lean_ctor_get(v_snd_580_, 0);
lean_inc(v_fst_582_);
lean_dec(v_snd_580_);
v___x_583_ = lean_nat_add(v___x_576_, v_fst_581_);
lean_dec(v_fst_581_);
v___x_584_ = lean_nat_dec_le(v___x_576_, v___x_543_);
if (v___x_584_ == 0)
{
v___y_534_ = v_val_560_;
v___y_535_ = v___x_583_;
v___y_536_ = v_array_561_;
v___y_537_ = v___x_563_;
v___y_538_ = v_fst_582_;
v___y_539_ = v___x_576_;
goto v___jp_533_;
}
else
{
lean_dec(v___x_576_);
v___y_534_ = v_val_560_;
v___y_535_ = v___x_583_;
v___y_536_ = v_array_561_;
v___y_537_ = v___x_563_;
v___y_538_ = v_fst_582_;
v___y_539_ = v___x_543_;
goto v___jp_533_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_589_; lean_object* v___x_591_; 
lean_dec(v___x_559_);
v___x_589_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1));
if (v_isShared_552_ == 0)
{
lean_ctor_set_tag(v___x_551_, 1);
lean_ctor_set(v___x_551_, 1, v___x_589_);
lean_ctor_set(v___x_551_, 0, v_fst_547_);
v___x_591_ = v___x_551_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_fst_547_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v___x_589_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
v___jp_595_:
{
uint8_t v___x_597_; 
v___x_597_ = lean_nat_dec_le(v___x_593_, v___x_594_);
if (v___x_597_ == 0)
{
lean_dec(v___x_593_);
v_lower_555_ = v___y_596_;
v_upper_556_ = v___x_594_;
goto v___jp_554_;
}
else
{
v_lower_555_ = v___y_596_;
v_upper_556_ = v___x_593_;
goto v___jp_554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___boxed(lean_object* v_config_600_, lean_object* v_a_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(v_config_600_, v_a_601_);
lean_dec_ref(v_config_600_);
return v_res_602_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(uint8_t v_x_603_){
_start:
{
uint8_t v___x_604_; uint8_t v___x_605_; uint8_t v___x_606_; uint8_t v___x_607_; uint8_t v___y_609_; uint8_t v___x_620_; uint8_t v___x_621_; 
v___x_604_ = 58;
v___x_605_ = lean_uint8_dec_eq(v_x_603_, v___x_604_);
v___x_606_ = 46;
v___x_607_ = lean_uint8_dec_eq(v_x_603_, v___x_606_);
v___x_620_ = 48;
v___x_621_ = lean_uint8_dec_le(v___x_620_, v_x_603_);
if (v___x_621_ == 0)
{
goto v___jp_615_;
}
else
{
uint8_t v___x_622_; uint8_t v___x_623_; 
v___x_622_ = 57;
v___x_623_ = lean_uint8_dec_le(v_x_603_, v___x_622_);
if (v___x_623_ == 0)
{
goto v___jp_615_;
}
else
{
v___y_609_ = v___x_623_;
goto v___jp_608_;
}
}
v___jp_608_:
{
if (v___x_607_ == 0)
{
if (v___x_605_ == 0)
{
return v___y_609_;
}
else
{
return v___x_605_;
}
}
else
{
if (v___x_605_ == 0)
{
return v___x_607_;
}
else
{
return v___x_605_;
}
}
}
v___jp_610_:
{
uint8_t v___x_611_; uint8_t v___x_612_; 
v___x_611_ = 65;
v___x_612_ = lean_uint8_dec_le(v___x_611_, v_x_603_);
if (v___x_612_ == 0)
{
v___y_609_ = v___x_612_;
goto v___jp_608_;
}
else
{
uint8_t v___x_613_; uint8_t v___x_614_; 
v___x_613_ = 70;
v___x_614_ = lean_uint8_dec_le(v_x_603_, v___x_613_);
v___y_609_ = v___x_614_;
goto v___jp_608_;
}
}
v___jp_615_:
{
uint8_t v___x_616_; uint8_t v___x_617_; 
v___x_616_ = 97;
v___x_617_ = lean_uint8_dec_le(v___x_616_, v_x_603_);
if (v___x_617_ == 0)
{
goto v___jp_610_;
}
else
{
uint8_t v___x_618_; uint8_t v___x_619_; 
v___x_618_ = 102;
v___x_619_ = lean_uint8_dec_le(v_x_603_, v___x_618_);
if (v___x_619_ == 0)
{
goto v___jp_610_;
}
else
{
v___y_609_ = v___x_619_;
goto v___jp_608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___boxed(lean_object* v_x_624_){
_start:
{
uint8_t v_x_boxed_625_; uint8_t v_res_626_; lean_object* v_r_627_; 
v_x_boxed_625_ = lean_unbox(v_x_624_);
v_res_626_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(v_x_boxed_625_);
v_r_627_ = lean_box(v_res_626_);
return v_r_627_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(lean_object* v_a_639_){
_start:
{
lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v_array_650_; lean_object* v_idx_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v_array_650_ = lean_ctor_get(v_a_639_, 0);
v_idx_651_ = lean_ctor_get(v_a_639_, 1);
v___x_652_ = lean_byte_array_size(v_array_650_);
v___x_653_ = lean_nat_dec_lt(v_idx_651_, v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_box(0);
v___x_655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_655_, 0, v_a_639_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
return v___x_655_;
}
else
{
uint8_t v___x_656_; uint8_t v_got_657_; uint8_t v___x_658_; 
v___x_656_ = 91;
v_got_657_ = lean_byte_array_fget(v_array_650_, v_idx_651_);
v___x_658_ = lean_uint8_dec_eq(v_got_657_, v___x_656_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_660_, 0, v_a_639_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
return v___x_660_;
}
else
{
lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_736_; 
lean_inc(v_idx_651_);
lean_inc_ref(v_array_650_);
v_isSharedCheck_736_ = !lean_is_exclusive(v_a_639_);
if (v_isSharedCheck_736_ == 0)
{
lean_object* v_unused_737_; lean_object* v_unused_738_; 
v_unused_737_ = lean_ctor_get(v_a_639_, 1);
lean_dec(v_unused_737_);
v_unused_738_ = lean_ctor_get(v_a_639_, 0);
lean_dec(v_unused_738_);
v___x_662_ = v_a_639_;
v_isShared_663_ = v_isSharedCheck_736_;
goto v_resetjp_661_;
}
else
{
lean_dec(v_a_639_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_736_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___f_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
v___f_664_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3));
v___x_665_ = lean_unsigned_to_nat(1u);
v___x_666_ = lean_nat_add(v_idx_651_, v___x_665_);
lean_dec(v_idx_651_);
lean_inc(v___x_666_);
lean_inc_ref(v_array_650_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 1, v___x_666_);
v___x_668_ = v___x_662_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_array_650_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v___x_666_);
v___x_668_ = v_reuseFailAlloc_735_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v_snd_672_; lean_object* v_fst_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_734_; 
v___x_669_ = lean_unsigned_to_nat(256u);
v___x_670_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___x_668_);
v___x_671_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_664_, v___x_669_, v___x_670_, v___x_668_);
v_snd_672_ = lean_ctor_get(v___x_671_, 1);
v_fst_673_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_734_ == 0)
{
v___x_675_ = v___x_671_;
v_isShared_676_ = v_isSharedCheck_734_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_snd_672_);
lean_inc(v_fst_673_);
lean_dec(v___x_671_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_734_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v_fst_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_732_; 
v_fst_677_ = lean_ctor_get(v_snd_672_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v_snd_672_);
if (v_isSharedCheck_732_ == 0)
{
lean_object* v_unused_733_; 
v_unused_733_ = lean_ctor_get(v_snd_672_, 1);
lean_dec(v_unused_733_);
v___x_679_ = v_snd_672_;
v_isShared_680_ = v_isSharedCheck_732_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_fst_677_);
lean_dec(v_snd_672_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_732_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___y_682_; uint8_t v___x_716_; 
v___x_716_ = lean_nat_dec_eq(v_fst_673_, v___x_670_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; lean_object* v___y_719_; uint8_t v___x_727_; 
lean_dec_ref(v___x_668_);
v___x_717_ = lean_nat_add(v___x_666_, v_fst_673_);
lean_dec(v_fst_673_);
v___x_727_ = lean_nat_dec_le(v___x_666_, v___x_670_);
if (v___x_727_ == 0)
{
v___y_719_ = v___x_666_;
goto v___jp_718_;
}
else
{
lean_dec(v___x_666_);
v___y_719_ = v___x_670_;
goto v___jp_718_;
}
v___jp_718_:
{
uint8_t v___x_720_; 
v___x_720_ = lean_nat_dec_le(v___x_717_, v___x_652_);
if (v___x_720_ == 0)
{
lean_object* v___x_722_; 
lean_dec(v___x_717_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 1, v___x_652_);
lean_ctor_set(v___x_675_, 0, v___y_719_);
v___x_722_ = v___x_675_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___y_719_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_652_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
v___y_682_ = v___x_722_;
goto v___jp_681_;
}
}
else
{
lean_object* v___x_725_; 
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 1, v___x_717_);
lean_ctor_set(v___x_675_, 0, v___y_719_);
v___x_725_ = v___x_675_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___y_719_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v___x_717_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
v___y_682_ = v___x_725_;
goto v___jp_681_;
}
}
}
}
else
{
lean_object* v___x_728_; lean_object* v___x_730_; 
lean_del_object(v___x_679_);
lean_dec(v_fst_677_);
lean_dec(v_fst_673_);
lean_dec(v___x_666_);
lean_dec_ref(v_array_650_);
v___x_728_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7));
if (v_isShared_676_ == 0)
{
lean_ctor_set_tag(v___x_675_, 1);
lean_ctor_set(v___x_675_, 1, v___x_728_);
lean_ctor_set(v___x_675_, 0, v___x_668_);
v___x_730_ = v___x_675_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
v___jp_681_:
{
lean_object* v_array_683_; lean_object* v_idx_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v_array_683_ = lean_ctor_get(v_fst_677_, 0);
v_idx_684_ = lean_ctor_get(v_fst_677_, 1);
v___x_685_ = lean_byte_array_size(v_array_683_);
v___x_686_ = lean_nat_dec_lt(v_idx_684_, v___x_685_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; lean_object* v___x_689_; 
lean_dec_ref(v___y_682_);
lean_dec_ref(v_array_650_);
v___x_687_ = lean_box(0);
if (v_isShared_680_ == 0)
{
lean_ctor_set_tag(v___x_679_, 1);
lean_ctor_set(v___x_679_, 1, v___x_687_);
v___x_689_ = v___x_679_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_fst_677_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v___x_687_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
else
{
uint8_t v___x_691_; uint8_t v_got_692_; uint8_t v___x_693_; 
v___x_691_ = 93;
v_got_692_ = lean_byte_array_fget(v_array_683_, v_idx_684_);
v___x_693_ = lean_uint8_dec_eq(v_got_692_, v___x_691_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_696_; 
lean_dec_ref(v___y_682_);
lean_dec_ref(v_array_650_);
v___x_694_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5));
if (v_isShared_680_ == 0)
{
lean_ctor_set_tag(v___x_679_, 1);
lean_ctor_set(v___x_679_, 1, v___x_694_);
v___x_696_ = v___x_679_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_fst_677_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
else
{
lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_713_; 
lean_inc(v_idx_684_);
lean_inc_ref(v_array_683_);
lean_del_object(v___x_679_);
v_isSharedCheck_713_ = !lean_is_exclusive(v_fst_677_);
if (v_isSharedCheck_713_ == 0)
{
lean_object* v_unused_714_; lean_object* v_unused_715_; 
v_unused_714_ = lean_ctor_get(v_fst_677_, 1);
lean_dec(v_unused_714_);
v_unused_715_ = lean_ctor_get(v_fst_677_, 0);
lean_dec(v_unused_715_);
v___x_699_ = v_fst_677_;
v_isShared_700_ = v_isSharedCheck_713_;
goto v_resetjp_698_;
}
else
{
lean_dec(v_fst_677_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_713_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v_lower_701_; lean_object* v_upper_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
v_lower_701_ = lean_ctor_get(v___y_682_, 0);
lean_inc(v_lower_701_);
v_upper_702_ = lean_ctor_get(v___y_682_, 1);
lean_inc(v_upper_702_);
lean_dec_ref(v___y_682_);
v___x_703_ = l_ByteArray_toByteSlice(v_array_650_, v_lower_701_, v_upper_702_);
v___x_704_ = lean_nat_add(v_idx_684_, v___x_665_);
lean_dec(v_idx_684_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 1, v___x_704_);
v___x_706_ = v___x_699_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_array_683_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v___x_704_);
v___x_706_ = v_reuseFailAlloc_712_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_707_ = l_ByteSlice_toByteArray(v___x_703_);
v___x_708_ = lean_string_validate_utf8(v___x_707_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; lean_object* v___x_710_; 
lean_dec_ref(v___x_707_);
v___x_709_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_710_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_709_);
v___y_641_ = v___x_706_;
v___y_642_ = v___x_710_;
goto v___jp_640_;
}
else
{
lean_object* v___x_711_; 
v___x_711_ = lean_string_from_utf8_unchecked(v___x_707_);
v___y_641_ = v___x_706_;
v___y_642_ = v___x_711_;
goto v___jp_640_;
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
v___jp_640_:
{
lean_object* v___x_643_; 
v___x_643_ = lean_uv_pton_v6(v___y_642_);
if (lean_obj_tag(v___x_643_) == 1)
{
lean_object* v_val_644_; lean_object* v___x_645_; 
lean_dec_ref(v___y_642_);
v_val_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_val_644_);
lean_dec_ref_known(v___x_643_, 1);
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v___y_641_);
lean_ctor_set(v___x_645_, 1, v_val_644_);
return v___x_645_;
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
lean_dec(v___x_643_);
v___x_646_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__0));
v___x_647_ = lean_string_append(v___x_646_, v___y_642_);
lean_dec_ref(v___y_642_);
v___x_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
v___x_649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_649_, 0, v___y_641_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
return v___x_649_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0(uint8_t v_x_739_){
_start:
{
uint8_t v___x_740_; uint8_t v___x_741_; uint8_t v___x_742_; uint8_t v___x_743_; 
v___x_740_ = 46;
v___x_741_ = lean_uint8_dec_eq(v_x_739_, v___x_740_);
v___x_742_ = 48;
v___x_743_ = lean_uint8_dec_le(v___x_742_, v_x_739_);
if (v___x_743_ == 0)
{
if (v___x_741_ == 0)
{
return v___x_743_;
}
else
{
return v___x_741_;
}
}
else
{
if (v___x_741_ == 0)
{
uint8_t v___x_744_; uint8_t v___x_745_; 
v___x_744_ = 57;
v___x_745_ = lean_uint8_dec_le(v_x_739_, v___x_744_);
return v___x_745_;
}
else
{
return v___x_741_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0___boxed(lean_object* v_x_746_){
_start:
{
uint8_t v_x_boxed_747_; uint8_t v_res_748_; lean_object* v_r_749_; 
v_x_boxed_747_ = lean_unbox(v_x_746_);
v_res_748_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0(v_x_boxed_747_);
v_r_749_ = lean_box(v_res_748_);
return v_r_749_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(lean_object* v_a_752_){
_start:
{
lean_object* v___f_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v_snd_757_; lean_object* v_fst_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_803_; 
v___f_753_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__0));
v___x_754_ = lean_unsigned_to_nat(256u);
v___x_755_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_752_);
v___x_756_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_753_, v___x_754_, v___x_755_, v_a_752_);
v_snd_757_ = lean_ctor_get(v___x_756_, 1);
v_fst_758_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_803_ == 0)
{
v___x_760_ = v___x_756_;
v_isShared_761_ = v_isSharedCheck_803_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_snd_757_);
lean_inc(v_fst_758_);
lean_dec(v___x_756_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_803_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v_fst_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_801_; 
v_fst_762_ = lean_ctor_get(v_snd_757_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v_snd_757_);
if (v_isSharedCheck_801_ == 0)
{
lean_object* v_unused_802_; 
v_unused_802_ = lean_ctor_get(v_snd_757_, 1);
lean_dec(v_unused_802_);
v___x_764_ = v_snd_757_;
v_isShared_765_ = v_isSharedCheck_801_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_fst_762_);
lean_dec(v_snd_757_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_801_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___y_767_; uint8_t v___x_779_; 
v___x_779_ = lean_nat_dec_eq(v_fst_758_, v___x_755_);
if (v___x_779_ == 0)
{
lean_object* v_array_780_; lean_object* v_idx_781_; lean_object* v_lower_783_; lean_object* v_upper_784_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___y_794_; uint8_t v___x_796_; 
lean_del_object(v___x_760_);
v_array_780_ = lean_ctor_get(v_a_752_, 0);
lean_inc_ref(v_array_780_);
v_idx_781_ = lean_ctor_get(v_a_752_, 1);
lean_inc(v_idx_781_);
lean_dec_ref(v_a_752_);
v___x_791_ = lean_nat_add(v_idx_781_, v_fst_758_);
lean_dec(v_fst_758_);
v___x_792_ = lean_byte_array_size(v_array_780_);
v___x_796_ = lean_nat_dec_le(v_idx_781_, v___x_755_);
if (v___x_796_ == 0)
{
v___y_794_ = v_idx_781_;
goto v___jp_793_;
}
else
{
lean_dec(v_idx_781_);
v___y_794_ = v___x_755_;
goto v___jp_793_;
}
v___jp_782_:
{
lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_785_ = l_ByteArray_toByteSlice(v_array_780_, v_lower_783_, v_upper_784_);
v___x_786_ = l_ByteSlice_toByteArray(v___x_785_);
v___x_787_ = lean_string_validate_utf8(v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; 
lean_dec_ref(v___x_786_);
v___x_788_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_789_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_788_);
v___y_767_ = v___x_789_;
goto v___jp_766_;
}
else
{
lean_object* v___x_790_; 
v___x_790_ = lean_string_from_utf8_unchecked(v___x_786_);
v___y_767_ = v___x_790_;
goto v___jp_766_;
}
}
v___jp_793_:
{
uint8_t v___x_795_; 
v___x_795_ = lean_nat_dec_le(v___x_791_, v___x_792_);
if (v___x_795_ == 0)
{
lean_dec(v___x_791_);
v_lower_783_ = v___y_794_;
v_upper_784_ = v___x_792_;
goto v___jp_782_;
}
else
{
v_lower_783_ = v___y_794_;
v_upper_784_ = v___x_791_;
goto v___jp_782_;
}
}
}
else
{
lean_object* v___x_797_; lean_object* v___x_799_; 
lean_del_object(v___x_764_);
lean_dec(v_fst_762_);
lean_dec(v_fst_758_);
v___x_797_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7));
if (v_isShared_761_ == 0)
{
lean_ctor_set_tag(v___x_760_, 1);
lean_ctor_set(v___x_760_, 1, v___x_797_);
lean_ctor_set(v___x_760_, 0, v_a_752_);
v___x_799_ = v___x_760_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_752_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
v___jp_766_:
{
lean_object* v___x_768_; 
v___x_768_ = lean_uv_pton_v4(v___y_767_);
if (lean_obj_tag(v___x_768_) == 1)
{
lean_object* v_val_769_; lean_object* v___x_771_; 
lean_dec_ref(v___y_767_);
v_val_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_val_769_);
lean_dec_ref_known(v___x_768_, 1);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 1, v_val_769_);
v___x_771_ = v___x_764_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_fst_762_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_val_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
else
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
lean_dec(v___x_768_);
v___x_773_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__1));
v___x_774_ = lean_string_append(v___x_773_, v___y_767_);
lean_dec_ref(v___y_767_);
v___x_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
if (v_isShared_765_ == 0)
{
lean_ctor_set_tag(v___x_764_, 1);
lean_ctor_set(v___x_764_, 1, v___x_775_);
v___x_777_ = v___x_764_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_fst_762_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
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
lean_object* v___x_807_; 
v___x_807_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0));
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___boxed(lean_object* v___dummy_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg();
return v_res_809_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0(void){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg();
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(lean_object* v_s_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___boxed(lean_object* v_s_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(v_s_813_);
lean_dec_ref(v_s_813_);
return v_res_814_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(uint8_t v_x_815_){
_start:
{
uint8_t v___y_817_; uint8_t v___x_832_; uint8_t v___x_833_; 
v___x_832_ = 48;
v___x_833_ = lean_uint8_dec_le(v___x_832_, v_x_815_);
if (v___x_833_ == 0)
{
goto v___jp_827_;
}
else
{
uint8_t v___x_834_; uint8_t v___x_835_; 
v___x_834_ = 57;
v___x_835_ = lean_uint8_dec_le(v_x_815_, v___x_834_);
if (v___x_835_ == 0)
{
goto v___jp_827_;
}
else
{
v___y_817_ = v___x_835_;
goto v___jp_816_;
}
}
v___jp_816_:
{
uint8_t v___x_818_; uint8_t v___x_819_; 
v___x_818_ = 45;
v___x_819_ = lean_uint8_dec_eq(v_x_815_, v___x_818_);
if (v___x_819_ == 0)
{
if (v___y_817_ == 0)
{
uint8_t v___x_820_; uint8_t v___x_821_; 
v___x_820_ = 46;
v___x_821_ = lean_uint8_dec_eq(v_x_815_, v___x_820_);
return v___x_821_;
}
else
{
return v___y_817_;
}
}
else
{
if (v___y_817_ == 0)
{
return v___x_819_;
}
else
{
return v___y_817_;
}
}
}
v___jp_822_:
{
uint8_t v___x_823_; uint8_t v___x_824_; 
v___x_823_ = 65;
v___x_824_ = lean_uint8_dec_le(v___x_823_, v_x_815_);
if (v___x_824_ == 0)
{
v___y_817_ = v___x_824_;
goto v___jp_816_;
}
else
{
uint8_t v___x_825_; uint8_t v___x_826_; 
v___x_825_ = 90;
v___x_826_ = lean_uint8_dec_le(v_x_815_, v___x_825_);
v___y_817_ = v___x_826_;
goto v___jp_816_;
}
}
v___jp_827_:
{
uint8_t v___x_828_; uint8_t v___x_829_; 
v___x_828_ = 97;
v___x_829_ = lean_uint8_dec_le(v___x_828_, v_x_815_);
if (v___x_829_ == 0)
{
goto v___jp_822_;
}
else
{
uint8_t v___x_830_; uint8_t v___x_831_; 
v___x_830_ = 122;
v___x_831_ = lean_uint8_dec_le(v_x_815_, v___x_830_);
if (v___x_831_ == 0)
{
goto v___jp_822_;
}
else
{
v___y_817_ = v___x_831_;
goto v___jp_816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed(lean_object* v_x_836_){
_start:
{
uint8_t v_x_boxed_837_; uint8_t v_res_838_; lean_object* v_r_839_; 
v_x_boxed_837_ = lean_unbox(v_x_836_);
v_res_838_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(v_x_boxed_837_);
v_r_839_ = lean_box(v_res_838_);
return v_r_839_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1___redArg(lean_object* v___x_840_, lean_object* v_a_841_, uint8_t v_b_842_){
_start:
{
if (lean_obj_tag(v_a_841_) == 0)
{
lean_object* v_currPos_843_; lean_object* v_searcher_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_864_; 
v_currPos_843_ = lean_ctor_get(v_a_841_, 0);
v_searcher_844_ = lean_ctor_get(v_a_841_, 1);
v_isSharedCheck_864_ = !lean_is_exclusive(v_a_841_);
if (v_isSharedCheck_864_ == 0)
{
v___x_846_ = v_a_841_;
v_isShared_847_ = v_isSharedCheck_864_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_searcher_844_);
lean_inc(v_currPos_843_);
lean_dec(v_a_841_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_864_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v_str_848_; lean_object* v_startInclusive_849_; lean_object* v_endExclusive_850_; uint8_t v___x_851_; lean_object* v___x_852_; uint8_t v_decide_853_; 
v_str_848_ = lean_ctor_get(v___x_840_, 0);
v_startInclusive_849_ = lean_ctor_get(v___x_840_, 1);
v_endExclusive_850_ = lean_ctor_get(v___x_840_, 2);
v___x_851_ = 0;
v___x_852_ = lean_nat_sub(v_endExclusive_850_, v_startInclusive_849_);
v_decide_853_ = lean_nat_dec_eq(v_searcher_844_, v___x_852_);
lean_dec(v___x_852_);
if (v_decide_853_ == 0)
{
uint32_t v___x_854_; lean_object* v___x_855_; uint32_t v___x_856_; uint8_t v___x_857_; 
v___x_854_ = 46;
v___x_855_ = lean_nat_add(v_startInclusive_849_, v_searcher_844_);
lean_dec(v_searcher_844_);
v___x_856_ = lean_string_utf8_get_fast(v_str_848_, v___x_855_);
v___x_857_ = lean_uint32_dec_eq(v___x_856_, v___x_854_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_858_ = lean_string_utf8_next_fast(v_str_848_, v___x_855_);
lean_dec(v___x_855_);
v___x_859_ = lean_nat_sub(v___x_858_, v_startInclusive_849_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 1, v___x_859_);
v___x_861_ = v___x_846_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_currPos_843_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v___x_859_);
v___x_861_ = v_reuseFailAlloc_863_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
v_a_841_ = v___x_861_;
goto _start;
}
}
else
{
lean_dec(v___x_855_);
lean_del_object(v___x_846_);
lean_dec(v_currPos_843_);
return v___x_851_;
}
}
else
{
lean_del_object(v___x_846_);
lean_dec(v_searcher_844_);
lean_dec(v_currPos_843_);
return v___x_851_;
}
}
}
else
{
return v_b_842_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1___redArg___boxed(lean_object* v___x_865_, lean_object* v_a_866_, lean_object* v_b_867_){
_start:
{
uint8_t v_b_boxed_868_; uint8_t v_res_869_; lean_object* v_r_870_; 
v_b_boxed_868_ = lean_unbox(v_b_867_);
v_res_869_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1___redArg(v___x_865_, v_a_866_, v_b_boxed_868_);
lean_dec_ref(v___x_865_);
v_r_870_ = lean_box(v_res_869_);
return v_r_870_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(lean_object* v___x_871_, lean_object* v___x_872_, lean_object* v___x_873_, lean_object* v_a_874_, uint8_t v_b_875_){
_start:
{
if (lean_obj_tag(v_a_874_) == 0)
{
lean_object* v_currPos_876_; lean_object* v_searcher_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_897_; 
v_currPos_876_ = lean_ctor_get(v_a_874_, 0);
v_searcher_877_ = lean_ctor_get(v_a_874_, 1);
v_isSharedCheck_897_ = !lean_is_exclusive(v_a_874_);
if (v_isSharedCheck_897_ == 0)
{
v___x_879_ = v_a_874_;
v_isShared_880_ = v_isSharedCheck_897_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_searcher_877_);
lean_inc(v_currPos_876_);
lean_dec(v_a_874_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_897_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v_str_881_; lean_object* v_startInclusive_882_; lean_object* v_endExclusive_883_; uint8_t v___x_884_; lean_object* v___x_885_; uint8_t v_decide_886_; 
v_str_881_ = lean_ctor_get(v___x_872_, 0);
v_startInclusive_882_ = lean_ctor_get(v___x_872_, 1);
v_endExclusive_883_ = lean_ctor_get(v___x_872_, 2);
v___x_884_ = 0;
v___x_885_ = lean_nat_sub(v_endExclusive_883_, v_startInclusive_882_);
v_decide_886_ = lean_nat_dec_eq(v_searcher_877_, v___x_885_);
lean_dec(v___x_885_);
if (v_decide_886_ == 0)
{
lean_object* v___x_887_; uint32_t v___x_888_; uint32_t v___x_889_; uint8_t v___x_890_; 
v___x_887_ = lean_nat_add(v_startInclusive_882_, v_searcher_877_);
lean_dec(v_searcher_877_);
v___x_888_ = lean_string_utf8_get_fast(v_str_881_, v___x_887_);
v___x_889_ = 46;
v___x_890_ = lean_uint32_dec_eq(v___x_888_, v___x_889_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_891_ = lean_string_utf8_next_fast(v_str_881_, v___x_887_);
lean_dec(v___x_887_);
v___x_892_ = lean_nat_sub(v___x_891_, v_startInclusive_882_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 1, v___x_892_);
v___x_894_ = v___x_879_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_currPos_876_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v___x_892_);
v___x_894_ = v_reuseFailAlloc_896_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
uint8_t v___x_895_; 
v___x_895_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1___redArg(v___x_872_, v___x_894_, v_b_875_);
return v___x_895_;
}
}
else
{
lean_dec(v___x_887_);
lean_del_object(v___x_879_);
lean_dec(v_currPos_876_);
return v___x_884_;
}
}
else
{
lean_del_object(v___x_879_);
lean_dec(v_searcher_877_);
lean_dec(v_currPos_876_);
return v___x_884_;
}
}
}
else
{
return v_b_875_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg___boxed(lean_object* v___x_898_, lean_object* v___x_899_, lean_object* v___x_900_, lean_object* v_a_901_, lean_object* v_b_902_){
_start:
{
uint8_t v_b_boxed_903_; uint8_t v_res_904_; lean_object* v_r_905_; 
v_b_boxed_903_ = lean_unbox(v_b_902_);
v_res_904_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_898_, v___x_899_, v___x_900_, v_a_901_, v_b_boxed_903_);
lean_dec(v___x_900_);
lean_dec_ref(v___x_899_);
lean_dec_ref(v___x_898_);
v_r_905_ = lean_box(v_res_904_);
return v_r_905_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3___redArg(uint8_t v___x_906_, lean_object* v___x_907_, lean_object* v___x_908_, lean_object* v___x_909_, lean_object* v_a_910_, uint8_t v_b_911_){
_start:
{
lean_object* v_it_913_; lean_object* v_startInclusive_914_; lean_object* v_endExclusive_915_; 
if (lean_obj_tag(v_a_910_) == 0)
{
lean_object* v_currPos_919_; lean_object* v_searcher_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_949_; 
v_currPos_919_ = lean_ctor_get(v_a_910_, 0);
v_searcher_920_ = lean_ctor_get(v_a_910_, 1);
v_isSharedCheck_949_ = !lean_is_exclusive(v_a_910_);
if (v_isSharedCheck_949_ == 0)
{
v___x_922_ = v_a_910_;
v_isShared_923_ = v_isSharedCheck_949_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_searcher_920_);
lean_inc(v_currPos_919_);
lean_dec(v_a_910_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_949_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v_str_924_; lean_object* v_startInclusive_925_; lean_object* v_endExclusive_926_; lean_object* v___x_927_; uint8_t v_decide_928_; 
v_str_924_ = lean_ctor_get(v___x_908_, 0);
v_startInclusive_925_ = lean_ctor_get(v___x_908_, 1);
v_endExclusive_926_ = lean_ctor_get(v___x_908_, 2);
v___x_927_ = lean_nat_sub(v_endExclusive_926_, v_startInclusive_925_);
v_decide_928_ = lean_nat_dec_eq(v_searcher_920_, v___x_927_);
lean_dec(v___x_927_);
if (v_decide_928_ == 0)
{
uint32_t v___x_929_; lean_object* v___x_930_; uint32_t v___x_931_; uint8_t v___x_932_; 
v___x_929_ = 46;
v___x_930_ = lean_nat_add(v_startInclusive_925_, v_searcher_920_);
v___x_931_ = lean_string_utf8_get_fast(v_str_924_, v___x_930_);
v___x_932_ = lean_uint32_dec_eq(v___x_931_, v___x_929_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_936_; 
lean_dec(v_searcher_920_);
v___x_933_ = lean_string_utf8_next_fast(v_str_924_, v___x_930_);
lean_dec(v___x_930_);
v___x_934_ = lean_nat_sub(v___x_933_, v_startInclusive_925_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 1, v___x_934_);
v___x_936_ = v___x_922_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_currPos_919_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v___x_934_);
v___x_936_ = v_reuseFailAlloc_938_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
v_a_910_ = v___x_936_;
goto _start;
}
}
else
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v_slice_942_; lean_object* v_nextIt_944_; 
v___x_939_ = lean_string_utf8_next_fast(v_str_924_, v___x_930_);
v___x_940_ = lean_nat_sub(v___x_939_, v___x_930_);
lean_dec(v___x_930_);
v___x_941_ = lean_nat_add(v_searcher_920_, v___x_940_);
lean_dec(v___x_940_);
v_slice_942_ = l_String_Slice_subslice_x21(v___x_908_, v_currPos_919_, v_searcher_920_);
lean_inc(v___x_941_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 1, v___x_941_);
lean_ctor_set(v___x_922_, 0, v___x_941_);
v_nextIt_944_ = v___x_922_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v___x_941_);
v_nextIt_944_ = v_reuseFailAlloc_947_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v_startInclusive_945_; lean_object* v_endExclusive_946_; 
v_startInclusive_945_ = lean_ctor_get(v_slice_942_, 0);
lean_inc(v_startInclusive_945_);
v_endExclusive_946_ = lean_ctor_get(v_slice_942_, 1);
lean_inc(v_endExclusive_946_);
lean_dec_ref(v_slice_942_);
v_it_913_ = v_nextIt_944_;
v_startInclusive_914_ = v_startInclusive_945_;
v_endExclusive_915_ = v_endExclusive_946_;
goto v___jp_912_;
}
}
}
else
{
lean_object* v___x_948_; 
lean_del_object(v___x_922_);
lean_dec(v_searcher_920_);
v___x_948_ = lean_box(1);
lean_inc(v___x_909_);
v_it_913_ = v___x_948_;
v_startInclusive_914_ = v_currPos_919_;
v_endExclusive_915_ = v___x_909_;
goto v___jp_912_;
}
}
}
else
{
lean_dec(v___x_909_);
return v_b_911_;
}
v___jp_912_:
{
lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_916_ = lean_string_utf8_extract_fast(v___x_907_, v_startInclusive_914_, v_endExclusive_915_);
lean_dec(v_endExclusive_915_);
lean_dec(v_startInclusive_914_);
v___x_917_ = l_Std_Http_URI_isValidDomainLabel(v___x_916_);
if (v___x_917_ == 0)
{
lean_dec(v_it_913_);
lean_dec(v___x_909_);
return v___x_917_;
}
else
{
{
lean_object* _tmp_4 = v_it_913_;
uint8_t _tmp_5 = v___x_906_;
v_a_910_ = _tmp_4;
v_b_911_ = _tmp_5;
}
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3___redArg___boxed(lean_object* v___x_950_, lean_object* v___x_951_, lean_object* v___x_952_, lean_object* v___x_953_, lean_object* v_a_954_, lean_object* v_b_955_){
_start:
{
uint8_t v___x_10937__boxed_956_; uint8_t v_b_boxed_957_; uint8_t v_res_958_; lean_object* v_r_959_; 
v___x_10937__boxed_956_ = lean_unbox(v___x_950_);
v_b_boxed_957_ = lean_unbox(v_b_955_);
v_res_958_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3___redArg(v___x_10937__boxed_956_, v___x_951_, v___x_952_, v___x_953_, v_a_954_, v_b_boxed_957_);
lean_dec_ref(v___x_952_);
lean_dec_ref(v___x_951_);
v_r_959_ = lean_box(v_res_958_);
return v_r_959_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(uint8_t v___x_960_, lean_object* v___x_961_, lean_object* v___x_962_, lean_object* v___x_963_, lean_object* v_a_964_, uint8_t v_b_965_){
_start:
{
lean_object* v_it_967_; lean_object* v_startInclusive_968_; lean_object* v_endExclusive_969_; 
if (lean_obj_tag(v_a_964_) == 0)
{
lean_object* v_currPos_973_; lean_object* v_searcher_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_1003_; 
v_currPos_973_ = lean_ctor_get(v_a_964_, 0);
v_searcher_974_ = lean_ctor_get(v_a_964_, 1);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_a_964_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_976_ = v_a_964_;
v_isShared_977_ = v_isSharedCheck_1003_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_searcher_974_);
lean_inc(v_currPos_973_);
lean_dec(v_a_964_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_1003_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v_str_978_; lean_object* v_startInclusive_979_; lean_object* v_endExclusive_980_; lean_object* v___x_981_; uint8_t v_decide_982_; 
v_str_978_ = lean_ctor_get(v___x_962_, 0);
v_startInclusive_979_ = lean_ctor_get(v___x_962_, 1);
v_endExclusive_980_ = lean_ctor_get(v___x_962_, 2);
v___x_981_ = lean_nat_sub(v_endExclusive_980_, v_startInclusive_979_);
v_decide_982_ = lean_nat_dec_eq(v_searcher_974_, v___x_981_);
lean_dec(v___x_981_);
if (v_decide_982_ == 0)
{
lean_object* v___x_983_; uint32_t v___x_984_; uint32_t v___x_985_; uint8_t v___x_986_; 
v___x_983_ = lean_nat_add(v_startInclusive_979_, v_searcher_974_);
v___x_984_ = lean_string_utf8_get_fast(v_str_978_, v___x_983_);
v___x_985_ = 46;
v___x_986_ = lean_uint32_dec_eq(v___x_984_, v___x_985_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
lean_dec(v_searcher_974_);
v___x_987_ = lean_string_utf8_next_fast(v_str_978_, v___x_983_);
lean_dec(v___x_983_);
v___x_988_ = lean_nat_sub(v___x_987_, v_startInclusive_979_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 1, v___x_988_);
v___x_990_ = v___x_976_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_currPos_973_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v___x_988_);
v___x_990_ = v_reuseFailAlloc_992_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
uint8_t v___x_991_; 
v___x_991_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3___redArg(v___x_960_, v___x_961_, v___x_962_, v___x_963_, v___x_990_, v_b_965_);
return v___x_991_;
}
}
else
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v_slice_996_; lean_object* v_nextIt_998_; 
v___x_993_ = lean_string_utf8_next_fast(v_str_978_, v___x_983_);
v___x_994_ = lean_nat_sub(v___x_993_, v___x_983_);
lean_dec(v___x_983_);
v___x_995_ = lean_nat_add(v_searcher_974_, v___x_994_);
lean_dec(v___x_994_);
v_slice_996_ = l_String_Slice_subslice_x21(v___x_962_, v_currPos_973_, v_searcher_974_);
lean_inc(v___x_995_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 1, v___x_995_);
lean_ctor_set(v___x_976_, 0, v___x_995_);
v_nextIt_998_ = v___x_976_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v___x_995_);
v_nextIt_998_ = v_reuseFailAlloc_1001_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v_startInclusive_999_; lean_object* v_endExclusive_1000_; 
v_startInclusive_999_ = lean_ctor_get(v_slice_996_, 0);
lean_inc(v_startInclusive_999_);
v_endExclusive_1000_ = lean_ctor_get(v_slice_996_, 1);
lean_inc(v_endExclusive_1000_);
lean_dec_ref(v_slice_996_);
v_it_967_ = v_nextIt_998_;
v_startInclusive_968_ = v_startInclusive_999_;
v_endExclusive_969_ = v_endExclusive_1000_;
goto v___jp_966_;
}
}
}
else
{
lean_object* v___x_1002_; 
lean_del_object(v___x_976_);
lean_dec(v_searcher_974_);
v___x_1002_ = lean_box(1);
lean_inc(v___x_963_);
v_it_967_ = v___x_1002_;
v_startInclusive_968_ = v_currPos_973_;
v_endExclusive_969_ = v___x_963_;
goto v___jp_966_;
}
}
}
else
{
lean_dec(v___x_963_);
return v_b_965_;
}
v___jp_966_:
{
lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_970_ = lean_string_utf8_extract_fast(v___x_961_, v_startInclusive_968_, v_endExclusive_969_);
lean_dec(v_endExclusive_969_);
lean_dec(v_startInclusive_968_);
v___x_971_ = l_Std_Http_URI_isValidDomainLabel(v___x_970_);
if (v___x_971_ == 0)
{
lean_dec(v_it_967_);
lean_dec(v___x_963_);
return v___x_971_;
}
else
{
uint8_t v___x_972_; 
v___x_972_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3___redArg(v___x_960_, v___x_961_, v___x_962_, v___x_963_, v_it_967_, v___x_960_);
return v___x_972_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg___boxed(lean_object* v___x_1004_, lean_object* v___x_1005_, lean_object* v___x_1006_, lean_object* v___x_1007_, lean_object* v_a_1008_, lean_object* v_b_1009_){
_start:
{
uint8_t v___x_11007__boxed_1010_; uint8_t v_b_boxed_1011_; uint8_t v_res_1012_; lean_object* v_r_1013_; 
v___x_11007__boxed_1010_ = lean_unbox(v___x_1004_);
v_b_boxed_1011_ = lean_unbox(v_b_1009_);
v_res_1012_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_11007__boxed_1010_, v___x_1005_, v___x_1006_, v___x_1007_, v_a_1008_, v_b_boxed_1011_);
lean_dec_ref(v___x_1006_);
lean_dec_ref(v___x_1005_);
v_r_1013_ = lean_box(v_res_1012_);
return v_r_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(lean_object* v_config_1019_, lean_object* v_a_1020_){
_start:
{
lean_object* v___y_1022_; lean_object* v___y_1023_; uint8_t v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; uint8_t v___y_1033_; uint8_t v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; uint8_t v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; uint8_t v___y_1044_; uint8_t v___y_1047_; uint8_t v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; uint8_t v___y_1053_; lean_object* v___y_1054_; uint8_t v___y_1055_; uint8_t v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; uint8_t v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; uint8_t v___y_1066_; uint8_t v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v_lower_1076_; lean_object* v_upper_1077_; uint8_t v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v_array_1098_; lean_object* v_idx_1099_; lean_object* v___f_1100_; lean_object* v___y_1102_; lean_object* v_pos_1125_; lean_object* v_pos_1149_; lean_object* v_res_1150_; lean_object* v_pos_1152_; lean_object* v_res_1153_; lean_object* v___x_1161_; uint8_t v___x_1162_; 
v_array_1098_ = lean_ctor_get(v_a_1020_, 0);
v_idx_1099_ = lean_ctor_get(v_a_1020_, 1);
v___f_1100_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3));
v___x_1161_ = lean_byte_array_size(v_array_1098_);
v___x_1162_ = lean_nat_dec_lt(v_idx_1099_, v___x_1161_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; 
lean_inc(v_idx_1099_);
lean_inc_ref(v_array_1098_);
v___x_1163_ = lean_box(0);
v_pos_1152_ = v_a_1020_;
v_res_1153_ = v___x_1163_;
goto v___jp_1151_;
}
else
{
uint8_t v___x_1164_; uint8_t v___x_1165_; uint8_t v___x_1166_; 
v___x_1164_ = lean_byte_array_fget(v_array_1098_, v_idx_1099_);
v___x_1165_ = 91;
v___x_1166_ = lean_uint8_dec_eq(v___x_1164_, v___x_1165_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; 
lean_inc(v_idx_1099_);
lean_inc_ref(v_array_1098_);
v___x_1167_ = lean_box(0);
v_pos_1152_ = v_a_1020_;
v_res_1153_ = v___x_1167_;
goto v___jp_1151_;
}
else
{
lean_object* v___x_1168_; 
v___x_1168_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(v_a_1020_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_pos_1169_; lean_object* v_res_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1178_; 
v_pos_1169_ = lean_ctor_get(v___x_1168_, 0);
v_res_1170_ = lean_ctor_get(v___x_1168_, 1);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1172_ = v___x_1168_;
v_isShared_1173_ = v_isSharedCheck_1178_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_res_1170_);
lean_inc(v_pos_1169_);
lean_dec(v___x_1168_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1178_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1174_; lean_object* v___x_1176_; 
v___x_1174_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1174_, 0, v_res_1170_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 1, v___x_1174_);
v___x_1176_ = v___x_1172_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_pos_1169_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v___x_1174_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
else
{
lean_object* v_pos_1179_; lean_object* v_err_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
v_pos_1179_ = lean_ctor_get(v___x_1168_, 0);
v_err_1180_ = lean_ctor_get(v___x_1168_, 1);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1168_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_err_1180_);
lean_inc(v_pos_1179_);
lean_dec(v___x_1168_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_pos_1179_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_err_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
v___jp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1024_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0));
v___x_1025_ = lean_string_append(v___x_1024_, v___y_1023_);
lean_dec_ref(v___y_1023_);
v___x_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
v___x_1027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___y_1022_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
return v___x_1027_;
}
v___jp_1028_:
{
if (v___y_1029_ == 0)
{
lean_dec_ref(v___y_1032_);
v___y_1022_ = v___y_1030_;
v___y_1023_ = v___y_1031_;
goto v___jp_1021_;
}
else
{
if (v___y_1033_ == 0)
{
lean_dec_ref(v___y_1032_);
v___y_1022_ = v___y_1030_;
v___y_1023_ = v___y_1031_;
goto v___jp_1021_;
}
else
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
lean_dec_ref(v___y_1031_);
v___x_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1034_, 0, v___y_1032_);
v___x_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___y_1030_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
return v___x_1035_;
}
}
}
v___jp_1036_:
{
uint8_t v___x_1045_; 
v___x_1045_ = lean_nat_dec_eq(v___y_1038_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec(v___y_1038_);
if (v___x_1045_ == 0)
{
v___y_1029_ = v___y_1044_;
v___y_1030_ = v___y_1039_;
v___y_1031_ = v___y_1040_;
v___y_1032_ = v___y_1043_;
v___y_1033_ = v___y_1041_;
goto v___jp_1028_;
}
else
{
v___y_1029_ = v___y_1044_;
v___y_1030_ = v___y_1039_;
v___y_1031_ = v___y_1040_;
v___y_1032_ = v___y_1043_;
v___y_1033_ = v___y_1037_;
goto v___jp_1028_;
}
}
v___jp_1046_:
{
if (v___y_1048_ == 0)
{
v___y_1037_ = v___y_1047_;
v___y_1038_ = v___y_1049_;
v___y_1039_ = v___y_1050_;
v___y_1040_ = v___y_1051_;
v___y_1041_ = v___y_1053_;
v___y_1042_ = v___y_1052_;
v___y_1043_ = v___y_1054_;
v___y_1044_ = v___y_1048_;
goto v___jp_1036_;
}
else
{
v___y_1037_ = v___y_1047_;
v___y_1038_ = v___y_1049_;
v___y_1039_ = v___y_1050_;
v___y_1040_ = v___y_1051_;
v___y_1041_ = v___y_1053_;
v___y_1042_ = v___y_1052_;
v___y_1043_ = v___y_1054_;
v___y_1044_ = v___y_1055_;
goto v___jp_1036_;
}
}
v___jp_1056_:
{
uint8_t v___x_1067_; 
lean_inc(v___y_1059_);
v___x_1067_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___y_1063_, v___y_1065_, v___y_1064_, v___y_1059_, v___y_1058_, v___y_1063_);
lean_dec_ref(v___y_1064_);
if (v___x_1067_ == 0)
{
v___y_1047_ = v___y_1057_;
v___y_1048_ = v___y_1066_;
v___y_1049_ = v___y_1059_;
v___y_1050_ = v___y_1060_;
v___y_1051_ = v___y_1061_;
v___y_1052_ = v___y_1062_;
v___y_1053_ = v___y_1063_;
v___y_1054_ = v___y_1065_;
v___y_1055_ = v___x_1067_;
goto v___jp_1046_;
}
else
{
lean_object* v___x_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; 
v___x_1068_ = lean_string_length(v___y_1065_);
v___x_1069_ = lean_unsigned_to_nat(255u);
v___x_1070_ = lean_nat_dec_le(v___x_1068_, v___x_1069_);
v___y_1047_ = v___y_1057_;
v___y_1048_ = v___y_1066_;
v___y_1049_ = v___y_1059_;
v___y_1050_ = v___y_1060_;
v___y_1051_ = v___y_1061_;
v___y_1052_ = v___y_1062_;
v___y_1053_ = v___y_1063_;
v___y_1054_ = v___y_1065_;
v___y_1055_ = v___x_1070_;
goto v___jp_1046_;
}
}
v___jp_1071_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1078_ = l_ByteArray_toByteSlice(v___y_1073_, v_lower_1076_, v_upper_1077_);
v___x_1079_ = l_ByteSlice_toByteArray(v___x_1078_);
v___x_1080_ = lean_string_validate_utf8(v___x_1079_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
lean_dec_ref(v___x_1079_);
lean_dec(v___y_1075_);
v___x_1081_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2));
v___x_1082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___y_1074_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
return v___x_1082_;
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1083_ = lean_string_from_utf8_unchecked(v___x_1079_);
lean_inc_n(v___y_1075_, 2);
lean_inc_ref(v___x_1083_);
v___x_1084_ = l_String_mapAux___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(v___x_1083_, v___y_1075_);
v___x_1085_ = lean_string_utf8_byte_size(v___x_1084_);
lean_inc_ref(v___x_1084_);
v___x_1086_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v___y_1075_);
lean_ctor_set(v___x_1086_, 2, v___x_1085_);
v___x_1087_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0);
v___x_1088_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_1084_, v___x_1086_, v___x_1085_, v___x_1087_, v___x_1080_);
if (v___x_1088_ == 0)
{
v___y_1057_ = v___y_1072_;
v___y_1058_ = v___x_1087_;
v___y_1059_ = v___x_1085_;
v___y_1060_ = v___y_1074_;
v___y_1061_ = v___x_1083_;
v___y_1062_ = v___y_1075_;
v___y_1063_ = v___x_1080_;
v___y_1064_ = v___x_1086_;
v___y_1065_ = v___x_1084_;
v___y_1066_ = v___x_1080_;
goto v___jp_1056_;
}
else
{
v___y_1057_ = v___y_1072_;
v___y_1058_ = v___x_1087_;
v___y_1059_ = v___x_1085_;
v___y_1060_ = v___y_1074_;
v___y_1061_ = v___x_1083_;
v___y_1062_ = v___y_1075_;
v___y_1063_ = v___x_1080_;
v___y_1064_ = v___x_1086_;
v___y_1065_ = v___x_1084_;
v___y_1066_ = v___y_1072_;
goto v___jp_1056_;
}
}
}
v___jp_1089_:
{
uint8_t v___x_1097_; 
v___x_1097_ = lean_nat_dec_le(v___y_1094_, v___y_1091_);
if (v___x_1097_ == 0)
{
lean_dec(v___y_1094_);
v___y_1072_ = v___y_1090_;
v___y_1073_ = v___y_1092_;
v___y_1074_ = v___y_1093_;
v___y_1075_ = v___y_1095_;
v_lower_1076_ = v___y_1096_;
v_upper_1077_ = v___y_1091_;
goto v___jp_1071_;
}
else
{
lean_dec(v___y_1091_);
v___y_1072_ = v___y_1090_;
v___y_1073_ = v___y_1092_;
v___y_1074_ = v___y_1093_;
v___y_1075_ = v___y_1095_;
v_lower_1076_ = v___y_1096_;
v_upper_1077_ = v___y_1094_;
goto v___jp_1071_;
}
}
v___jp_1101_:
{
lean_object* v_maxHostLength_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v_snd_1106_; lean_object* v_fst_1107_; lean_object* v_fst_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1122_; 
v_maxHostLength_1103_ = lean_ctor_get(v_config_1019_, 1);
v___x_1104_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___y_1102_);
v___x_1105_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1100_, v_maxHostLength_1103_, v___x_1104_, v___y_1102_);
v_snd_1106_ = lean_ctor_get(v___x_1105_, 1);
lean_inc(v_snd_1106_);
v_fst_1107_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_fst_1107_);
lean_dec_ref(v___x_1105_);
v_fst_1108_ = lean_ctor_get(v_snd_1106_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_snd_1106_);
if (v_isSharedCheck_1122_ == 0)
{
lean_object* v_unused_1123_; 
v_unused_1123_ = lean_ctor_get(v_snd_1106_, 1);
lean_dec(v_unused_1123_);
v___x_1110_ = v_snd_1106_;
v_isShared_1111_ = v_isSharedCheck_1122_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_fst_1108_);
lean_dec(v_snd_1106_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1122_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
uint8_t v___x_1112_; 
v___x_1112_ = lean_nat_dec_eq(v_fst_1107_, v___x_1104_);
if (v___x_1112_ == 0)
{
lean_object* v_array_1113_; lean_object* v_idx_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
lean_del_object(v___x_1110_);
v_array_1113_ = lean_ctor_get(v___y_1102_, 0);
lean_inc_ref(v_array_1113_);
v_idx_1114_ = lean_ctor_get(v___y_1102_, 1);
lean_inc(v_idx_1114_);
lean_dec_ref(v___y_1102_);
v___x_1115_ = lean_nat_add(v_idx_1114_, v_fst_1107_);
lean_dec(v_fst_1107_);
v___x_1116_ = lean_byte_array_size(v_array_1113_);
v___x_1117_ = lean_nat_dec_le(v_idx_1114_, v___x_1104_);
if (v___x_1117_ == 0)
{
v___y_1090_ = v___x_1112_;
v___y_1091_ = v___x_1116_;
v___y_1092_ = v_array_1113_;
v___y_1093_ = v_fst_1108_;
v___y_1094_ = v___x_1115_;
v___y_1095_ = v___x_1104_;
v___y_1096_ = v_idx_1114_;
goto v___jp_1089_;
}
else
{
lean_dec(v_idx_1114_);
v___y_1090_ = v___x_1112_;
v___y_1091_ = v___x_1116_;
v___y_1092_ = v_array_1113_;
v___y_1093_ = v_fst_1108_;
v___y_1094_ = v___x_1115_;
v___y_1095_ = v___x_1104_;
v___y_1096_ = v___x_1104_;
goto v___jp_1089_;
}
}
else
{
lean_object* v___x_1118_; lean_object* v___x_1120_; 
lean_dec(v_fst_1108_);
lean_dec(v_fst_1107_);
v___x_1118_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7));
if (v_isShared_1111_ == 0)
{
lean_ctor_set_tag(v___x_1110_, 1);
lean_ctor_set(v___x_1110_, 1, v___x_1118_);
lean_ctor_set(v___x_1110_, 0, v___y_1102_);
v___x_1120_ = v___x_1110_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___y_1102_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
v___jp_1124_:
{
lean_object* v___x_1126_; 
lean_inc_ref(v_pos_1125_);
v___x_1126_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(v_pos_1125_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_pos_1127_; lean_object* v_res_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1136_; 
lean_dec_ref(v_pos_1125_);
v_pos_1127_ = lean_ctor_get(v___x_1126_, 0);
v_res_1128_ = lean_ctor_get(v___x_1126_, 1);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1130_ = v___x_1126_;
v_isShared_1131_ = v_isSharedCheck_1136_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_res_1128_);
lean_inc(v_pos_1127_);
lean_dec(v___x_1126_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1136_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1132_, 0, v_res_1128_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 1, v___x_1132_);
v___x_1134_ = v___x_1130_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_pos_1127_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
else
{
lean_object* v_err_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1146_; 
v_err_1137_ = lean_ctor_get(v___x_1126_, 1);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1146_ == 0)
{
lean_object* v_unused_1147_; 
v_unused_1147_ = lean_ctor_get(v___x_1126_, 0);
lean_dec(v_unused_1147_);
v___x_1139_ = v___x_1126_;
v_isShared_1140_ = v_isSharedCheck_1146_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_err_1137_);
lean_dec(v___x_1126_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1146_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v_idx_1141_; uint8_t v___x_1142_; 
v_idx_1141_ = lean_ctor_get(v_pos_1125_, 1);
v___x_1142_ = lean_nat_dec_eq(v_idx_1141_, v_idx_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1144_; 
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v_pos_1125_);
v___x_1144_ = v___x_1139_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_pos_1125_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v_err_1137_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
else
{
lean_del_object(v___x_1139_);
lean_dec(v_err_1137_);
v___y_1102_ = v_pos_1125_;
goto v___jp_1101_;
}
}
}
}
v___jp_1148_:
{
v___y_1102_ = v_pos_1149_;
goto v___jp_1101_;
}
v___jp_1151_:
{
lean_object* v___x_1154_; uint8_t v___x_1155_; 
v___x_1154_ = lean_byte_array_size(v_array_1098_);
v___x_1155_ = lean_nat_dec_lt(v_idx_1099_, v___x_1154_);
if (v___x_1155_ == 0)
{
lean_dec(v_idx_1099_);
lean_dec_ref(v_array_1098_);
v_pos_1149_ = v_pos_1152_;
v_res_1150_ = v_res_1153_;
goto v___jp_1148_;
}
else
{
uint8_t v___x_1156_; uint8_t v___x_1157_; uint8_t v___x_1158_; 
v___x_1156_ = lean_byte_array_fget(v_array_1098_, v_idx_1099_);
lean_dec(v_idx_1099_);
lean_dec_ref(v_array_1098_);
v___x_1157_ = 48;
v___x_1158_ = lean_uint8_dec_le(v___x_1157_, v___x_1156_);
if (v___x_1158_ == 0)
{
v_pos_1149_ = v_pos_1152_;
v_res_1150_ = v_res_1153_;
goto v___jp_1148_;
}
else
{
uint8_t v___x_1159_; uint8_t v___x_1160_; 
v___x_1159_ = 57;
v___x_1160_ = lean_uint8_dec_le(v___x_1156_, v___x_1159_);
if (v___x_1160_ == 0)
{
v_pos_1149_ = v_pos_1152_;
v_res_1150_ = v_res_1153_;
goto v___jp_1148_;
}
else
{
v_pos_1125_ = v_pos_1152_;
goto v___jp_1124_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___boxed(lean_object* v_config_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_1188_, v_a_1189_);
lean_dec_ref(v_config_1188_);
return v_res_1190_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(lean_object* v___x_1191_, lean_object* v___x_1192_, lean_object* v___x_1193_, lean_object* v_inst_1194_, lean_object* v_R_1195_, lean_object* v_a_1196_, uint8_t v_b_1197_, lean_object* v_c_1198_){
_start:
{
uint8_t v___x_1199_; 
v___x_1199_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_1191_, v___x_1192_, v___x_1193_, v_a_1196_, v_b_1197_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___boxed(lean_object* v___x_1200_, lean_object* v___x_1201_, lean_object* v___x_1202_, lean_object* v_inst_1203_, lean_object* v_R_1204_, lean_object* v_a_1205_, lean_object* v_b_1206_, lean_object* v_c_1207_){
_start:
{
uint8_t v_b_boxed_1208_; uint8_t v_res_1209_; lean_object* v_r_1210_; 
v_b_boxed_1208_ = lean_unbox(v_b_1206_);
v_res_1209_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(v___x_1200_, v___x_1201_, v___x_1202_, v_inst_1203_, v_R_1204_, v_a_1205_, v_b_boxed_1208_, v_c_1207_);
lean_dec(v___x_1202_);
lean_dec_ref(v___x_1201_);
lean_dec_ref(v___x_1200_);
v_r_1210_ = lean_box(v_res_1209_);
return v_r_1210_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(uint8_t v___x_1211_, lean_object* v___x_1212_, lean_object* v___x_1213_, lean_object* v___x_1214_, lean_object* v_inst_1215_, lean_object* v_R_1216_, lean_object* v_a_1217_, uint8_t v_b_1218_, lean_object* v_c_1219_){
_start:
{
uint8_t v___x_1220_; 
v___x_1220_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_1211_, v___x_1212_, v___x_1213_, v___x_1214_, v_a_1217_, v_b_1218_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___boxed(lean_object* v___x_1221_, lean_object* v___x_1222_, lean_object* v___x_1223_, lean_object* v___x_1224_, lean_object* v_inst_1225_, lean_object* v_R_1226_, lean_object* v_a_1227_, lean_object* v_b_1228_, lean_object* v_c_1229_){
_start:
{
uint8_t v___x_11437__boxed_1230_; uint8_t v_b_boxed_1231_; uint8_t v_res_1232_; lean_object* v_r_1233_; 
v___x_11437__boxed_1230_ = lean_unbox(v___x_1221_);
v_b_boxed_1231_ = lean_unbox(v_b_1228_);
v_res_1232_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(v___x_11437__boxed_1230_, v___x_1222_, v___x_1223_, v___x_1224_, v_inst_1225_, v_R_1226_, v_a_1227_, v_b_boxed_1231_, v_c_1229_);
lean_dec_ref(v___x_1223_);
lean_dec_ref(v___x_1222_);
v_r_1233_ = lean_box(v_res_1232_);
return v_r_1233_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1(lean_object* v___x_1234_, lean_object* v___x_1235_, lean_object* v___x_1236_, lean_object* v_inst_1237_, lean_object* v_R_1238_, lean_object* v_a_1239_, uint8_t v_b_1240_, lean_object* v_c_1241_){
_start:
{
uint8_t v___x_1242_; 
v___x_1242_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1___redArg(v___x_1235_, v_a_1239_, v_b_1240_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1___boxed(lean_object* v___x_1243_, lean_object* v___x_1244_, lean_object* v___x_1245_, lean_object* v_inst_1246_, lean_object* v_R_1247_, lean_object* v_a_1248_, lean_object* v_b_1249_, lean_object* v_c_1250_){
_start:
{
uint8_t v_b_boxed_1251_; uint8_t v_res_1252_; lean_object* v_r_1253_; 
v_b_boxed_1251_ = lean_unbox(v_b_1249_);
v_res_1252_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1(v___x_1243_, v___x_1244_, v___x_1245_, v_inst_1246_, v_R_1247_, v_a_1248_, v_b_boxed_1251_, v_c_1250_);
lean_dec(v___x_1245_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v___x_1243_);
v_r_1253_ = lean_box(v_res_1252_);
return v_r_1253_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3(uint8_t v___x_1254_, lean_object* v___x_1255_, lean_object* v___x_1256_, lean_object* v___x_1257_, lean_object* v_inst_1258_, lean_object* v_R_1259_, lean_object* v_a_1260_, uint8_t v_b_1261_, lean_object* v_c_1262_){
_start:
{
uint8_t v___x_1263_; 
v___x_1263_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3___redArg(v___x_1254_, v___x_1255_, v___x_1256_, v___x_1257_, v_a_1260_, v_b_1261_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3___boxed(lean_object* v___x_1264_, lean_object* v___x_1265_, lean_object* v___x_1266_, lean_object* v___x_1267_, lean_object* v_inst_1268_, lean_object* v_R_1269_, lean_object* v_a_1270_, lean_object* v_b_1271_, lean_object* v_c_1272_){
_start:
{
uint8_t v___x_11468__boxed_1273_; uint8_t v_b_boxed_1274_; uint8_t v_res_1275_; lean_object* v_r_1276_; 
v___x_11468__boxed_1273_ = lean_unbox(v___x_1264_);
v_b_boxed_1274_ = lean_unbox(v_b_1271_);
v_res_1275_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3(v___x_11468__boxed_1273_, v___x_1265_, v___x_1266_, v___x_1267_, v_inst_1268_, v_R_1269_, v_a_1270_, v_b_boxed_1274_, v_c_1272_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
v_r_1276_ = lean_box(v_res_1275_);
return v_r_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(lean_object* v_config_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v_port_1291_; lean_object* v___y_1292_; lean_object* v___y_1296_; lean_object* v___y_1300_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1305_; lean_object* v___y_1306_; uint8_t v___y_1307_; lean_object* v___y_1308_; uint8_t v___y_1309_; lean_object* v___y_1311_; lean_object* v___y_1312_; uint8_t v_val_1313_; lean_object* v___y_1314_; lean_object* v___y_1322_; uint8_t v___y_1323_; lean_object* v___y_1324_; lean_object* v_pos_1325_; lean_object* v_array_1326_; lean_object* v_idx_1327_; lean_object* v_res_1328_; lean_object* v___y_1333_; lean_object* v___y_1334_; uint8_t v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v_pos_1343_; lean_object* v_pos_1346_; lean_object* v_res_1347_; lean_object* v_pos_1412_; lean_object* v_res_1413_; lean_object* v_err_1416_; lean_object* v___x_1421_; 
lean_inc_ref(v_a_1287_);
v___x_1421_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(v_config_1286_, v_a_1287_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_pos_1422_; lean_object* v_res_1423_; lean_object* v_array_1424_; lean_object* v_idx_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1441_; 
v_pos_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_pos_1422_);
v_res_1423_ = lean_ctor_get(v___x_1421_, 1);
lean_inc(v_res_1423_);
lean_dec_ref_known(v___x_1421_, 2);
v_array_1424_ = lean_ctor_get(v_pos_1422_, 0);
v_idx_1425_ = lean_ctor_get(v_pos_1422_, 1);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_pos_1422_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1427_ = v_pos_1422_;
v_isShared_1428_ = v_isSharedCheck_1441_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_idx_1425_);
lean_inc(v_array_1424_);
lean_dec(v_pos_1422_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1441_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1429_ = lean_byte_array_size(v_array_1424_);
v___x_1430_ = lean_nat_dec_lt(v_idx_1425_, v___x_1429_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; 
lean_del_object(v___x_1427_);
lean_dec(v_idx_1425_);
lean_dec_ref(v_array_1424_);
lean_dec(v_res_1423_);
v___x_1431_ = lean_box(0);
v_err_1416_ = v___x_1431_;
goto v___jp_1415_;
}
else
{
uint8_t v___x_1432_; uint8_t v_got_1433_; uint8_t v___x_1434_; 
v___x_1432_ = 64;
v_got_1433_ = lean_byte_array_fget(v_array_1424_, v_idx_1425_);
v___x_1434_ = lean_uint8_dec_eq(v_got_1433_, v___x_1432_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; 
lean_del_object(v___x_1427_);
lean_dec(v_idx_1425_);
lean_dec_ref(v_array_1424_);
lean_dec(v_res_1423_);
v___x_1435_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5));
v_err_1416_ = v___x_1435_;
goto v___jp_1415_;
}
else
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1439_; 
lean_dec_ref(v_a_1287_);
v___x_1436_ = lean_unsigned_to_nat(1u);
v___x_1437_ = lean_nat_add(v_idx_1425_, v___x_1436_);
lean_dec(v_idx_1425_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 1, v___x_1437_);
v___x_1439_ = v___x_1427_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_array_1424_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v___x_1437_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
v_pos_1412_ = v___x_1439_;
v_res_1413_ = v_res_1423_;
goto v___jp_1411_;
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_pos_1442_; lean_object* v_res_1443_; 
lean_dec_ref(v_a_1287_);
v_pos_1442_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_pos_1442_);
v_res_1443_ = lean_ctor_get(v___x_1421_, 1);
lean_inc(v_res_1443_);
lean_dec_ref_known(v___x_1421_, 2);
v_pos_1412_ = v_pos_1442_;
v_res_1413_ = v_res_1443_;
goto v___jp_1411_;
}
else
{
lean_object* v_err_1444_; 
v_err_1444_ = lean_ctor_get(v___x_1421_, 1);
lean_inc(v_err_1444_);
lean_dec_ref_known(v___x_1421_, 2);
v_err_1416_ = v_err_1444_;
goto v___jp_1415_;
}
}
v___jp_1288_:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1293_, 0, v___y_1289_);
lean_ctor_set(v___x_1293_, 1, v___y_1290_);
lean_ctor_set(v___x_1293_, 2, v_port_1291_);
v___x_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___y_1292_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
return v___x_1294_;
}
v___jp_1295_:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__1));
v___x_1298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___y_1296_);
lean_ctor_set(v___x_1298_, 1, v___x_1297_);
return v___x_1298_;
}
v___jp_1299_:
{
lean_object* v___x_1303_; 
v___x_1303_ = lean_box(1);
v___y_1289_ = v___y_1301_;
v___y_1290_ = v___y_1302_;
v_port_1291_ = v___x_1303_;
v___y_1292_ = v___y_1300_;
goto v___jp_1288_;
}
v___jp_1304_:
{
if (v___y_1307_ == 0)
{
if (v___y_1309_ == 0)
{
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1306_);
v___y_1296_ = v___y_1305_;
goto v___jp_1295_;
}
else
{
v___y_1300_ = v___y_1305_;
v___y_1301_ = v___y_1306_;
v___y_1302_ = v___y_1308_;
goto v___jp_1299_;
}
}
else
{
v___y_1300_ = v___y_1305_;
v___y_1301_ = v___y_1306_;
v___y_1302_ = v___y_1308_;
goto v___jp_1299_;
}
}
v___jp_1310_:
{
uint8_t v___x_1315_; uint8_t v___x_1316_; uint8_t v___x_1317_; uint8_t v___x_1318_; 
v___x_1315_ = 47;
v___x_1316_ = lean_uint8_dec_eq(v_val_1313_, v___x_1315_);
v___x_1317_ = 63;
v___x_1318_ = lean_uint8_dec_eq(v_val_1313_, v___x_1317_);
if (v___x_1318_ == 0)
{
uint8_t v___x_1319_; uint8_t v___x_1320_; 
v___x_1319_ = 35;
v___x_1320_ = lean_uint8_dec_eq(v_val_1313_, v___x_1319_);
v___y_1305_ = v___y_1311_;
v___y_1306_ = v___y_1312_;
v___y_1307_ = v___x_1316_;
v___y_1308_ = v___y_1314_;
v___y_1309_ = v___x_1320_;
goto v___jp_1304_;
}
else
{
v___y_1305_ = v___y_1311_;
v___y_1306_ = v___y_1312_;
v___y_1307_ = v___x_1316_;
v___y_1308_ = v___y_1314_;
v___y_1309_ = v___x_1318_;
goto v___jp_1304_;
}
}
v___jp_1321_:
{
lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1329_ = lean_byte_array_size(v_array_1326_);
v___x_1330_ = lean_nat_dec_lt(v_idx_1327_, v___x_1329_);
if (v___x_1330_ == 0)
{
lean_dec(v_idx_1327_);
lean_dec_ref(v_array_1326_);
if (v___y_1323_ == 0)
{
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1322_);
v___y_1296_ = v_pos_1325_;
goto v___jp_1295_;
}
else
{
v___y_1300_ = v_pos_1325_;
v___y_1301_ = v___y_1322_;
v___y_1302_ = v___y_1324_;
goto v___jp_1299_;
}
}
else
{
uint8_t v___x_1331_; 
v___x_1331_ = lean_byte_array_fget(v_array_1326_, v_idx_1327_);
lean_dec(v_idx_1327_);
lean_dec_ref(v_array_1326_);
v___y_1311_ = v_pos_1325_;
v___y_1312_ = v___y_1322_;
v_val_1313_ = v___x_1331_;
v___y_1314_ = v___y_1324_;
goto v___jp_1310_;
}
}
v___jp_1332_:
{
lean_object* v___x_1339_; 
v___x_1339_ = lean_box(0);
v___y_1322_ = v___y_1333_;
v___y_1323_ = v___y_1335_;
v___y_1324_ = v___y_1338_;
v_pos_1325_ = v___y_1334_;
v_array_1326_ = v___y_1336_;
v_idx_1327_ = v___y_1337_;
v_res_1328_ = v___x_1339_;
goto v___jp_1321_;
}
v___jp_1340_:
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_box(0);
v___y_1289_ = v___y_1341_;
v___y_1290_ = v___y_1342_;
v_port_1291_ = v___x_1344_;
v___y_1292_ = v_pos_1343_;
goto v___jp_1288_;
}
v___jp_1345_:
{
lean_object* v___x_1348_; 
v___x_1348_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_1286_, v_pos_1346_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_pos_1349_; lean_object* v_res_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1401_; 
v_pos_1349_ = lean_ctor_get(v___x_1348_, 0);
v_res_1350_ = lean_ctor_get(v___x_1348_, 1);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1352_ = v___x_1348_;
v_isShared_1353_ = v_isSharedCheck_1401_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_res_1350_);
lean_inc(v_pos_1349_);
lean_dec(v___x_1348_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1401_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v_array_1354_; lean_object* v_idx_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v_array_1354_ = lean_ctor_get(v_pos_1349_, 0);
v_idx_1355_ = lean_ctor_get(v_pos_1349_, 1);
v___x_1356_ = lean_byte_array_size(v_array_1354_);
v___x_1357_ = lean_nat_dec_lt(v_idx_1355_, v___x_1356_);
if (v___x_1357_ == 0)
{
lean_del_object(v___x_1352_);
v___y_1341_ = v_res_1347_;
v___y_1342_ = v_res_1350_;
v_pos_1343_ = v_pos_1349_;
goto v___jp_1340_;
}
else
{
uint8_t v___x_1358_; uint8_t v___x_1359_; uint8_t v___x_1360_; 
v___x_1358_ = lean_byte_array_fget(v_array_1354_, v_idx_1355_);
v___x_1359_ = 58;
v___x_1360_ = lean_uint8_dec_eq(v___x_1358_, v___x_1359_);
if (v___x_1360_ == 0)
{
lean_del_object(v___x_1352_);
v___y_1341_ = v_res_1347_;
v___y_1342_ = v_res_1350_;
v_pos_1343_ = v_pos_1349_;
goto v___jp_1340_;
}
else
{
if (v___x_1360_ == 0)
{
lean_del_object(v___x_1352_);
v___y_1341_ = v_res_1347_;
v___y_1342_ = v_res_1350_;
v_pos_1343_ = v_pos_1349_;
goto v___jp_1340_;
}
else
{
if (v___x_1357_ == 0)
{
lean_object* v___x_1361_; lean_object* v___x_1363_; 
lean_dec(v_res_1350_);
lean_dec(v_res_1347_);
v___x_1361_ = lean_box(0);
if (v_isShared_1353_ == 0)
{
lean_ctor_set_tag(v___x_1352_, 1);
lean_ctor_set(v___x_1352_, 1, v___x_1361_);
v___x_1363_ = v___x_1352_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_pos_1349_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
else
{
if (v___x_1360_ == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
lean_dec(v_res_1350_);
lean_dec(v_res_1347_);
v___x_1365_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_1353_ == 0)
{
lean_ctor_set_tag(v___x_1352_, 1);
lean_ctor_set(v___x_1352_, 1, v___x_1365_);
v___x_1367_ = v___x_1352_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_pos_1349_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
else
{
lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1398_; 
lean_inc(v_idx_1355_);
lean_inc_ref(v_array_1354_);
lean_del_object(v___x_1352_);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_pos_1349_);
if (v_isSharedCheck_1398_ == 0)
{
lean_object* v_unused_1399_; lean_object* v_unused_1400_; 
v_unused_1399_ = lean_ctor_get(v_pos_1349_, 1);
lean_dec(v_unused_1399_);
v_unused_1400_ = lean_ctor_get(v_pos_1349_, 0);
lean_dec(v_unused_1400_);
v___x_1370_ = v_pos_1349_;
v_isShared_1371_ = v_isSharedCheck_1398_;
goto v_resetjp_1369_;
}
else
{
lean_dec(v_pos_1349_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1398_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1372_ = lean_unsigned_to_nat(1u);
v___x_1373_ = lean_nat_add(v_idx_1355_, v___x_1372_);
lean_dec(v_idx_1355_);
lean_inc(v___x_1373_);
lean_inc_ref(v_array_1354_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 1, v___x_1373_);
v___x_1375_ = v___x_1370_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_array_1354_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
uint8_t v___x_1376_; 
v___x_1376_ = lean_nat_dec_lt(v___x_1373_, v___x_1356_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; 
v___x_1377_ = lean_box(0);
v___y_1322_ = v_res_1347_;
v___y_1323_ = v___x_1360_;
v___y_1324_ = v_res_1350_;
v_pos_1325_ = v___x_1375_;
v_array_1326_ = v_array_1354_;
v_idx_1327_ = v___x_1373_;
v_res_1328_ = v___x_1377_;
goto v___jp_1321_;
}
else
{
uint8_t v___x_1378_; uint8_t v___x_1379_; uint8_t v___x_1380_; 
v___x_1378_ = lean_byte_array_fget(v_array_1354_, v___x_1373_);
v___x_1379_ = 48;
v___x_1380_ = lean_uint8_dec_le(v___x_1379_, v___x_1378_);
if (v___x_1380_ == 0)
{
v___y_1333_ = v_res_1347_;
v___y_1334_ = v___x_1375_;
v___y_1335_ = v___x_1360_;
v___y_1336_ = v_array_1354_;
v___y_1337_ = v___x_1373_;
v___y_1338_ = v_res_1350_;
goto v___jp_1332_;
}
else
{
uint8_t v___x_1381_; uint8_t v___x_1382_; 
v___x_1381_ = 57;
v___x_1382_ = lean_uint8_dec_le(v___x_1378_, v___x_1381_);
if (v___x_1382_ == 0)
{
v___y_1333_ = v_res_1347_;
v___y_1334_ = v___x_1375_;
v___y_1335_ = v___x_1360_;
v___y_1336_ = v_array_1354_;
v___y_1337_ = v___x_1373_;
v___y_1338_ = v_res_1350_;
goto v___jp_1332_;
}
else
{
lean_object* v___x_1383_; 
lean_dec(v___x_1373_);
lean_dec_ref(v_array_1354_);
v___x_1383_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_1375_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_pos_1384_; lean_object* v_res_1385_; lean_object* v___x_1386_; uint16_t v___x_1387_; 
v_pos_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_pos_1384_);
v_res_1385_ = lean_ctor_get(v___x_1383_, 1);
lean_inc(v_res_1385_);
lean_dec_ref_known(v___x_1383_, 2);
v___x_1386_ = lean_alloc_ctor(2, 0, 2);
v___x_1387_ = lean_unbox(v_res_1385_);
lean_dec(v_res_1385_);
lean_ctor_set_uint16(v___x_1386_, 0, v___x_1387_);
v___y_1289_ = v_res_1347_;
v___y_1290_ = v_res_1350_;
v_port_1291_ = v___x_1386_;
v___y_1292_ = v_pos_1384_;
goto v___jp_1288_;
}
else
{
lean_object* v_pos_1388_; lean_object* v_err_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_dec(v_res_1350_);
lean_dec(v_res_1347_);
v_pos_1388_ = lean_ctor_get(v___x_1383_, 0);
v_err_1389_ = lean_ctor_get(v___x_1383_, 1);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1383_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_err_1389_);
lean_inc(v_pos_1388_);
lean_dec(v___x_1383_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_pos_1388_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_err_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
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
lean_object* v_pos_1402_; lean_object* v_err_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
lean_dec(v_res_1347_);
v_pos_1402_ = lean_ctor_get(v___x_1348_, 0);
v_err_1403_ = lean_ctor_get(v___x_1348_, 1);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1348_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_err_1403_);
lean_inc(v_pos_1402_);
lean_dec(v___x_1348_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_pos_1402_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_err_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
v___jp_1411_:
{
lean_object* v___x_1414_; 
v___x_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1414_, 0, v_res_1413_);
v_pos_1346_ = v_pos_1412_;
v_res_1347_ = v___x_1414_;
goto v___jp_1345_;
}
v___jp_1415_:
{
lean_object* v_idx_1417_; uint8_t v___x_1418_; 
v_idx_1417_ = lean_ctor_get(v_a_1287_, 1);
v___x_1418_ = lean_nat_dec_eq(v_idx_1417_, v_idx_1417_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1419_, 0, v_a_1287_);
lean_ctor_set(v___x_1419_, 1, v_err_1416_);
return v___x_1419_;
}
else
{
lean_object* v___x_1420_; 
lean_dec(v_err_1416_);
v___x_1420_ = lean_box(0);
v_pos_1346_ = v_a_1287_;
v_res_1347_ = v___x_1420_;
goto v___jp_1345_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___boxed(lean_object* v_config_1445_, lean_object* v_a_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_1445_, v_a_1446_);
lean_dec_ref(v_config_1445_);
return v_res_1447_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(uint8_t v_c_1448_){
_start:
{
uint8_t v___y_1450_; uint8_t v___x_1498_; uint8_t v___x_1499_; 
v___x_1498_ = 48;
v___x_1499_ = lean_uint8_dec_le(v___x_1498_, v_c_1448_);
if (v___x_1499_ == 0)
{
goto v___jp_1493_;
}
else
{
uint8_t v___x_1500_; uint8_t v___x_1501_; 
v___x_1500_ = 57;
v___x_1501_ = lean_uint8_dec_le(v_c_1448_, v___x_1500_);
if (v___x_1501_ == 0)
{
goto v___jp_1493_;
}
else
{
v___y_1450_ = v___x_1501_;
goto v___jp_1449_;
}
}
v___jp_1449_:
{
if (v___y_1450_ == 0)
{
uint8_t v___x_1451_; uint8_t v___x_1452_; 
v___x_1451_ = 37;
v___x_1452_ = lean_uint8_dec_eq(v_c_1448_, v___x_1451_);
return v___x_1452_;
}
else
{
return v___y_1450_;
}
}
v___jp_1453_:
{
uint8_t v___x_1454_; uint8_t v___x_1455_; 
v___x_1454_ = 45;
v___x_1455_ = lean_uint8_dec_eq(v_c_1448_, v___x_1454_);
if (v___x_1455_ == 0)
{
uint8_t v___x_1456_; uint8_t v___x_1457_; 
v___x_1456_ = 46;
v___x_1457_ = lean_uint8_dec_eq(v_c_1448_, v___x_1456_);
if (v___x_1457_ == 0)
{
uint8_t v___x_1458_; uint8_t v___x_1459_; 
v___x_1458_ = 95;
v___x_1459_ = lean_uint8_dec_eq(v_c_1448_, v___x_1458_);
if (v___x_1459_ == 0)
{
uint8_t v___x_1460_; uint8_t v___x_1461_; 
v___x_1460_ = 126;
v___x_1461_ = lean_uint8_dec_eq(v_c_1448_, v___x_1460_);
if (v___x_1461_ == 0)
{
uint8_t v___x_1462_; uint8_t v___x_1463_; 
v___x_1462_ = 33;
v___x_1463_ = lean_uint8_dec_eq(v_c_1448_, v___x_1462_);
if (v___x_1463_ == 0)
{
uint8_t v___x_1464_; uint8_t v___x_1465_; 
v___x_1464_ = 36;
v___x_1465_ = lean_uint8_dec_eq(v_c_1448_, v___x_1464_);
if (v___x_1465_ == 0)
{
uint8_t v___x_1466_; uint8_t v___x_1467_; 
v___x_1466_ = 38;
v___x_1467_ = lean_uint8_dec_eq(v_c_1448_, v___x_1466_);
if (v___x_1467_ == 0)
{
uint8_t v___x_1468_; uint8_t v___x_1469_; 
v___x_1468_ = 39;
v___x_1469_ = lean_uint8_dec_eq(v_c_1448_, v___x_1468_);
if (v___x_1469_ == 0)
{
uint8_t v___x_1470_; uint8_t v___x_1471_; 
v___x_1470_ = 40;
v___x_1471_ = lean_uint8_dec_eq(v_c_1448_, v___x_1470_);
if (v___x_1471_ == 0)
{
uint8_t v___x_1472_; uint8_t v___x_1473_; 
v___x_1472_ = 41;
v___x_1473_ = lean_uint8_dec_eq(v_c_1448_, v___x_1472_);
if (v___x_1473_ == 0)
{
uint8_t v___x_1474_; uint8_t v___x_1475_; 
v___x_1474_ = 42;
v___x_1475_ = lean_uint8_dec_eq(v_c_1448_, v___x_1474_);
if (v___x_1475_ == 0)
{
uint8_t v___x_1476_; uint8_t v___x_1477_; 
v___x_1476_ = 43;
v___x_1477_ = lean_uint8_dec_eq(v_c_1448_, v___x_1476_);
if (v___x_1477_ == 0)
{
uint8_t v___x_1478_; uint8_t v___x_1479_; 
v___x_1478_ = 44;
v___x_1479_ = lean_uint8_dec_eq(v_c_1448_, v___x_1478_);
if (v___x_1479_ == 0)
{
uint8_t v___x_1480_; uint8_t v___x_1481_; 
v___x_1480_ = 59;
v___x_1481_ = lean_uint8_dec_eq(v_c_1448_, v___x_1480_);
if (v___x_1481_ == 0)
{
uint8_t v___x_1482_; uint8_t v___x_1483_; 
v___x_1482_ = 61;
v___x_1483_ = lean_uint8_dec_eq(v_c_1448_, v___x_1482_);
if (v___x_1483_ == 0)
{
uint8_t v___x_1484_; uint8_t v___x_1485_; 
v___x_1484_ = 58;
v___x_1485_ = lean_uint8_dec_eq(v_c_1448_, v___x_1484_);
if (v___x_1485_ == 0)
{
uint8_t v___x_1486_; uint8_t v___x_1487_; 
v___x_1486_ = 64;
v___x_1487_ = lean_uint8_dec_eq(v_c_1448_, v___x_1486_);
v___y_1450_ = v___x_1487_;
goto v___jp_1449_;
}
else
{
v___y_1450_ = v___x_1485_;
goto v___jp_1449_;
}
}
else
{
v___y_1450_ = v___x_1483_;
goto v___jp_1449_;
}
}
else
{
v___y_1450_ = v___x_1481_;
goto v___jp_1449_;
}
}
else
{
v___y_1450_ = v___x_1479_;
goto v___jp_1449_;
}
}
else
{
v___y_1450_ = v___x_1477_;
goto v___jp_1449_;
}
}
else
{
v___y_1450_ = v___x_1475_;
goto v___jp_1449_;
}
}
else
{
v___y_1450_ = v___x_1473_;
goto v___jp_1449_;
}
}
else
{
v___y_1450_ = v___x_1471_;
goto v___jp_1449_;
}
}
else
{
v___y_1450_ = v___x_1469_;
goto v___jp_1449_;
}
}
else
{
v___y_1450_ = v___x_1467_;
goto v___jp_1449_;
}
}
else
{
v___y_1450_ = v___x_1465_;
goto v___jp_1449_;
}
}
else
{
v___y_1450_ = v___x_1463_;
goto v___jp_1449_;
}
}
else
{
v___y_1450_ = v___x_1461_;
goto v___jp_1449_;
}
}
else
{
v___y_1450_ = v___x_1459_;
goto v___jp_1449_;
}
}
else
{
v___y_1450_ = v___x_1457_;
goto v___jp_1449_;
}
}
else
{
v___y_1450_ = v___x_1455_;
goto v___jp_1449_;
}
}
v___jp_1488_:
{
uint8_t v___x_1489_; uint8_t v___x_1490_; 
v___x_1489_ = 65;
v___x_1490_ = lean_uint8_dec_le(v___x_1489_, v_c_1448_);
if (v___x_1490_ == 0)
{
goto v___jp_1453_;
}
else
{
uint8_t v___x_1491_; uint8_t v___x_1492_; 
v___x_1491_ = 90;
v___x_1492_ = lean_uint8_dec_le(v_c_1448_, v___x_1491_);
if (v___x_1492_ == 0)
{
goto v___jp_1453_;
}
else
{
v___y_1450_ = v___x_1492_;
goto v___jp_1449_;
}
}
}
v___jp_1493_:
{
uint8_t v___x_1494_; uint8_t v___x_1495_; 
v___x_1494_ = 97;
v___x_1495_ = lean_uint8_dec_le(v___x_1494_, v_c_1448_);
if (v___x_1495_ == 0)
{
goto v___jp_1488_;
}
else
{
uint8_t v___x_1496_; uint8_t v___x_1497_; 
v___x_1496_ = 122;
v___x_1497_ = lean_uint8_dec_le(v_c_1448_, v___x_1496_);
if (v___x_1497_ == 0)
{
goto v___jp_1488_;
}
else
{
v___y_1450_ = v___x_1497_;
goto v___jp_1449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0___boxed(lean_object* v_c_1502_){
_start:
{
uint8_t v_c_boxed_1503_; uint8_t v_res_1504_; lean_object* v_r_1505_; 
v_c_boxed_1503_ = lean_unbox(v_c_1502_);
v_res_1504_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(v_c_boxed_1503_);
v_r_1505_ = lean_box(v_res_1504_);
return v_r_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(lean_object* v_config_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v_maxSegmentLength_1509_; lean_object* v___f_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v_snd_1513_; lean_object* v_fst_1514_; lean_object* v_fst_1515_; lean_object* v_array_1516_; lean_object* v_idx_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1534_; 
v_maxSegmentLength_1509_ = lean_ctor_get(v_config_1507_, 3);
v___f_1510_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___closed__0));
v___x_1511_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1508_);
v___x_1512_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1510_, v_maxSegmentLength_1509_, v___x_1511_, v_a_1508_);
v_snd_1513_ = lean_ctor_get(v___x_1512_, 1);
lean_inc(v_snd_1513_);
v_fst_1514_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_fst_1514_);
lean_dec_ref(v___x_1512_);
v_fst_1515_ = lean_ctor_get(v_snd_1513_, 0);
lean_inc(v_fst_1515_);
lean_dec(v_snd_1513_);
v_array_1516_ = lean_ctor_get(v_a_1508_, 0);
v_idx_1517_ = lean_ctor_get(v_a_1508_, 1);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_a_1508_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1519_ = v_a_1508_;
v_isShared_1520_ = v_isSharedCheck_1534_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_idx_1517_);
lean_inc(v_array_1516_);
lean_dec(v_a_1508_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1534_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v_lower_1522_; lean_object* v_upper_1523_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___y_1531_; uint8_t v___x_1533_; 
v___x_1528_ = lean_nat_add(v_idx_1517_, v_fst_1514_);
lean_dec(v_fst_1514_);
v___x_1529_ = lean_byte_array_size(v_array_1516_);
v___x_1533_ = lean_nat_dec_le(v_idx_1517_, v___x_1511_);
if (v___x_1533_ == 0)
{
v___y_1531_ = v_idx_1517_;
goto v___jp_1530_;
}
else
{
lean_dec(v_idx_1517_);
v___y_1531_ = v___x_1511_;
goto v___jp_1530_;
}
v___jp_1521_:
{
lean_object* v___x_1524_; lean_object* v___x_1526_; 
v___x_1524_ = l_ByteArray_toByteSlice(v_array_1516_, v_lower_1522_, v_upper_1523_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 1, v___x_1524_);
lean_ctor_set(v___x_1519_, 0, v_fst_1515_);
v___x_1526_ = v___x_1519_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_fst_1515_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v___x_1524_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
v___jp_1530_:
{
uint8_t v___x_1532_; 
v___x_1532_ = lean_nat_dec_le(v___x_1528_, v___x_1529_);
if (v___x_1532_ == 0)
{
lean_dec(v___x_1528_);
v_lower_1522_ = v___y_1531_;
v_upper_1523_ = v___x_1529_;
goto v___jp_1521_;
}
else
{
v_lower_1522_ = v___y_1531_;
v_upper_1523_ = v___x_1528_;
goto v___jp_1521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___boxed(lean_object* v_config_1535_, lean_object* v_a_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1535_, v_a_1536_);
lean_dec_ref(v_config_1535_);
return v_res_1537_;
}
}
LEAN_EXPORT uint8_t l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(uint8_t v_c_1538_){
_start:
{
uint8_t v___x_1539_; uint8_t v___x_1540_; 
v___x_1539_ = 63;
v___x_1540_ = lean_uint8_dec_eq(v_c_1538_, v___x_1539_);
if (v___x_1540_ == 0)
{
uint8_t v___x_1541_; uint8_t v___x_1542_; 
v___x_1541_ = 35;
v___x_1542_ = lean_uint8_dec_eq(v_c_1538_, v___x_1541_);
return v___x_1542_;
}
else
{
return v___x_1540_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0___boxed(lean_object* v_c_1543_){
_start:
{
uint8_t v_c_boxed_1544_; uint8_t v_res_1545_; lean_object* v_r_1546_; 
v_c_boxed_1544_ = lean_unbox(v_c_1543_);
v_res_1545_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v_c_boxed_1544_);
v_r_1546_ = lean_box(v_res_1545_);
return v_r_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(lean_object* v_config_1554_, lean_object* v_a_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v_array_1581_; lean_object* v_idx_1582_; lean_object* v_fst_1583_; lean_object* v_snd_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1760_; 
v_array_1581_ = lean_ctor_get(v___y_1556_, 0);
v_idx_1582_ = lean_ctor_get(v___y_1556_, 1);
v_fst_1583_ = lean_ctor_get(v_a_1555_, 0);
v_snd_1584_ = lean_ctor_get(v_a_1555_, 1);
v_isSharedCheck_1760_ = !lean_is_exclusive(v_a_1555_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1586_ = v_a_1555_;
v_isShared_1587_ = v_isSharedCheck_1760_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_snd_1584_);
lean_inc(v_fst_1583_);
lean_dec(v_a_1555_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1760_;
goto v_resetjp_1585_;
}
v___jp_1557_:
{
lean_object* v___x_1562_; uint8_t v___x_1563_; 
v___x_1562_ = lean_array_get_size(v___y_1560_);
v___x_1563_ = lean_nat_dec_le(v___y_1558_, v___x_1562_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
lean_dec(v___y_1558_);
v___x_1564_ = l_ByteArray_empty;
v___x_1565_ = lean_array_push(v___y_1560_, v___x_1564_);
v___x_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
lean_ctor_set(v___x_1566_, 1, v___y_1561_);
v_a_1555_ = v___x_1566_;
v___y_1556_ = v___y_1559_;
goto _start;
}
else
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec_ref(v_config_1554_);
v___x_1568_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1569_ = l_Nat_reprFast(v___y_1558_);
v___x_1570_ = lean_string_append(v___x_1568_, v___x_1569_);
lean_dec_ref(v___x_1569_);
v___x_1571_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1572_ = lean_string_append(v___x_1570_, v___x_1571_);
v___x_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
v___x_1574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___y_1559_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
return v___x_1574_;
}
}
v___jp_1575_:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___y_1577_);
lean_ctor_set(v___x_1579_, 1, v___y_1576_);
v___x_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___y_1578_);
lean_ctor_set(v___x_1580_, 1, v___x_1579_);
return v___x_1580_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; uint8_t v___x_1589_; 
v___x_1588_ = lean_byte_array_size(v_array_1581_);
v___x_1589_ = lean_nat_dec_lt(v_idx_1582_, v___x_1588_);
if (v___x_1589_ == 0)
{
lean_object* v___x_1591_; 
lean_dec_ref(v_config_1554_);
if (v_isShared_1587_ == 0)
{
v___x_1591_ = v___x_1586_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_fst_1583_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_snd_1584_);
v___x_1591_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1592_; 
v___x_1592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___y_1556_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
return v___x_1592_;
}
}
else
{
if (v___x_1589_ == 0)
{
lean_object* v___x_1595_; 
lean_dec_ref(v_config_1554_);
if (v_isShared_1587_ == 0)
{
v___x_1595_ = v___x_1586_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_fst_1583_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_snd_1584_);
v___x_1595_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1596_; 
v___x_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___y_1556_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
return v___x_1596_;
}
}
else
{
uint8_t v___x_1598_; uint8_t v___x_1599_; 
v___x_1598_ = lean_byte_array_fget(v_array_1581_, v_idx_1582_);
v___x_1599_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1598_);
if (v___x_1599_ == 0)
{
uint8_t v___x_1600_; uint8_t v___y_1697_; uint8_t v___x_1700_; uint8_t v___y_1702_; uint8_t v___y_1704_; uint8_t v___x_1752_; uint8_t v___x_1753_; 
v___x_1600_ = 47;
v___x_1700_ = lean_uint8_dec_eq(v___x_1598_, v___x_1600_);
v___x_1752_ = 48;
v___x_1753_ = lean_uint8_dec_le(v___x_1752_, v___x_1598_);
if (v___x_1753_ == 0)
{
goto v___jp_1747_;
}
else
{
uint8_t v___x_1754_; uint8_t v___x_1755_; 
v___x_1754_ = 57;
v___x_1755_ = lean_uint8_dec_le(v___x_1598_, v___x_1754_);
if (v___x_1755_ == 0)
{
goto v___jp_1747_;
}
else
{
v___y_1704_ = v___x_1755_;
goto v___jp_1703_;
}
}
v___jp_1601_:
{
lean_object* v_maxPathSegments_1602_; lean_object* v_maxTotalPathLength_1603_; lean_object* v___x_1604_; uint8_t v___x_1605_; 
v_maxPathSegments_1602_ = lean_ctor_get(v_config_1554_, 6);
v_maxTotalPathLength_1603_ = lean_ctor_get(v_config_1554_, 7);
v___x_1604_ = lean_array_get_size(v_fst_1583_);
v___x_1605_ = lean_nat_dec_le(v_maxPathSegments_1602_, v___x_1604_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; 
v___x_1606_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1554_, v___y_1556_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_pos_1607_; lean_object* v_res_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1679_; 
v_pos_1607_ = lean_ctor_get(v___x_1606_, 0);
v_res_1608_ = lean_ctor_get(v___x_1606_, 1);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1610_ = v___x_1606_;
v_isShared_1611_ = v_isSharedCheck_1679_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_res_1608_);
lean_inc(v_pos_1607_);
lean_dec(v___x_1606_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1679_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
lean_inc(v_res_1608_);
v___x_1612_ = l_ByteSlice_toByteArray(v_res_1608_);
v___x_1613_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_1612_);
if (lean_obj_tag(v___x_1613_) == 1)
{
lean_object* v_val_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1674_; 
v_val_1614_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1616_ = v___x_1613_;
v_isShared_1617_ = v_isSharedCheck_1674_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_val_1614_);
lean_dec(v___x_1613_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1674_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v___x_1618_ = l_ByteSlice_size(v_res_1608_);
lean_dec(v_res_1608_);
v___x_1619_ = lean_nat_add(v_snd_1584_, v___x_1618_);
lean_dec(v___x_1618_);
lean_dec(v_snd_1584_);
v___x_1620_ = lean_nat_dec_lt(v_maxTotalPathLength_1603_, v___x_1619_);
if (v___x_1620_ == 0)
{
lean_object* v_array_1621_; lean_object* v_idx_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v_array_1621_ = lean_ctor_get(v_pos_1607_, 0);
v_idx_1622_ = lean_ctor_get(v_pos_1607_, 1);
v___x_1623_ = lean_array_push(v_fst_1583_, v_val_1614_);
v___x_1624_ = lean_byte_array_size(v_array_1621_);
v___x_1625_ = lean_nat_dec_lt(v_idx_1622_, v___x_1624_);
if (v___x_1625_ == 0)
{
lean_del_object(v___x_1616_);
lean_del_object(v___x_1610_);
lean_del_object(v___x_1586_);
lean_dec_ref(v_config_1554_);
v___y_1576_ = v___x_1619_;
v___y_1577_ = v___x_1623_;
v___y_1578_ = v_pos_1607_;
goto v___jp_1575_;
}
else
{
uint8_t v___x_1626_; uint8_t v___x_1627_; 
v___x_1626_ = lean_byte_array_fget(v_array_1621_, v_idx_1622_);
v___x_1627_ = lean_uint8_dec_eq(v___x_1626_, v___x_1600_);
if (v___x_1627_ == 0)
{
lean_del_object(v___x_1616_);
lean_del_object(v___x_1610_);
lean_del_object(v___x_1586_);
lean_dec_ref(v_config_1554_);
v___y_1576_ = v___x_1619_;
v___y_1577_ = v___x_1623_;
v___y_1578_ = v_pos_1607_;
goto v___jp_1575_;
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; uint8_t v___x_1630_; 
v___x_1628_ = lean_unsigned_to_nat(1u);
v___x_1629_ = lean_nat_add(v___x_1619_, v___x_1628_);
lean_dec(v___x_1619_);
v___x_1630_ = lean_nat_dec_lt(v_maxTotalPathLength_1603_, v___x_1629_);
if (v___x_1630_ == 0)
{
lean_del_object(v___x_1616_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1631_; lean_object* v___x_1633_; 
lean_dec(v___x_1629_);
lean_dec_ref(v___x_1623_);
lean_del_object(v___x_1586_);
lean_dec_ref(v_config_1554_);
v___x_1631_ = lean_box(0);
if (v_isShared_1611_ == 0)
{
lean_ctor_set_tag(v___x_1610_, 1);
lean_ctor_set(v___x_1610_, 1, v___x_1631_);
v___x_1633_ = v___x_1610_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_pos_1607_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v___x_1631_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
else
{
lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1649_; 
lean_inc(v_idx_1622_);
lean_inc_ref(v_array_1621_);
lean_del_object(v___x_1610_);
v_isSharedCheck_1649_ = !lean_is_exclusive(v_pos_1607_);
if (v_isSharedCheck_1649_ == 0)
{
lean_object* v_unused_1650_; lean_object* v_unused_1651_; 
v_unused_1650_ = lean_ctor_get(v_pos_1607_, 1);
lean_dec(v_unused_1650_);
v_unused_1651_ = lean_ctor_get(v_pos_1607_, 0);
lean_dec(v_unused_1651_);
v___x_1636_ = v_pos_1607_;
v_isShared_1637_ = v_isSharedCheck_1649_;
goto v_resetjp_1635_;
}
else
{
lean_dec(v_pos_1607_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1649_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1638_; lean_object* v___x_1640_; 
v___x_1638_ = lean_nat_add(v_idx_1622_, v___x_1628_);
lean_dec(v_idx_1622_);
lean_inc(v___x_1638_);
lean_inc_ref(v_array_1621_);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 1, v___x_1638_);
v___x_1640_ = v___x_1636_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_array_1621_);
lean_ctor_set(v_reuseFailAlloc_1648_, 1, v___x_1638_);
v___x_1640_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
uint8_t v___x_1641_; 
v___x_1641_ = lean_nat_dec_lt(v___x_1638_, v___x_1624_);
if (v___x_1641_ == 0)
{
lean_dec(v___x_1638_);
lean_dec_ref(v_array_1621_);
lean_del_object(v___x_1586_);
lean_inc(v_maxPathSegments_1602_);
v___y_1558_ = v_maxPathSegments_1602_;
v___y_1559_ = v___x_1640_;
v___y_1560_ = v___x_1623_;
v___y_1561_ = v___x_1629_;
goto v___jp_1557_;
}
else
{
uint8_t v___x_1642_; uint8_t v___x_1643_; 
v___x_1642_ = lean_byte_array_fget(v_array_1621_, v___x_1638_);
lean_dec(v___x_1638_);
lean_dec_ref(v_array_1621_);
v___x_1643_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1642_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1645_; 
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 1, v___x_1629_);
lean_ctor_set(v___x_1586_, 0, v___x_1623_);
v___x_1645_ = v___x_1586_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1623_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v___x_1629_);
v___x_1645_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
v_a_1555_ = v___x_1645_;
v___y_1556_ = v___x_1640_;
goto _start;
}
}
else
{
lean_del_object(v___x_1586_);
lean_inc(v_maxPathSegments_1602_);
v___y_1558_ = v_maxPathSegments_1602_;
v___y_1559_ = v___x_1640_;
v___y_1560_ = v___x_1623_;
v___y_1561_ = v___x_1629_;
goto v___jp_1557_;
}
}
}
}
}
}
else
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1658_; 
lean_inc(v_maxTotalPathLength_1603_);
lean_dec(v___x_1629_);
lean_dec_ref(v___x_1623_);
lean_del_object(v___x_1586_);
lean_dec_ref(v_config_1554_);
v___x_1652_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1653_ = l_Nat_reprFast(v_maxTotalPathLength_1603_);
v___x_1654_ = lean_string_append(v___x_1652_, v___x_1653_);
lean_dec_ref(v___x_1653_);
v___x_1655_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1656_ = lean_string_append(v___x_1654_, v___x_1655_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 0, v___x_1656_);
v___x_1658_ = v___x_1616_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1656_);
v___x_1658_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
lean_object* v___x_1660_; 
if (v_isShared_1611_ == 0)
{
lean_ctor_set_tag(v___x_1610_, 1);
lean_ctor_set(v___x_1610_, 1, v___x_1658_);
v___x_1660_ = v___x_1610_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_pos_1607_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v___x_1658_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
}
}
else
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1669_; 
lean_inc(v_maxTotalPathLength_1603_);
lean_dec(v___x_1619_);
lean_dec(v_val_1614_);
lean_del_object(v___x_1586_);
lean_dec(v_fst_1583_);
lean_dec_ref(v_config_1554_);
v___x_1663_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1664_ = l_Nat_reprFast(v_maxTotalPathLength_1603_);
v___x_1665_ = lean_string_append(v___x_1663_, v___x_1664_);
lean_dec_ref(v___x_1664_);
v___x_1666_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1667_ = lean_string_append(v___x_1665_, v___x_1666_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 0, v___x_1667_);
v___x_1669_ = v___x_1616_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1671_; 
if (v_isShared_1611_ == 0)
{
lean_ctor_set_tag(v___x_1610_, 1);
lean_ctor_set(v___x_1610_, 1, v___x_1669_);
v___x_1671_ = v___x_1610_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_pos_1607_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
}
else
{
lean_object* v___x_1675_; lean_object* v___x_1677_; 
lean_dec(v___x_1613_);
lean_dec(v_res_1608_);
lean_del_object(v___x_1586_);
lean_dec(v_snd_1584_);
lean_dec(v_fst_1583_);
lean_dec_ref(v_config_1554_);
v___x_1675_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5));
if (v_isShared_1611_ == 0)
{
lean_ctor_set_tag(v___x_1610_, 1);
lean_ctor_set(v___x_1610_, 1, v___x_1675_);
v___x_1677_ = v___x_1610_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_pos_1607_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
else
{
lean_object* v_pos_1680_; lean_object* v_err_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_del_object(v___x_1586_);
lean_dec(v_snd_1584_);
lean_dec(v_fst_1583_);
lean_dec_ref(v_config_1554_);
v_pos_1680_ = lean_ctor_get(v___x_1606_, 0);
v_err_1681_ = lean_ctor_get(v___x_1606_, 1);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1606_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_err_1681_);
lean_inc(v_pos_1680_);
lean_dec(v___x_1606_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_pos_1680_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_err_1681_);
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
else
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_inc(v_maxPathSegments_1602_);
lean_del_object(v___x_1586_);
lean_dec(v_snd_1584_);
lean_dec(v_fst_1583_);
lean_dec_ref(v_config_1554_);
v___x_1689_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1690_ = l_Nat_reprFast(v_maxPathSegments_1602_);
v___x_1691_ = lean_string_append(v___x_1689_, v___x_1690_);
lean_dec_ref(v___x_1690_);
v___x_1692_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1693_ = lean_string_append(v___x_1691_, v___x_1692_);
v___x_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1693_);
v___x_1695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___y_1556_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
return v___x_1695_;
}
}
v___jp_1696_:
{
if (v___y_1697_ == 0)
{
if (v___x_1589_ == 0)
{
goto v___jp_1601_;
}
else
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
lean_del_object(v___x_1586_);
lean_dec_ref(v_config_1554_);
v___x_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1698_, 0, v_fst_1583_);
lean_ctor_set(v___x_1698_, 1, v_snd_1584_);
v___x_1699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___y_1556_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
return v___x_1699_;
}
}
else
{
goto v___jp_1601_;
}
}
v___jp_1701_:
{
if (v___x_1700_ == 0)
{
v___y_1697_ = v___y_1702_;
goto v___jp_1696_;
}
else
{
v___y_1697_ = v___x_1700_;
goto v___jp_1696_;
}
}
v___jp_1703_:
{
if (v___y_1704_ == 0)
{
uint8_t v___x_1705_; uint8_t v___x_1706_; 
v___x_1705_ = 37;
v___x_1706_ = lean_uint8_dec_eq(v___x_1598_, v___x_1705_);
v___y_1702_ = v___x_1706_;
goto v___jp_1701_;
}
else
{
v___y_1702_ = v___y_1704_;
goto v___jp_1701_;
}
}
v___jp_1707_:
{
uint8_t v___x_1708_; uint8_t v___x_1709_; 
v___x_1708_ = 45;
v___x_1709_ = lean_uint8_dec_eq(v___x_1598_, v___x_1708_);
if (v___x_1709_ == 0)
{
uint8_t v___x_1710_; uint8_t v___x_1711_; 
v___x_1710_ = 46;
v___x_1711_ = lean_uint8_dec_eq(v___x_1598_, v___x_1710_);
if (v___x_1711_ == 0)
{
uint8_t v___x_1712_; uint8_t v___x_1713_; 
v___x_1712_ = 95;
v___x_1713_ = lean_uint8_dec_eq(v___x_1598_, v___x_1712_);
if (v___x_1713_ == 0)
{
uint8_t v___x_1714_; uint8_t v___x_1715_; 
v___x_1714_ = 126;
v___x_1715_ = lean_uint8_dec_eq(v___x_1598_, v___x_1714_);
if (v___x_1715_ == 0)
{
uint8_t v___x_1716_; uint8_t v___x_1717_; 
v___x_1716_ = 33;
v___x_1717_ = lean_uint8_dec_eq(v___x_1598_, v___x_1716_);
if (v___x_1717_ == 0)
{
uint8_t v___x_1718_; uint8_t v___x_1719_; 
v___x_1718_ = 36;
v___x_1719_ = lean_uint8_dec_eq(v___x_1598_, v___x_1718_);
if (v___x_1719_ == 0)
{
uint8_t v___x_1720_; uint8_t v___x_1721_; 
v___x_1720_ = 38;
v___x_1721_ = lean_uint8_dec_eq(v___x_1598_, v___x_1720_);
if (v___x_1721_ == 0)
{
uint8_t v___x_1722_; uint8_t v___x_1723_; 
v___x_1722_ = 39;
v___x_1723_ = lean_uint8_dec_eq(v___x_1598_, v___x_1722_);
if (v___x_1723_ == 0)
{
uint8_t v___x_1724_; uint8_t v___x_1725_; 
v___x_1724_ = 40;
v___x_1725_ = lean_uint8_dec_eq(v___x_1598_, v___x_1724_);
if (v___x_1725_ == 0)
{
uint8_t v___x_1726_; uint8_t v___x_1727_; 
v___x_1726_ = 41;
v___x_1727_ = lean_uint8_dec_eq(v___x_1598_, v___x_1726_);
if (v___x_1727_ == 0)
{
uint8_t v___x_1728_; uint8_t v___x_1729_; 
v___x_1728_ = 42;
v___x_1729_ = lean_uint8_dec_eq(v___x_1598_, v___x_1728_);
if (v___x_1729_ == 0)
{
uint8_t v___x_1730_; uint8_t v___x_1731_; 
v___x_1730_ = 43;
v___x_1731_ = lean_uint8_dec_eq(v___x_1598_, v___x_1730_);
if (v___x_1731_ == 0)
{
uint8_t v___x_1732_; uint8_t v___x_1733_; 
v___x_1732_ = 44;
v___x_1733_ = lean_uint8_dec_eq(v___x_1598_, v___x_1732_);
if (v___x_1733_ == 0)
{
uint8_t v___x_1734_; uint8_t v___x_1735_; 
v___x_1734_ = 59;
v___x_1735_ = lean_uint8_dec_eq(v___x_1598_, v___x_1734_);
if (v___x_1735_ == 0)
{
uint8_t v___x_1736_; uint8_t v___x_1737_; 
v___x_1736_ = 61;
v___x_1737_ = lean_uint8_dec_eq(v___x_1598_, v___x_1736_);
if (v___x_1737_ == 0)
{
uint8_t v___x_1738_; uint8_t v___x_1739_; 
v___x_1738_ = 58;
v___x_1739_ = lean_uint8_dec_eq(v___x_1598_, v___x_1738_);
if (v___x_1739_ == 0)
{
uint8_t v___x_1740_; uint8_t v___x_1741_; 
v___x_1740_ = 64;
v___x_1741_ = lean_uint8_dec_eq(v___x_1598_, v___x_1740_);
v___y_1704_ = v___x_1741_;
goto v___jp_1703_;
}
else
{
v___y_1704_ = v___x_1739_;
goto v___jp_1703_;
}
}
else
{
v___y_1704_ = v___x_1737_;
goto v___jp_1703_;
}
}
else
{
v___y_1704_ = v___x_1735_;
goto v___jp_1703_;
}
}
else
{
v___y_1704_ = v___x_1733_;
goto v___jp_1703_;
}
}
else
{
v___y_1704_ = v___x_1731_;
goto v___jp_1703_;
}
}
else
{
v___y_1704_ = v___x_1729_;
goto v___jp_1703_;
}
}
else
{
v___y_1704_ = v___x_1727_;
goto v___jp_1703_;
}
}
else
{
v___y_1704_ = v___x_1725_;
goto v___jp_1703_;
}
}
else
{
v___y_1704_ = v___x_1723_;
goto v___jp_1703_;
}
}
else
{
v___y_1704_ = v___x_1721_;
goto v___jp_1703_;
}
}
else
{
v___y_1704_ = v___x_1719_;
goto v___jp_1703_;
}
}
else
{
v___y_1704_ = v___x_1717_;
goto v___jp_1703_;
}
}
else
{
v___y_1704_ = v___x_1715_;
goto v___jp_1703_;
}
}
else
{
v___y_1704_ = v___x_1713_;
goto v___jp_1703_;
}
}
else
{
v___y_1704_ = v___x_1711_;
goto v___jp_1703_;
}
}
else
{
v___y_1704_ = v___x_1709_;
goto v___jp_1703_;
}
}
v___jp_1742_:
{
uint8_t v___x_1743_; uint8_t v___x_1744_; 
v___x_1743_ = 65;
v___x_1744_ = lean_uint8_dec_le(v___x_1743_, v___x_1598_);
if (v___x_1744_ == 0)
{
goto v___jp_1707_;
}
else
{
uint8_t v___x_1745_; uint8_t v___x_1746_; 
v___x_1745_ = 90;
v___x_1746_ = lean_uint8_dec_le(v___x_1598_, v___x_1745_);
if (v___x_1746_ == 0)
{
goto v___jp_1707_;
}
else
{
v___y_1704_ = v___x_1746_;
goto v___jp_1703_;
}
}
}
v___jp_1747_:
{
uint8_t v___x_1748_; uint8_t v___x_1749_; 
v___x_1748_ = 97;
v___x_1749_ = lean_uint8_dec_le(v___x_1748_, v___x_1598_);
if (v___x_1749_ == 0)
{
goto v___jp_1742_;
}
else
{
uint8_t v___x_1750_; uint8_t v___x_1751_; 
v___x_1750_ = 122;
v___x_1751_ = lean_uint8_dec_le(v___x_1598_, v___x_1750_);
if (v___x_1751_ == 0)
{
goto v___jp_1742_;
}
else
{
v___y_1704_ = v___x_1751_;
goto v___jp_1703_;
}
}
}
}
else
{
lean_object* v___x_1757_; 
lean_dec_ref(v_config_1554_);
if (v_isShared_1587_ == 0)
{
v___x_1757_ = v___x_1586_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_fst_1583_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_snd_1584_);
v___x_1757_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v___x_1758_; 
v___x_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___y_1556_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
return v___x_1758_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(lean_object* v_config_1761_, lean_object* v_a_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v_array_1788_; lean_object* v_idx_1789_; lean_object* v_fst_1790_; lean_object* v_snd_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1967_; 
v_array_1788_ = lean_ctor_get(v___y_1763_, 0);
v_idx_1789_ = lean_ctor_get(v___y_1763_, 1);
v_fst_1790_ = lean_ctor_get(v_a_1762_, 0);
v_snd_1791_ = lean_ctor_get(v_a_1762_, 1);
v_isSharedCheck_1967_ = !lean_is_exclusive(v_a_1762_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1793_ = v_a_1762_;
v_isShared_1794_ = v_isSharedCheck_1967_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_snd_1791_);
lean_inc(v_fst_1790_);
lean_dec(v_a_1762_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1967_;
goto v_resetjp_1792_;
}
v___jp_1764_:
{
lean_object* v___x_1769_; uint8_t v___x_1770_; 
v___x_1769_ = lean_array_get_size(v___y_1767_);
v___x_1770_ = lean_nat_dec_le(v___y_1766_, v___x_1769_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
lean_dec(v___y_1766_);
v___x_1771_ = l_ByteArray_empty;
v___x_1772_ = lean_array_push(v___y_1767_, v___x_1771_);
v___x_1773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
lean_ctor_set(v___x_1773_, 1, v___y_1768_);
v___x_1774_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_1761_, v___x_1773_, v___y_1765_);
return v___x_1774_;
}
else
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec_ref(v_config_1761_);
v___x_1775_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1776_ = l_Nat_reprFast(v___y_1766_);
v___x_1777_ = lean_string_append(v___x_1775_, v___x_1776_);
lean_dec_ref(v___x_1776_);
v___x_1778_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1779_ = lean_string_append(v___x_1777_, v___x_1778_);
v___x_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1779_);
v___x_1781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___y_1765_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
return v___x_1781_;
}
}
v___jp_1782_:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___y_1783_);
lean_ctor_set(v___x_1786_, 1, v___y_1784_);
v___x_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___y_1785_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
return v___x_1787_;
}
v_resetjp_1792_:
{
lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1795_ = lean_byte_array_size(v_array_1788_);
v___x_1796_ = lean_nat_dec_lt(v_idx_1789_, v___x_1795_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1798_; 
lean_dec_ref(v_config_1761_);
if (v_isShared_1794_ == 0)
{
v___x_1798_ = v___x_1793_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_fst_1790_);
lean_ctor_set(v_reuseFailAlloc_1800_, 1, v_snd_1791_);
v___x_1798_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
lean_object* v___x_1799_; 
v___x_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___y_1763_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
return v___x_1799_;
}
}
else
{
if (v___x_1796_ == 0)
{
lean_object* v___x_1802_; 
lean_dec_ref(v_config_1761_);
if (v_isShared_1794_ == 0)
{
v___x_1802_ = v___x_1793_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_fst_1790_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v_snd_1791_);
v___x_1802_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1803_; 
v___x_1803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___y_1763_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
return v___x_1803_;
}
}
else
{
uint8_t v___x_1805_; uint8_t v___x_1806_; 
v___x_1805_ = lean_byte_array_fget(v_array_1788_, v_idx_1789_);
v___x_1806_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1805_);
if (v___x_1806_ == 0)
{
uint8_t v___x_1807_; uint8_t v___y_1904_; uint8_t v___x_1907_; uint8_t v___y_1909_; uint8_t v___y_1911_; uint8_t v___x_1959_; uint8_t v___x_1960_; 
v___x_1807_ = 47;
v___x_1907_ = lean_uint8_dec_eq(v___x_1805_, v___x_1807_);
v___x_1959_ = 48;
v___x_1960_ = lean_uint8_dec_le(v___x_1959_, v___x_1805_);
if (v___x_1960_ == 0)
{
goto v___jp_1954_;
}
else
{
uint8_t v___x_1961_; uint8_t v___x_1962_; 
v___x_1961_ = 57;
v___x_1962_ = lean_uint8_dec_le(v___x_1805_, v___x_1961_);
if (v___x_1962_ == 0)
{
goto v___jp_1954_;
}
else
{
v___y_1911_ = v___x_1962_;
goto v___jp_1910_;
}
}
v___jp_1808_:
{
lean_object* v_maxPathSegments_1809_; lean_object* v_maxTotalPathLength_1810_; lean_object* v___x_1811_; uint8_t v___x_1812_; 
v_maxPathSegments_1809_ = lean_ctor_get(v_config_1761_, 6);
v_maxTotalPathLength_1810_ = lean_ctor_get(v_config_1761_, 7);
v___x_1811_ = lean_array_get_size(v_fst_1790_);
v___x_1812_ = lean_nat_dec_le(v_maxPathSegments_1809_, v___x_1811_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; 
v___x_1813_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1761_, v___y_1763_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_pos_1814_; lean_object* v_res_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1886_; 
v_pos_1814_ = lean_ctor_get(v___x_1813_, 0);
v_res_1815_ = lean_ctor_get(v___x_1813_, 1);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1817_ = v___x_1813_;
v_isShared_1818_ = v_isSharedCheck_1886_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_res_1815_);
lean_inc(v_pos_1814_);
lean_dec(v___x_1813_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1886_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
lean_inc(v_res_1815_);
v___x_1819_ = l_ByteSlice_toByteArray(v_res_1815_);
v___x_1820_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_1819_);
if (lean_obj_tag(v___x_1820_) == 1)
{
lean_object* v_val_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1881_; 
v_val_1821_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1823_ = v___x_1820_;
v_isShared_1824_ = v_isSharedCheck_1881_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_val_1821_);
lean_dec(v___x_1820_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1881_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; 
v___x_1825_ = l_ByteSlice_size(v_res_1815_);
lean_dec(v_res_1815_);
v___x_1826_ = lean_nat_add(v_snd_1791_, v___x_1825_);
lean_dec(v___x_1825_);
lean_dec(v_snd_1791_);
v___x_1827_ = lean_nat_dec_lt(v_maxTotalPathLength_1810_, v___x_1826_);
if (v___x_1827_ == 0)
{
lean_object* v_array_1828_; lean_object* v_idx_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; uint8_t v___x_1832_; 
v_array_1828_ = lean_ctor_get(v_pos_1814_, 0);
v_idx_1829_ = lean_ctor_get(v_pos_1814_, 1);
v___x_1830_ = lean_array_push(v_fst_1790_, v_val_1821_);
v___x_1831_ = lean_byte_array_size(v_array_1828_);
v___x_1832_ = lean_nat_dec_lt(v_idx_1829_, v___x_1831_);
if (v___x_1832_ == 0)
{
lean_del_object(v___x_1823_);
lean_del_object(v___x_1817_);
lean_del_object(v___x_1793_);
lean_dec_ref(v_config_1761_);
v___y_1783_ = v___x_1830_;
v___y_1784_ = v___x_1826_;
v___y_1785_ = v_pos_1814_;
goto v___jp_1782_;
}
else
{
uint8_t v___x_1833_; uint8_t v___x_1834_; 
v___x_1833_ = lean_byte_array_fget(v_array_1828_, v_idx_1829_);
v___x_1834_ = lean_uint8_dec_eq(v___x_1833_, v___x_1807_);
if (v___x_1834_ == 0)
{
lean_del_object(v___x_1823_);
lean_del_object(v___x_1817_);
lean_del_object(v___x_1793_);
lean_dec_ref(v_config_1761_);
v___y_1783_ = v___x_1830_;
v___y_1784_ = v___x_1826_;
v___y_1785_ = v_pos_1814_;
goto v___jp_1782_;
}
else
{
lean_object* v___x_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
v___x_1835_ = lean_unsigned_to_nat(1u);
v___x_1836_ = lean_nat_add(v___x_1826_, v___x_1835_);
lean_dec(v___x_1826_);
v___x_1837_ = lean_nat_dec_lt(v_maxTotalPathLength_1810_, v___x_1836_);
if (v___x_1837_ == 0)
{
lean_del_object(v___x_1823_);
if (v___x_1832_ == 0)
{
lean_object* v___x_1838_; lean_object* v___x_1840_; 
lean_dec(v___x_1836_);
lean_dec_ref(v___x_1830_);
lean_del_object(v___x_1793_);
lean_dec_ref(v_config_1761_);
v___x_1838_ = lean_box(0);
if (v_isShared_1818_ == 0)
{
lean_ctor_set_tag(v___x_1817_, 1);
lean_ctor_set(v___x_1817_, 1, v___x_1838_);
v___x_1840_ = v___x_1817_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_pos_1814_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
else
{
lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1856_; 
lean_inc(v_idx_1829_);
lean_inc_ref(v_array_1828_);
lean_del_object(v___x_1817_);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_pos_1814_);
if (v_isSharedCheck_1856_ == 0)
{
lean_object* v_unused_1857_; lean_object* v_unused_1858_; 
v_unused_1857_ = lean_ctor_get(v_pos_1814_, 1);
lean_dec(v_unused_1857_);
v_unused_1858_ = lean_ctor_get(v_pos_1814_, 0);
lean_dec(v_unused_1858_);
v___x_1843_ = v_pos_1814_;
v_isShared_1844_ = v_isSharedCheck_1856_;
goto v_resetjp_1842_;
}
else
{
lean_dec(v_pos_1814_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1856_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1845_; lean_object* v___x_1847_; 
v___x_1845_ = lean_nat_add(v_idx_1829_, v___x_1835_);
lean_dec(v_idx_1829_);
lean_inc(v___x_1845_);
lean_inc_ref(v_array_1828_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 1, v___x_1845_);
v___x_1847_ = v___x_1843_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_array_1828_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v___x_1845_);
v___x_1847_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
uint8_t v___x_1848_; 
v___x_1848_ = lean_nat_dec_lt(v___x_1845_, v___x_1831_);
if (v___x_1848_ == 0)
{
lean_dec(v___x_1845_);
lean_dec_ref(v_array_1828_);
lean_del_object(v___x_1793_);
lean_inc(v_maxPathSegments_1809_);
v___y_1765_ = v___x_1847_;
v___y_1766_ = v_maxPathSegments_1809_;
v___y_1767_ = v___x_1830_;
v___y_1768_ = v___x_1836_;
goto v___jp_1764_;
}
else
{
uint8_t v___x_1849_; uint8_t v___x_1850_; 
v___x_1849_ = lean_byte_array_fget(v_array_1828_, v___x_1845_);
lean_dec(v___x_1845_);
lean_dec_ref(v_array_1828_);
v___x_1850_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1849_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1852_; 
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 1, v___x_1836_);
lean_ctor_set(v___x_1793_, 0, v___x_1830_);
v___x_1852_ = v___x_1793_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1830_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v___x_1836_);
v___x_1852_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
lean_object* v___x_1853_; 
v___x_1853_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_1761_, v___x_1852_, v___x_1847_);
return v___x_1853_;
}
}
else
{
lean_del_object(v___x_1793_);
lean_inc(v_maxPathSegments_1809_);
v___y_1765_ = v___x_1847_;
v___y_1766_ = v_maxPathSegments_1809_;
v___y_1767_ = v___x_1830_;
v___y_1768_ = v___x_1836_;
goto v___jp_1764_;
}
}
}
}
}
}
else
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1865_; 
lean_inc(v_maxTotalPathLength_1810_);
lean_dec(v___x_1836_);
lean_dec_ref(v___x_1830_);
lean_del_object(v___x_1793_);
lean_dec_ref(v_config_1761_);
v___x_1859_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1860_ = l_Nat_reprFast(v_maxTotalPathLength_1810_);
v___x_1861_ = lean_string_append(v___x_1859_, v___x_1860_);
lean_dec_ref(v___x_1860_);
v___x_1862_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1863_ = lean_string_append(v___x_1861_, v___x_1862_);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 0, v___x_1863_);
v___x_1865_ = v___x_1823_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
lean_object* v___x_1867_; 
if (v_isShared_1818_ == 0)
{
lean_ctor_set_tag(v___x_1817_, 1);
lean_ctor_set(v___x_1817_, 1, v___x_1865_);
v___x_1867_ = v___x_1817_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_pos_1814_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
}
}
else
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1876_; 
lean_inc(v_maxTotalPathLength_1810_);
lean_dec(v___x_1826_);
lean_dec(v_val_1821_);
lean_del_object(v___x_1793_);
lean_dec(v_fst_1790_);
lean_dec_ref(v_config_1761_);
v___x_1870_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1871_ = l_Nat_reprFast(v_maxTotalPathLength_1810_);
v___x_1872_ = lean_string_append(v___x_1870_, v___x_1871_);
lean_dec_ref(v___x_1871_);
v___x_1873_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1874_ = lean_string_append(v___x_1872_, v___x_1873_);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 0, v___x_1874_);
v___x_1876_ = v___x_1823_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
lean_object* v___x_1878_; 
if (v_isShared_1818_ == 0)
{
lean_ctor_set_tag(v___x_1817_, 1);
lean_ctor_set(v___x_1817_, 1, v___x_1876_);
v___x_1878_ = v___x_1817_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_pos_1814_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
}
else
{
lean_object* v___x_1882_; lean_object* v___x_1884_; 
lean_dec(v___x_1820_);
lean_dec(v_res_1815_);
lean_del_object(v___x_1793_);
lean_dec(v_snd_1791_);
lean_dec(v_fst_1790_);
lean_dec_ref(v_config_1761_);
v___x_1882_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5));
if (v_isShared_1818_ == 0)
{
lean_ctor_set_tag(v___x_1817_, 1);
lean_ctor_set(v___x_1817_, 1, v___x_1882_);
v___x_1884_ = v___x_1817_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_pos_1814_);
lean_ctor_set(v_reuseFailAlloc_1885_, 1, v___x_1882_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
else
{
lean_object* v_pos_1887_; lean_object* v_err_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_del_object(v___x_1793_);
lean_dec(v_snd_1791_);
lean_dec(v_fst_1790_);
lean_dec_ref(v_config_1761_);
v_pos_1887_ = lean_ctor_get(v___x_1813_, 0);
v_err_1888_ = lean_ctor_get(v___x_1813_, 1);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1813_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_err_1888_);
lean_inc(v_pos_1887_);
lean_dec(v___x_1813_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_pos_1887_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_err_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
lean_inc(v_maxPathSegments_1809_);
lean_del_object(v___x_1793_);
lean_dec(v_snd_1791_);
lean_dec(v_fst_1790_);
lean_dec_ref(v_config_1761_);
v___x_1896_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1897_ = l_Nat_reprFast(v_maxPathSegments_1809_);
v___x_1898_ = lean_string_append(v___x_1896_, v___x_1897_);
lean_dec_ref(v___x_1897_);
v___x_1899_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1900_ = lean_string_append(v___x_1898_, v___x_1899_);
v___x_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
v___x_1902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___y_1763_);
lean_ctor_set(v___x_1902_, 1, v___x_1901_);
return v___x_1902_;
}
}
v___jp_1903_:
{
if (v___y_1904_ == 0)
{
if (v___x_1796_ == 0)
{
goto v___jp_1808_;
}
else
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
lean_del_object(v___x_1793_);
lean_dec_ref(v_config_1761_);
v___x_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1905_, 0, v_fst_1790_);
lean_ctor_set(v___x_1905_, 1, v_snd_1791_);
v___x_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___y_1763_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
return v___x_1906_;
}
}
else
{
goto v___jp_1808_;
}
}
v___jp_1908_:
{
if (v___x_1907_ == 0)
{
v___y_1904_ = v___y_1909_;
goto v___jp_1903_;
}
else
{
v___y_1904_ = v___x_1907_;
goto v___jp_1903_;
}
}
v___jp_1910_:
{
if (v___y_1911_ == 0)
{
uint8_t v___x_1912_; uint8_t v___x_1913_; 
v___x_1912_ = 37;
v___x_1913_ = lean_uint8_dec_eq(v___x_1805_, v___x_1912_);
v___y_1909_ = v___x_1913_;
goto v___jp_1908_;
}
else
{
v___y_1909_ = v___y_1911_;
goto v___jp_1908_;
}
}
v___jp_1914_:
{
uint8_t v___x_1915_; uint8_t v___x_1916_; 
v___x_1915_ = 45;
v___x_1916_ = lean_uint8_dec_eq(v___x_1805_, v___x_1915_);
if (v___x_1916_ == 0)
{
uint8_t v___x_1917_; uint8_t v___x_1918_; 
v___x_1917_ = 46;
v___x_1918_ = lean_uint8_dec_eq(v___x_1805_, v___x_1917_);
if (v___x_1918_ == 0)
{
uint8_t v___x_1919_; uint8_t v___x_1920_; 
v___x_1919_ = 95;
v___x_1920_ = lean_uint8_dec_eq(v___x_1805_, v___x_1919_);
if (v___x_1920_ == 0)
{
uint8_t v___x_1921_; uint8_t v___x_1922_; 
v___x_1921_ = 126;
v___x_1922_ = lean_uint8_dec_eq(v___x_1805_, v___x_1921_);
if (v___x_1922_ == 0)
{
uint8_t v___x_1923_; uint8_t v___x_1924_; 
v___x_1923_ = 33;
v___x_1924_ = lean_uint8_dec_eq(v___x_1805_, v___x_1923_);
if (v___x_1924_ == 0)
{
uint8_t v___x_1925_; uint8_t v___x_1926_; 
v___x_1925_ = 36;
v___x_1926_ = lean_uint8_dec_eq(v___x_1805_, v___x_1925_);
if (v___x_1926_ == 0)
{
uint8_t v___x_1927_; uint8_t v___x_1928_; 
v___x_1927_ = 38;
v___x_1928_ = lean_uint8_dec_eq(v___x_1805_, v___x_1927_);
if (v___x_1928_ == 0)
{
uint8_t v___x_1929_; uint8_t v___x_1930_; 
v___x_1929_ = 39;
v___x_1930_ = lean_uint8_dec_eq(v___x_1805_, v___x_1929_);
if (v___x_1930_ == 0)
{
uint8_t v___x_1931_; uint8_t v___x_1932_; 
v___x_1931_ = 40;
v___x_1932_ = lean_uint8_dec_eq(v___x_1805_, v___x_1931_);
if (v___x_1932_ == 0)
{
uint8_t v___x_1933_; uint8_t v___x_1934_; 
v___x_1933_ = 41;
v___x_1934_ = lean_uint8_dec_eq(v___x_1805_, v___x_1933_);
if (v___x_1934_ == 0)
{
uint8_t v___x_1935_; uint8_t v___x_1936_; 
v___x_1935_ = 42;
v___x_1936_ = lean_uint8_dec_eq(v___x_1805_, v___x_1935_);
if (v___x_1936_ == 0)
{
uint8_t v___x_1937_; uint8_t v___x_1938_; 
v___x_1937_ = 43;
v___x_1938_ = lean_uint8_dec_eq(v___x_1805_, v___x_1937_);
if (v___x_1938_ == 0)
{
uint8_t v___x_1939_; uint8_t v___x_1940_; 
v___x_1939_ = 44;
v___x_1940_ = lean_uint8_dec_eq(v___x_1805_, v___x_1939_);
if (v___x_1940_ == 0)
{
uint8_t v___x_1941_; uint8_t v___x_1942_; 
v___x_1941_ = 59;
v___x_1942_ = lean_uint8_dec_eq(v___x_1805_, v___x_1941_);
if (v___x_1942_ == 0)
{
uint8_t v___x_1943_; uint8_t v___x_1944_; 
v___x_1943_ = 61;
v___x_1944_ = lean_uint8_dec_eq(v___x_1805_, v___x_1943_);
if (v___x_1944_ == 0)
{
uint8_t v___x_1945_; uint8_t v___x_1946_; 
v___x_1945_ = 58;
v___x_1946_ = lean_uint8_dec_eq(v___x_1805_, v___x_1945_);
if (v___x_1946_ == 0)
{
uint8_t v___x_1947_; uint8_t v___x_1948_; 
v___x_1947_ = 64;
v___x_1948_ = lean_uint8_dec_eq(v___x_1805_, v___x_1947_);
v___y_1911_ = v___x_1948_;
goto v___jp_1910_;
}
else
{
v___y_1911_ = v___x_1946_;
goto v___jp_1910_;
}
}
else
{
v___y_1911_ = v___x_1944_;
goto v___jp_1910_;
}
}
else
{
v___y_1911_ = v___x_1942_;
goto v___jp_1910_;
}
}
else
{
v___y_1911_ = v___x_1940_;
goto v___jp_1910_;
}
}
else
{
v___y_1911_ = v___x_1938_;
goto v___jp_1910_;
}
}
else
{
v___y_1911_ = v___x_1936_;
goto v___jp_1910_;
}
}
else
{
v___y_1911_ = v___x_1934_;
goto v___jp_1910_;
}
}
else
{
v___y_1911_ = v___x_1932_;
goto v___jp_1910_;
}
}
else
{
v___y_1911_ = v___x_1930_;
goto v___jp_1910_;
}
}
else
{
v___y_1911_ = v___x_1928_;
goto v___jp_1910_;
}
}
else
{
v___y_1911_ = v___x_1926_;
goto v___jp_1910_;
}
}
else
{
v___y_1911_ = v___x_1924_;
goto v___jp_1910_;
}
}
else
{
v___y_1911_ = v___x_1922_;
goto v___jp_1910_;
}
}
else
{
v___y_1911_ = v___x_1920_;
goto v___jp_1910_;
}
}
else
{
v___y_1911_ = v___x_1918_;
goto v___jp_1910_;
}
}
else
{
v___y_1911_ = v___x_1916_;
goto v___jp_1910_;
}
}
v___jp_1949_:
{
uint8_t v___x_1950_; uint8_t v___x_1951_; 
v___x_1950_ = 65;
v___x_1951_ = lean_uint8_dec_le(v___x_1950_, v___x_1805_);
if (v___x_1951_ == 0)
{
goto v___jp_1914_;
}
else
{
uint8_t v___x_1952_; uint8_t v___x_1953_; 
v___x_1952_ = 90;
v___x_1953_ = lean_uint8_dec_le(v___x_1805_, v___x_1952_);
if (v___x_1953_ == 0)
{
goto v___jp_1914_;
}
else
{
v___y_1911_ = v___x_1953_;
goto v___jp_1910_;
}
}
}
v___jp_1954_:
{
uint8_t v___x_1955_; uint8_t v___x_1956_; 
v___x_1955_ = 97;
v___x_1956_ = lean_uint8_dec_le(v___x_1955_, v___x_1805_);
if (v___x_1956_ == 0)
{
goto v___jp_1949_;
}
else
{
uint8_t v___x_1957_; uint8_t v___x_1958_; 
v___x_1957_ = 122;
v___x_1958_ = lean_uint8_dec_le(v___x_1805_, v___x_1957_);
if (v___x_1958_ == 0)
{
goto v___jp_1949_;
}
else
{
v___y_1911_ = v___x_1958_;
goto v___jp_1910_;
}
}
}
}
else
{
lean_object* v___x_1964_; 
lean_dec_ref(v_config_1761_);
if (v_isShared_1794_ == 0)
{
v___x_1964_ = v___x_1793_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_fst_1790_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v_snd_1791_);
v___x_1964_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
lean_object* v___x_1965_; 
v___x_1965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___y_1763_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
return v___x_1965_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath(lean_object* v_config_1979_, uint8_t v_forceAbsolute_1980_, uint8_t v_allowEmpty_1981_, lean_object* v_a_1982_){
_start:
{
lean_object* v___y_1984_; lean_object* v_array_1987_; lean_object* v_idx_1988_; uint8_t v_isAbsolute_1989_; lean_object* v___x_1990_; lean_object* v_segments_1991_; uint8_t v_isAbsolute_1993_; lean_object* v_totalLength_1994_; lean_object* v___y_1995_; lean_object* v___y_2019_; uint8_t v___y_2020_; uint8_t v___y_2024_; lean_object* v___y_2025_; uint8_t v___y_2026_; uint8_t v___y_2028_; lean_object* v_pos_2029_; uint8_t v_res_2030_; uint8_t v___y_2033_; lean_object* v_pos_2034_; uint8_t v_res_2035_; uint8_t v___y_2041_; lean_object* v___y_2042_; uint8_t v___y_2043_; uint8_t v___y_2065_; uint8_t v___y_2066_; lean_object* v___y_2067_; uint8_t v___y_2068_; uint8_t v___y_2072_; uint8_t v___y_2073_; uint8_t v___y_2074_; lean_object* v___y_2075_; uint8_t v___y_2076_; uint8_t v___y_2078_; uint8_t v___y_2079_; lean_object* v___y_2080_; uint8_t v___y_2081_; uint8_t v___y_2084_; lean_object* v_pos_2085_; uint8_t v_res_2086_; lean_object* v_pos_2089_; lean_object* v_array_2090_; lean_object* v_idx_2091_; uint8_t v_res_2092_; uint8_t v___y_2097_; uint8_t v___y_2098_; lean_object* v___x_2099_; uint8_t v___x_2100_; 
v_array_1987_ = lean_ctor_get(v_a_1982_, 0);
lean_inc_ref(v_array_1987_);
v_idx_1988_ = lean_ctor_get(v_a_1982_, 1);
lean_inc(v_idx_1988_);
v_isAbsolute_1989_ = 0;
v___x_1990_ = lean_unsigned_to_nat(0u);
v_segments_1991_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__2));
v___x_2099_ = lean_byte_array_size(v_array_1987_);
v___x_2100_ = lean_nat_dec_lt(v_idx_1988_, v___x_2099_);
if (v___x_2100_ == 0)
{
v_pos_2089_ = v_a_1982_;
v_array_2090_ = v_array_1987_;
v_idx_2091_ = v_idx_1988_;
v_res_2092_ = v_isAbsolute_1989_;
goto v___jp_2088_;
}
else
{
uint8_t v___x_2101_; uint8_t v___y_2103_; uint8_t v___x_2153_; uint8_t v___x_2154_; 
v___x_2101_ = lean_byte_array_fget(v_array_1987_, v_idx_1988_);
v___x_2153_ = 48;
v___x_2154_ = lean_uint8_dec_le(v___x_2153_, v___x_2101_);
if (v___x_2154_ == 0)
{
goto v___jp_2148_;
}
else
{
uint8_t v___x_2155_; uint8_t v___x_2156_; 
v___x_2155_ = 57;
v___x_2156_ = lean_uint8_dec_le(v___x_2101_, v___x_2155_);
if (v___x_2156_ == 0)
{
goto v___jp_2148_;
}
else
{
v___y_2103_ = v___x_2156_;
goto v___jp_2102_;
}
}
v___jp_2102_:
{
uint8_t v___x_2104_; uint8_t v___x_2105_; 
v___x_2104_ = 37;
v___x_2105_ = lean_uint8_dec_eq(v___x_2101_, v___x_2104_);
if (v___x_2105_ == 0)
{
uint8_t v___x_2106_; uint8_t v___x_2107_; 
v___x_2106_ = 47;
v___x_2107_ = lean_uint8_dec_eq(v___x_2101_, v___x_2106_);
v___y_2097_ = v___y_2103_;
v___y_2098_ = v___x_2107_;
goto v___jp_2096_;
}
else
{
v___y_2097_ = v___y_2103_;
v___y_2098_ = v___x_2105_;
goto v___jp_2096_;
}
}
v___jp_2108_:
{
uint8_t v___x_2109_; uint8_t v___x_2110_; 
v___x_2109_ = 45;
v___x_2110_ = lean_uint8_dec_eq(v___x_2101_, v___x_2109_);
if (v___x_2110_ == 0)
{
uint8_t v___x_2111_; uint8_t v___x_2112_; 
v___x_2111_ = 46;
v___x_2112_ = lean_uint8_dec_eq(v___x_2101_, v___x_2111_);
if (v___x_2112_ == 0)
{
uint8_t v___x_2113_; uint8_t v___x_2114_; 
v___x_2113_ = 95;
v___x_2114_ = lean_uint8_dec_eq(v___x_2101_, v___x_2113_);
if (v___x_2114_ == 0)
{
uint8_t v___x_2115_; uint8_t v___x_2116_; 
v___x_2115_ = 126;
v___x_2116_ = lean_uint8_dec_eq(v___x_2101_, v___x_2115_);
if (v___x_2116_ == 0)
{
uint8_t v___x_2117_; uint8_t v___x_2118_; 
v___x_2117_ = 33;
v___x_2118_ = lean_uint8_dec_eq(v___x_2101_, v___x_2117_);
if (v___x_2118_ == 0)
{
uint8_t v___x_2119_; uint8_t v___x_2120_; 
v___x_2119_ = 36;
v___x_2120_ = lean_uint8_dec_eq(v___x_2101_, v___x_2119_);
if (v___x_2120_ == 0)
{
uint8_t v___x_2121_; uint8_t v___x_2122_; 
v___x_2121_ = 38;
v___x_2122_ = lean_uint8_dec_eq(v___x_2101_, v___x_2121_);
if (v___x_2122_ == 0)
{
uint8_t v___x_2123_; uint8_t v___x_2124_; 
v___x_2123_ = 39;
v___x_2124_ = lean_uint8_dec_eq(v___x_2101_, v___x_2123_);
if (v___x_2124_ == 0)
{
uint8_t v___x_2125_; uint8_t v___x_2126_; 
v___x_2125_ = 40;
v___x_2126_ = lean_uint8_dec_eq(v___x_2101_, v___x_2125_);
if (v___x_2126_ == 0)
{
uint8_t v___x_2127_; uint8_t v___x_2128_; 
v___x_2127_ = 41;
v___x_2128_ = lean_uint8_dec_eq(v___x_2101_, v___x_2127_);
if (v___x_2128_ == 0)
{
uint8_t v___x_2129_; uint8_t v___x_2130_; 
v___x_2129_ = 42;
v___x_2130_ = lean_uint8_dec_eq(v___x_2101_, v___x_2129_);
if (v___x_2130_ == 0)
{
uint8_t v___x_2131_; uint8_t v___x_2132_; 
v___x_2131_ = 43;
v___x_2132_ = lean_uint8_dec_eq(v___x_2101_, v___x_2131_);
if (v___x_2132_ == 0)
{
uint8_t v___x_2133_; uint8_t v___x_2134_; 
v___x_2133_ = 44;
v___x_2134_ = lean_uint8_dec_eq(v___x_2101_, v___x_2133_);
if (v___x_2134_ == 0)
{
uint8_t v___x_2135_; uint8_t v___x_2136_; 
v___x_2135_ = 59;
v___x_2136_ = lean_uint8_dec_eq(v___x_2101_, v___x_2135_);
if (v___x_2136_ == 0)
{
uint8_t v___x_2137_; uint8_t v___x_2138_; 
v___x_2137_ = 61;
v___x_2138_ = lean_uint8_dec_eq(v___x_2101_, v___x_2137_);
if (v___x_2138_ == 0)
{
uint8_t v___x_2139_; uint8_t v___x_2140_; 
v___x_2139_ = 58;
v___x_2140_ = lean_uint8_dec_eq(v___x_2101_, v___x_2139_);
if (v___x_2140_ == 0)
{
uint8_t v___x_2141_; uint8_t v___x_2142_; 
v___x_2141_ = 64;
v___x_2142_ = lean_uint8_dec_eq(v___x_2101_, v___x_2141_);
v___y_2103_ = v___x_2142_;
goto v___jp_2102_;
}
else
{
v___y_2103_ = v___x_2140_;
goto v___jp_2102_;
}
}
else
{
v___y_2103_ = v___x_2138_;
goto v___jp_2102_;
}
}
else
{
v___y_2103_ = v___x_2136_;
goto v___jp_2102_;
}
}
else
{
v___y_2103_ = v___x_2134_;
goto v___jp_2102_;
}
}
else
{
v___y_2103_ = v___x_2132_;
goto v___jp_2102_;
}
}
else
{
v___y_2103_ = v___x_2130_;
goto v___jp_2102_;
}
}
else
{
v___y_2103_ = v___x_2128_;
goto v___jp_2102_;
}
}
else
{
v___y_2103_ = v___x_2126_;
goto v___jp_2102_;
}
}
else
{
v___y_2103_ = v___x_2124_;
goto v___jp_2102_;
}
}
else
{
v___y_2103_ = v___x_2122_;
goto v___jp_2102_;
}
}
else
{
v___y_2103_ = v___x_2120_;
goto v___jp_2102_;
}
}
else
{
v___y_2103_ = v___x_2118_;
goto v___jp_2102_;
}
}
else
{
v___y_2103_ = v___x_2116_;
goto v___jp_2102_;
}
}
else
{
v___y_2103_ = v___x_2114_;
goto v___jp_2102_;
}
}
else
{
v___y_2103_ = v___x_2112_;
goto v___jp_2102_;
}
}
else
{
v___y_2103_ = v___x_2110_;
goto v___jp_2102_;
}
}
v___jp_2143_:
{
uint8_t v___x_2144_; uint8_t v___x_2145_; 
v___x_2144_ = 65;
v___x_2145_ = lean_uint8_dec_le(v___x_2144_, v___x_2101_);
if (v___x_2145_ == 0)
{
goto v___jp_2108_;
}
else
{
uint8_t v___x_2146_; uint8_t v___x_2147_; 
v___x_2146_ = 90;
v___x_2147_ = lean_uint8_dec_le(v___x_2101_, v___x_2146_);
if (v___x_2147_ == 0)
{
goto v___jp_2108_;
}
else
{
v___y_2103_ = v___x_2147_;
goto v___jp_2102_;
}
}
}
v___jp_2148_:
{
uint8_t v___x_2149_; uint8_t v___x_2150_; 
v___x_2149_ = 97;
v___x_2150_ = lean_uint8_dec_le(v___x_2149_, v___x_2101_);
if (v___x_2150_ == 0)
{
goto v___jp_2143_;
}
else
{
uint8_t v___x_2151_; uint8_t v___x_2152_; 
v___x_2151_ = 122;
v___x_2152_ = lean_uint8_dec_le(v___x_2101_, v___x_2151_);
if (v___x_2152_ == 0)
{
goto v___jp_2143_;
}
else
{
v___y_2103_ = v___x_2152_;
goto v___jp_2102_;
}
}
}
}
v___jp_1983_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1985_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__1));
v___x_1986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1986_, 0, v___y_1984_);
lean_ctor_set(v___x_1986_, 1, v___x_1985_);
return v___x_1986_;
}
v___jp_1992_:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1996_, 0, v_segments_1991_);
lean_ctor_set(v___x_1996_, 1, v_totalLength_1994_);
v___x_1997_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(v_config_1979_, v___x_1996_, v___y_1995_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_res_1998_; lean_object* v_pos_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2008_; 
v_res_1998_ = lean_ctor_get(v___x_1997_, 1);
v_pos_1999_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2001_ = v___x_1997_;
v_isShared_2002_ = v_isSharedCheck_2008_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_res_1998_);
lean_inc(v_pos_1999_);
lean_dec(v___x_1997_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2008_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v_fst_2003_; lean_object* v___x_2004_; lean_object* v___x_2006_; 
v_fst_2003_ = lean_ctor_get(v_res_1998_, 0);
lean_inc(v_fst_2003_);
lean_dec(v_res_1998_);
v___x_2004_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2004_, 0, v_fst_2003_);
lean_ctor_set_uint8(v___x_2004_, sizeof(void*)*1, v_isAbsolute_1993_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 1, v___x_2004_);
v___x_2006_ = v___x_2001_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_pos_1999_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
else
{
lean_object* v_pos_2009_; lean_object* v_err_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
v_pos_2009_ = lean_ctor_get(v___x_1997_, 0);
v_err_2010_ = lean_ctor_get(v___x_1997_, 1);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v___x_1997_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_err_2010_);
lean_inc(v_pos_2009_);
lean_dec(v___x_1997_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_pos_2009_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_err_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
v___jp_2018_:
{
if (v_allowEmpty_1981_ == 0)
{
v___y_1984_ = v___y_2019_;
goto v___jp_1983_;
}
else
{
if (v___y_2020_ == 0)
{
v___y_1984_ = v___y_2019_;
goto v___jp_1983_;
}
else
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2021_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__3));
v___x_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___y_2019_);
lean_ctor_set(v___x_2022_, 1, v___x_2021_);
return v___x_2022_;
}
}
}
v___jp_2023_:
{
if (v___y_2024_ == 0)
{
v___y_2019_ = v___y_2025_;
v___y_2020_ = v___y_2026_;
goto v___jp_2018_;
}
else
{
v___y_2019_ = v___y_2025_;
v___y_2020_ = v___y_2024_;
goto v___jp_2018_;
}
}
v___jp_2027_:
{
if (v___y_2028_ == 0)
{
uint8_t v___x_2031_; 
v___x_2031_ = 1;
v___y_2024_ = v_res_2030_;
v___y_2025_ = v_pos_2029_;
v___y_2026_ = v___x_2031_;
goto v___jp_2023_;
}
else
{
v___y_2024_ = v_res_2030_;
v___y_2025_ = v_pos_2029_;
v___y_2026_ = v_isAbsolute_1989_;
goto v___jp_2023_;
}
}
v___jp_2032_:
{
if (v_forceAbsolute_1980_ == 0)
{
v_isAbsolute_1993_ = v_isAbsolute_1989_;
v_totalLength_1994_ = v___x_1990_;
v___y_1995_ = v_pos_2034_;
goto v___jp_1992_;
}
else
{
lean_object* v_array_2036_; lean_object* v_idx_2037_; lean_object* v___x_2038_; uint8_t v___x_2039_; 
lean_dec_ref(v_config_1979_);
v_array_2036_ = lean_ctor_get(v_pos_2034_, 0);
v_idx_2037_ = lean_ctor_get(v_pos_2034_, 1);
v___x_2038_ = lean_byte_array_size(v_array_2036_);
v___x_2039_ = lean_nat_dec_lt(v_idx_2037_, v___x_2038_);
if (v___x_2039_ == 0)
{
v___y_2028_ = v___y_2033_;
v_pos_2029_ = v_pos_2034_;
v_res_2030_ = v_forceAbsolute_1980_;
goto v___jp_2027_;
}
else
{
v___y_2028_ = v___y_2033_;
v_pos_2029_ = v_pos_2034_;
v_res_2030_ = v_res_2035_;
goto v___jp_2027_;
}
}
}
v___jp_2040_:
{
lean_object* v_array_2044_; lean_object* v_idx_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; 
v_array_2044_ = lean_ctor_get(v___y_2042_, 0);
v_idx_2045_ = lean_ctor_get(v___y_2042_, 1);
v___x_2046_ = lean_byte_array_size(v_array_2044_);
v___x_2047_ = lean_nat_dec_lt(v_idx_2045_, v___x_2046_);
if (v___x_2047_ == 0)
{
v___y_2033_ = v___y_2041_;
v_pos_2034_ = v___y_2042_;
v_res_2035_ = v___y_2043_;
goto v___jp_2032_;
}
else
{
uint8_t v___x_2048_; uint8_t v___x_2049_; uint8_t v___x_2050_; 
v___x_2048_ = lean_byte_array_fget(v_array_2044_, v_idx_2045_);
v___x_2049_ = 47;
v___x_2050_ = lean_uint8_dec_eq(v___x_2048_, v___x_2049_);
if (v___x_2050_ == 0)
{
v___y_2033_ = v___y_2041_;
v_pos_2034_ = v___y_2042_;
v_res_2035_ = v___y_2043_;
goto v___jp_2032_;
}
else
{
if (v___x_2047_ == 0)
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
lean_dec_ref(v_config_1979_);
v___x_2051_ = lean_box(0);
v___x_2052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___y_2042_);
lean_ctor_set(v___x_2052_, 1, v___x_2051_);
return v___x_2052_;
}
else
{
lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2061_; 
lean_inc(v_idx_2045_);
lean_inc_ref(v_array_2044_);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___y_2042_);
if (v_isSharedCheck_2061_ == 0)
{
lean_object* v_unused_2062_; lean_object* v_unused_2063_; 
v_unused_2062_ = lean_ctor_get(v___y_2042_, 1);
lean_dec(v_unused_2062_);
v_unused_2063_ = lean_ctor_get(v___y_2042_, 0);
lean_dec(v_unused_2063_);
v___x_2054_ = v___y_2042_;
v_isShared_2055_ = v_isSharedCheck_2061_;
goto v_resetjp_2053_;
}
else
{
lean_dec(v___y_2042_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2061_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2059_; 
v___x_2056_ = lean_unsigned_to_nat(1u);
v___x_2057_ = lean_nat_add(v_idx_2045_, v___x_2056_);
lean_dec(v_idx_2045_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 1, v___x_2057_);
v___x_2059_ = v___x_2054_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_array_2044_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v___x_2057_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
v_isAbsolute_1993_ = v___x_2047_;
v_totalLength_1994_ = v___x_2056_;
v___y_1995_ = v___x_2059_;
goto v___jp_1992_;
}
}
}
}
}
}
v___jp_2064_:
{
if (v___y_2065_ == 0)
{
v___y_2041_ = v___y_2066_;
v___y_2042_ = v___y_2067_;
v___y_2043_ = v___y_2065_;
goto v___jp_2040_;
}
else
{
if (v___y_2068_ == 0)
{
v___y_2041_ = v___y_2066_;
v___y_2042_ = v___y_2067_;
v___y_2043_ = v___y_2068_;
goto v___jp_2040_;
}
else
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
lean_dec_ref(v_config_1979_);
v___x_2069_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__5));
v___x_2070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___y_2067_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
return v___x_2070_;
}
}
}
v___jp_2071_:
{
if (v___y_2074_ == 0)
{
v___y_2065_ = v___y_2072_;
v___y_2066_ = v___y_2073_;
v___y_2067_ = v___y_2075_;
v___y_2068_ = v___y_2076_;
goto v___jp_2064_;
}
else
{
v___y_2065_ = v___y_2072_;
v___y_2066_ = v___y_2073_;
v___y_2067_ = v___y_2075_;
v___y_2068_ = v___y_2074_;
goto v___jp_2064_;
}
}
v___jp_2077_:
{
if (v___y_2078_ == 0)
{
uint8_t v___x_2082_; 
v___x_2082_ = 1;
v___y_2072_ = v___y_2081_;
v___y_2073_ = v___y_2078_;
v___y_2074_ = v___y_2079_;
v___y_2075_ = v___y_2080_;
v___y_2076_ = v___x_2082_;
goto v___jp_2071_;
}
else
{
v___y_2072_ = v___y_2081_;
v___y_2073_ = v___y_2078_;
v___y_2074_ = v___y_2079_;
v___y_2075_ = v___y_2080_;
v___y_2076_ = v_isAbsolute_1989_;
goto v___jp_2071_;
}
}
v___jp_2083_:
{
if (v_allowEmpty_1981_ == 0)
{
uint8_t v___x_2087_; 
v___x_2087_ = 1;
v___y_2078_ = v___y_2084_;
v___y_2079_ = v_res_2086_;
v___y_2080_ = v_pos_2085_;
v___y_2081_ = v___x_2087_;
goto v___jp_2077_;
}
else
{
v___y_2078_ = v___y_2084_;
v___y_2079_ = v_res_2086_;
v___y_2080_ = v_pos_2085_;
v___y_2081_ = v_isAbsolute_1989_;
goto v___jp_2077_;
}
}
v___jp_2088_:
{
lean_object* v___x_2093_; uint8_t v___x_2094_; 
v___x_2093_ = lean_byte_array_size(v_array_2090_);
lean_dec_ref(v_array_2090_);
v___x_2094_ = lean_nat_dec_lt(v_idx_2091_, v___x_2093_);
lean_dec(v_idx_2091_);
if (v___x_2094_ == 0)
{
uint8_t v___x_2095_; 
v___x_2095_ = 1;
v___y_2084_ = v_res_2092_;
v_pos_2085_ = v_pos_2089_;
v_res_2086_ = v___x_2095_;
goto v___jp_2083_;
}
else
{
v___y_2084_ = v_res_2092_;
v_pos_2085_ = v_pos_2089_;
v_res_2086_ = v_isAbsolute_1989_;
goto v___jp_2083_;
}
}
v___jp_2096_:
{
if (v___y_2097_ == 0)
{
if (v___y_2098_ == 0)
{
v_pos_2089_ = v_a_1982_;
v_array_2090_ = v_array_1987_;
v_idx_2091_ = v_idx_1988_;
v_res_2092_ = v_isAbsolute_1989_;
goto v___jp_2088_;
}
else
{
v_pos_2089_ = v_a_1982_;
v_array_2090_ = v_array_1987_;
v_idx_2091_ = v_idx_1988_;
v_res_2092_ = v___y_2098_;
goto v___jp_2088_;
}
}
else
{
v_pos_2089_ = v_a_1982_;
v_array_2090_ = v_array_1987_;
v_idx_2091_ = v_idx_1988_;
v_res_2092_ = v___y_2097_;
goto v___jp_2088_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath___boxed(lean_object* v_config_2157_, lean_object* v_forceAbsolute_2158_, lean_object* v_allowEmpty_2159_, lean_object* v_a_2160_){
_start:
{
uint8_t v_forceAbsolute_boxed_2161_; uint8_t v_allowEmpty_boxed_2162_; lean_object* v_res_2163_; 
v_forceAbsolute_boxed_2161_ = lean_unbox(v_forceAbsolute_2158_);
v_allowEmpty_boxed_2162_ = lean_unbox(v_allowEmpty_2159_);
v_res_2163_ = l_Std_Http_URI_Parser_parsePath(v_config_2157_, v_forceAbsolute_boxed_2161_, v_allowEmpty_boxed_2162_, v_a_2160_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0(lean_object* v_config_2164_, lean_object* v_inst_2165_, lean_object* v_a_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v___x_2168_; 
v___x_2168_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(v_config_2164_, v_a_2166_, v___y_2167_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0(lean_object* v_config_2169_, lean_object* v_inst_2170_, lean_object* v_a_2171_, lean_object* v___y_2172_){
_start:
{
lean_object* v___x_2173_; 
v___x_2173_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_2169_, v_a_2171_, v___y_2172_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg(){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0));
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg___boxed(lean_object* v___dummy_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg();
return v_res_2177_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg();
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(lean_object* v_s_2179_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___boxed(lean_object* v_s_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(v_s_2181_);
lean_dec_ref(v_s_2181_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg(){
_start:
{
lean_object* v___x_2184_; 
v___x_2184_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0));
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg___boxed(lean_object* v___dummy_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg();
return v_res_2186_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2187_; 
v___x_2187_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg();
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(lean_object* v_s_2188_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___boxed(lean_object* v_s_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(v_s_2190_);
lean_dec_ref(v_s_2190_);
return v_res_2191_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(uint8_t v_c_2192_){
_start:
{
uint8_t v___y_2194_; uint8_t v___x_2246_; uint8_t v___x_2247_; 
v___x_2246_ = 48;
v___x_2247_ = lean_uint8_dec_le(v___x_2246_, v_c_2192_);
if (v___x_2247_ == 0)
{
goto v___jp_2241_;
}
else
{
uint8_t v___x_2248_; uint8_t v___x_2249_; 
v___x_2248_ = 57;
v___x_2249_ = lean_uint8_dec_le(v_c_2192_, v___x_2248_);
if (v___x_2249_ == 0)
{
goto v___jp_2241_;
}
else
{
v___y_2194_ = v___x_2249_;
goto v___jp_2193_;
}
}
v___jp_2193_:
{
if (v___y_2194_ == 0)
{
uint8_t v___x_2195_; uint8_t v___x_2196_; 
v___x_2195_ = 37;
v___x_2196_ = lean_uint8_dec_eq(v_c_2192_, v___x_2195_);
return v___x_2196_;
}
else
{
return v___y_2194_;
}
}
v___jp_2197_:
{
uint8_t v___x_2198_; uint8_t v___x_2199_; 
v___x_2198_ = 45;
v___x_2199_ = lean_uint8_dec_eq(v_c_2192_, v___x_2198_);
if (v___x_2199_ == 0)
{
uint8_t v___x_2200_; uint8_t v___x_2201_; 
v___x_2200_ = 46;
v___x_2201_ = lean_uint8_dec_eq(v_c_2192_, v___x_2200_);
if (v___x_2201_ == 0)
{
uint8_t v___x_2202_; uint8_t v___x_2203_; 
v___x_2202_ = 95;
v___x_2203_ = lean_uint8_dec_eq(v_c_2192_, v___x_2202_);
if (v___x_2203_ == 0)
{
uint8_t v___x_2204_; uint8_t v___x_2205_; 
v___x_2204_ = 126;
v___x_2205_ = lean_uint8_dec_eq(v_c_2192_, v___x_2204_);
if (v___x_2205_ == 0)
{
uint8_t v___x_2206_; uint8_t v___x_2207_; 
v___x_2206_ = 33;
v___x_2207_ = lean_uint8_dec_eq(v_c_2192_, v___x_2206_);
if (v___x_2207_ == 0)
{
uint8_t v___x_2208_; uint8_t v___x_2209_; 
v___x_2208_ = 36;
v___x_2209_ = lean_uint8_dec_eq(v_c_2192_, v___x_2208_);
if (v___x_2209_ == 0)
{
uint8_t v___x_2210_; uint8_t v___x_2211_; 
v___x_2210_ = 38;
v___x_2211_ = lean_uint8_dec_eq(v_c_2192_, v___x_2210_);
if (v___x_2211_ == 0)
{
uint8_t v___x_2212_; uint8_t v___x_2213_; 
v___x_2212_ = 39;
v___x_2213_ = lean_uint8_dec_eq(v_c_2192_, v___x_2212_);
if (v___x_2213_ == 0)
{
uint8_t v___x_2214_; uint8_t v___x_2215_; 
v___x_2214_ = 40;
v___x_2215_ = lean_uint8_dec_eq(v_c_2192_, v___x_2214_);
if (v___x_2215_ == 0)
{
uint8_t v___x_2216_; uint8_t v___x_2217_; 
v___x_2216_ = 41;
v___x_2217_ = lean_uint8_dec_eq(v_c_2192_, v___x_2216_);
if (v___x_2217_ == 0)
{
uint8_t v___x_2218_; uint8_t v___x_2219_; 
v___x_2218_ = 42;
v___x_2219_ = lean_uint8_dec_eq(v_c_2192_, v___x_2218_);
if (v___x_2219_ == 0)
{
uint8_t v___x_2220_; uint8_t v___x_2221_; 
v___x_2220_ = 43;
v___x_2221_ = lean_uint8_dec_eq(v_c_2192_, v___x_2220_);
if (v___x_2221_ == 0)
{
uint8_t v___x_2222_; uint8_t v___x_2223_; 
v___x_2222_ = 44;
v___x_2223_ = lean_uint8_dec_eq(v_c_2192_, v___x_2222_);
if (v___x_2223_ == 0)
{
uint8_t v___x_2224_; uint8_t v___x_2225_; 
v___x_2224_ = 59;
v___x_2225_ = lean_uint8_dec_eq(v_c_2192_, v___x_2224_);
if (v___x_2225_ == 0)
{
uint8_t v___x_2226_; uint8_t v___x_2227_; 
v___x_2226_ = 61;
v___x_2227_ = lean_uint8_dec_eq(v_c_2192_, v___x_2226_);
if (v___x_2227_ == 0)
{
uint8_t v___x_2228_; uint8_t v___x_2229_; 
v___x_2228_ = 58;
v___x_2229_ = lean_uint8_dec_eq(v_c_2192_, v___x_2228_);
if (v___x_2229_ == 0)
{
uint8_t v___x_2230_; uint8_t v___x_2231_; 
v___x_2230_ = 64;
v___x_2231_ = lean_uint8_dec_eq(v_c_2192_, v___x_2230_);
if (v___x_2231_ == 0)
{
uint8_t v___x_2232_; uint8_t v___x_2233_; 
v___x_2232_ = 47;
v___x_2233_ = lean_uint8_dec_eq(v_c_2192_, v___x_2232_);
if (v___x_2233_ == 0)
{
uint8_t v___x_2234_; uint8_t v___x_2235_; 
v___x_2234_ = 63;
v___x_2235_ = lean_uint8_dec_eq(v_c_2192_, v___x_2234_);
v___y_2194_ = v___x_2235_;
goto v___jp_2193_;
}
else
{
v___y_2194_ = v___x_2233_;
goto v___jp_2193_;
}
}
else
{
v___y_2194_ = v___x_2231_;
goto v___jp_2193_;
}
}
else
{
v___y_2194_ = v___x_2229_;
goto v___jp_2193_;
}
}
else
{
v___y_2194_ = v___x_2227_;
goto v___jp_2193_;
}
}
else
{
v___y_2194_ = v___x_2225_;
goto v___jp_2193_;
}
}
else
{
v___y_2194_ = v___x_2223_;
goto v___jp_2193_;
}
}
else
{
v___y_2194_ = v___x_2221_;
goto v___jp_2193_;
}
}
else
{
v___y_2194_ = v___x_2219_;
goto v___jp_2193_;
}
}
else
{
v___y_2194_ = v___x_2217_;
goto v___jp_2193_;
}
}
else
{
v___y_2194_ = v___x_2215_;
goto v___jp_2193_;
}
}
else
{
v___y_2194_ = v___x_2213_;
goto v___jp_2193_;
}
}
else
{
v___y_2194_ = v___x_2211_;
goto v___jp_2193_;
}
}
else
{
v___y_2194_ = v___x_2209_;
goto v___jp_2193_;
}
}
else
{
v___y_2194_ = v___x_2207_;
goto v___jp_2193_;
}
}
else
{
v___y_2194_ = v___x_2205_;
goto v___jp_2193_;
}
}
else
{
v___y_2194_ = v___x_2203_;
goto v___jp_2193_;
}
}
else
{
v___y_2194_ = v___x_2201_;
goto v___jp_2193_;
}
}
else
{
v___y_2194_ = v___x_2199_;
goto v___jp_2193_;
}
}
v___jp_2236_:
{
uint8_t v___x_2237_; uint8_t v___x_2238_; 
v___x_2237_ = 65;
v___x_2238_ = lean_uint8_dec_le(v___x_2237_, v_c_2192_);
if (v___x_2238_ == 0)
{
goto v___jp_2197_;
}
else
{
uint8_t v___x_2239_; uint8_t v___x_2240_; 
v___x_2239_ = 90;
v___x_2240_ = lean_uint8_dec_le(v_c_2192_, v___x_2239_);
if (v___x_2240_ == 0)
{
goto v___jp_2197_;
}
else
{
v___y_2194_ = v___x_2240_;
goto v___jp_2193_;
}
}
}
v___jp_2241_:
{
uint8_t v___x_2242_; uint8_t v___x_2243_; 
v___x_2242_ = 97;
v___x_2243_ = lean_uint8_dec_le(v___x_2242_, v_c_2192_);
if (v___x_2243_ == 0)
{
goto v___jp_2236_;
}
else
{
uint8_t v___x_2244_; uint8_t v___x_2245_; 
v___x_2244_ = 122;
v___x_2245_ = lean_uint8_dec_le(v_c_2192_, v___x_2244_);
if (v___x_2245_ == 0)
{
goto v___jp_2236_;
}
else
{
v___y_2194_ = v___x_2245_;
goto v___jp_2193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0___boxed(lean_object* v_c_2250_){
_start:
{
uint8_t v_c_boxed_2251_; uint8_t v_res_2252_; lean_object* v_r_2253_; 
v_c_boxed_2251_ = lean_unbox(v_c_2250_);
v_res_2252_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(v_c_boxed_2251_);
v_r_2253_ = lean_box(v_res_2252_);
return v_r_2253_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(lean_object* v___x_2254_, lean_object* v___x_2255_, lean_object* v_a_2256_, lean_object* v_b_2257_){
_start:
{
lean_object* v_it_2259_; 
if (lean_obj_tag(v_a_2256_) == 0)
{
lean_object* v_currPos_2263_; lean_object* v_searcher_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2290_; 
v_currPos_2263_ = lean_ctor_get(v_a_2256_, 0);
v_searcher_2264_ = lean_ctor_get(v_a_2256_, 1);
v_isSharedCheck_2290_ = !lean_is_exclusive(v_a_2256_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2266_ = v_a_2256_;
v_isShared_2267_ = v_isSharedCheck_2290_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_searcher_2264_);
lean_inc(v_currPos_2263_);
lean_dec(v_a_2256_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2290_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v_str_2268_; lean_object* v_startInclusive_2269_; lean_object* v_endExclusive_2270_; lean_object* v___x_2271_; uint8_t v_decide_2272_; 
v_str_2268_ = lean_ctor_get(v___x_2254_, 0);
v_startInclusive_2269_ = lean_ctor_get(v___x_2254_, 1);
v_endExclusive_2270_ = lean_ctor_get(v___x_2254_, 2);
v___x_2271_ = lean_nat_sub(v_endExclusive_2270_, v_startInclusive_2269_);
v_decide_2272_ = lean_nat_dec_eq(v_searcher_2264_, v___x_2271_);
lean_dec(v___x_2271_);
if (v_decide_2272_ == 0)
{
uint32_t v___x_2273_; lean_object* v___x_2274_; uint32_t v___x_2275_; uint8_t v___x_2276_; 
v___x_2273_ = 38;
v___x_2274_ = lean_nat_add(v_startInclusive_2269_, v_searcher_2264_);
v___x_2275_ = lean_string_utf8_get_fast(v_str_2268_, v___x_2274_);
v___x_2276_ = lean_uint32_dec_eq(v___x_2275_, v___x_2273_);
if (v___x_2276_ == 0)
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2280_; 
lean_dec(v_searcher_2264_);
v___x_2277_ = lean_string_utf8_next_fast(v_str_2268_, v___x_2274_);
lean_dec(v___x_2274_);
v___x_2278_ = lean_nat_sub(v___x_2277_, v_startInclusive_2269_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 1, v___x_2278_);
v___x_2280_ = v___x_2266_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_currPos_2263_);
lean_ctor_set(v_reuseFailAlloc_2282_, 1, v___x_2278_);
v___x_2280_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
v_a_2256_ = v___x_2280_;
goto _start;
}
}
else
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v_nextIt_2287_; 
lean_dec(v_currPos_2263_);
v___x_2283_ = lean_string_utf8_next_fast(v_str_2268_, v___x_2274_);
v___x_2284_ = lean_nat_sub(v___x_2283_, v___x_2274_);
lean_dec(v___x_2274_);
v___x_2285_ = lean_nat_add(v_searcher_2264_, v___x_2284_);
lean_dec(v___x_2284_);
lean_dec(v_searcher_2264_);
lean_inc(v___x_2285_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 1, v___x_2285_);
lean_ctor_set(v___x_2266_, 0, v___x_2285_);
v_nextIt_2287_ = v___x_2266_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2285_);
lean_ctor_set(v_reuseFailAlloc_2288_, 1, v___x_2285_);
v_nextIt_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
v_it_2259_ = v_nextIt_2287_;
goto v___jp_2258_;
}
}
}
else
{
lean_object* v___x_2289_; 
lean_del_object(v___x_2266_);
lean_dec(v_searcher_2264_);
lean_dec(v_currPos_2263_);
v___x_2289_ = lean_box(1);
v_it_2259_ = v___x_2289_;
goto v___jp_2258_;
}
}
}
else
{
return v_b_2257_;
}
v___jp_2258_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2260_ = lean_unsigned_to_nat(1u);
v___x_2261_ = lean_nat_add(v_b_2257_, v___x_2260_);
lean_dec(v_b_2257_);
v_a_2256_ = v_it_2259_;
v_b_2257_ = v___x_2261_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg___boxed(lean_object* v___x_2291_, lean_object* v___x_2292_, lean_object* v_a_2293_, lean_object* v_b_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2291_, v___x_2292_, v_a_2293_, v_b_2294_);
lean_dec(v___x_2292_);
lean_dec_ref(v___x_2291_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(lean_object* v___x_2296_, lean_object* v___x_2297_, lean_object* v___x_2298_, lean_object* v_a_2299_, lean_object* v_b_2300_){
_start:
{
lean_object* v_it_2302_; 
if (lean_obj_tag(v_a_2299_) == 0)
{
lean_object* v_currPos_2306_; lean_object* v_searcher_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2333_; 
v_currPos_2306_ = lean_ctor_get(v_a_2299_, 0);
v_searcher_2307_ = lean_ctor_get(v_a_2299_, 1);
v_isSharedCheck_2333_ = !lean_is_exclusive(v_a_2299_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2309_ = v_a_2299_;
v_isShared_2310_ = v_isSharedCheck_2333_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_searcher_2307_);
lean_inc(v_currPos_2306_);
lean_dec(v_a_2299_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2333_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v_str_2311_; lean_object* v_startInclusive_2312_; lean_object* v_endExclusive_2313_; lean_object* v___x_2314_; uint8_t v_decide_2315_; 
v_str_2311_ = lean_ctor_get(v___x_2297_, 0);
v_startInclusive_2312_ = lean_ctor_get(v___x_2297_, 1);
v_endExclusive_2313_ = lean_ctor_get(v___x_2297_, 2);
v___x_2314_ = lean_nat_sub(v_endExclusive_2313_, v_startInclusive_2312_);
v_decide_2315_ = lean_nat_dec_eq(v_searcher_2307_, v___x_2314_);
lean_dec(v___x_2314_);
if (v_decide_2315_ == 0)
{
lean_object* v___x_2316_; uint32_t v___x_2317_; uint32_t v___x_2318_; uint8_t v___x_2319_; 
v___x_2316_ = lean_nat_add(v_startInclusive_2312_, v_searcher_2307_);
v___x_2317_ = lean_string_utf8_get_fast(v_str_2311_, v___x_2316_);
v___x_2318_ = 38;
v___x_2319_ = lean_uint32_dec_eq(v___x_2317_, v___x_2318_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2323_; 
lean_dec(v_searcher_2307_);
v___x_2320_ = lean_string_utf8_next_fast(v_str_2311_, v___x_2316_);
lean_dec(v___x_2316_);
v___x_2321_ = lean_nat_sub(v___x_2320_, v_startInclusive_2312_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 1, v___x_2321_);
v___x_2323_ = v___x_2309_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_currPos_2306_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v___x_2321_);
v___x_2323_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2297_, v___x_2298_, v___x_2323_, v_b_2300_);
return v___x_2324_;
}
}
else
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v_nextIt_2330_; 
lean_dec(v_currPos_2306_);
v___x_2326_ = lean_string_utf8_next_fast(v_str_2311_, v___x_2316_);
v___x_2327_ = lean_nat_sub(v___x_2326_, v___x_2316_);
lean_dec(v___x_2316_);
v___x_2328_ = lean_nat_add(v_searcher_2307_, v___x_2327_);
lean_dec(v___x_2327_);
lean_dec(v_searcher_2307_);
lean_inc(v___x_2328_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 1, v___x_2328_);
lean_ctor_set(v___x_2309_, 0, v___x_2328_);
v_nextIt_2330_ = v___x_2309_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2328_);
lean_ctor_set(v_reuseFailAlloc_2331_, 1, v___x_2328_);
v_nextIt_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
v_it_2302_ = v_nextIt_2330_;
goto v___jp_2301_;
}
}
}
else
{
lean_object* v___x_2332_; 
lean_del_object(v___x_2309_);
lean_dec(v_searcher_2307_);
lean_dec(v_currPos_2306_);
v___x_2332_ = lean_box(1);
v_it_2302_ = v___x_2332_;
goto v___jp_2301_;
}
}
}
else
{
return v_b_2300_;
}
v___jp_2301_:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2303_ = lean_unsigned_to_nat(1u);
v___x_2304_ = lean_nat_add(v_b_2300_, v___x_2303_);
lean_dec(v_b_2300_);
v___x_2305_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2297_, v___x_2298_, v_it_2302_, v___x_2304_);
return v___x_2305_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg___boxed(lean_object* v___x_2334_, lean_object* v___x_2335_, lean_object* v___x_2336_, lean_object* v_a_2337_, lean_object* v_b_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2334_, v___x_2335_, v___x_2336_, v_a_2337_, v_b_2338_);
lean_dec(v___x_2336_);
lean_dec_ref(v___x_2335_);
lean_dec_ref(v___x_2334_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(lean_object* v_out_2340_, lean_object* v_a_2341_, lean_object* v_b_2342_){
_start:
{
if (lean_obj_tag(v_a_2341_) == 0)
{
lean_object* v_currPos_2343_; lean_object* v_searcher_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2383_; 
v_currPos_2343_ = lean_ctor_get(v_a_2341_, 0);
v_searcher_2344_ = lean_ctor_get(v_a_2341_, 1);
v_isSharedCheck_2383_ = !lean_is_exclusive(v_a_2341_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2346_ = v_a_2341_;
v_isShared_2347_ = v_isSharedCheck_2383_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_searcher_2344_);
lean_inc(v_currPos_2343_);
lean_dec(v_a_2341_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2383_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v_str_2348_; lean_object* v_startInclusive_2349_; lean_object* v_endExclusive_2350_; lean_object* v_it_2352_; lean_object* v_startInclusive_2353_; lean_object* v_endExclusive_2354_; lean_object* v___x_2361_; uint8_t v_decide_2362_; 
v_str_2348_ = lean_ctor_get(v_out_2340_, 0);
v_startInclusive_2349_ = lean_ctor_get(v_out_2340_, 1);
v_endExclusive_2350_ = lean_ctor_get(v_out_2340_, 2);
v___x_2361_ = lean_nat_sub(v_endExclusive_2350_, v_startInclusive_2349_);
v_decide_2362_ = lean_nat_dec_eq(v_searcher_2344_, v___x_2361_);
if (v_decide_2362_ == 0)
{
uint32_t v___x_2363_; lean_object* v___x_2364_; uint32_t v___x_2365_; uint8_t v___x_2366_; 
lean_dec(v___x_2361_);
v___x_2363_ = 61;
v___x_2364_ = lean_nat_add(v_startInclusive_2349_, v_searcher_2344_);
v___x_2365_ = lean_string_utf8_get_fast(v_str_2348_, v___x_2364_);
v___x_2366_ = lean_uint32_dec_eq(v___x_2365_, v___x_2363_);
if (v___x_2366_ == 0)
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2370_; 
lean_dec(v_searcher_2344_);
v___x_2367_ = lean_string_utf8_next_fast(v_str_2348_, v___x_2364_);
lean_dec(v___x_2364_);
v___x_2368_ = lean_nat_sub(v___x_2367_, v_startInclusive_2349_);
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 1, v___x_2368_);
v___x_2370_ = v___x_2346_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_currPos_2343_);
lean_ctor_set(v_reuseFailAlloc_2372_, 1, v___x_2368_);
v___x_2370_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
v_a_2341_ = v___x_2370_;
goto _start;
}
}
else
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v_slice_2376_; lean_object* v_nextIt_2378_; 
v___x_2373_ = lean_string_utf8_next_fast(v_str_2348_, v___x_2364_);
v___x_2374_ = lean_nat_sub(v___x_2373_, v___x_2364_);
lean_dec(v___x_2364_);
v___x_2375_ = lean_nat_add(v_searcher_2344_, v___x_2374_);
lean_dec(v___x_2374_);
v_slice_2376_ = l_String_Slice_subslice_x21(v_out_2340_, v_currPos_2343_, v_searcher_2344_);
lean_inc(v___x_2375_);
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 1, v___x_2375_);
lean_ctor_set(v___x_2346_, 0, v___x_2375_);
v_nextIt_2378_ = v___x_2346_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v___x_2375_);
lean_ctor_set(v_reuseFailAlloc_2381_, 1, v___x_2375_);
v_nextIt_2378_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
lean_object* v_startInclusive_2379_; lean_object* v_endExclusive_2380_; 
v_startInclusive_2379_ = lean_ctor_get(v_slice_2376_, 0);
lean_inc(v_startInclusive_2379_);
v_endExclusive_2380_ = lean_ctor_get(v_slice_2376_, 1);
lean_inc(v_endExclusive_2380_);
lean_dec_ref(v_slice_2376_);
v_it_2352_ = v_nextIt_2378_;
v_startInclusive_2353_ = v_startInclusive_2379_;
v_endExclusive_2354_ = v_endExclusive_2380_;
goto v___jp_2351_;
}
}
}
else
{
lean_object* v___x_2382_; 
lean_del_object(v___x_2346_);
lean_dec(v_searcher_2344_);
v___x_2382_ = lean_box(1);
v_it_2352_ = v___x_2382_;
v_startInclusive_2353_ = v_currPos_2343_;
v_endExclusive_2354_ = v___x_2361_;
goto v___jp_2351_;
}
v___jp_2351_:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2355_ = lean_nat_add(v_startInclusive_2349_, v_startInclusive_2353_);
lean_dec(v_startInclusive_2353_);
v___x_2356_ = lean_nat_add(v_startInclusive_2349_, v_endExclusive_2354_);
lean_dec(v_endExclusive_2354_);
lean_inc_ref(v_str_2348_);
v___x_2357_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2357_, 0, v_str_2348_);
lean_ctor_set(v___x_2357_, 1, v___x_2355_);
lean_ctor_set(v___x_2357_, 2, v___x_2356_);
v___x_2358_ = l_String_Slice_toString(v___x_2357_);
lean_dec_ref_known(v___x_2357_, 3);
v___x_2359_ = lean_array_push(v_b_2342_, v___x_2358_);
v_a_2341_ = v_it_2352_;
v_b_2342_ = v___x_2359_;
goto _start;
}
}
}
else
{
return v_b_2342_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg___boxed(lean_object* v_out_2384_, lean_object* v_a_2385_, lean_object* v_b_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_2384_, v_a_2385_, v_b_2386_);
lean_dec_ref(v_out_2384_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(lean_object* v___x_2391_, lean_object* v___x_2392_, lean_object* v___x_2393_, lean_object* v_a_2394_, lean_object* v_b_2395_){
_start:
{
lean_object* v_it_2397_; lean_object* v_startInclusive_2398_; lean_object* v_endExclusive_2399_; 
if (lean_obj_tag(v_a_2394_) == 0)
{
lean_object* v_currPos_2424_; lean_object* v_searcher_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2454_; 
v_currPos_2424_ = lean_ctor_get(v_a_2394_, 0);
v_searcher_2425_ = lean_ctor_get(v_a_2394_, 1);
v_isSharedCheck_2454_ = !lean_is_exclusive(v_a_2394_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2427_ = v_a_2394_;
v_isShared_2428_ = v_isSharedCheck_2454_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_searcher_2425_);
lean_inc(v_currPos_2424_);
lean_dec(v_a_2394_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2454_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v_str_2429_; lean_object* v_startInclusive_2430_; lean_object* v_endExclusive_2431_; lean_object* v___x_2432_; uint8_t v_decide_2433_; 
v_str_2429_ = lean_ctor_get(v___x_2392_, 0);
v_startInclusive_2430_ = lean_ctor_get(v___x_2392_, 1);
v_endExclusive_2431_ = lean_ctor_get(v___x_2392_, 2);
v___x_2432_ = lean_nat_sub(v_endExclusive_2431_, v_startInclusive_2430_);
v_decide_2433_ = lean_nat_dec_eq(v_searcher_2425_, v___x_2432_);
lean_dec(v___x_2432_);
if (v_decide_2433_ == 0)
{
uint32_t v___x_2434_; lean_object* v___x_2435_; uint32_t v___x_2436_; uint8_t v___x_2437_; 
v___x_2434_ = 38;
v___x_2435_ = lean_nat_add(v_startInclusive_2430_, v_searcher_2425_);
v___x_2436_ = lean_string_utf8_get_fast(v_str_2429_, v___x_2435_);
v___x_2437_ = lean_uint32_dec_eq(v___x_2436_, v___x_2434_);
if (v___x_2437_ == 0)
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2441_; 
lean_dec(v_searcher_2425_);
v___x_2438_ = lean_string_utf8_next_fast(v_str_2429_, v___x_2435_);
lean_dec(v___x_2435_);
v___x_2439_ = lean_nat_sub(v___x_2438_, v_startInclusive_2430_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 1, v___x_2439_);
v___x_2441_ = v___x_2427_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_currPos_2424_);
lean_ctor_set(v_reuseFailAlloc_2443_, 1, v___x_2439_);
v___x_2441_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
v_a_2394_ = v___x_2441_;
goto _start;
}
}
else
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v_slice_2447_; lean_object* v_nextIt_2449_; 
v___x_2444_ = lean_string_utf8_next_fast(v_str_2429_, v___x_2435_);
v___x_2445_ = lean_nat_sub(v___x_2444_, v___x_2435_);
lean_dec(v___x_2435_);
v___x_2446_ = lean_nat_add(v_searcher_2425_, v___x_2445_);
lean_dec(v___x_2445_);
v_slice_2447_ = l_String_Slice_subslice_x21(v___x_2392_, v_currPos_2424_, v_searcher_2425_);
lean_inc(v___x_2446_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 1, v___x_2446_);
lean_ctor_set(v___x_2427_, 0, v___x_2446_);
v_nextIt_2449_ = v___x_2427_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2446_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v___x_2446_);
v_nextIt_2449_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v_startInclusive_2450_; lean_object* v_endExclusive_2451_; 
v_startInclusive_2450_ = lean_ctor_get(v_slice_2447_, 0);
lean_inc(v_startInclusive_2450_);
v_endExclusive_2451_ = lean_ctor_get(v_slice_2447_, 1);
lean_inc(v_endExclusive_2451_);
lean_dec_ref(v_slice_2447_);
v_it_2397_ = v_nextIt_2449_;
v_startInclusive_2398_ = v_startInclusive_2450_;
v_endExclusive_2399_ = v_endExclusive_2451_;
goto v___jp_2396_;
}
}
}
else
{
lean_object* v___x_2453_; 
lean_del_object(v___x_2427_);
lean_dec(v_searcher_2425_);
v___x_2453_ = lean_box(1);
lean_inc(v___x_2393_);
v_it_2397_ = v___x_2453_;
v_startInclusive_2398_ = v_currPos_2424_;
v_endExclusive_2399_ = v___x_2393_;
goto v___jp_2396_;
}
}
}
else
{
lean_object* v___x_2455_; 
lean_dec(v___x_2393_);
lean_dec_ref(v___x_2391_);
v___x_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2455_, 0, v_b_2395_);
return v___x_2455_;
}
v___jp_2396_:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
lean_inc_ref(v___x_2391_);
v___x_2400_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2391_);
lean_ctor_set(v___x_2400_, 1, v_startInclusive_2398_);
lean_ctor_set(v___x_2400_, 2, v_endExclusive_2399_);
v___x_2401_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
v___x_2402_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0));
v___x_2403_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_2400_, v___x_2401_, v___x_2402_);
lean_dec_ref_known(v___x_2400_, 3);
v___x_2404_ = lean_array_to_list(v___x_2403_);
if (lean_obj_tag(v___x_2404_) == 0)
{
v_a_2394_ = v_it_2397_;
goto _start;
}
else
{
lean_object* v_tail_2406_; 
v_tail_2406_ = lean_ctor_get(v___x_2404_, 1);
if (lean_obj_tag(v_tail_2406_) == 0)
{
lean_object* v_head_2407_; lean_object* v___x_2408_; 
v_head_2407_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_head_2407_);
lean_dec_ref_known(v___x_2404_, 2);
v___x_2408_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2407_);
lean_dec(v_head_2407_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v___x_2409_; 
lean_dec(v_it_2397_);
lean_dec_ref(v_b_2395_);
lean_dec(v___x_2393_);
lean_dec_ref(v___x_2391_);
v___x_2409_ = lean_box(0);
return v___x_2409_;
}
else
{
lean_object* v_val_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v_val_2410_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_val_2410_);
lean_dec_ref_known(v___x_2408_, 1);
v___x_2411_ = lean_box(0);
v___x_2412_ = l_Std_Http_URI_Query_insertEncoded(v_b_2395_, v_val_2410_, v___x_2411_);
v_a_2394_ = v_it_2397_;
v_b_2395_ = v___x_2412_;
goto _start;
}
}
else
{
lean_object* v_head_2414_; lean_object* v___x_2415_; 
lean_inc(v_tail_2406_);
v_head_2414_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_head_2414_);
lean_dec_ref_known(v___x_2404_, 2);
v___x_2415_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2414_);
lean_dec(v_head_2414_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v___x_2416_; 
lean_dec(v_tail_2406_);
lean_dec(v_it_2397_);
lean_dec_ref(v_b_2395_);
lean_dec(v___x_2393_);
lean_dec_ref(v___x_2391_);
v___x_2416_ = lean_box(0);
return v___x_2416_;
}
else
{
lean_object* v_val_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v_val_2417_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_val_2417_);
lean_dec_ref_known(v___x_2415_, 1);
v___x_2418_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1));
v___x_2419_ = l_String_intercalate(v___x_2418_, v_tail_2406_);
v___x_2420_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2419_);
lean_dec_ref(v___x_2419_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v___x_2421_; 
lean_dec(v_val_2417_);
lean_dec(v_it_2397_);
lean_dec_ref(v_b_2395_);
lean_dec(v___x_2393_);
lean_dec_ref(v___x_2391_);
v___x_2421_ = lean_box(0);
return v___x_2421_;
}
else
{
lean_object* v___x_2422_; 
v___x_2422_ = l_Std_Http_URI_Query_insertEncoded(v_b_2395_, v_val_2417_, v___x_2420_);
v_a_2394_ = v_it_2397_;
v_b_2395_ = v___x_2422_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___boxed(lean_object* v___x_2456_, lean_object* v___x_2457_, lean_object* v___x_2458_, lean_object* v_a_2459_, lean_object* v_b_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2456_, v___x_2457_, v___x_2458_, v_a_2459_, v_b_2460_);
lean_dec_ref(v___x_2457_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(lean_object* v___x_2462_, lean_object* v___x_2463_, lean_object* v___x_2464_, lean_object* v_a_2465_, lean_object* v_b_2466_){
_start:
{
lean_object* v_it_2468_; lean_object* v_startInclusive_2469_; lean_object* v_endExclusive_2470_; 
if (lean_obj_tag(v_a_2465_) == 0)
{
lean_object* v_currPos_2495_; lean_object* v_searcher_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2525_; 
v_currPos_2495_ = lean_ctor_get(v_a_2465_, 0);
v_searcher_2496_ = lean_ctor_get(v_a_2465_, 1);
v_isSharedCheck_2525_ = !lean_is_exclusive(v_a_2465_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2498_ = v_a_2465_;
v_isShared_2499_ = v_isSharedCheck_2525_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_searcher_2496_);
lean_inc(v_currPos_2495_);
lean_dec(v_a_2465_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2525_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v_str_2500_; lean_object* v_startInclusive_2501_; lean_object* v_endExclusive_2502_; lean_object* v___x_2503_; uint8_t v_decide_2504_; 
v_str_2500_ = lean_ctor_get(v___x_2463_, 0);
v_startInclusive_2501_ = lean_ctor_get(v___x_2463_, 1);
v_endExclusive_2502_ = lean_ctor_get(v___x_2463_, 2);
v___x_2503_ = lean_nat_sub(v_endExclusive_2502_, v_startInclusive_2501_);
v_decide_2504_ = lean_nat_dec_eq(v_searcher_2496_, v___x_2503_);
lean_dec(v___x_2503_);
if (v_decide_2504_ == 0)
{
lean_object* v___x_2505_; uint32_t v___x_2506_; uint32_t v___x_2507_; uint8_t v___x_2508_; 
v___x_2505_ = lean_nat_add(v_startInclusive_2501_, v_searcher_2496_);
v___x_2506_ = lean_string_utf8_get_fast(v_str_2500_, v___x_2505_);
v___x_2507_ = 38;
v___x_2508_ = lean_uint32_dec_eq(v___x_2506_, v___x_2507_);
if (v___x_2508_ == 0)
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2512_; 
lean_dec(v_searcher_2496_);
v___x_2509_ = lean_string_utf8_next_fast(v_str_2500_, v___x_2505_);
lean_dec(v___x_2505_);
v___x_2510_ = lean_nat_sub(v___x_2509_, v_startInclusive_2501_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 1, v___x_2510_);
v___x_2512_ = v___x_2498_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_currPos_2495_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v___x_2510_);
v___x_2512_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
lean_object* v___x_2513_; 
v___x_2513_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2462_, v___x_2463_, v___x_2464_, v___x_2512_, v_b_2466_);
return v___x_2513_;
}
}
else
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v_slice_2518_; lean_object* v_nextIt_2520_; 
v___x_2515_ = lean_string_utf8_next_fast(v_str_2500_, v___x_2505_);
v___x_2516_ = lean_nat_sub(v___x_2515_, v___x_2505_);
lean_dec(v___x_2505_);
v___x_2517_ = lean_nat_add(v_searcher_2496_, v___x_2516_);
lean_dec(v___x_2516_);
v_slice_2518_ = l_String_Slice_subslice_x21(v___x_2463_, v_currPos_2495_, v_searcher_2496_);
lean_inc(v___x_2517_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 1, v___x_2517_);
lean_ctor_set(v___x_2498_, 0, v___x_2517_);
v_nextIt_2520_ = v___x_2498_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v___x_2517_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v___x_2517_);
v_nextIt_2520_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
lean_object* v_startInclusive_2521_; lean_object* v_endExclusive_2522_; 
v_startInclusive_2521_ = lean_ctor_get(v_slice_2518_, 0);
lean_inc(v_startInclusive_2521_);
v_endExclusive_2522_ = lean_ctor_get(v_slice_2518_, 1);
lean_inc(v_endExclusive_2522_);
lean_dec_ref(v_slice_2518_);
v_it_2468_ = v_nextIt_2520_;
v_startInclusive_2469_ = v_startInclusive_2521_;
v_endExclusive_2470_ = v_endExclusive_2522_;
goto v___jp_2467_;
}
}
}
else
{
lean_object* v___x_2524_; 
lean_del_object(v___x_2498_);
lean_dec(v_searcher_2496_);
v___x_2524_ = lean_box(1);
lean_inc(v___x_2464_);
v_it_2468_ = v___x_2524_;
v_startInclusive_2469_ = v_currPos_2495_;
v_endExclusive_2470_ = v___x_2464_;
goto v___jp_2467_;
}
}
}
else
{
lean_object* v___x_2526_; 
lean_dec(v___x_2464_);
lean_dec_ref(v___x_2462_);
v___x_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2526_, 0, v_b_2466_);
return v___x_2526_;
}
v___jp_2467_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
lean_inc_ref(v___x_2462_);
v___x_2471_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2462_);
lean_ctor_set(v___x_2471_, 1, v_startInclusive_2469_);
lean_ctor_set(v___x_2471_, 2, v_endExclusive_2470_);
v___x_2472_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
v___x_2473_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0));
v___x_2474_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_2471_, v___x_2472_, v___x_2473_);
lean_dec_ref_known(v___x_2471_, 3);
v___x_2475_ = lean_array_to_list(v___x_2474_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v___x_2476_; 
v___x_2476_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2462_, v___x_2463_, v___x_2464_, v_it_2468_, v_b_2466_);
return v___x_2476_;
}
else
{
lean_object* v_tail_2477_; 
v_tail_2477_ = lean_ctor_get(v___x_2475_, 1);
if (lean_obj_tag(v_tail_2477_) == 0)
{
lean_object* v_head_2478_; lean_object* v___x_2479_; 
v_head_2478_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_head_2478_);
lean_dec_ref_known(v___x_2475_, 2);
v___x_2479_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2478_);
lean_dec(v_head_2478_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v___x_2480_; 
lean_dec(v_it_2468_);
lean_dec_ref(v_b_2466_);
lean_dec(v___x_2464_);
lean_dec_ref(v___x_2462_);
v___x_2480_ = lean_box(0);
return v___x_2480_;
}
else
{
lean_object* v_val_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v_val_2481_ = lean_ctor_get(v___x_2479_, 0);
lean_inc(v_val_2481_);
lean_dec_ref_known(v___x_2479_, 1);
v___x_2482_ = lean_box(0);
v___x_2483_ = l_Std_Http_URI_Query_insertEncoded(v_b_2466_, v_val_2481_, v___x_2482_);
v___x_2484_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2462_, v___x_2463_, v___x_2464_, v_it_2468_, v___x_2483_);
return v___x_2484_;
}
}
else
{
lean_object* v_head_2485_; lean_object* v___x_2486_; 
lean_inc(v_tail_2477_);
v_head_2485_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_head_2485_);
lean_dec_ref_known(v___x_2475_, 2);
v___x_2486_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2485_);
lean_dec(v_head_2485_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v___x_2487_; 
lean_dec(v_tail_2477_);
lean_dec(v_it_2468_);
lean_dec_ref(v_b_2466_);
lean_dec(v___x_2464_);
lean_dec_ref(v___x_2462_);
v___x_2487_ = lean_box(0);
return v___x_2487_;
}
else
{
lean_object* v_val_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v_val_2488_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_val_2488_);
lean_dec_ref_known(v___x_2486_, 1);
v___x_2489_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1));
v___x_2490_ = l_String_intercalate(v___x_2489_, v_tail_2477_);
v___x_2491_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2490_);
lean_dec_ref(v___x_2490_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v___x_2492_; 
lean_dec(v_val_2488_);
lean_dec(v_it_2468_);
lean_dec_ref(v_b_2466_);
lean_dec(v___x_2464_);
lean_dec_ref(v___x_2462_);
v___x_2492_ = lean_box(0);
return v___x_2492_;
}
else
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = l_Std_Http_URI_Query_insertEncoded(v_b_2466_, v_val_2488_, v___x_2491_);
v___x_2494_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2462_, v___x_2463_, v___x_2464_, v_it_2468_, v___x_2493_);
return v___x_2494_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg___boxed(lean_object* v___x_2527_, lean_object* v___x_2528_, lean_object* v___x_2529_, lean_object* v_a_2530_, lean_object* v_b_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2527_, v___x_2528_, v___x_2529_, v_a_2530_, v_b_2531_);
lean_dec_ref(v___x_2528_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(lean_object* v_config_2538_, lean_object* v_a_2539_){
_start:
{
lean_object* v_maxQueryLength_2540_; lean_object* v_maxQueryParams_2541_; lean_object* v___f_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v_snd_2545_; lean_object* v_fst_2546_; lean_object* v_fst_2547_; lean_object* v_array_2548_; lean_object* v_idx_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2599_; 
v_maxQueryLength_2540_ = lean_ctor_get(v_config_2538_, 4);
lean_inc(v_maxQueryLength_2540_);
v_maxQueryParams_2541_ = lean_ctor_get(v_config_2538_, 8);
lean_inc(v_maxQueryParams_2541_);
lean_dec_ref(v_config_2538_);
v___f_2542_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2543_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2539_);
v___x_2544_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2542_, v_maxQueryLength_2540_, v___x_2543_, v_a_2539_);
lean_dec(v_maxQueryLength_2540_);
v_snd_2545_ = lean_ctor_get(v___x_2544_, 1);
lean_inc(v_snd_2545_);
v_fst_2546_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_fst_2546_);
lean_dec_ref(v___x_2544_);
v_fst_2547_ = lean_ctor_get(v_snd_2545_, 0);
lean_inc(v_fst_2547_);
lean_dec(v_snd_2545_);
v_array_2548_ = lean_ctor_get(v_a_2539_, 0);
v_idx_2549_ = lean_ctor_get(v_a_2539_, 1);
v_isSharedCheck_2599_ = !lean_is_exclusive(v_a_2539_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2551_ = v_a_2539_;
v_isShared_2552_ = v_isSharedCheck_2599_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_idx_2549_);
lean_inc(v_array_2548_);
lean_dec(v_a_2539_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2599_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v_lower_2554_; lean_object* v_upper_2555_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___y_2596_; uint8_t v___x_2598_; 
v___x_2593_ = lean_nat_add(v_idx_2549_, v_fst_2546_);
lean_dec(v_fst_2546_);
v___x_2594_ = lean_byte_array_size(v_array_2548_);
v___x_2598_ = lean_nat_dec_le(v_idx_2549_, v___x_2543_);
if (v___x_2598_ == 0)
{
v___y_2596_ = v_idx_2549_;
goto v___jp_2595_;
}
else
{
lean_dec(v_idx_2549_);
v___y_2596_ = v___x_2543_;
goto v___jp_2595_;
}
v___jp_2553_:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; uint8_t v___x_2558_; 
v___x_2556_ = l_ByteArray_toByteSlice(v_array_2548_, v_lower_2554_, v_upper_2555_);
v___x_2557_ = l_ByteSlice_toByteArray(v___x_2556_);
v___x_2558_ = lean_string_validate_utf8(v___x_2557_);
if (v___x_2558_ == 0)
{
lean_object* v___x_2559_; lean_object* v___x_2561_; 
lean_dec_ref(v___x_2557_);
lean_dec(v_maxQueryParams_2541_);
v___x_2559_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2552_ == 0)
{
lean_ctor_set_tag(v___x_2551_, 1);
lean_ctor_set(v___x_2551_, 1, v___x_2559_);
lean_ctor_set(v___x_2551_, 0, v_fst_2547_);
v___x_2561_ = v___x_2551_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_fst_2547_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v___x_2559_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
else
{
lean_object* v___x_2563_; lean_object* v___x_2564_; uint8_t v___x_2565_; 
v___x_2563_ = lean_string_from_utf8_unchecked(v___x_2557_);
v___x_2564_ = lean_string_utf8_byte_size(v___x_2563_);
v___x_2565_ = lean_nat_dec_eq(v___x_2564_, v___x_2543_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; 
lean_inc_ref(v___x_2563_);
v___x_2566_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2563_);
lean_ctor_set(v___x_2566_, 1, v___x_2543_);
lean_ctor_set(v___x_2566_, 2, v___x_2564_);
v___x_2567_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0);
v___x_2568_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2563_, v___x_2566_, v___x_2564_, v___x_2567_, v___x_2543_);
v___x_2569_ = lean_nat_dec_lt(v_maxQueryParams_2541_, v___x_2568_);
lean_dec(v___x_2568_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
lean_dec(v_maxQueryParams_2541_);
v___x_2570_ = l_Std_Http_URI_Query_empty;
v___x_2571_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2563_, v___x_2566_, v___x_2564_, v___x_2567_, v___x_2570_);
lean_dec_ref_known(v___x_2566_, 3);
if (lean_obj_tag(v___x_2571_) == 1)
{
lean_object* v_val_2572_; lean_object* v___x_2574_; 
v_val_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_val_2572_);
lean_dec_ref_known(v___x_2571_, 1);
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 1, v_val_2572_);
lean_ctor_set(v___x_2551_, 0, v_fst_2547_);
v___x_2574_ = v___x_2551_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_fst_2547_);
lean_ctor_set(v_reuseFailAlloc_2575_, 1, v_val_2572_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
else
{
lean_object* v___x_2576_; lean_object* v___x_2578_; 
lean_dec(v___x_2571_);
v___x_2576_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2552_ == 0)
{
lean_ctor_set_tag(v___x_2551_, 1);
lean_ctor_set(v___x_2551_, 1, v___x_2576_);
lean_ctor_set(v___x_2551_, 0, v_fst_2547_);
v___x_2578_ = v___x_2551_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_fst_2547_);
lean_ctor_set(v_reuseFailAlloc_2579_, 1, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
else
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2587_; 
lean_dec_ref_known(v___x_2566_, 3);
lean_dec_ref(v___x_2563_);
v___x_2580_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3));
v___x_2581_ = l_Nat_reprFast(v_maxQueryParams_2541_);
v___x_2582_ = lean_string_append(v___x_2580_, v___x_2581_);
lean_dec_ref(v___x_2581_);
v___x_2583_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_2584_ = lean_string_append(v___x_2582_, v___x_2583_);
v___x_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2584_);
if (v_isShared_2552_ == 0)
{
lean_ctor_set_tag(v___x_2551_, 1);
lean_ctor_set(v___x_2551_, 1, v___x_2585_);
lean_ctor_set(v___x_2551_, 0, v_fst_2547_);
v___x_2587_ = v___x_2551_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_fst_2547_);
lean_ctor_set(v_reuseFailAlloc_2588_, 1, v___x_2585_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
else
{
lean_object* v___x_2589_; lean_object* v___x_2591_; 
lean_dec_ref(v___x_2563_);
lean_dec(v_maxQueryParams_2541_);
v___x_2589_ = l_Std_Http_URI_Query_empty;
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 1, v___x_2589_);
lean_ctor_set(v___x_2551_, 0, v_fst_2547_);
v___x_2591_ = v___x_2551_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_fst_2547_);
lean_ctor_set(v_reuseFailAlloc_2592_, 1, v___x_2589_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
v___jp_2595_:
{
uint8_t v___x_2597_; 
v___x_2597_ = lean_nat_dec_le(v___x_2593_, v___x_2594_);
if (v___x_2597_ == 0)
{
lean_dec(v___x_2593_);
v_lower_2554_ = v___y_2596_;
v_upper_2555_ = v___x_2594_;
goto v___jp_2553_;
}
else
{
v_lower_2554_ = v___y_2596_;
v_upper_2555_ = v___x_2593_;
goto v___jp_2553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(lean_object* v___x_2600_, lean_object* v___x_2601_, lean_object* v___x_2602_, lean_object* v_inst_2603_, lean_object* v_R_2604_, lean_object* v_a_2605_, lean_object* v_b_2606_, lean_object* v_c_2607_){
_start:
{
lean_object* v___x_2608_; 
v___x_2608_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2600_, v___x_2601_, v___x_2602_, v_a_2605_, v_b_2606_);
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___boxed(lean_object* v___x_2609_, lean_object* v___x_2610_, lean_object* v___x_2611_, lean_object* v_inst_2612_, lean_object* v_R_2613_, lean_object* v_a_2614_, lean_object* v_b_2615_, lean_object* v_c_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(v___x_2609_, v___x_2610_, v___x_2611_, v_inst_2612_, v_R_2613_, v_a_2614_, v_b_2615_, v_c_2616_);
lean_dec(v___x_2611_);
lean_dec_ref(v___x_2610_);
lean_dec_ref(v___x_2609_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(lean_object* v_out_2618_, lean_object* v_inst_2619_, lean_object* v_R_2620_, lean_object* v_a_2621_, lean_object* v_b_2622_){
_start:
{
lean_object* v___x_2623_; 
v___x_2623_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_2618_, v_a_2621_, v_b_2622_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___boxed(lean_object* v_out_2624_, lean_object* v_inst_2625_, lean_object* v_R_2626_, lean_object* v_a_2627_, lean_object* v_b_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(v_out_2624_, v_inst_2625_, v_R_2626_, v_a_2627_, v_b_2628_);
lean_dec_ref(v_out_2624_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(lean_object* v___x_2630_, lean_object* v___x_2631_, lean_object* v___x_2632_, lean_object* v_inst_2633_, lean_object* v_R_2634_, lean_object* v_a_2635_, lean_object* v_b_2636_, lean_object* v_c_2637_){
_start:
{
lean_object* v___x_2638_; 
v___x_2638_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2630_, v___x_2631_, v___x_2632_, v_a_2635_, v_b_2636_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___boxed(lean_object* v___x_2639_, lean_object* v___x_2640_, lean_object* v___x_2641_, lean_object* v_inst_2642_, lean_object* v_R_2643_, lean_object* v_a_2644_, lean_object* v_b_2645_, lean_object* v_c_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(v___x_2639_, v___x_2640_, v___x_2641_, v_inst_2642_, v_R_2643_, v_a_2644_, v_b_2645_, v_c_2646_);
lean_dec_ref(v___x_2640_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(lean_object* v___x_2648_, lean_object* v___x_2649_, lean_object* v___x_2650_, lean_object* v_inst_2651_, lean_object* v_R_2652_, lean_object* v_a_2653_, lean_object* v_b_2654_, lean_object* v_c_2655_){
_start:
{
lean_object* v___x_2656_; 
v___x_2656_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2649_, v___x_2650_, v_a_2653_, v_b_2654_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___boxed(lean_object* v___x_2657_, lean_object* v___x_2658_, lean_object* v___x_2659_, lean_object* v_inst_2660_, lean_object* v_R_2661_, lean_object* v_a_2662_, lean_object* v_b_2663_, lean_object* v_c_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(v___x_2657_, v___x_2658_, v___x_2659_, v_inst_2660_, v_R_2661_, v_a_2662_, v_b_2663_, v_c_2664_);
lean_dec(v___x_2659_);
lean_dec_ref(v___x_2658_);
lean_dec_ref(v___x_2657_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(lean_object* v___x_2666_, lean_object* v___x_2667_, lean_object* v___x_2668_, lean_object* v_inst_2669_, lean_object* v_R_2670_, lean_object* v_a_2671_, lean_object* v_b_2672_, lean_object* v_c_2673_){
_start:
{
lean_object* v___x_2674_; 
v___x_2674_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2666_, v___x_2667_, v___x_2668_, v_a_2671_, v_b_2672_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___boxed(lean_object* v___x_2675_, lean_object* v___x_2676_, lean_object* v___x_2677_, lean_object* v_inst_2678_, lean_object* v_R_2679_, lean_object* v_a_2680_, lean_object* v_b_2681_, lean_object* v_c_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(v___x_2675_, v___x_2676_, v___x_2677_, v_inst_2678_, v_R_2679_, v_a_2680_, v_b_2681_, v_c_2682_);
lean_dec_ref(v___x_2676_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(lean_object* v_config_2687_, lean_object* v_a_2688_){
_start:
{
lean_object* v_maxFragmentLength_2689_; lean_object* v___f_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v_snd_2693_; lean_object* v_fst_2694_; lean_object* v_fst_2695_; lean_object* v_array_2696_; lean_object* v_idx_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2721_; 
v_maxFragmentLength_2689_ = lean_ctor_get(v_config_2687_, 5);
v___f_2690_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2691_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2688_);
v___x_2692_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2690_, v_maxFragmentLength_2689_, v___x_2691_, v_a_2688_);
v_snd_2693_ = lean_ctor_get(v___x_2692_, 1);
lean_inc(v_snd_2693_);
v_fst_2694_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_fst_2694_);
lean_dec_ref(v___x_2692_);
v_fst_2695_ = lean_ctor_get(v_snd_2693_, 0);
lean_inc(v_fst_2695_);
lean_dec(v_snd_2693_);
v_array_2696_ = lean_ctor_get(v_a_2688_, 0);
v_idx_2697_ = lean_ctor_get(v_a_2688_, 1);
v_isSharedCheck_2721_ = !lean_is_exclusive(v_a_2688_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2699_ = v_a_2688_;
v_isShared_2700_ = v_isSharedCheck_2721_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_idx_2697_);
lean_inc(v_array_2696_);
lean_dec(v_a_2688_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2721_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v_lower_2702_; lean_object* v_upper_2703_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___y_2718_; uint8_t v___x_2720_; 
v___x_2715_ = lean_nat_add(v_idx_2697_, v_fst_2694_);
lean_dec(v_fst_2694_);
v___x_2716_ = lean_byte_array_size(v_array_2696_);
v___x_2720_ = lean_nat_dec_le(v_idx_2697_, v___x_2691_);
if (v___x_2720_ == 0)
{
v___y_2718_ = v_idx_2697_;
goto v___jp_2717_;
}
else
{
lean_dec(v_idx_2697_);
v___y_2718_ = v___x_2691_;
goto v___jp_2717_;
}
v___jp_2701_:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2704_ = l_ByteArray_toByteSlice(v_array_2696_, v_lower_2702_, v_upper_2703_);
v___x_2705_ = l_ByteSlice_toByteArray(v___x_2704_);
v___x_2706_ = l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(v___x_2705_);
if (lean_obj_tag(v___x_2706_) == 1)
{
lean_object* v_val_2707_; lean_object* v___x_2709_; 
v_val_2707_ = lean_ctor_get(v___x_2706_, 0);
lean_inc(v_val_2707_);
lean_dec_ref_known(v___x_2706_, 1);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 1, v_val_2707_);
lean_ctor_set(v___x_2699_, 0, v_fst_2695_);
v___x_2709_ = v___x_2699_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_fst_2695_);
lean_ctor_set(v_reuseFailAlloc_2710_, 1, v_val_2707_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
else
{
lean_object* v___x_2711_; lean_object* v___x_2713_; 
lean_dec(v___x_2706_);
v___x_2711_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1));
if (v_isShared_2700_ == 0)
{
lean_ctor_set_tag(v___x_2699_, 1);
lean_ctor_set(v___x_2699_, 1, v___x_2711_);
lean_ctor_set(v___x_2699_, 0, v_fst_2695_);
v___x_2713_ = v___x_2699_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_fst_2695_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v___x_2711_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
v___jp_2717_:
{
uint8_t v___x_2719_; 
v___x_2719_ = lean_nat_dec_le(v___x_2715_, v___x_2716_);
if (v___x_2719_ == 0)
{
lean_dec(v___x_2715_);
v_lower_2702_ = v___y_2718_;
v_upper_2703_ = v___x_2716_;
goto v___jp_2701_;
}
else
{
v_lower_2702_ = v___y_2718_;
v_upper_2703_ = v___x_2715_;
goto v___jp_2701_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___boxed(lean_object* v_config_2722_, lean_object* v_a_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2722_, v_a_2723_);
lean_dec_ref(v_config_2722_);
return v_res_2724_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1(void){
_start:
{
lean_object* v___x_2726_; lean_object* v_utf8_2727_; 
v___x_2726_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0));
v_utf8_2727_ = lean_string_to_utf8(v___x_2726_);
return v_utf8_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(lean_object* v_config_2728_, lean_object* v_a_2729_){
_start:
{
uint8_t v___y_2731_; lean_object* v_pos_2732_; lean_object* v_res_2733_; lean_object* v___y_2755_; uint8_t v___y_2756_; lean_object* v_err_2757_; lean_object* v_pos_2763_; lean_object* v_utf8_2771_; lean_object* v___x_2772_; 
v_utf8_2771_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1);
lean_inc_ref(v_a_2729_);
v___x_2772_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_2771_, v_a_2729_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_pos_2773_; 
lean_dec_ref(v_a_2729_);
v_pos_2773_ = lean_ctor_get(v___x_2772_, 0);
lean_inc(v_pos_2773_);
lean_dec_ref_known(v___x_2772_, 2);
v_pos_2763_ = v_pos_2773_;
goto v___jp_2762_;
}
else
{
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_pos_2774_; 
lean_dec_ref(v_a_2729_);
v_pos_2774_ = lean_ctor_get(v___x_2772_, 0);
lean_inc(v_pos_2774_);
lean_dec_ref_known(v___x_2772_, 2);
v_pos_2763_ = v_pos_2774_;
goto v___jp_2762_;
}
else
{
lean_object* v_err_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2806_; 
v_err_2775_ = lean_ctor_get(v___x_2772_, 1);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2806_ == 0)
{
lean_object* v_unused_2807_; 
v_unused_2807_ = lean_ctor_get(v___x_2772_, 0);
lean_dec(v_unused_2807_);
v___x_2777_ = v___x_2772_;
v_isShared_2778_ = v_isSharedCheck_2806_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_err_2775_);
lean_dec(v___x_2772_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2806_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v_idx_2779_; uint8_t v___x_2780_; 
v_idx_2779_ = lean_ctor_get(v_a_2729_, 1);
v___x_2780_ = lean_nat_dec_eq(v_idx_2779_, v_idx_2779_);
if (v___x_2780_ == 0)
{
lean_object* v___x_2782_; 
lean_dec_ref(v_config_2728_);
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 0, v_a_2729_);
v___x_2782_ = v___x_2777_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2729_);
lean_ctor_set(v_reuseFailAlloc_2783_, 1, v_err_2775_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
else
{
uint8_t v___x_2784_; lean_object* v___x_2785_; 
lean_del_object(v___x_2777_);
lean_dec(v_err_2775_);
v___x_2784_ = 0;
v___x_2785_ = l_Std_Http_URI_Parser_parsePath(v_config_2728_, v___x_2784_, v___x_2780_, v_a_2729_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_pos_2786_; lean_object* v_res_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2796_; 
v_pos_2786_ = lean_ctor_get(v___x_2785_, 0);
v_res_2787_ = lean_ctor_get(v___x_2785_, 1);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2789_ = v___x_2785_;
v_isShared_2790_ = v_isSharedCheck_2796_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_res_2787_);
lean_inc(v_pos_2786_);
lean_dec(v___x_2785_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2796_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2794_; 
v___x_2791_ = lean_box(0);
v___x_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2791_);
lean_ctor_set(v___x_2792_, 1, v_res_2787_);
if (v_isShared_2790_ == 0)
{
lean_ctor_set(v___x_2789_, 1, v___x_2792_);
v___x_2794_ = v___x_2789_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_pos_2786_);
lean_ctor_set(v_reuseFailAlloc_2795_, 1, v___x_2792_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
else
{
lean_object* v_pos_2797_; lean_object* v_err_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2805_; 
v_pos_2797_ = lean_ctor_get(v___x_2785_, 0);
v_err_2798_ = lean_ctor_get(v___x_2785_, 1);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2800_ = v___x_2785_;
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_err_2798_);
lean_inc(v_pos_2797_);
lean_dec(v___x_2785_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2803_; 
if (v_isShared_2801_ == 0)
{
v___x_2803_ = v___x_2800_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_pos_2797_);
lean_ctor_set(v_reuseFailAlloc_2804_, 1, v_err_2798_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
}
}
}
v___jp_2730_:
{
lean_object* v___x_2734_; 
v___x_2734_ = l_Std_Http_URI_Parser_parsePath(v_config_2728_, v___y_2731_, v___y_2731_, v_pos_2732_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_pos_2735_; lean_object* v_res_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2744_; 
v_pos_2735_ = lean_ctor_get(v___x_2734_, 0);
v_res_2736_ = lean_ctor_get(v___x_2734_, 1);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2738_ = v___x_2734_;
v_isShared_2739_ = v_isSharedCheck_2744_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_res_2736_);
lean_inc(v_pos_2735_);
lean_dec(v___x_2734_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2744_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2740_; lean_object* v___x_2742_; 
v___x_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2740_, 0, v_res_2733_);
lean_ctor_set(v___x_2740_, 1, v_res_2736_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 1, v___x_2740_);
v___x_2742_ = v___x_2738_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_pos_2735_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v___x_2740_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
else
{
lean_object* v_pos_2745_; lean_object* v_err_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_dec(v_res_2733_);
v_pos_2745_ = lean_ctor_get(v___x_2734_, 0);
v_err_2746_ = lean_ctor_get(v___x_2734_, 1);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2734_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_err_2746_);
lean_inc(v_pos_2745_);
lean_dec(v___x_2734_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_pos_2745_);
lean_ctor_set(v_reuseFailAlloc_2752_, 1, v_err_2746_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
v___jp_2754_:
{
lean_object* v_idx_2758_; uint8_t v___x_2759_; 
v_idx_2758_ = lean_ctor_get(v___y_2755_, 1);
v___x_2759_ = lean_nat_dec_eq(v_idx_2758_, v_idx_2758_);
if (v___x_2759_ == 0)
{
lean_object* v___x_2760_; 
lean_dec_ref(v_config_2728_);
v___x_2760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___y_2755_);
lean_ctor_set(v___x_2760_, 1, v_err_2757_);
return v___x_2760_;
}
else
{
lean_object* v___x_2761_; 
lean_dec(v_err_2757_);
v___x_2761_ = lean_box(0);
v___y_2731_ = v___y_2756_;
v_pos_2732_ = v___y_2755_;
v_res_2733_ = v___x_2761_;
goto v___jp_2730_;
}
}
v___jp_2762_:
{
uint8_t v___x_2764_; lean_object* v___x_2765_; 
v___x_2764_ = 1;
lean_inc_ref(v_pos_2763_);
v___x_2765_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_2728_, v_pos_2763_);
if (lean_obj_tag(v___x_2765_) == 0)
{
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_pos_2766_; lean_object* v_res_2767_; lean_object* v___x_2768_; 
lean_dec_ref(v_pos_2763_);
v_pos_2766_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_pos_2766_);
v_res_2767_ = lean_ctor_get(v___x_2765_, 1);
lean_inc(v_res_2767_);
lean_dec_ref_known(v___x_2765_, 2);
v___x_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2768_, 0, v_res_2767_);
v___y_2731_ = v___x_2764_;
v_pos_2732_ = v_pos_2766_;
v_res_2733_ = v___x_2768_;
goto v___jp_2730_;
}
else
{
lean_object* v_err_2769_; 
v_err_2769_ = lean_ctor_get(v___x_2765_, 1);
lean_inc(v_err_2769_);
lean_dec_ref_known(v___x_2765_, 2);
v___y_2755_ = v_pos_2763_;
v___y_2756_ = v___x_2764_;
v_err_2757_ = v_err_2769_;
goto v___jp_2754_;
}
}
else
{
lean_object* v_err_2770_; 
v_err_2770_ = lean_ctor_get(v___x_2765_, 1);
lean_inc(v_err_2770_);
lean_dec_ref_known(v___x_2765_, 2);
v___y_2755_ = v_pos_2763_;
v___y_2756_ = v___x_2764_;
v_err_2757_ = v_err_2770_;
goto v___jp_2754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURI(lean_object* v_config_2817_, lean_object* v_a_2818_){
_start:
{
lean_object* v___x_2819_; 
v___x_2819_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_2817_, v_a_2818_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_pos_2820_; lean_object* v_res_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2952_; 
v_pos_2820_ = lean_ctor_get(v___x_2819_, 0);
v_res_2821_ = lean_ctor_get(v___x_2819_, 1);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2823_ = v___x_2819_;
v_isShared_2824_ = v_isSharedCheck_2952_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_res_2821_);
lean_inc(v_pos_2820_);
lean_dec(v___x_2819_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2952_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v_array_2825_; lean_object* v_idx_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; 
v_array_2825_ = lean_ctor_get(v_pos_2820_, 0);
v_idx_2826_ = lean_ctor_get(v_pos_2820_, 1);
v___x_2827_ = lean_byte_array_size(v_array_2825_);
v___x_2828_ = lean_nat_dec_lt(v_idx_2826_, v___x_2827_);
if (v___x_2828_ == 0)
{
lean_object* v___x_2829_; lean_object* v___x_2831_; 
lean_dec(v_res_2821_);
lean_dec_ref(v_config_2817_);
v___x_2829_ = lean_box(0);
if (v_isShared_2824_ == 0)
{
lean_ctor_set_tag(v___x_2823_, 1);
lean_ctor_set(v___x_2823_, 1, v___x_2829_);
v___x_2831_ = v___x_2823_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_pos_2820_);
lean_ctor_set(v_reuseFailAlloc_2832_, 1, v___x_2829_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
else
{
uint8_t v___x_2833_; uint8_t v_got_2834_; uint8_t v___x_2835_; 
v___x_2833_ = 58;
v_got_2834_ = lean_byte_array_fget(v_array_2825_, v_idx_2826_);
v___x_2835_ = lean_uint8_dec_eq(v_got_2834_, v___x_2833_);
if (v___x_2835_ == 0)
{
lean_object* v___x_2836_; lean_object* v___x_2838_; 
lean_dec(v_res_2821_);
lean_dec_ref(v_config_2817_);
v___x_2836_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_2824_ == 0)
{
lean_ctor_set_tag(v___x_2823_, 1);
lean_ctor_set(v___x_2823_, 1, v___x_2836_);
v___x_2838_ = v___x_2823_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_pos_2820_);
lean_ctor_set(v_reuseFailAlloc_2839_, 1, v___x_2836_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
else
{
lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2949_; 
lean_inc(v_idx_2826_);
lean_inc_ref(v_array_2825_);
v_isSharedCheck_2949_ = !lean_is_exclusive(v_pos_2820_);
if (v_isSharedCheck_2949_ == 0)
{
lean_object* v_unused_2950_; lean_object* v_unused_2951_; 
v_unused_2950_ = lean_ctor_get(v_pos_2820_, 1);
lean_dec(v_unused_2950_);
v_unused_2951_ = lean_ctor_get(v_pos_2820_, 0);
lean_dec(v_unused_2951_);
v___x_2841_ = v_pos_2820_;
v_isShared_2842_ = v_isSharedCheck_2949_;
goto v_resetjp_2840_;
}
else
{
lean_dec(v_pos_2820_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2949_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2846_; 
v___x_2843_ = lean_unsigned_to_nat(1u);
v___x_2844_ = lean_nat_add(v_idx_2826_, v___x_2843_);
lean_dec(v_idx_2826_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 1, v___x_2844_);
v___x_2846_ = v___x_2841_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_array_2825_);
lean_ctor_set(v_reuseFailAlloc_2948_, 1, v___x_2844_);
v___x_2846_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
lean_object* v___x_2847_; 
lean_inc_ref(v_config_2817_);
v___x_2847_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2817_, v___x_2846_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_res_2848_; lean_object* v_pos_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2938_; 
v_res_2848_ = lean_ctor_get(v___x_2847_, 1);
v_pos_2849_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2851_ = v___x_2847_;
v_isShared_2852_ = v_isSharedCheck_2938_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_res_2848_);
lean_inc(v_pos_2849_);
lean_dec(v___x_2847_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2938_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v_fst_2853_; lean_object* v_snd_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2937_; 
v_fst_2853_ = lean_ctor_get(v_res_2848_, 0);
v_snd_2854_ = lean_ctor_get(v_res_2848_, 1);
v_isSharedCheck_2937_ = !lean_is_exclusive(v_res_2848_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2856_ = v_res_2848_;
v_isShared_2857_ = v_isSharedCheck_2937_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_snd_2854_);
lean_inc(v_fst_2853_);
lean_dec(v_res_2848_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2937_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___y_2859_; lean_object* v_pos_2860_; lean_object* v_res_2861_; lean_object* v_idx_2867_; lean_object* v___y_2868_; lean_object* v_pos_2869_; lean_object* v_err_2870_; lean_object* v_pos_2878_; lean_object* v_array_2879_; lean_object* v_idx_2880_; lean_object* v_res_2881_; lean_object* v_array_2900_; lean_object* v_idx_2901_; lean_object* v_pos_2903_; lean_object* v_array_2904_; lean_object* v_idx_2905_; lean_object* v_err_2906_; lean_object* v___x_2910_; uint8_t v___x_2911_; 
v_array_2900_ = lean_ctor_get(v_pos_2849_, 0);
lean_inc_ref(v_array_2900_);
v_idx_2901_ = lean_ctor_get(v_pos_2849_, 1);
lean_inc(v_idx_2901_);
v___x_2910_ = lean_byte_array_size(v_array_2900_);
v___x_2911_ = lean_nat_dec_lt(v_idx_2901_, v___x_2910_);
if (v___x_2911_ == 0)
{
lean_object* v___x_2912_; 
v___x_2912_ = lean_box(0);
lean_inc(v_idx_2901_);
v_pos_2903_ = v_pos_2849_;
v_array_2904_ = v_array_2900_;
v_idx_2905_ = v_idx_2901_;
v_err_2906_ = v___x_2912_;
goto v___jp_2902_;
}
else
{
uint8_t v___x_2913_; uint8_t v_got_2914_; uint8_t v___x_2915_; 
v___x_2913_ = 63;
v_got_2914_ = lean_byte_array_fget(v_array_2900_, v_idx_2901_);
v___x_2915_ = lean_uint8_dec_eq(v_got_2914_, v___x_2913_);
if (v___x_2915_ == 0)
{
lean_object* v___x_2916_; 
v___x_2916_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_2901_);
v_pos_2903_ = v_pos_2849_;
v_array_2904_ = v_array_2900_;
v_idx_2905_ = v_idx_2901_;
v_err_2906_ = v___x_2916_;
goto v___jp_2902_;
}
else
{
lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2934_; 
v_isSharedCheck_2934_ = !lean_is_exclusive(v_pos_2849_);
if (v_isSharedCheck_2934_ == 0)
{
lean_object* v_unused_2935_; lean_object* v_unused_2936_; 
v_unused_2935_ = lean_ctor_get(v_pos_2849_, 1);
lean_dec(v_unused_2935_);
v_unused_2936_ = lean_ctor_get(v_pos_2849_, 0);
lean_dec(v_unused_2936_);
v___x_2918_ = v_pos_2849_;
v_isShared_2919_ = v_isSharedCheck_2934_;
goto v_resetjp_2917_;
}
else
{
lean_dec(v_pos_2849_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2934_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2920_; lean_object* v___x_2922_; 
v___x_2920_ = lean_nat_add(v_idx_2901_, v___x_2843_);
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 1, v___x_2920_);
v___x_2922_ = v___x_2918_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_array_2900_);
lean_ctor_set(v_reuseFailAlloc_2933_, 1, v___x_2920_);
v___x_2922_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
lean_object* v___x_2923_; 
lean_inc_ref(v_config_2817_);
v___x_2923_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2817_, v___x_2922_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v_pos_2924_; lean_object* v_res_2925_; lean_object* v_array_2926_; lean_object* v_idx_2927_; lean_object* v___x_2928_; 
lean_dec(v_idx_2901_);
v_pos_2924_ = lean_ctor_get(v___x_2923_, 0);
lean_inc(v_pos_2924_);
v_res_2925_ = lean_ctor_get(v___x_2923_, 1);
lean_inc(v_res_2925_);
lean_dec_ref_known(v___x_2923_, 2);
v_array_2926_ = lean_ctor_get(v_pos_2924_, 0);
lean_inc_ref(v_array_2926_);
v_idx_2927_ = lean_ctor_get(v_pos_2924_, 1);
lean_inc(v_idx_2927_);
v___x_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2928_, 0, v_res_2925_);
v_pos_2878_ = v_pos_2924_;
v_array_2879_ = v_array_2926_;
v_idx_2880_ = v_idx_2927_;
v_res_2881_ = v___x_2928_;
goto v___jp_2877_;
}
else
{
lean_object* v_pos_2929_; lean_object* v_err_2930_; lean_object* v_array_2931_; lean_object* v_idx_2932_; 
v_pos_2929_ = lean_ctor_get(v___x_2923_, 0);
lean_inc(v_pos_2929_);
v_err_2930_ = lean_ctor_get(v___x_2923_, 1);
lean_inc(v_err_2930_);
lean_dec_ref_known(v___x_2923_, 2);
v_array_2931_ = lean_ctor_get(v_pos_2929_, 0);
lean_inc_ref(v_array_2931_);
v_idx_2932_ = lean_ctor_get(v_pos_2929_, 1);
lean_inc(v_idx_2932_);
v_pos_2903_ = v_pos_2929_;
v_array_2904_ = v_array_2931_;
v_idx_2905_ = v_idx_2932_;
v_err_2906_ = v_err_2930_;
goto v___jp_2902_;
}
}
}
}
}
v___jp_2858_:
{
lean_object* v___x_2862_; lean_object* v___x_2864_; 
v___x_2862_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2862_, 0, v_res_2821_);
lean_ctor_set(v___x_2862_, 1, v_fst_2853_);
lean_ctor_set(v___x_2862_, 2, v_snd_2854_);
lean_ctor_set(v___x_2862_, 3, v___y_2859_);
lean_ctor_set(v___x_2862_, 4, v_res_2861_);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 1, v___x_2862_);
lean_ctor_set(v___x_2851_, 0, v_pos_2860_);
v___x_2864_ = v___x_2851_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_pos_2860_);
lean_ctor_set(v_reuseFailAlloc_2865_, 1, v___x_2862_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
v___jp_2866_:
{
lean_object* v_idx_2871_; uint8_t v___x_2872_; 
v_idx_2871_ = lean_ctor_get(v_pos_2869_, 1);
v___x_2872_ = lean_nat_dec_eq(v_idx_2867_, v_idx_2871_);
lean_dec(v_idx_2867_);
if (v___x_2872_ == 0)
{
lean_object* v___x_2874_; 
lean_dec(v___y_2868_);
lean_dec(v_snd_2854_);
lean_dec(v_fst_2853_);
lean_del_object(v___x_2851_);
lean_dec(v_res_2821_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set_tag(v___x_2823_, 1);
lean_ctor_set(v___x_2823_, 1, v_err_2870_);
lean_ctor_set(v___x_2823_, 0, v_pos_2869_);
v___x_2874_ = v___x_2823_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_pos_2869_);
lean_ctor_set(v_reuseFailAlloc_2875_, 1, v_err_2870_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
else
{
lean_object* v___x_2876_; 
lean_dec(v_err_2870_);
lean_del_object(v___x_2823_);
v___x_2876_ = lean_box(0);
v___y_2859_ = v___y_2868_;
v_pos_2860_ = v_pos_2869_;
v_res_2861_ = v___x_2876_;
goto v___jp_2858_;
}
}
v___jp_2877_:
{
lean_object* v___x_2882_; uint8_t v___x_2883_; 
v___x_2882_ = lean_byte_array_size(v_array_2879_);
v___x_2883_ = lean_nat_dec_lt(v_idx_2880_, v___x_2882_);
if (v___x_2883_ == 0)
{
lean_object* v___x_2884_; 
lean_dec_ref(v_array_2879_);
lean_del_object(v___x_2856_);
lean_dec_ref(v_config_2817_);
v___x_2884_ = lean_box(0);
v_idx_2867_ = v_idx_2880_;
v___y_2868_ = v_res_2881_;
v_pos_2869_ = v_pos_2878_;
v_err_2870_ = v___x_2884_;
goto v___jp_2866_;
}
else
{
uint8_t v___x_2885_; uint8_t v_got_2886_; uint8_t v___x_2887_; 
v___x_2885_ = 35;
v_got_2886_ = lean_byte_array_fget(v_array_2879_, v_idx_2880_);
v___x_2887_ = lean_uint8_dec_eq(v_got_2886_, v___x_2885_);
if (v___x_2887_ == 0)
{
lean_object* v___x_2888_; 
lean_dec_ref(v_array_2879_);
lean_del_object(v___x_2856_);
lean_dec_ref(v_config_2817_);
v___x_2888_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v_idx_2867_ = v_idx_2880_;
v___y_2868_ = v_res_2881_;
v_pos_2869_ = v_pos_2878_;
v_err_2870_ = v___x_2888_;
goto v___jp_2866_;
}
else
{
lean_object* v___x_2889_; lean_object* v___x_2891_; 
lean_dec_ref(v_pos_2878_);
v___x_2889_ = lean_nat_add(v_idx_2880_, v___x_2843_);
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 1, v___x_2889_);
lean_ctor_set(v___x_2856_, 0, v_array_2879_);
v___x_2891_ = v___x_2856_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_array_2879_);
lean_ctor_set(v_reuseFailAlloc_2899_, 1, v___x_2889_);
v___x_2891_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
lean_object* v___x_2892_; 
v___x_2892_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2817_, v___x_2891_);
lean_dec_ref(v_config_2817_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_pos_2893_; lean_object* v_res_2894_; lean_object* v___x_2895_; 
v_pos_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_pos_2893_);
v_res_2894_ = lean_ctor_get(v___x_2892_, 1);
lean_inc(v_res_2894_);
lean_dec_ref_known(v___x_2892_, 2);
v___x_2895_ = l_Std_Http_URI_EncodedFragment_decode(v_res_2894_);
lean_dec(v_res_2894_);
if (lean_obj_tag(v___x_2895_) == 1)
{
lean_dec(v_idx_2880_);
lean_del_object(v___x_2823_);
v___y_2859_ = v_res_2881_;
v_pos_2860_ = v_pos_2893_;
v_res_2861_ = v___x_2895_;
goto v___jp_2858_;
}
else
{
lean_object* v___x_2896_; 
lean_dec(v___x_2895_);
v___x_2896_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__3));
v_idx_2867_ = v_idx_2880_;
v___y_2868_ = v_res_2881_;
v_pos_2869_ = v_pos_2893_;
v_err_2870_ = v___x_2896_;
goto v___jp_2866_;
}
}
else
{
lean_object* v_pos_2897_; lean_object* v_err_2898_; 
v_pos_2897_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_pos_2897_);
v_err_2898_ = lean_ctor_get(v___x_2892_, 1);
lean_inc(v_err_2898_);
lean_dec_ref_known(v___x_2892_, 2);
v_idx_2867_ = v_idx_2880_;
v___y_2868_ = v_res_2881_;
v_pos_2869_ = v_pos_2897_;
v_err_2870_ = v_err_2898_;
goto v___jp_2866_;
}
}
}
}
}
v___jp_2902_:
{
uint8_t v___x_2907_; 
v___x_2907_ = lean_nat_dec_eq(v_idx_2901_, v_idx_2905_);
lean_dec(v_idx_2901_);
if (v___x_2907_ == 0)
{
lean_object* v___x_2908_; 
lean_dec(v_idx_2905_);
lean_dec_ref(v_array_2904_);
lean_del_object(v___x_2856_);
lean_dec(v_snd_2854_);
lean_dec(v_fst_2853_);
lean_del_object(v___x_2851_);
lean_del_object(v___x_2823_);
lean_dec(v_res_2821_);
lean_dec_ref(v_config_2817_);
v___x_2908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2908_, 0, v_pos_2903_);
lean_ctor_set(v___x_2908_, 1, v_err_2906_);
return v___x_2908_;
}
else
{
lean_object* v___x_2909_; 
lean_dec(v_err_2906_);
v___x_2909_ = lean_box(0);
v_pos_2878_ = v_pos_2903_;
v_array_2879_ = v_array_2904_;
v_idx_2880_ = v_idx_2905_;
v_res_2881_ = v___x_2909_;
goto v___jp_2877_;
}
}
}
}
}
else
{
lean_object* v_pos_2939_; lean_object* v_err_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2947_; 
lean_del_object(v___x_2823_);
lean_dec(v_res_2821_);
lean_dec_ref(v_config_2817_);
v_pos_2939_ = lean_ctor_get(v___x_2847_, 0);
v_err_2940_ = lean_ctor_get(v___x_2847_, 1);
v_isSharedCheck_2947_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2942_ = v___x_2847_;
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_err_2940_);
lean_inc(v_pos_2939_);
lean_dec(v___x_2847_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2945_; 
if (v_isShared_2943_ == 0)
{
v___x_2945_ = v___x_2942_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_pos_2939_);
lean_ctor_set(v_reuseFailAlloc_2946_, 1, v_err_2940_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
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
lean_object* v_pos_2953_; lean_object* v_err_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
lean_dec_ref(v_config_2817_);
v_pos_2953_ = lean_ctor_get(v___x_2819_, 0);
v_err_2954_ = lean_ctor_get(v___x_2819_, 1);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2956_ = v___x_2819_;
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_err_2954_);
lean_inc(v_pos_2953_);
lean_dec(v___x_2819_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_pos_2953_);
lean_ctor_set(v_reuseFailAlloc_2960_, 1, v_err_2954_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(lean_object* v_a_2965_){
_start:
{
lean_object* v_array_2966_; lean_object* v_idx_2967_; lean_object* v___x_2968_; uint8_t v___x_2969_; 
v_array_2966_ = lean_ctor_get(v_a_2965_, 0);
v_idx_2967_ = lean_ctor_get(v_a_2965_, 1);
v___x_2968_ = lean_byte_array_size(v_array_2966_);
v___x_2969_ = lean_nat_dec_lt(v_idx_2967_, v___x_2968_);
if (v___x_2969_ == 0)
{
lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2970_ = lean_box(0);
v___x_2971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2971_, 0, v_a_2965_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
return v___x_2971_;
}
else
{
uint8_t v___x_2972_; uint8_t v_got_2973_; uint8_t v___x_2974_; 
v___x_2972_ = 42;
v_got_2973_ = lean_byte_array_fget(v_array_2966_, v_idx_2967_);
v___x_2974_ = lean_uint8_dec_eq(v_got_2973_, v___x_2972_);
if (v___x_2974_ == 0)
{
lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2975_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1));
v___x_2976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2976_, 0, v_a_2965_);
lean_ctor_set(v___x_2976_, 1, v___x_2975_);
return v___x_2976_;
}
else
{
lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2987_; 
lean_inc(v_idx_2967_);
lean_inc_ref(v_array_2966_);
v_isSharedCheck_2987_ = !lean_is_exclusive(v_a_2965_);
if (v_isSharedCheck_2987_ == 0)
{
lean_object* v_unused_2988_; lean_object* v_unused_2989_; 
v_unused_2988_ = lean_ctor_get(v_a_2965_, 1);
lean_dec(v_unused_2988_);
v_unused_2989_ = lean_ctor_get(v_a_2965_, 0);
lean_dec(v_unused_2989_);
v___x_2978_ = v_a_2965_;
v_isShared_2979_ = v_isSharedCheck_2987_;
goto v_resetjp_2977_;
}
else
{
lean_dec(v_a_2965_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2987_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2983_; 
v___x_2980_ = lean_unsigned_to_nat(1u);
v___x_2981_ = lean_nat_add(v_idx_2967_, v___x_2980_);
lean_dec(v_idx_2967_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 1, v___x_2981_);
v___x_2983_ = v___x_2978_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_array_2966_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v___x_2981_);
v___x_2983_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = lean_box(3);
v___x_2985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2983_);
lean_ctor_set(v___x_2985_, 1, v___x_2984_);
return v___x_2985_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(lean_object* v_config_2993_, lean_object* v_a_2994_){
_start:
{
lean_object* v_array_2998_; lean_object* v_idx_2999_; lean_object* v___x_3000_; uint8_t v___x_3001_; 
v_array_2998_ = lean_ctor_get(v_a_2994_, 0);
v_idx_2999_ = lean_ctor_get(v_a_2994_, 1);
v___x_3000_ = lean_byte_array_size(v_array_2998_);
v___x_3001_ = lean_nat_dec_lt(v_idx_2999_, v___x_3000_);
if (v___x_3001_ == 0)
{
lean_dec_ref(v_config_2993_);
goto v___jp_2995_;
}
else
{
uint8_t v___x_3002_; uint8_t v___x_3003_; uint8_t v___x_3004_; 
v___x_3002_ = lean_byte_array_fget(v_array_2998_, v_idx_2999_);
v___x_3003_ = 47;
v___x_3004_ = lean_uint8_dec_eq(v___x_3002_, v___x_3003_);
if (v___x_3004_ == 0)
{
lean_dec_ref(v_config_2993_);
goto v___jp_2995_;
}
else
{
lean_object* v___x_3005_; 
lean_inc_ref(v_a_2994_);
lean_inc_ref(v_config_2993_);
v___x_3005_ = l_Std_Http_URI_Parser_parsePath(v_config_2993_, v___x_3004_, v___x_3004_, v_a_2994_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_pos_3006_; lean_object* v_res_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3052_; 
v_pos_3006_ = lean_ctor_get(v___x_3005_, 0);
v_res_3007_ = lean_ctor_get(v___x_3005_, 1);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3009_ = v___x_3005_;
v_isShared_3010_ = v_isSharedCheck_3052_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_res_3007_);
lean_inc(v_pos_3006_);
lean_dec(v___x_3005_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3052_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v_pos_3012_; lean_object* v_res_3013_; lean_object* v_array_3018_; lean_object* v_idx_3019_; lean_object* v_pos_3021_; lean_object* v_idx_3022_; lean_object* v_err_3023_; lean_object* v___x_3027_; uint8_t v___x_3028_; 
v_array_3018_ = lean_ctor_get(v_pos_3006_, 0);
v_idx_3019_ = lean_ctor_get(v_pos_3006_, 1);
lean_inc(v_idx_3019_);
v___x_3027_ = lean_byte_array_size(v_array_3018_);
v___x_3028_ = lean_nat_dec_lt(v_idx_3019_, v___x_3027_);
if (v___x_3028_ == 0)
{
lean_object* v___x_3029_; 
lean_dec_ref(v_config_2993_);
v___x_3029_ = lean_box(0);
lean_inc(v_idx_3019_);
v_pos_3021_ = v_pos_3006_;
v_idx_3022_ = v_idx_3019_;
v_err_3023_ = v___x_3029_;
goto v___jp_3020_;
}
else
{
uint8_t v___x_3030_; uint8_t v_got_3031_; uint8_t v___x_3032_; 
v___x_3030_ = 63;
v_got_3031_ = lean_byte_array_fget(v_array_3018_, v_idx_3019_);
v___x_3032_ = lean_uint8_dec_eq(v_got_3031_, v___x_3030_);
if (v___x_3032_ == 0)
{
lean_object* v___x_3033_; 
lean_dec_ref(v_config_2993_);
v___x_3033_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_3019_);
v_pos_3021_ = v_pos_3006_;
v_idx_3022_ = v_idx_3019_;
v_err_3023_ = v___x_3033_;
goto v___jp_3020_;
}
else
{
lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3049_; 
lean_inc_ref(v_array_3018_);
v_isSharedCheck_3049_ = !lean_is_exclusive(v_pos_3006_);
if (v_isSharedCheck_3049_ == 0)
{
lean_object* v_unused_3050_; lean_object* v_unused_3051_; 
v_unused_3050_ = lean_ctor_get(v_pos_3006_, 1);
lean_dec(v_unused_3050_);
v_unused_3051_ = lean_ctor_get(v_pos_3006_, 0);
lean_dec(v_unused_3051_);
v___x_3035_ = v_pos_3006_;
v_isShared_3036_ = v_isSharedCheck_3049_;
goto v_resetjp_3034_;
}
else
{
lean_dec(v_pos_3006_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3049_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3040_; 
v___x_3037_ = lean_unsigned_to_nat(1u);
v___x_3038_ = lean_nat_add(v_idx_3019_, v___x_3037_);
if (v_isShared_3036_ == 0)
{
lean_ctor_set(v___x_3035_, 1, v___x_3038_);
v___x_3040_ = v___x_3035_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_array_3018_);
lean_ctor_set(v_reuseFailAlloc_3048_, 1, v___x_3038_);
v___x_3040_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
lean_object* v___x_3041_; 
v___x_3041_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2993_, v___x_3040_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v_pos_3042_; lean_object* v_res_3043_; lean_object* v___x_3044_; 
lean_dec(v_idx_3019_);
lean_dec_ref(v_a_2994_);
v_pos_3042_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_pos_3042_);
v_res_3043_ = lean_ctor_get(v___x_3041_, 1);
lean_inc(v_res_3043_);
lean_dec_ref_known(v___x_3041_, 2);
v___x_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3044_, 0, v_res_3043_);
v_pos_3012_ = v_pos_3042_;
v_res_3013_ = v___x_3044_;
goto v___jp_3011_;
}
else
{
lean_object* v_pos_3045_; lean_object* v_err_3046_; lean_object* v_idx_3047_; 
v_pos_3045_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_pos_3045_);
v_err_3046_ = lean_ctor_get(v___x_3041_, 1);
lean_inc(v_err_3046_);
lean_dec_ref_known(v___x_3041_, 2);
v_idx_3047_ = lean_ctor_get(v_pos_3045_, 1);
lean_inc(v_idx_3047_);
v_pos_3021_ = v_pos_3045_;
v_idx_3022_ = v_idx_3047_;
v_err_3023_ = v_err_3046_;
goto v___jp_3020_;
}
}
}
}
}
v___jp_3011_:
{
lean_object* v___x_3014_; lean_object* v___x_3016_; 
v___x_3014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3014_, 0, v_res_3007_);
lean_ctor_set(v___x_3014_, 1, v_res_3013_);
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 1, v___x_3014_);
lean_ctor_set(v___x_3009_, 0, v_pos_3012_);
v___x_3016_ = v___x_3009_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_pos_3012_);
lean_ctor_set(v_reuseFailAlloc_3017_, 1, v___x_3014_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
v___jp_3020_:
{
uint8_t v___x_3024_; 
v___x_3024_ = lean_nat_dec_eq(v_idx_3019_, v_idx_3022_);
lean_dec(v_idx_3022_);
lean_dec(v_idx_3019_);
if (v___x_3024_ == 0)
{
lean_object* v___x_3025_; 
lean_dec_ref(v_pos_3021_);
lean_del_object(v___x_3009_);
lean_dec(v_res_3007_);
v___x_3025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3025_, 0, v_a_2994_);
lean_ctor_set(v___x_3025_, 1, v_err_3023_);
return v___x_3025_;
}
else
{
lean_object* v___x_3026_; 
lean_dec(v_err_3023_);
lean_dec_ref(v_a_2994_);
v___x_3026_ = lean_box(0);
v_pos_3012_ = v_pos_3021_;
v_res_3013_ = v___x_3026_;
goto v___jp_3011_;
}
}
}
}
else
{
lean_object* v_err_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
lean_dec_ref(v_config_2993_);
v_err_3053_ = lean_ctor_get(v___x_3005_, 1);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3060_ == 0)
{
lean_object* v_unused_3061_; 
v_unused_3061_ = lean_ctor_get(v___x_3005_, 0);
lean_dec(v_unused_3061_);
v___x_3055_ = v___x_3005_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_err_3053_);
lean_dec(v___x_3005_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
lean_ctor_set(v___x_3055_, 0, v_a_2994_);
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_2994_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v_err_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
}
v___jp_2995_:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2996_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1));
v___x_2997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2997_, 0, v_a_2994_);
lean_ctor_set(v___x_2997_, 1, v___x_2996_);
return v___x_2997_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(lean_object* v_config_3062_, lean_object* v_scheme_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v_array_3065_; lean_object* v_idx_3066_; lean_object* v___x_3067_; uint8_t v___x_3068_; 
v_array_3065_ = lean_ctor_get(v_a_3064_, 0);
v_idx_3066_ = lean_ctor_get(v_a_3064_, 1);
v___x_3067_ = lean_byte_array_size(v_array_3065_);
v___x_3068_ = lean_nat_dec_lt(v_idx_3066_, v___x_3067_);
if (v___x_3068_ == 0)
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
lean_dec_ref(v_scheme_3063_);
lean_dec_ref(v_config_3062_);
v___x_3069_ = lean_box(0);
v___x_3070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3070_, 0, v_a_3064_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
return v___x_3070_;
}
else
{
uint8_t v___x_3071_; uint8_t v_got_3072_; uint8_t v___x_3073_; 
v___x_3071_ = 58;
v_got_3072_ = lean_byte_array_fget(v_array_3065_, v_idx_3066_);
v___x_3073_ = lean_uint8_dec_eq(v_got_3072_, v___x_3071_);
if (v___x_3073_ == 0)
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
lean_dec_ref(v_scheme_3063_);
lean_dec_ref(v_config_3062_);
v___x_3074_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
v___x_3075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3075_, 0, v_a_3064_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
return v___x_3075_;
}
else
{
lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3150_; 
lean_inc(v_idx_3066_);
lean_inc_ref(v_array_3065_);
v_isSharedCheck_3150_ = !lean_is_exclusive(v_a_3064_);
if (v_isSharedCheck_3150_ == 0)
{
lean_object* v_unused_3151_; lean_object* v_unused_3152_; 
v_unused_3151_ = lean_ctor_get(v_a_3064_, 1);
lean_dec(v_unused_3151_);
v_unused_3152_ = lean_ctor_get(v_a_3064_, 0);
lean_dec(v_unused_3152_);
v___x_3077_ = v_a_3064_;
v_isShared_3078_ = v_isSharedCheck_3150_;
goto v_resetjp_3076_;
}
else
{
lean_dec(v_a_3064_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3150_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3082_; 
v___x_3079_ = lean_unsigned_to_nat(1u);
v___x_3080_ = lean_nat_add(v_idx_3066_, v___x_3079_);
lean_dec(v_idx_3066_);
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 1, v___x_3080_);
v___x_3082_ = v___x_3077_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_array_3065_);
lean_ctor_set(v_reuseFailAlloc_3149_, 1, v___x_3080_);
v___x_3082_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
lean_object* v___x_3083_; 
lean_inc_ref(v_config_3062_);
v___x_3083_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_3062_, v___x_3082_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_res_3084_; lean_object* v_pos_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3139_; 
v_res_3084_ = lean_ctor_get(v___x_3083_, 1);
v_pos_3085_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3087_ = v___x_3083_;
v_isShared_3088_ = v_isSharedCheck_3139_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_res_3084_);
lean_inc(v_pos_3085_);
lean_dec(v___x_3083_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3139_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v_fst_3089_; lean_object* v_snd_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3138_; 
v_fst_3089_ = lean_ctor_get(v_res_3084_, 0);
v_snd_3090_ = lean_ctor_get(v_res_3084_, 1);
v_isSharedCheck_3138_ = !lean_is_exclusive(v_res_3084_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3092_ = v_res_3084_;
v_isShared_3093_ = v_isSharedCheck_3138_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_snd_3090_);
lean_inc(v_fst_3089_);
lean_dec(v_res_3084_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3138_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v_pos_3095_; lean_object* v_res_3096_; lean_object* v_array_3103_; lean_object* v_idx_3104_; lean_object* v_pos_3106_; lean_object* v_idx_3107_; lean_object* v_err_3108_; lean_object* v___x_3114_; uint8_t v___x_3115_; 
v_array_3103_ = lean_ctor_get(v_pos_3085_, 0);
v_idx_3104_ = lean_ctor_get(v_pos_3085_, 1);
lean_inc(v_idx_3104_);
v___x_3114_ = lean_byte_array_size(v_array_3103_);
v___x_3115_ = lean_nat_dec_lt(v_idx_3104_, v___x_3114_);
if (v___x_3115_ == 0)
{
lean_object* v___x_3116_; 
lean_dec_ref(v_config_3062_);
v___x_3116_ = lean_box(0);
lean_inc(v_idx_3104_);
v_pos_3106_ = v_pos_3085_;
v_idx_3107_ = v_idx_3104_;
v_err_3108_ = v___x_3116_;
goto v___jp_3105_;
}
else
{
uint8_t v___x_3117_; uint8_t v_got_3118_; uint8_t v___x_3119_; 
v___x_3117_ = 63;
v_got_3118_ = lean_byte_array_fget(v_array_3103_, v_idx_3104_);
v___x_3119_ = lean_uint8_dec_eq(v_got_3118_, v___x_3117_);
if (v___x_3119_ == 0)
{
lean_object* v___x_3120_; 
lean_dec_ref(v_config_3062_);
v___x_3120_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_3104_);
v_pos_3106_ = v_pos_3085_;
v_idx_3107_ = v_idx_3104_;
v_err_3108_ = v___x_3120_;
goto v___jp_3105_;
}
else
{
lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3135_; 
lean_inc_ref(v_array_3103_);
v_isSharedCheck_3135_ = !lean_is_exclusive(v_pos_3085_);
if (v_isSharedCheck_3135_ == 0)
{
lean_object* v_unused_3136_; lean_object* v_unused_3137_; 
v_unused_3136_ = lean_ctor_get(v_pos_3085_, 1);
lean_dec(v_unused_3136_);
v_unused_3137_ = lean_ctor_get(v_pos_3085_, 0);
lean_dec(v_unused_3137_);
v___x_3122_ = v_pos_3085_;
v_isShared_3123_ = v_isSharedCheck_3135_;
goto v_resetjp_3121_;
}
else
{
lean_dec(v_pos_3085_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3135_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3124_; lean_object* v___x_3126_; 
v___x_3124_ = lean_nat_add(v_idx_3104_, v___x_3079_);
if (v_isShared_3123_ == 0)
{
lean_ctor_set(v___x_3122_, 1, v___x_3124_);
v___x_3126_ = v___x_3122_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_array_3103_);
lean_ctor_set(v_reuseFailAlloc_3134_, 1, v___x_3124_);
v___x_3126_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
lean_object* v___x_3127_; 
v___x_3127_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3062_, v___x_3126_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_pos_3128_; lean_object* v_res_3129_; lean_object* v___x_3130_; 
lean_dec(v_idx_3104_);
lean_del_object(v___x_3092_);
v_pos_3128_ = lean_ctor_get(v___x_3127_, 0);
lean_inc(v_pos_3128_);
v_res_3129_ = lean_ctor_get(v___x_3127_, 1);
lean_inc(v_res_3129_);
lean_dec_ref_known(v___x_3127_, 2);
v___x_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3130_, 0, v_res_3129_);
v_pos_3095_ = v_pos_3128_;
v_res_3096_ = v___x_3130_;
goto v___jp_3094_;
}
else
{
lean_object* v_pos_3131_; lean_object* v_err_3132_; lean_object* v_idx_3133_; 
v_pos_3131_ = lean_ctor_get(v___x_3127_, 0);
lean_inc(v_pos_3131_);
v_err_3132_ = lean_ctor_get(v___x_3127_, 1);
lean_inc(v_err_3132_);
lean_dec_ref_known(v___x_3127_, 2);
v_idx_3133_ = lean_ctor_get(v_pos_3131_, 1);
lean_inc(v_idx_3133_);
v_pos_3106_ = v_pos_3131_;
v_idx_3107_ = v_idx_3133_;
v_err_3108_ = v_err_3132_;
goto v___jp_3105_;
}
}
}
}
}
v___jp_3094_:
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3101_; 
v___x_3097_ = lean_box(0);
v___x_3098_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3098_, 0, v_scheme_3063_);
lean_ctor_set(v___x_3098_, 1, v_fst_3089_);
lean_ctor_set(v___x_3098_, 2, v_snd_3090_);
lean_ctor_set(v___x_3098_, 3, v_res_3096_);
lean_ctor_set(v___x_3098_, 4, v___x_3097_);
v___x_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3098_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 1, v___x_3099_);
lean_ctor_set(v___x_3087_, 0, v_pos_3095_);
v___x_3101_ = v___x_3087_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_pos_3095_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v___x_3099_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
v___jp_3105_:
{
uint8_t v___x_3109_; 
v___x_3109_ = lean_nat_dec_eq(v_idx_3104_, v_idx_3107_);
lean_dec(v_idx_3107_);
lean_dec(v_idx_3104_);
if (v___x_3109_ == 0)
{
lean_object* v___x_3111_; 
lean_dec(v_snd_3090_);
lean_dec(v_fst_3089_);
lean_del_object(v___x_3087_);
lean_dec_ref(v_scheme_3063_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set_tag(v___x_3092_, 1);
lean_ctor_set(v___x_3092_, 1, v_err_3108_);
lean_ctor_set(v___x_3092_, 0, v_pos_3106_);
v___x_3111_ = v___x_3092_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_pos_3106_);
lean_ctor_set(v_reuseFailAlloc_3112_, 1, v_err_3108_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
else
{
lean_object* v___x_3113_; 
lean_dec(v_err_3108_);
lean_del_object(v___x_3092_);
v___x_3113_ = lean_box(0);
v_pos_3095_ = v_pos_3106_;
v_res_3096_ = v___x_3113_;
goto v___jp_3094_;
}
}
}
}
}
else
{
lean_object* v_pos_3140_; lean_object* v_err_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
lean_dec_ref(v_scheme_3063_);
lean_dec_ref(v_config_3062_);
v_pos_3140_ = lean_ctor_get(v___x_3083_, 0);
v_err_3141_ = lean_ctor_get(v___x_3083_, 1);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3083_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_err_3141_);
lean_inc(v_pos_3140_);
lean_dec(v___x_3083_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_pos_3140_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v_err_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(lean_object* v_config_3161_, lean_object* v_a_3162_){
_start:
{
lean_object* v___x_3166_; 
lean_inc_ref(v_a_3162_);
v___x_3166_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3161_, v_a_3162_);
if (lean_obj_tag(v___x_3166_) == 0)
{
lean_object* v_pos_3167_; lean_object* v_res_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3264_; 
v_pos_3167_ = lean_ctor_get(v___x_3166_, 0);
v_res_3168_ = lean_ctor_get(v___x_3166_, 1);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3170_ = v___x_3166_;
v_isShared_3171_ = v_isSharedCheck_3264_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_res_3168_);
lean_inc(v_pos_3167_);
lean_dec(v___x_3166_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3264_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v_pos_3175_; lean_object* v_res_3176_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v_idx_3186_; lean_object* v_pos_3187_; lean_object* v_idx_3188_; lean_object* v_err_3189_; lean_object* v___x_3258_; uint8_t v___x_3259_; 
v___x_3258_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2));
v___x_3259_ = lean_string_dec_eq(v_res_3168_, v___x_3258_);
if (v___x_3259_ == 0)
{
lean_object* v___x_3260_; uint8_t v___x_3261_; 
v___x_3260_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3));
v___x_3261_ = lean_string_dec_eq(v_res_3168_, v___x_3260_);
if (v___x_3261_ == 0)
{
lean_object* v___x_3262_; lean_object* v___x_3263_; 
lean_del_object(v___x_3170_);
lean_dec(v_res_3168_);
lean_dec(v_pos_3167_);
lean_dec_ref(v_config_3161_);
v___x_3262_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5));
v___x_3263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3263_, 0, v_a_3162_);
lean_ctor_set(v___x_3263_, 1, v___x_3262_);
return v___x_3263_;
}
else
{
goto v___jp_3193_;
}
}
else
{
goto v___jp_3193_;
}
v___jp_3172_:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3181_; 
v___x_3177_ = lean_box(0);
v___x_3178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3178_, 0, v_res_3168_);
lean_ctor_set(v___x_3178_, 1, v___y_3174_);
lean_ctor_set(v___x_3178_, 2, v___y_3173_);
lean_ctor_set(v___x_3178_, 3, v_res_3176_);
lean_ctor_set(v___x_3178_, 4, v___x_3177_);
v___x_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3178_);
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 1, v___x_3179_);
lean_ctor_set(v___x_3170_, 0, v_pos_3175_);
v___x_3181_ = v___x_3170_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_pos_3175_);
lean_ctor_set(v_reuseFailAlloc_3182_, 1, v___x_3179_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
v___jp_3183_:
{
uint8_t v___x_3190_; 
v___x_3190_ = lean_nat_dec_eq(v_idx_3186_, v_idx_3188_);
lean_dec(v_idx_3188_);
lean_dec(v_idx_3186_);
if (v___x_3190_ == 0)
{
lean_object* v___x_3191_; 
lean_dec_ref(v_pos_3187_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_del_object(v___x_3170_);
lean_dec(v_res_3168_);
v___x_3191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3191_, 0, v_a_3162_);
lean_ctor_set(v___x_3191_, 1, v_err_3189_);
return v___x_3191_;
}
else
{
lean_object* v___x_3192_; 
lean_dec(v_err_3189_);
lean_dec_ref(v_a_3162_);
v___x_3192_ = lean_box(0);
v___y_3173_ = v___y_3184_;
v___y_3174_ = v___y_3185_;
v_pos_3175_ = v_pos_3187_;
v_res_3176_ = v___x_3192_;
goto v___jp_3172_;
}
}
v___jp_3193_:
{
lean_object* v_array_3194_; lean_object* v_idx_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3257_; 
v_array_3194_ = lean_ctor_get(v_pos_3167_, 0);
v_idx_3195_ = lean_ctor_get(v_pos_3167_, 1);
v_isSharedCheck_3257_ = !lean_is_exclusive(v_pos_3167_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3197_ = v_pos_3167_;
v_isShared_3198_ = v_isSharedCheck_3257_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_idx_3195_);
lean_inc(v_array_3194_);
lean_dec(v_pos_3167_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3257_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3199_; uint8_t v___x_3200_; 
v___x_3199_ = lean_byte_array_size(v_array_3194_);
v___x_3200_ = lean_nat_dec_lt(v_idx_3195_, v___x_3199_);
if (v___x_3200_ == 0)
{
lean_object* v___x_3201_; lean_object* v___x_3202_; 
lean_del_object(v___x_3197_);
lean_dec(v_idx_3195_);
lean_dec_ref(v_array_3194_);
lean_del_object(v___x_3170_);
lean_dec(v_res_3168_);
lean_dec_ref(v_config_3161_);
v___x_3201_ = lean_box(0);
v___x_3202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3202_, 0, v_a_3162_);
lean_ctor_set(v___x_3202_, 1, v___x_3201_);
return v___x_3202_;
}
else
{
uint8_t v___x_3203_; uint8_t v_got_3204_; uint8_t v___x_3205_; 
v___x_3203_ = 58;
v_got_3204_ = lean_byte_array_fget(v_array_3194_, v_idx_3195_);
v___x_3205_ = lean_uint8_dec_eq(v_got_3204_, v___x_3203_);
if (v___x_3205_ == 0)
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
lean_del_object(v___x_3197_);
lean_dec(v_idx_3195_);
lean_dec_ref(v_array_3194_);
lean_del_object(v___x_3170_);
lean_dec(v_res_3168_);
lean_dec_ref(v_config_3161_);
v___x_3206_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
v___x_3207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3207_, 0, v_a_3162_);
lean_ctor_set(v___x_3207_, 1, v___x_3206_);
return v___x_3207_;
}
else
{
lean_object* v___x_3208_; lean_object* v___x_3209_; uint8_t v___x_3210_; 
v___x_3208_ = lean_unsigned_to_nat(1u);
v___x_3209_ = lean_nat_add(v_idx_3195_, v___x_3208_);
lean_dec(v_idx_3195_);
v___x_3210_ = lean_nat_dec_lt(v___x_3209_, v___x_3199_);
if (v___x_3210_ == 0)
{
lean_dec(v___x_3209_);
lean_del_object(v___x_3197_);
lean_dec_ref(v_array_3194_);
lean_del_object(v___x_3170_);
lean_dec(v_res_3168_);
lean_dec_ref(v_config_3161_);
goto v___jp_3163_;
}
else
{
uint8_t v___x_3211_; uint8_t v___x_3212_; uint8_t v___x_3213_; 
v___x_3211_ = lean_byte_array_fget(v_array_3194_, v___x_3209_);
v___x_3212_ = 47;
v___x_3213_ = lean_uint8_dec_eq(v___x_3211_, v___x_3212_);
if (v___x_3213_ == 0)
{
lean_dec(v___x_3209_);
lean_del_object(v___x_3197_);
lean_dec_ref(v_array_3194_);
lean_del_object(v___x_3170_);
lean_dec(v_res_3168_);
lean_dec_ref(v_config_3161_);
goto v___jp_3163_;
}
else
{
lean_object* v___x_3215_; 
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 1, v___x_3209_);
v___x_3215_ = v___x_3197_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_array_3194_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v___x_3209_);
v___x_3215_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
lean_object* v___x_3216_; 
lean_inc_ref(v_config_3161_);
v___x_3216_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_3161_, v___x_3215_);
if (lean_obj_tag(v___x_3216_) == 0)
{
lean_object* v_res_3217_; lean_object* v_pos_3218_; lean_object* v_fst_3219_; lean_object* v_snd_3220_; lean_object* v_array_3221_; lean_object* v_idx_3222_; lean_object* v___x_3223_; uint8_t v___x_3224_; 
v_res_3217_ = lean_ctor_get(v___x_3216_, 1);
lean_inc(v_res_3217_);
v_pos_3218_ = lean_ctor_get(v___x_3216_, 0);
lean_inc(v_pos_3218_);
lean_dec_ref_known(v___x_3216_, 2);
v_fst_3219_ = lean_ctor_get(v_res_3217_, 0);
lean_inc(v_fst_3219_);
v_snd_3220_ = lean_ctor_get(v_res_3217_, 1);
lean_inc(v_snd_3220_);
lean_dec(v_res_3217_);
v_array_3221_ = lean_ctor_get(v_pos_3218_, 0);
v_idx_3222_ = lean_ctor_get(v_pos_3218_, 1);
lean_inc(v_idx_3222_);
v___x_3223_ = lean_byte_array_size(v_array_3221_);
v___x_3224_ = lean_nat_dec_lt(v_idx_3222_, v___x_3223_);
if (v___x_3224_ == 0)
{
lean_object* v___x_3225_; 
lean_dec_ref(v_config_3161_);
v___x_3225_ = lean_box(0);
lean_inc(v_idx_3222_);
v___y_3184_ = v_snd_3220_;
v___y_3185_ = v_fst_3219_;
v_idx_3186_ = v_idx_3222_;
v_pos_3187_ = v_pos_3218_;
v_idx_3188_ = v_idx_3222_;
v_err_3189_ = v___x_3225_;
goto v___jp_3183_;
}
else
{
uint8_t v___x_3226_; uint8_t v_got_3227_; uint8_t v___x_3228_; 
v___x_3226_ = 63;
v_got_3227_ = lean_byte_array_fget(v_array_3221_, v_idx_3222_);
v___x_3228_ = lean_uint8_dec_eq(v_got_3227_, v___x_3226_);
if (v___x_3228_ == 0)
{
lean_object* v___x_3229_; 
lean_dec_ref(v_config_3161_);
v___x_3229_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_3222_);
v___y_3184_ = v_snd_3220_;
v___y_3185_ = v_fst_3219_;
v_idx_3186_ = v_idx_3222_;
v_pos_3187_ = v_pos_3218_;
v_idx_3188_ = v_idx_3222_;
v_err_3189_ = v___x_3229_;
goto v___jp_3183_;
}
else
{
lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3244_; 
lean_inc_ref(v_array_3221_);
v_isSharedCheck_3244_ = !lean_is_exclusive(v_pos_3218_);
if (v_isSharedCheck_3244_ == 0)
{
lean_object* v_unused_3245_; lean_object* v_unused_3246_; 
v_unused_3245_ = lean_ctor_get(v_pos_3218_, 1);
lean_dec(v_unused_3245_);
v_unused_3246_ = lean_ctor_get(v_pos_3218_, 0);
lean_dec(v_unused_3246_);
v___x_3231_ = v_pos_3218_;
v_isShared_3232_ = v_isSharedCheck_3244_;
goto v_resetjp_3230_;
}
else
{
lean_dec(v_pos_3218_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3244_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3233_; lean_object* v___x_3235_; 
v___x_3233_ = lean_nat_add(v_idx_3222_, v___x_3208_);
if (v_isShared_3232_ == 0)
{
lean_ctor_set(v___x_3231_, 1, v___x_3233_);
v___x_3235_ = v___x_3231_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_array_3221_);
lean_ctor_set(v_reuseFailAlloc_3243_, 1, v___x_3233_);
v___x_3235_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
lean_object* v___x_3236_; 
v___x_3236_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3161_, v___x_3235_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_pos_3237_; lean_object* v_res_3238_; lean_object* v___x_3239_; 
lean_dec(v_idx_3222_);
lean_dec_ref(v_a_3162_);
v_pos_3237_ = lean_ctor_get(v___x_3236_, 0);
lean_inc(v_pos_3237_);
v_res_3238_ = lean_ctor_get(v___x_3236_, 1);
lean_inc(v_res_3238_);
lean_dec_ref_known(v___x_3236_, 2);
v___x_3239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3239_, 0, v_res_3238_);
v___y_3173_ = v_snd_3220_;
v___y_3174_ = v_fst_3219_;
v_pos_3175_ = v_pos_3237_;
v_res_3176_ = v___x_3239_;
goto v___jp_3172_;
}
else
{
lean_object* v_pos_3240_; lean_object* v_err_3241_; lean_object* v_idx_3242_; 
v_pos_3240_ = lean_ctor_get(v___x_3236_, 0);
lean_inc(v_pos_3240_);
v_err_3241_ = lean_ctor_get(v___x_3236_, 1);
lean_inc(v_err_3241_);
lean_dec_ref_known(v___x_3236_, 2);
v_idx_3242_ = lean_ctor_get(v_pos_3240_, 1);
lean_inc(v_idx_3242_);
v___y_3184_ = v_snd_3220_;
v___y_3185_ = v_fst_3219_;
v_idx_3186_ = v_idx_3222_;
v_pos_3187_ = v_pos_3240_;
v_idx_3188_ = v_idx_3242_;
v_err_3189_ = v_err_3241_;
goto v___jp_3183_;
}
}
}
}
}
}
else
{
lean_object* v_err_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3254_; 
lean_del_object(v___x_3170_);
lean_dec(v_res_3168_);
lean_dec_ref(v_config_3161_);
v_err_3247_ = lean_ctor_get(v___x_3216_, 1);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3254_ == 0)
{
lean_object* v_unused_3255_; 
v_unused_3255_ = lean_ctor_get(v___x_3216_, 0);
lean_dec(v_unused_3255_);
v___x_3249_ = v___x_3216_;
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_err_3247_);
lean_dec(v___x_3216_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3252_; 
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 0, v_a_3162_);
v___x_3252_ = v___x_3249_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_a_3162_);
lean_ctor_set(v_reuseFailAlloc_3253_, 1, v_err_3247_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
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
lean_object* v_err_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3272_; 
lean_dec_ref(v_config_3161_);
v_err_3265_ = lean_ctor_get(v___x_3166_, 1);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3272_ == 0)
{
lean_object* v_unused_3273_; 
v_unused_3273_ = lean_ctor_get(v___x_3166_, 0);
lean_dec(v_unused_3273_);
v___x_3267_ = v___x_3166_;
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_err_3265_);
lean_dec(v___x_3166_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3270_; 
if (v_isShared_3268_ == 0)
{
lean_ctor_set(v___x_3267_, 0, v_a_3162_);
v___x_3270_ = v___x_3267_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_a_3162_);
lean_ctor_set(v_reuseFailAlloc_3271_, 1, v_err_3265_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
v___jp_3163_:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3164_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1));
v___x_3165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3165_, 0, v_a_3162_);
lean_ctor_set(v___x_3165_, 1, v___x_3164_);
return v___x_3165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(lean_object* v_config_3274_, lean_object* v_a_3275_){
_start:
{
lean_object* v___x_3276_; 
lean_inc_ref(v_a_3275_);
v___x_3276_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3274_, v_a_3275_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_pos_3277_; lean_object* v_res_3278_; lean_object* v___x_3279_; 
v_pos_3277_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_pos_3277_);
v_res_3278_ = lean_ctor_get(v___x_3276_, 1);
lean_inc(v_res_3278_);
lean_dec_ref_known(v___x_3276_, 2);
v___x_3279_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(v_config_3274_, v_res_3278_, v_pos_3277_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_dec_ref(v_a_3275_);
return v___x_3279_;
}
else
{
lean_object* v_err_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
v_err_3280_ = lean_ctor_get(v___x_3279_, 1);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3287_ == 0)
{
lean_object* v_unused_3288_; 
v_unused_3288_ = lean_ctor_get(v___x_3279_, 0);
lean_dec(v_unused_3288_);
v___x_3282_ = v___x_3279_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_err_3280_);
lean_dec(v___x_3279_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
lean_ctor_set(v___x_3282_, 0, v_a_3275_);
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3275_);
lean_ctor_set(v_reuseFailAlloc_3286_, 1, v_err_3280_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
else
{
lean_object* v_err_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3296_; 
lean_dec_ref(v_config_3274_);
v_err_3289_ = lean_ctor_get(v___x_3276_, 1);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3296_ == 0)
{
lean_object* v_unused_3297_; 
v_unused_3297_ = lean_ctor_get(v___x_3276_, 0);
lean_dec(v_unused_3297_);
v___x_3291_ = v___x_3276_;
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_err_3289_);
lean_dec(v___x_3276_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 0, v_a_3275_);
v___x_3294_ = v___x_3291_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3275_);
lean_ctor_set(v_reuseFailAlloc_3295_, 1, v_err_3289_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(lean_object* v_config_3298_, lean_object* v_a_3299_){
_start:
{
lean_object* v___x_3300_; 
lean_inc_ref(v_a_3299_);
v___x_3300_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v_pos_3301_; lean_object* v_res_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3354_; 
v_pos_3301_ = lean_ctor_get(v___x_3300_, 0);
v_res_3302_ = lean_ctor_get(v___x_3300_, 1);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3304_ = v___x_3300_;
v_isShared_3305_ = v_isSharedCheck_3354_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_res_3302_);
lean_inc(v_pos_3301_);
lean_dec(v___x_3300_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3354_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v_array_3306_; lean_object* v_idx_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3353_; 
v_array_3306_ = lean_ctor_get(v_pos_3301_, 0);
v_idx_3307_ = lean_ctor_get(v_pos_3301_, 1);
v_isSharedCheck_3353_ = !lean_is_exclusive(v_pos_3301_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3309_ = v_pos_3301_;
v_isShared_3310_ = v_isSharedCheck_3353_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_idx_3307_);
lean_inc(v_array_3306_);
lean_dec(v_pos_3301_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3353_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3311_; uint8_t v___x_3312_; 
v___x_3311_ = lean_byte_array_size(v_array_3306_);
v___x_3312_ = lean_nat_dec_lt(v_idx_3307_, v___x_3311_);
if (v___x_3312_ == 0)
{
lean_object* v___x_3313_; lean_object* v___x_3315_; 
lean_del_object(v___x_3309_);
lean_dec(v_idx_3307_);
lean_dec_ref(v_array_3306_);
lean_dec(v_res_3302_);
v___x_3313_ = lean_box(0);
if (v_isShared_3305_ == 0)
{
lean_ctor_set_tag(v___x_3304_, 1);
lean_ctor_set(v___x_3304_, 1, v___x_3313_);
lean_ctor_set(v___x_3304_, 0, v_a_3299_);
v___x_3315_ = v___x_3304_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_a_3299_);
lean_ctor_set(v_reuseFailAlloc_3316_, 1, v___x_3313_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
else
{
uint8_t v___x_3317_; uint8_t v_got_3318_; uint8_t v___x_3319_; 
v___x_3317_ = 58;
v_got_3318_ = lean_byte_array_fget(v_array_3306_, v_idx_3307_);
v___x_3319_ = lean_uint8_dec_eq(v_got_3318_, v___x_3317_);
if (v___x_3319_ == 0)
{
lean_object* v___x_3320_; lean_object* v___x_3322_; 
lean_del_object(v___x_3309_);
lean_dec(v_idx_3307_);
lean_dec_ref(v_array_3306_);
lean_dec(v_res_3302_);
v___x_3320_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_3305_ == 0)
{
lean_ctor_set_tag(v___x_3304_, 1);
lean_ctor_set(v___x_3304_, 1, v___x_3320_);
lean_ctor_set(v___x_3304_, 0, v_a_3299_);
v___x_3322_ = v___x_3304_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3299_);
lean_ctor_set(v_reuseFailAlloc_3323_, 1, v___x_3320_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
else
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3327_; 
lean_del_object(v___x_3304_);
v___x_3324_ = lean_unsigned_to_nat(1u);
v___x_3325_ = lean_nat_add(v_idx_3307_, v___x_3324_);
lean_dec(v_idx_3307_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 1, v___x_3325_);
v___x_3327_ = v___x_3309_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_array_3306_);
lean_ctor_set(v_reuseFailAlloc_3352_, 1, v___x_3325_);
v___x_3327_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
lean_object* v___x_3328_; 
v___x_3328_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_3327_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_pos_3329_; lean_object* v_res_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3342_; 
lean_dec_ref(v_a_3299_);
v_pos_3329_ = lean_ctor_get(v___x_3328_, 0);
v_res_3330_ = lean_ctor_get(v___x_3328_, 1);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3332_ = v___x_3328_;
v_isShared_3333_ = v_isSharedCheck_3342_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_res_3330_);
lean_inc(v_pos_3329_);
lean_dec(v___x_3328_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3342_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; uint16_t v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3340_; 
v___x_3334_ = lean_box(0);
v___x_3335_ = lean_alloc_ctor(2, 0, 2);
v___x_3336_ = lean_unbox(v_res_3330_);
lean_dec(v_res_3330_);
lean_ctor_set_uint16(v___x_3335_, 0, v___x_3336_);
v___x_3337_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3334_);
lean_ctor_set(v___x_3337_, 1, v_res_3302_);
lean_ctor_set(v___x_3337_, 2, v___x_3335_);
v___x_3338_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3337_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 1, v___x_3338_);
v___x_3340_ = v___x_3332_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_pos_3329_);
lean_ctor_set(v_reuseFailAlloc_3341_, 1, v___x_3338_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
else
{
lean_object* v_err_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3350_; 
lean_dec(v_res_3302_);
v_err_3343_ = lean_ctor_get(v___x_3328_, 1);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3350_ == 0)
{
lean_object* v_unused_3351_; 
v_unused_3351_ = lean_ctor_get(v___x_3328_, 0);
lean_dec(v_unused_3351_);
v___x_3345_ = v___x_3328_;
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_err_3343_);
lean_dec(v___x_3328_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3348_; 
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 0, v_a_3299_);
v___x_3348_ = v___x_3345_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3299_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v_err_3343_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
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
lean_object* v_err_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3362_; 
v_err_3355_ = lean_ctor_get(v___x_3300_, 1);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3362_ == 0)
{
lean_object* v_unused_3363_; 
v_unused_3363_ = lean_ctor_get(v___x_3300_, 0);
lean_dec(v_unused_3363_);
v___x_3357_ = v___x_3300_;
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_err_3355_);
lean_dec(v___x_3300_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3360_; 
if (v_isShared_3358_ == 0)
{
lean_ctor_set(v___x_3357_, 0, v_a_3299_);
v___x_3360_ = v___x_3357_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_a_3299_);
lean_ctor_set(v_reuseFailAlloc_3361_, 1, v_err_3355_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority___boxed(lean_object* v_config_3364_, lean_object* v_a_3365_){
_start:
{
lean_object* v_res_3366_; 
v_res_3366_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3364_, v_a_3365_);
lean_dec_ref(v_config_3364_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object* v_config_3367_, lean_object* v_a_3368_){
_start:
{
lean_object* v___x_3369_; 
lean_inc_ref(v_a_3368_);
v___x_3369_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(v_a_3368_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_dec_ref(v_a_3368_);
lean_dec_ref(v_config_3367_);
return v___x_3369_;
}
else
{
lean_object* v_pos_3370_; lean_object* v_idx_3371_; lean_object* v_idx_3372_; uint8_t v___x_3373_; 
v_pos_3370_ = lean_ctor_get(v___x_3369_, 0);
v_idx_3371_ = lean_ctor_get(v_a_3368_, 1);
lean_inc(v_idx_3371_);
lean_dec_ref(v_a_3368_);
v_idx_3372_ = lean_ctor_get(v_pos_3370_, 1);
v___x_3373_ = lean_nat_dec_eq(v_idx_3371_, v_idx_3372_);
lean_dec(v_idx_3371_);
if (v___x_3373_ == 0)
{
lean_dec_ref(v_config_3367_);
return v___x_3369_;
}
else
{
lean_object* v___x_3374_; 
lean_inc(v_idx_3372_);
lean_inc(v_pos_3370_);
lean_dec_ref_known(v___x_3369_, 2);
lean_inc_ref(v_config_3367_);
v___x_3374_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(v_config_3367_, v_pos_3370_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_dec(v_idx_3372_);
lean_dec_ref(v_config_3367_);
return v___x_3374_;
}
else
{
lean_object* v_pos_3375_; lean_object* v_idx_3376_; uint8_t v___x_3377_; 
v_pos_3375_ = lean_ctor_get(v___x_3374_, 0);
v_idx_3376_ = lean_ctor_get(v_pos_3375_, 1);
v___x_3377_ = lean_nat_dec_eq(v_idx_3372_, v_idx_3376_);
lean_dec(v_idx_3372_);
if (v___x_3377_ == 0)
{
lean_dec_ref(v_config_3367_);
return v___x_3374_;
}
else
{
lean_object* v___x_3378_; 
lean_inc(v_idx_3376_);
lean_inc(v_pos_3375_);
lean_dec_ref_known(v___x_3374_, 2);
lean_inc_ref(v_config_3367_);
v___x_3378_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(v_config_3367_, v_pos_3375_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_dec(v_idx_3376_);
lean_dec_ref(v_config_3367_);
return v___x_3378_;
}
else
{
lean_object* v_pos_3379_; lean_object* v_idx_3380_; uint8_t v___x_3381_; 
v_pos_3379_ = lean_ctor_get(v___x_3378_, 0);
v_idx_3380_ = lean_ctor_get(v_pos_3379_, 1);
v___x_3381_ = lean_nat_dec_eq(v_idx_3376_, v_idx_3380_);
lean_dec(v_idx_3376_);
if (v___x_3381_ == 0)
{
lean_dec_ref(v_config_3367_);
return v___x_3378_;
}
else
{
lean_object* v___x_3382_; 
lean_inc(v_idx_3380_);
lean_inc(v_pos_3379_);
lean_dec_ref_known(v___x_3378_, 2);
v___x_3382_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3367_, v_pos_3379_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_dec(v_idx_3380_);
lean_dec_ref(v_config_3367_);
return v___x_3382_;
}
else
{
lean_object* v_pos_3383_; lean_object* v_idx_3384_; uint8_t v___x_3385_; 
v_pos_3383_ = lean_ctor_get(v___x_3382_, 0);
v_idx_3384_ = lean_ctor_get(v_pos_3383_, 1);
v___x_3385_ = lean_nat_dec_eq(v_idx_3380_, v_idx_3384_);
lean_dec(v_idx_3380_);
if (v___x_3385_ == 0)
{
lean_dec_ref(v_config_3367_);
return v___x_3382_;
}
else
{
lean_object* v___x_3386_; 
lean_inc(v_pos_3383_);
lean_dec_ref_known(v___x_3382_, 2);
v___x_3386_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(v_config_3367_, v_pos_3383_);
return v___x_3386_;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(lean_object* v_config_3390_, lean_object* v_a_3391_){
_start:
{
lean_object* v___x_3392_; 
v___x_3392_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_3390_, v_a_3391_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v_pos_3393_; lean_object* v_res_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3407_; 
v_pos_3393_ = lean_ctor_get(v___x_3392_, 0);
v_res_3394_ = lean_ctor_get(v___x_3392_, 1);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3396_ = v___x_3392_;
v_isShared_3397_ = v_isSharedCheck_3407_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_res_3394_);
lean_inc(v_pos_3393_);
lean_dec(v___x_3392_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3407_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3398_; 
v___x_3398_ = l_Std_Http_URI_EncodedFragment_decode(v_res_3394_);
lean_dec(v_res_3394_);
if (lean_obj_tag(v___x_3398_) == 1)
{
lean_object* v_val_3399_; lean_object* v___x_3401_; 
v_val_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_val_3399_);
lean_dec_ref_known(v___x_3398_, 1);
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 1, v_val_3399_);
v___x_3401_ = v___x_3396_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_pos_3393_);
lean_ctor_set(v_reuseFailAlloc_3402_, 1, v_val_3399_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
else
{
lean_object* v___x_3403_; lean_object* v___x_3405_; 
lean_dec(v___x_3398_);
v___x_3403_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___closed__1));
if (v_isShared_3397_ == 0)
{
lean_ctor_set_tag(v___x_3396_, 1);
lean_ctor_set(v___x_3396_, 1, v___x_3403_);
v___x_3405_ = v___x_3396_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_pos_3393_);
lean_ctor_set(v_reuseFailAlloc_3406_, 1, v___x_3403_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
else
{
lean_object* v_pos_3408_; lean_object* v_err_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
v_pos_3408_ = lean_ctor_get(v___x_3392_, 0);
v_err_3409_ = lean_ctor_get(v___x_3392_, 1);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3392_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_err_3409_);
lean_inc(v_pos_3408_);
lean_dec(v___x_3392_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_pos_3408_);
lean_ctor_set(v_reuseFailAlloc_3415_, 1, v_err_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___boxed(lean_object* v_config_3417_, lean_object* v_a_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3417_, v_a_3418_);
lean_dec_ref(v_config_3417_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_uri(lean_object* v_config_3420_, lean_object* v_a_3421_){
_start:
{
lean_object* v___x_3422_; 
lean_inc_ref(v_a_3421_);
v___x_3422_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3420_, v_a_3421_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v_pos_3423_; lean_object* v_res_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3553_; 
v_pos_3423_ = lean_ctor_get(v___x_3422_, 0);
v_res_3424_ = lean_ctor_get(v___x_3422_, 1);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3426_ = v___x_3422_;
v_isShared_3427_ = v_isSharedCheck_3553_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_res_3424_);
lean_inc(v_pos_3423_);
lean_dec(v___x_3422_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3553_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v_array_3428_; lean_object* v_idx_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3552_; 
v_array_3428_ = lean_ctor_get(v_pos_3423_, 0);
v_idx_3429_ = lean_ctor_get(v_pos_3423_, 1);
v_isSharedCheck_3552_ = !lean_is_exclusive(v_pos_3423_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3431_ = v_pos_3423_;
v_isShared_3432_ = v_isSharedCheck_3552_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_idx_3429_);
lean_inc(v_array_3428_);
lean_dec(v_pos_3423_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3552_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3433_; uint8_t v___x_3434_; 
v___x_3433_ = lean_byte_array_size(v_array_3428_);
v___x_3434_ = lean_nat_dec_lt(v_idx_3429_, v___x_3433_);
if (v___x_3434_ == 0)
{
lean_object* v___x_3435_; lean_object* v___x_3437_; 
lean_del_object(v___x_3431_);
lean_dec(v_idx_3429_);
lean_dec_ref(v_array_3428_);
lean_dec(v_res_3424_);
lean_dec_ref(v_config_3420_);
v___x_3435_ = lean_box(0);
if (v_isShared_3427_ == 0)
{
lean_ctor_set_tag(v___x_3426_, 1);
lean_ctor_set(v___x_3426_, 1, v___x_3435_);
lean_ctor_set(v___x_3426_, 0, v_a_3421_);
v___x_3437_ = v___x_3426_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3421_);
lean_ctor_set(v_reuseFailAlloc_3438_, 1, v___x_3435_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
else
{
uint8_t v___x_3439_; uint8_t v_got_3440_; uint8_t v___x_3441_; 
v___x_3439_ = 58;
v_got_3440_ = lean_byte_array_fget(v_array_3428_, v_idx_3429_);
v___x_3441_ = lean_uint8_dec_eq(v_got_3440_, v___x_3439_);
if (v___x_3441_ == 0)
{
lean_object* v___x_3442_; lean_object* v___x_3444_; 
lean_del_object(v___x_3431_);
lean_dec(v_idx_3429_);
lean_dec_ref(v_array_3428_);
lean_dec(v_res_3424_);
lean_dec_ref(v_config_3420_);
v___x_3442_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_3427_ == 0)
{
lean_ctor_set_tag(v___x_3426_, 1);
lean_ctor_set(v___x_3426_, 1, v___x_3442_);
lean_ctor_set(v___x_3426_, 0, v_a_3421_);
v___x_3444_ = v___x_3426_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_a_3421_);
lean_ctor_set(v_reuseFailAlloc_3445_, 1, v___x_3442_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
else
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3449_; 
v___x_3446_ = lean_unsigned_to_nat(1u);
v___x_3447_ = lean_nat_add(v_idx_3429_, v___x_3446_);
lean_dec(v_idx_3429_);
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 1, v___x_3447_);
v___x_3449_ = v___x_3431_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_array_3428_);
lean_ctor_set(v_reuseFailAlloc_3551_, 1, v___x_3447_);
v___x_3449_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
lean_object* v___x_3450_; 
lean_inc_ref(v_config_3420_);
v___x_3450_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_3420_, v___x_3449_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_object* v_res_3451_; lean_object* v_pos_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3541_; 
v_res_3451_ = lean_ctor_get(v___x_3450_, 1);
v_pos_3452_ = lean_ctor_get(v___x_3450_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3454_ = v___x_3450_;
v_isShared_3455_ = v_isSharedCheck_3541_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_res_3451_);
lean_inc(v_pos_3452_);
lean_dec(v___x_3450_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3541_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v_fst_3456_; lean_object* v_snd_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3540_; 
v_fst_3456_ = lean_ctor_get(v_res_3451_, 0);
v_snd_3457_ = lean_ctor_get(v_res_3451_, 1);
v_isSharedCheck_3540_ = !lean_is_exclusive(v_res_3451_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3459_ = v_res_3451_;
v_isShared_3460_ = v_isSharedCheck_3540_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_snd_3457_);
lean_inc(v_fst_3456_);
lean_dec(v_res_3451_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3540_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___y_3462_; lean_object* v_pos_3463_; lean_object* v_res_3464_; lean_object* v___y_3471_; lean_object* v_idx_3472_; lean_object* v_pos_3473_; lean_object* v_err_3474_; lean_object* v_pos_3482_; lean_object* v_array_3483_; lean_object* v_idx_3484_; lean_object* v_res_3485_; lean_object* v_array_3503_; lean_object* v_idx_3504_; lean_object* v_pos_3506_; lean_object* v_array_3507_; lean_object* v_idx_3508_; lean_object* v_err_3509_; lean_object* v___x_3513_; uint8_t v___x_3514_; 
v_array_3503_ = lean_ctor_get(v_pos_3452_, 0);
lean_inc_ref(v_array_3503_);
v_idx_3504_ = lean_ctor_get(v_pos_3452_, 1);
lean_inc(v_idx_3504_);
v___x_3513_ = lean_byte_array_size(v_array_3503_);
v___x_3514_ = lean_nat_dec_lt(v_idx_3504_, v___x_3513_);
if (v___x_3514_ == 0)
{
lean_object* v___x_3515_; 
v___x_3515_ = lean_box(0);
lean_inc(v_idx_3504_);
v_pos_3506_ = v_pos_3452_;
v_array_3507_ = v_array_3503_;
v_idx_3508_ = v_idx_3504_;
v_err_3509_ = v___x_3515_;
goto v___jp_3505_;
}
else
{
uint8_t v___x_3516_; uint8_t v_got_3517_; uint8_t v___x_3518_; 
v___x_3516_ = 63;
v_got_3517_ = lean_byte_array_fget(v_array_3503_, v_idx_3504_);
v___x_3518_ = lean_uint8_dec_eq(v_got_3517_, v___x_3516_);
if (v___x_3518_ == 0)
{
lean_object* v___x_3519_; 
v___x_3519_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_3504_);
v_pos_3506_ = v_pos_3452_;
v_array_3507_ = v_array_3503_;
v_idx_3508_ = v_idx_3504_;
v_err_3509_ = v___x_3519_;
goto v___jp_3505_;
}
else
{
lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3537_; 
v_isSharedCheck_3537_ = !lean_is_exclusive(v_pos_3452_);
if (v_isSharedCheck_3537_ == 0)
{
lean_object* v_unused_3538_; lean_object* v_unused_3539_; 
v_unused_3538_ = lean_ctor_get(v_pos_3452_, 1);
lean_dec(v_unused_3538_);
v_unused_3539_ = lean_ctor_get(v_pos_3452_, 0);
lean_dec(v_unused_3539_);
v___x_3521_ = v_pos_3452_;
v_isShared_3522_ = v_isSharedCheck_3537_;
goto v_resetjp_3520_;
}
else
{
lean_dec(v_pos_3452_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3537_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3523_; lean_object* v___x_3525_; 
v___x_3523_ = lean_nat_add(v_idx_3504_, v___x_3446_);
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 1, v___x_3523_);
v___x_3525_ = v___x_3521_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_array_3503_);
lean_ctor_set(v_reuseFailAlloc_3536_, 1, v___x_3523_);
v___x_3525_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
lean_object* v___x_3526_; 
lean_inc_ref(v_config_3420_);
v___x_3526_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3420_, v___x_3525_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_pos_3527_; lean_object* v_res_3528_; lean_object* v_array_3529_; lean_object* v_idx_3530_; lean_object* v___x_3531_; 
lean_dec(v_idx_3504_);
v_pos_3527_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_pos_3527_);
v_res_3528_ = lean_ctor_get(v___x_3526_, 1);
lean_inc(v_res_3528_);
lean_dec_ref_known(v___x_3526_, 2);
v_array_3529_ = lean_ctor_get(v_pos_3527_, 0);
lean_inc_ref(v_array_3529_);
v_idx_3530_ = lean_ctor_get(v_pos_3527_, 1);
lean_inc(v_idx_3530_);
v___x_3531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3531_, 0, v_res_3528_);
v_pos_3482_ = v_pos_3527_;
v_array_3483_ = v_array_3529_;
v_idx_3484_ = v_idx_3530_;
v_res_3485_ = v___x_3531_;
goto v___jp_3481_;
}
else
{
lean_object* v_pos_3532_; lean_object* v_err_3533_; lean_object* v_array_3534_; lean_object* v_idx_3535_; 
v_pos_3532_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_pos_3532_);
v_err_3533_ = lean_ctor_get(v___x_3526_, 1);
lean_inc(v_err_3533_);
lean_dec_ref_known(v___x_3526_, 2);
v_array_3534_ = lean_ctor_get(v_pos_3532_, 0);
lean_inc_ref(v_array_3534_);
v_idx_3535_ = lean_ctor_get(v_pos_3532_, 1);
lean_inc(v_idx_3535_);
v_pos_3506_ = v_pos_3532_;
v_array_3507_ = v_array_3534_;
v_idx_3508_ = v_idx_3535_;
v_err_3509_ = v_err_3533_;
goto v___jp_3505_;
}
}
}
}
}
v___jp_3461_:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3468_; 
v___x_3465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3465_, 0, v_res_3424_);
lean_ctor_set(v___x_3465_, 1, v_fst_3456_);
lean_ctor_set(v___x_3465_, 2, v_snd_3457_);
lean_ctor_set(v___x_3465_, 3, v___y_3462_);
lean_ctor_set(v___x_3465_, 4, v_res_3464_);
v___x_3466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3465_);
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 1, v___x_3466_);
lean_ctor_set(v___x_3454_, 0, v_pos_3463_);
v___x_3468_ = v___x_3454_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_pos_3463_);
lean_ctor_set(v_reuseFailAlloc_3469_, 1, v___x_3466_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
v___jp_3470_:
{
lean_object* v_idx_3475_; uint8_t v___x_3476_; 
v_idx_3475_ = lean_ctor_get(v_pos_3473_, 1);
v___x_3476_ = lean_nat_dec_eq(v_idx_3472_, v_idx_3475_);
lean_dec(v_idx_3472_);
if (v___x_3476_ == 0)
{
lean_object* v___x_3478_; 
lean_dec_ref(v_pos_3473_);
lean_dec(v___y_3471_);
lean_dec(v_snd_3457_);
lean_dec(v_fst_3456_);
lean_del_object(v___x_3454_);
lean_dec(v_res_3424_);
if (v_isShared_3427_ == 0)
{
lean_ctor_set_tag(v___x_3426_, 1);
lean_ctor_set(v___x_3426_, 1, v_err_3474_);
lean_ctor_set(v___x_3426_, 0, v_a_3421_);
v___x_3478_ = v___x_3426_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3421_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v_err_3474_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
else
{
lean_object* v___x_3480_; 
lean_dec(v_err_3474_);
lean_del_object(v___x_3426_);
lean_dec_ref(v_a_3421_);
v___x_3480_ = lean_box(0);
v___y_3462_ = v___y_3471_;
v_pos_3463_ = v_pos_3473_;
v_res_3464_ = v___x_3480_;
goto v___jp_3461_;
}
}
v___jp_3481_:
{
lean_object* v___x_3486_; uint8_t v___x_3487_; 
v___x_3486_ = lean_byte_array_size(v_array_3483_);
v___x_3487_ = lean_nat_dec_lt(v_idx_3484_, v___x_3486_);
if (v___x_3487_ == 0)
{
lean_object* v___x_3488_; 
lean_dec_ref(v_array_3483_);
lean_del_object(v___x_3459_);
lean_dec_ref(v_config_3420_);
v___x_3488_ = lean_box(0);
v___y_3471_ = v_res_3485_;
v_idx_3472_ = v_idx_3484_;
v_pos_3473_ = v_pos_3482_;
v_err_3474_ = v___x_3488_;
goto v___jp_3470_;
}
else
{
uint8_t v___x_3489_; uint8_t v_got_3490_; uint8_t v___x_3491_; 
v___x_3489_ = 35;
v_got_3490_ = lean_byte_array_fget(v_array_3483_, v_idx_3484_);
v___x_3491_ = lean_uint8_dec_eq(v_got_3490_, v___x_3489_);
if (v___x_3491_ == 0)
{
lean_object* v___x_3492_; 
lean_dec_ref(v_array_3483_);
lean_del_object(v___x_3459_);
lean_dec_ref(v_config_3420_);
v___x_3492_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v___y_3471_ = v_res_3485_;
v_idx_3472_ = v_idx_3484_;
v_pos_3473_ = v_pos_3482_;
v_err_3474_ = v___x_3492_;
goto v___jp_3470_;
}
else
{
lean_object* v___x_3493_; lean_object* v___x_3495_; 
lean_dec_ref(v_pos_3482_);
v___x_3493_ = lean_nat_add(v_idx_3484_, v___x_3446_);
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 1, v___x_3493_);
lean_ctor_set(v___x_3459_, 0, v_array_3483_);
v___x_3495_ = v___x_3459_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_array_3483_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v___x_3493_);
v___x_3495_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
lean_object* v___x_3496_; 
v___x_3496_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3420_, v___x_3495_);
lean_dec_ref(v_config_3420_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_pos_3497_; lean_object* v_res_3498_; lean_object* v___x_3499_; 
lean_dec(v_idx_3484_);
lean_del_object(v___x_3426_);
lean_dec_ref(v_a_3421_);
v_pos_3497_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_pos_3497_);
v_res_3498_ = lean_ctor_get(v___x_3496_, 1);
lean_inc(v_res_3498_);
lean_dec_ref_known(v___x_3496_, 2);
v___x_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3499_, 0, v_res_3498_);
v___y_3462_ = v_res_3485_;
v_pos_3463_ = v_pos_3497_;
v_res_3464_ = v___x_3499_;
goto v___jp_3461_;
}
else
{
lean_object* v_pos_3500_; lean_object* v_err_3501_; 
v_pos_3500_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_pos_3500_);
v_err_3501_ = lean_ctor_get(v___x_3496_, 1);
lean_inc(v_err_3501_);
lean_dec_ref_known(v___x_3496_, 2);
v___y_3471_ = v_res_3485_;
v_idx_3472_ = v_idx_3484_;
v_pos_3473_ = v_pos_3500_;
v_err_3474_ = v_err_3501_;
goto v___jp_3470_;
}
}
}
}
}
v___jp_3505_:
{
uint8_t v___x_3510_; 
v___x_3510_ = lean_nat_dec_eq(v_idx_3504_, v_idx_3508_);
lean_dec(v_idx_3504_);
if (v___x_3510_ == 0)
{
lean_object* v___x_3511_; 
lean_dec(v_idx_3508_);
lean_dec_ref(v_array_3507_);
lean_dec_ref(v_pos_3506_);
lean_del_object(v___x_3459_);
lean_dec(v_snd_3457_);
lean_dec(v_fst_3456_);
lean_del_object(v___x_3454_);
lean_del_object(v___x_3426_);
lean_dec(v_res_3424_);
lean_dec_ref(v_config_3420_);
v___x_3511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3511_, 0, v_a_3421_);
lean_ctor_set(v___x_3511_, 1, v_err_3509_);
return v___x_3511_;
}
else
{
lean_object* v___x_3512_; 
lean_dec(v_err_3509_);
v___x_3512_ = lean_box(0);
v_pos_3482_ = v_pos_3506_;
v_array_3483_ = v_array_3507_;
v_idx_3484_ = v_idx_3508_;
v_res_3485_ = v___x_3512_;
goto v___jp_3481_;
}
}
}
}
}
else
{
lean_object* v_err_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3549_; 
lean_del_object(v___x_3426_);
lean_dec(v_res_3424_);
lean_dec_ref(v_config_3420_);
v_err_3542_ = lean_ctor_get(v___x_3450_, 1);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3549_ == 0)
{
lean_object* v_unused_3550_; 
v_unused_3550_ = lean_ctor_get(v___x_3450_, 0);
lean_dec(v_unused_3550_);
v___x_3544_ = v___x_3450_;
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_err_3542_);
lean_dec(v___x_3450_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3547_; 
if (v_isShared_3545_ == 0)
{
lean_ctor_set(v___x_3544_, 0, v_a_3421_);
v___x_3547_ = v___x_3544_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_a_3421_);
lean_ctor_set(v_reuseFailAlloc_3548_, 1, v_err_3542_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
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
lean_object* v_err_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3561_; 
lean_dec_ref(v_config_3420_);
v_err_3554_ = lean_ctor_get(v___x_3422_, 1);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3561_ == 0)
{
lean_object* v_unused_3562_; 
v_unused_3562_ = lean_ctor_get(v___x_3422_, 0);
lean_dec(v_unused_3562_);
v___x_3556_ = v___x_3422_;
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_err_3554_);
lean_dec(v___x_3422_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3559_; 
if (v_isShared_3557_ == 0)
{
lean_ctor_set(v___x_3556_, 0, v_a_3421_);
v___x_3559_ = v___x_3556_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3421_);
lean_ctor_set(v_reuseFailAlloc_3560_, 1, v_err_3554_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withAuthority(lean_object* v_config_3563_, lean_object* v_a_3564_){
_start:
{
lean_object* v___y_3566_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v_pos_3569_; lean_object* v_res_3570_; lean_object* v___y_3575_; lean_object* v_idx_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v_pos_3579_; lean_object* v_err_3580_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v_pos_3596_; lean_object* v_array_3597_; lean_object* v_idx_3598_; lean_object* v_res_3599_; lean_object* v___y_3617_; lean_object* v_idx_3618_; lean_object* v___y_3619_; lean_object* v_pos_3620_; lean_object* v_array_3621_; lean_object* v_idx_3622_; lean_object* v_err_3623_; lean_object* v_pos_3628_; lean_object* v_utf8_3684_; lean_object* v___x_3685_; 
v_utf8_3684_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1);
lean_inc_ref(v_a_3564_);
v___x_3685_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_3684_, v_a_3564_);
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v_pos_3686_; 
v_pos_3686_ = lean_ctor_get(v___x_3685_, 0);
lean_inc(v_pos_3686_);
lean_dec_ref_known(v___x_3685_, 2);
v_pos_3628_ = v_pos_3686_;
goto v___jp_3627_;
}
else
{
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v_pos_3687_; 
v_pos_3687_ = lean_ctor_get(v___x_3685_, 0);
lean_inc(v_pos_3687_);
lean_dec_ref_known(v___x_3685_, 2);
v_pos_3628_ = v_pos_3687_;
goto v___jp_3627_;
}
else
{
lean_object* v_err_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3695_; 
lean_dec_ref(v_config_3563_);
v_err_3688_ = lean_ctor_get(v___x_3685_, 1);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3695_ == 0)
{
lean_object* v_unused_3696_; 
v_unused_3696_ = lean_ctor_get(v___x_3685_, 0);
lean_dec(v_unused_3696_);
v___x_3690_ = v___x_3685_;
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_err_3688_);
lean_dec(v___x_3685_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3693_; 
if (v_isShared_3691_ == 0)
{
lean_ctor_set(v___x_3690_, 0, v_a_3564_);
v___x_3693_ = v___x_3690_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_a_3564_);
lean_ctor_set(v_reuseFailAlloc_3694_, 1, v_err_3688_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
}
v___jp_3565_:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3571_, 0, v___y_3567_);
v___x_3572_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3571_);
lean_ctor_set(v___x_3572_, 1, v___y_3568_);
lean_ctor_set(v___x_3572_, 2, v___y_3566_);
lean_ctor_set(v___x_3572_, 3, v_res_3570_);
v___x_3573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3573_, 0, v_pos_3569_);
lean_ctor_set(v___x_3573_, 1, v___x_3572_);
return v___x_3573_;
}
v___jp_3574_:
{
lean_object* v_idx_3581_; uint8_t v___x_3582_; 
v_idx_3581_ = lean_ctor_get(v_pos_3579_, 1);
v___x_3582_ = lean_nat_dec_eq(v_idx_3576_, v_idx_3581_);
lean_dec(v_idx_3576_);
if (v___x_3582_ == 0)
{
lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3589_; 
lean_dec_ref(v___y_3578_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3575_);
v_isSharedCheck_3589_ = !lean_is_exclusive(v_pos_3579_);
if (v_isSharedCheck_3589_ == 0)
{
lean_object* v_unused_3590_; lean_object* v_unused_3591_; 
v_unused_3590_ = lean_ctor_get(v_pos_3579_, 1);
lean_dec(v_unused_3590_);
v_unused_3591_ = lean_ctor_get(v_pos_3579_, 0);
lean_dec(v_unused_3591_);
v___x_3584_ = v_pos_3579_;
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
else
{
lean_dec(v_pos_3579_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3587_; 
if (v_isShared_3585_ == 0)
{
lean_ctor_set_tag(v___x_3584_, 1);
lean_ctor_set(v___x_3584_, 1, v_err_3580_);
lean_ctor_set(v___x_3584_, 0, v_a_3564_);
v___x_3587_ = v___x_3584_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_a_3564_);
lean_ctor_set(v_reuseFailAlloc_3588_, 1, v_err_3580_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
else
{
lean_object* v___x_3592_; 
lean_dec(v_err_3580_);
lean_dec_ref(v_a_3564_);
v___x_3592_ = lean_box(0);
v___y_3566_ = v___y_3575_;
v___y_3567_ = v___y_3577_;
v___y_3568_ = v___y_3578_;
v_pos_3569_ = v_pos_3579_;
v_res_3570_ = v___x_3592_;
goto v___jp_3565_;
}
}
v___jp_3593_:
{
lean_object* v___x_3600_; uint8_t v___x_3601_; 
v___x_3600_ = lean_byte_array_size(v_array_3597_);
v___x_3601_ = lean_nat_dec_lt(v_idx_3598_, v___x_3600_);
if (v___x_3601_ == 0)
{
lean_object* v___x_3602_; 
lean_dec_ref(v_array_3597_);
lean_dec_ref(v_config_3563_);
v___x_3602_ = lean_box(0);
v___y_3575_ = v_res_3599_;
v_idx_3576_ = v_idx_3598_;
v___y_3577_ = v___y_3594_;
v___y_3578_ = v___y_3595_;
v_pos_3579_ = v_pos_3596_;
v_err_3580_ = v___x_3602_;
goto v___jp_3574_;
}
else
{
uint8_t v___x_3603_; uint8_t v_got_3604_; uint8_t v___x_3605_; 
v___x_3603_ = 35;
v_got_3604_ = lean_byte_array_fget(v_array_3597_, v_idx_3598_);
v___x_3605_ = lean_uint8_dec_eq(v_got_3604_, v___x_3603_);
if (v___x_3605_ == 0)
{
lean_object* v___x_3606_; 
lean_dec_ref(v_array_3597_);
lean_dec_ref(v_config_3563_);
v___x_3606_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v___y_3575_ = v_res_3599_;
v_idx_3576_ = v_idx_3598_;
v___y_3577_ = v___y_3594_;
v___y_3578_ = v___y_3595_;
v_pos_3579_ = v_pos_3596_;
v_err_3580_ = v___x_3606_;
goto v___jp_3574_;
}
else
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
lean_dec_ref(v_pos_3596_);
v___x_3607_ = lean_unsigned_to_nat(1u);
v___x_3608_ = lean_nat_add(v_idx_3598_, v___x_3607_);
v___x_3609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3609_, 0, v_array_3597_);
lean_ctor_set(v___x_3609_, 1, v___x_3608_);
v___x_3610_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3563_, v___x_3609_);
lean_dec_ref(v_config_3563_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_pos_3611_; lean_object* v_res_3612_; lean_object* v___x_3613_; 
lean_dec(v_idx_3598_);
lean_dec_ref(v_a_3564_);
v_pos_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc(v_pos_3611_);
v_res_3612_ = lean_ctor_get(v___x_3610_, 1);
lean_inc(v_res_3612_);
lean_dec_ref_known(v___x_3610_, 2);
v___x_3613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3613_, 0, v_res_3612_);
v___y_3566_ = v_res_3599_;
v___y_3567_ = v___y_3594_;
v___y_3568_ = v___y_3595_;
v_pos_3569_ = v_pos_3611_;
v_res_3570_ = v___x_3613_;
goto v___jp_3565_;
}
else
{
lean_object* v_pos_3614_; lean_object* v_err_3615_; 
v_pos_3614_ = lean_ctor_get(v___x_3610_, 0);
lean_inc(v_pos_3614_);
v_err_3615_ = lean_ctor_get(v___x_3610_, 1);
lean_inc(v_err_3615_);
lean_dec_ref_known(v___x_3610_, 2);
v___y_3575_ = v_res_3599_;
v_idx_3576_ = v_idx_3598_;
v___y_3577_ = v___y_3594_;
v___y_3578_ = v___y_3595_;
v_pos_3579_ = v_pos_3614_;
v_err_3580_ = v_err_3615_;
goto v___jp_3574_;
}
}
}
}
v___jp_3616_:
{
uint8_t v___x_3624_; 
v___x_3624_ = lean_nat_dec_eq(v_idx_3618_, v_idx_3622_);
lean_dec(v_idx_3618_);
if (v___x_3624_ == 0)
{
lean_object* v___x_3625_; 
lean_dec(v_idx_3622_);
lean_dec_ref(v_array_3621_);
lean_dec_ref(v_pos_3620_);
lean_dec_ref(v___y_3619_);
lean_dec_ref(v___y_3617_);
lean_dec_ref(v_config_3563_);
v___x_3625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3625_, 0, v_a_3564_);
lean_ctor_set(v___x_3625_, 1, v_err_3623_);
return v___x_3625_;
}
else
{
lean_object* v___x_3626_; 
lean_dec(v_err_3623_);
v___x_3626_ = lean_box(0);
v___y_3594_ = v___y_3617_;
v___y_3595_ = v___y_3619_;
v_pos_3596_ = v_pos_3620_;
v_array_3597_ = v_array_3621_;
v_idx_3598_ = v_idx_3622_;
v_res_3599_ = v___x_3626_;
goto v___jp_3593_;
}
}
v___jp_3627_:
{
lean_object* v___x_3629_; 
v___x_3629_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_3563_, v_pos_3628_);
if (lean_obj_tag(v___x_3629_) == 0)
{
lean_object* v_pos_3630_; lean_object* v_res_3631_; uint8_t v___x_3632_; lean_object* v___x_3633_; 
v_pos_3630_ = lean_ctor_get(v___x_3629_, 0);
lean_inc(v_pos_3630_);
v_res_3631_ = lean_ctor_get(v___x_3629_, 1);
lean_inc(v_res_3631_);
lean_dec_ref_known(v___x_3629_, 2);
v___x_3632_ = 1;
lean_inc_ref(v_config_3563_);
v___x_3633_ = l_Std_Http_URI_Parser_parsePath(v_config_3563_, v___x_3632_, v___x_3632_, v_pos_3630_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_pos_3634_; lean_object* v_res_3635_; lean_object* v_array_3636_; lean_object* v_idx_3637_; lean_object* v___x_3638_; uint8_t v___x_3639_; 
v_pos_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_pos_3634_);
v_res_3635_ = lean_ctor_get(v___x_3633_, 1);
lean_inc(v_res_3635_);
lean_dec_ref_known(v___x_3633_, 2);
v_array_3636_ = lean_ctor_get(v_pos_3634_, 0);
lean_inc_ref(v_array_3636_);
v_idx_3637_ = lean_ctor_get(v_pos_3634_, 1);
lean_inc(v_idx_3637_);
v___x_3638_ = lean_byte_array_size(v_array_3636_);
v___x_3639_ = lean_nat_dec_lt(v_idx_3637_, v___x_3638_);
if (v___x_3639_ == 0)
{
lean_object* v___x_3640_; 
v___x_3640_ = lean_box(0);
lean_inc(v_idx_3637_);
v___y_3617_ = v_res_3631_;
v_idx_3618_ = v_idx_3637_;
v___y_3619_ = v_res_3635_;
v_pos_3620_ = v_pos_3634_;
v_array_3621_ = v_array_3636_;
v_idx_3622_ = v_idx_3637_;
v_err_3623_ = v___x_3640_;
goto v___jp_3616_;
}
else
{
uint8_t v___x_3641_; uint8_t v_got_3642_; uint8_t v___x_3643_; 
v___x_3641_ = 63;
v_got_3642_ = lean_byte_array_fget(v_array_3636_, v_idx_3637_);
v___x_3643_ = lean_uint8_dec_eq(v_got_3642_, v___x_3641_);
if (v___x_3643_ == 0)
{
lean_object* v___x_3644_; 
v___x_3644_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_3637_);
v___y_3617_ = v_res_3631_;
v_idx_3618_ = v_idx_3637_;
v___y_3619_ = v_res_3635_;
v_pos_3620_ = v_pos_3634_;
v_array_3621_ = v_array_3636_;
v_idx_3622_ = v_idx_3637_;
v_err_3623_ = v___x_3644_;
goto v___jp_3616_;
}
else
{
lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3663_; 
v_isSharedCheck_3663_ = !lean_is_exclusive(v_pos_3634_);
if (v_isSharedCheck_3663_ == 0)
{
lean_object* v_unused_3664_; lean_object* v_unused_3665_; 
v_unused_3664_ = lean_ctor_get(v_pos_3634_, 1);
lean_dec(v_unused_3664_);
v_unused_3665_ = lean_ctor_get(v_pos_3634_, 0);
lean_dec(v_unused_3665_);
v___x_3646_ = v_pos_3634_;
v_isShared_3647_ = v_isSharedCheck_3663_;
goto v_resetjp_3645_;
}
else
{
lean_dec(v_pos_3634_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3663_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3651_; 
v___x_3648_ = lean_unsigned_to_nat(1u);
v___x_3649_ = lean_nat_add(v_idx_3637_, v___x_3648_);
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 1, v___x_3649_);
v___x_3651_ = v___x_3646_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_array_3636_);
lean_ctor_set(v_reuseFailAlloc_3662_, 1, v___x_3649_);
v___x_3651_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
lean_object* v___x_3652_; 
lean_inc_ref(v_config_3563_);
v___x_3652_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3563_, v___x_3651_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v_pos_3653_; lean_object* v_res_3654_; lean_object* v_array_3655_; lean_object* v_idx_3656_; lean_object* v___x_3657_; 
lean_dec(v_idx_3637_);
v_pos_3653_ = lean_ctor_get(v___x_3652_, 0);
lean_inc(v_pos_3653_);
v_res_3654_ = lean_ctor_get(v___x_3652_, 1);
lean_inc(v_res_3654_);
lean_dec_ref_known(v___x_3652_, 2);
v_array_3655_ = lean_ctor_get(v_pos_3653_, 0);
lean_inc_ref(v_array_3655_);
v_idx_3656_ = lean_ctor_get(v_pos_3653_, 1);
lean_inc(v_idx_3656_);
v___x_3657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3657_, 0, v_res_3654_);
v___y_3594_ = v_res_3631_;
v___y_3595_ = v_res_3635_;
v_pos_3596_ = v_pos_3653_;
v_array_3597_ = v_array_3655_;
v_idx_3598_ = v_idx_3656_;
v_res_3599_ = v___x_3657_;
goto v___jp_3593_;
}
else
{
lean_object* v_pos_3658_; lean_object* v_err_3659_; lean_object* v_array_3660_; lean_object* v_idx_3661_; 
v_pos_3658_ = lean_ctor_get(v___x_3652_, 0);
lean_inc(v_pos_3658_);
v_err_3659_ = lean_ctor_get(v___x_3652_, 1);
lean_inc(v_err_3659_);
lean_dec_ref_known(v___x_3652_, 2);
v_array_3660_ = lean_ctor_get(v_pos_3658_, 0);
lean_inc_ref(v_array_3660_);
v_idx_3661_ = lean_ctor_get(v_pos_3658_, 1);
lean_inc(v_idx_3661_);
v___y_3617_ = v_res_3631_;
v_idx_3618_ = v_idx_3637_;
v___y_3619_ = v_res_3635_;
v_pos_3620_ = v_pos_3658_;
v_array_3621_ = v_array_3660_;
v_idx_3622_ = v_idx_3661_;
v_err_3623_ = v_err_3659_;
goto v___jp_3616_;
}
}
}
}
}
}
else
{
lean_object* v_err_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3673_; 
lean_dec(v_res_3631_);
lean_dec_ref(v_config_3563_);
v_err_3666_ = lean_ctor_get(v___x_3633_, 1);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3673_ == 0)
{
lean_object* v_unused_3674_; 
v_unused_3674_ = lean_ctor_get(v___x_3633_, 0);
lean_dec(v_unused_3674_);
v___x_3668_ = v___x_3633_;
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_err_3666_);
lean_dec(v___x_3633_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3671_; 
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 0, v_a_3564_);
v___x_3671_ = v___x_3668_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_a_3564_);
lean_ctor_set(v_reuseFailAlloc_3672_, 1, v_err_3666_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
}
else
{
lean_object* v_err_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3682_; 
lean_dec_ref(v_config_3563_);
v_err_3675_ = lean_ctor_get(v___x_3629_, 1);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3682_ == 0)
{
lean_object* v_unused_3683_; 
v_unused_3683_ = lean_ctor_get(v___x_3629_, 0);
lean_dec(v_unused_3683_);
v___x_3677_ = v___x_3629_;
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_err_3675_);
lean_dec(v___x_3629_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3680_; 
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 0, v_a_3564_);
v___x_3680_ = v___x_3677_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_a_3564_);
lean_ctor_set(v_reuseFailAlloc_3681_, 1, v_err_3675_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath(lean_object* v_config_3697_, lean_object* v_a_3698_){
_start:
{
uint8_t v___x_3699_; uint8_t v___x_3700_; lean_object* v___x_3701_; 
v___x_3699_ = 0;
v___x_3700_ = 1;
lean_inc_ref(v_config_3697_);
v___x_3701_ = l_Std_Http_URI_Parser_parsePath(v_config_3697_, v___x_3699_, v___x_3700_, v_a_3698_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v_pos_3702_; lean_object* v_res_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3784_; 
v_pos_3702_ = lean_ctor_get(v___x_3701_, 0);
v_res_3703_ = lean_ctor_get(v___x_3701_, 1);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3705_ = v___x_3701_;
v_isShared_3706_ = v_isSharedCheck_3784_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_res_3703_);
lean_inc(v_pos_3702_);
lean_dec(v___x_3701_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3784_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___y_3708_; lean_object* v_pos_3709_; lean_object* v_res_3710_; lean_object* v___y_3717_; lean_object* v_idx_3718_; lean_object* v_pos_3719_; lean_object* v_err_3720_; lean_object* v_pos_3726_; lean_object* v_array_3727_; lean_object* v_idx_3728_; lean_object* v_res_3729_; lean_object* v_array_3746_; lean_object* v_idx_3747_; lean_object* v_pos_3749_; lean_object* v_array_3750_; lean_object* v_idx_3751_; lean_object* v_err_3752_; lean_object* v___x_3756_; uint8_t v___x_3757_; 
v_array_3746_ = lean_ctor_get(v_pos_3702_, 0);
lean_inc_ref(v_array_3746_);
v_idx_3747_ = lean_ctor_get(v_pos_3702_, 1);
lean_inc(v_idx_3747_);
v___x_3756_ = lean_byte_array_size(v_array_3746_);
v___x_3757_ = lean_nat_dec_lt(v_idx_3747_, v___x_3756_);
if (v___x_3757_ == 0)
{
lean_object* v___x_3758_; 
v___x_3758_ = lean_box(0);
lean_inc(v_idx_3747_);
v_pos_3749_ = v_pos_3702_;
v_array_3750_ = v_array_3746_;
v_idx_3751_ = v_idx_3747_;
v_err_3752_ = v___x_3758_;
goto v___jp_3748_;
}
else
{
uint8_t v___x_3759_; uint8_t v_got_3760_; uint8_t v___x_3761_; 
v___x_3759_ = 63;
v_got_3760_ = lean_byte_array_fget(v_array_3746_, v_idx_3747_);
v___x_3761_ = lean_uint8_dec_eq(v_got_3760_, v___x_3759_);
if (v___x_3761_ == 0)
{
lean_object* v___x_3762_; 
v___x_3762_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_3747_);
v_pos_3749_ = v_pos_3702_;
v_array_3750_ = v_array_3746_;
v_idx_3751_ = v_idx_3747_;
v_err_3752_ = v___x_3762_;
goto v___jp_3748_;
}
else
{
lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3781_; 
v_isSharedCheck_3781_ = !lean_is_exclusive(v_pos_3702_);
if (v_isSharedCheck_3781_ == 0)
{
lean_object* v_unused_3782_; lean_object* v_unused_3783_; 
v_unused_3782_ = lean_ctor_get(v_pos_3702_, 1);
lean_dec(v_unused_3782_);
v_unused_3783_ = lean_ctor_get(v_pos_3702_, 0);
lean_dec(v_unused_3783_);
v___x_3764_ = v_pos_3702_;
v_isShared_3765_ = v_isSharedCheck_3781_;
goto v_resetjp_3763_;
}
else
{
lean_dec(v_pos_3702_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3781_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3769_; 
v___x_3766_ = lean_unsigned_to_nat(1u);
v___x_3767_ = lean_nat_add(v_idx_3747_, v___x_3766_);
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 1, v___x_3767_);
v___x_3769_ = v___x_3764_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_array_3746_);
lean_ctor_set(v_reuseFailAlloc_3780_, 1, v___x_3767_);
v___x_3769_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
lean_object* v___x_3770_; 
lean_inc_ref(v_config_3697_);
v___x_3770_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3697_, v___x_3769_);
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_object* v_pos_3771_; lean_object* v_res_3772_; lean_object* v_array_3773_; lean_object* v_idx_3774_; lean_object* v___x_3775_; 
lean_dec(v_idx_3747_);
v_pos_3771_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_pos_3771_);
v_res_3772_ = lean_ctor_get(v___x_3770_, 1);
lean_inc(v_res_3772_);
lean_dec_ref_known(v___x_3770_, 2);
v_array_3773_ = lean_ctor_get(v_pos_3771_, 0);
lean_inc_ref(v_array_3773_);
v_idx_3774_ = lean_ctor_get(v_pos_3771_, 1);
lean_inc(v_idx_3774_);
v___x_3775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3775_, 0, v_res_3772_);
v_pos_3726_ = v_pos_3771_;
v_array_3727_ = v_array_3773_;
v_idx_3728_ = v_idx_3774_;
v_res_3729_ = v___x_3775_;
goto v___jp_3725_;
}
else
{
lean_object* v_pos_3776_; lean_object* v_err_3777_; lean_object* v_array_3778_; lean_object* v_idx_3779_; 
v_pos_3776_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_pos_3776_);
v_err_3777_ = lean_ctor_get(v___x_3770_, 1);
lean_inc(v_err_3777_);
lean_dec_ref_known(v___x_3770_, 2);
v_array_3778_ = lean_ctor_get(v_pos_3776_, 0);
lean_inc_ref(v_array_3778_);
v_idx_3779_ = lean_ctor_get(v_pos_3776_, 1);
lean_inc(v_idx_3779_);
v_pos_3749_ = v_pos_3776_;
v_array_3750_ = v_array_3778_;
v_idx_3751_ = v_idx_3779_;
v_err_3752_ = v_err_3777_;
goto v___jp_3748_;
}
}
}
}
}
v___jp_3707_:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3714_; 
v___x_3711_ = lean_box(0);
v___x_3712_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3711_);
lean_ctor_set(v___x_3712_, 1, v_res_3703_);
lean_ctor_set(v___x_3712_, 2, v___y_3708_);
lean_ctor_set(v___x_3712_, 3, v_res_3710_);
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 1, v___x_3712_);
lean_ctor_set(v___x_3705_, 0, v_pos_3709_);
v___x_3714_ = v___x_3705_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_pos_3709_);
lean_ctor_set(v_reuseFailAlloc_3715_, 1, v___x_3712_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
v___jp_3716_:
{
lean_object* v_idx_3721_; uint8_t v___x_3722_; 
v_idx_3721_ = lean_ctor_get(v_pos_3719_, 1);
v___x_3722_ = lean_nat_dec_eq(v_idx_3718_, v_idx_3721_);
lean_dec(v_idx_3718_);
if (v___x_3722_ == 0)
{
lean_object* v___x_3723_; 
lean_dec(v___y_3717_);
lean_del_object(v___x_3705_);
lean_dec(v_res_3703_);
v___x_3723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3723_, 0, v_pos_3719_);
lean_ctor_set(v___x_3723_, 1, v_err_3720_);
return v___x_3723_;
}
else
{
lean_object* v___x_3724_; 
lean_dec(v_err_3720_);
v___x_3724_ = lean_box(0);
v___y_3708_ = v___y_3717_;
v_pos_3709_ = v_pos_3719_;
v_res_3710_ = v___x_3724_;
goto v___jp_3707_;
}
}
v___jp_3725_:
{
lean_object* v___x_3730_; uint8_t v___x_3731_; 
v___x_3730_ = lean_byte_array_size(v_array_3727_);
v___x_3731_ = lean_nat_dec_lt(v_idx_3728_, v___x_3730_);
if (v___x_3731_ == 0)
{
lean_object* v___x_3732_; 
lean_dec_ref(v_array_3727_);
lean_dec_ref(v_config_3697_);
v___x_3732_ = lean_box(0);
v___y_3717_ = v_res_3729_;
v_idx_3718_ = v_idx_3728_;
v_pos_3719_ = v_pos_3726_;
v_err_3720_ = v___x_3732_;
goto v___jp_3716_;
}
else
{
uint8_t v___x_3733_; uint8_t v_got_3734_; uint8_t v___x_3735_; 
v___x_3733_ = 35;
v_got_3734_ = lean_byte_array_fget(v_array_3727_, v_idx_3728_);
v___x_3735_ = lean_uint8_dec_eq(v_got_3734_, v___x_3733_);
if (v___x_3735_ == 0)
{
lean_object* v___x_3736_; 
lean_dec_ref(v_array_3727_);
lean_dec_ref(v_config_3697_);
v___x_3736_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v___y_3717_ = v_res_3729_;
v_idx_3718_ = v_idx_3728_;
v_pos_3719_ = v_pos_3726_;
v_err_3720_ = v___x_3736_;
goto v___jp_3716_;
}
else
{
lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
lean_dec_ref(v_pos_3726_);
v___x_3737_ = lean_unsigned_to_nat(1u);
v___x_3738_ = lean_nat_add(v_idx_3728_, v___x_3737_);
v___x_3739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3739_, 0, v_array_3727_);
lean_ctor_set(v___x_3739_, 1, v___x_3738_);
v___x_3740_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3697_, v___x_3739_);
lean_dec_ref(v_config_3697_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v_pos_3741_; lean_object* v_res_3742_; lean_object* v___x_3743_; 
lean_dec(v_idx_3728_);
v_pos_3741_ = lean_ctor_get(v___x_3740_, 0);
lean_inc(v_pos_3741_);
v_res_3742_ = lean_ctor_get(v___x_3740_, 1);
lean_inc(v_res_3742_);
lean_dec_ref_known(v___x_3740_, 2);
v___x_3743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3743_, 0, v_res_3742_);
v___y_3708_ = v_res_3729_;
v_pos_3709_ = v_pos_3741_;
v_res_3710_ = v___x_3743_;
goto v___jp_3707_;
}
else
{
lean_object* v_pos_3744_; lean_object* v_err_3745_; 
v_pos_3744_ = lean_ctor_get(v___x_3740_, 0);
lean_inc(v_pos_3744_);
v_err_3745_ = lean_ctor_get(v___x_3740_, 1);
lean_inc(v_err_3745_);
lean_dec_ref_known(v___x_3740_, 2);
v___y_3717_ = v_res_3729_;
v_idx_3718_ = v_idx_3728_;
v_pos_3719_ = v_pos_3744_;
v_err_3720_ = v_err_3745_;
goto v___jp_3716_;
}
}
}
}
v___jp_3748_:
{
uint8_t v___x_3753_; 
v___x_3753_ = lean_nat_dec_eq(v_idx_3747_, v_idx_3751_);
lean_dec(v_idx_3747_);
if (v___x_3753_ == 0)
{
lean_object* v___x_3754_; 
lean_dec(v_idx_3751_);
lean_dec_ref(v_array_3750_);
lean_del_object(v___x_3705_);
lean_dec(v_res_3703_);
lean_dec_ref(v_config_3697_);
v___x_3754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3754_, 0, v_pos_3749_);
lean_ctor_set(v___x_3754_, 1, v_err_3752_);
return v___x_3754_;
}
else
{
lean_object* v___x_3755_; 
lean_dec(v_err_3752_);
v___x_3755_ = lean_box(0);
v_pos_3726_ = v_pos_3749_;
v_array_3727_ = v_array_3750_;
v_idx_3728_ = v_idx_3751_;
v_res_3729_ = v___x_3755_;
goto v___jp_3725_;
}
}
}
}
else
{
lean_object* v_pos_3785_; lean_object* v_err_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
lean_dec_ref(v_config_3697_);
v_pos_3785_ = lean_ctor_get(v___x_3701_, 0);
v_err_3786_ = lean_ctor_get(v___x_3701_, 1);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3788_ = v___x_3701_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_err_3786_);
lean_inc(v_pos_3785_);
lean_dec(v___x_3701_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_pos_3785_);
lean_ctor_set(v_reuseFailAlloc_3792_, 1, v_err_3786_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_relative(lean_object* v_config_3794_, lean_object* v_a_3795_){
_start:
{
lean_object* v___y_3797_; lean_object* v___x_3817_; 
lean_inc_ref(v_a_3795_);
lean_inc_ref(v_config_3794_);
v___x_3817_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withAuthority(v_config_3794_, v_a_3795_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_dec_ref(v_a_3795_);
lean_dec_ref(v_config_3794_);
v___y_3797_ = v___x_3817_;
goto v___jp_3796_;
}
else
{
lean_object* v_pos_3818_; lean_object* v_idx_3819_; lean_object* v_idx_3820_; uint8_t v___x_3821_; 
v_pos_3818_ = lean_ctor_get(v___x_3817_, 0);
v_idx_3819_ = lean_ctor_get(v_a_3795_, 1);
lean_inc(v_idx_3819_);
lean_dec_ref(v_a_3795_);
v_idx_3820_ = lean_ctor_get(v_pos_3818_, 1);
v___x_3821_ = lean_nat_dec_eq(v_idx_3819_, v_idx_3820_);
lean_dec(v_idx_3819_);
if (v___x_3821_ == 0)
{
lean_dec_ref(v_config_3794_);
v___y_3797_ = v___x_3817_;
goto v___jp_3796_;
}
else
{
lean_object* v___x_3822_; 
lean_inc(v_pos_3818_);
lean_dec_ref_known(v___x_3817_, 2);
v___x_3822_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath(v_config_3794_, v_pos_3818_);
v___y_3797_ = v___x_3822_;
goto v___jp_3796_;
}
}
v___jp_3796_:
{
if (lean_obj_tag(v___y_3797_) == 0)
{
lean_object* v_pos_3798_; lean_object* v_res_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3807_; 
v_pos_3798_ = lean_ctor_get(v___y_3797_, 0);
v_res_3799_ = lean_ctor_get(v___y_3797_, 1);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___y_3797_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3801_ = v___y_3797_;
v_isShared_3802_ = v_isSharedCheck_3807_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_res_3799_);
lean_inc(v_pos_3798_);
lean_dec(v___y_3797_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3807_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3803_; lean_object* v___x_3805_; 
v___x_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3803_, 0, v_res_3799_);
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 1, v___x_3803_);
v___x_3805_ = v___x_3801_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_pos_3798_);
lean_ctor_set(v_reuseFailAlloc_3806_, 1, v___x_3803_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
else
{
lean_object* v_pos_3808_; lean_object* v_err_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3816_; 
v_pos_3808_ = lean_ctor_get(v___y_3797_, 0);
v_err_3809_ = lean_ctor_get(v___y_3797_, 1);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___y_3797_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3811_ = v___y_3797_;
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_err_3809_);
lean_inc(v_pos_3808_);
lean_dec(v___y_3797_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3814_; 
if (v_isShared_3812_ == 0)
{
v___x_3814_ = v___x_3811_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_pos_3808_);
lean_ctor_set(v_reuseFailAlloc_3815_, 1, v_err_3809_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURIReference(lean_object* v_config_3823_, lean_object* v_a_3824_){
_start:
{
lean_object* v___y_3826_; lean_object* v_pos_3827_; lean_object* v___x_3832_; 
lean_inc_ref(v_a_3824_);
lean_inc_ref(v_config_3823_);
v___x_3832_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_uri(v_config_3823_, v_a_3824_);
if (lean_obj_tag(v___x_3832_) == 0)
{
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_dec_ref(v_a_3824_);
lean_dec_ref(v_config_3823_);
return v___x_3832_;
}
else
{
lean_object* v_pos_3833_; 
v_pos_3833_ = lean_ctor_get(v___x_3832_, 0);
lean_inc(v_pos_3833_);
v___y_3826_ = v___x_3832_;
v_pos_3827_ = v_pos_3833_;
goto v___jp_3825_;
}
}
else
{
lean_object* v_err_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3841_; 
v_err_3834_ = lean_ctor_get(v___x_3832_, 1);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3841_ == 0)
{
lean_object* v_unused_3842_; 
v_unused_3842_ = lean_ctor_get(v___x_3832_, 0);
lean_dec(v_unused_3842_);
v___x_3836_ = v___x_3832_;
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_err_3834_);
lean_dec(v___x_3832_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
lean_inc_ref(v_a_3824_);
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 0, v_a_3824_);
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3824_);
lean_ctor_set(v_reuseFailAlloc_3840_, 1, v_err_3834_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
lean_inc_ref(v_a_3824_);
v___y_3826_ = v___x_3839_;
v_pos_3827_ = v_a_3824_;
goto v___jp_3825_;
}
}
}
v___jp_3825_:
{
lean_object* v_idx_3828_; lean_object* v_idx_3829_; uint8_t v___x_3830_; 
v_idx_3828_ = lean_ctor_get(v_a_3824_, 1);
lean_inc(v_idx_3828_);
lean_dec_ref(v_a_3824_);
v_idx_3829_ = lean_ctor_get(v_pos_3827_, 1);
v___x_3830_ = lean_nat_dec_eq(v_idx_3828_, v_idx_3829_);
lean_dec(v_idx_3828_);
if (v___x_3830_ == 0)
{
lean_dec_ref(v_pos_3827_);
lean_dec_ref(v_config_3823_);
return v___y_3826_;
}
else
{
lean_object* v___x_3831_; 
lean_dec_ref(v___y_3826_);
v___x_3831_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_relative(v_config_3823_, v_pos_3827_);
return v___x_3831_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader(lean_object* v_config_3849_, lean_object* v_a_3850_){
_start:
{
lean_object* v___x_3851_; 
v___x_3851_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_3849_, v_a_3850_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_object* v_pos_3852_; lean_object* v_res_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3926_; 
v_pos_3852_ = lean_ctor_get(v___x_3851_, 0);
v_res_3853_ = lean_ctor_get(v___x_3851_, 1);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3855_ = v___x_3851_;
v_isShared_3856_ = v_isSharedCheck_3926_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_res_3853_);
lean_inc(v_pos_3852_);
lean_dec(v___x_3851_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3926_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v_port_3858_; lean_object* v___y_3859_; lean_object* v_pos_3873_; lean_object* v_pos_3876_; lean_object* v_array_3877_; lean_object* v_idx_3878_; lean_object* v_array_3884_; lean_object* v_idx_3885_; lean_object* v___x_3886_; uint8_t v___x_3887_; 
v_array_3884_ = lean_ctor_get(v_pos_3852_, 0);
v_idx_3885_ = lean_ctor_get(v_pos_3852_, 1);
v___x_3886_ = lean_byte_array_size(v_array_3884_);
v___x_3887_ = lean_nat_dec_lt(v_idx_3885_, v___x_3886_);
if (v___x_3887_ == 0)
{
v_pos_3873_ = v_pos_3852_;
goto v___jp_3872_;
}
else
{
uint8_t v___x_3888_; uint8_t v___x_3889_; uint8_t v___x_3890_; 
v___x_3888_ = lean_byte_array_fget(v_array_3884_, v_idx_3885_);
v___x_3889_ = 58;
v___x_3890_ = lean_uint8_dec_eq(v___x_3888_, v___x_3889_);
if (v___x_3890_ == 0)
{
v_pos_3873_ = v_pos_3852_;
goto v___jp_3872_;
}
else
{
if (v___x_3887_ == 0)
{
lean_object* v___x_3891_; lean_object* v___x_3892_; 
lean_del_object(v___x_3855_);
lean_dec(v_res_3853_);
v___x_3891_ = lean_box(0);
v___x_3892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3892_, 0, v_pos_3852_);
lean_ctor_set(v___x_3892_, 1, v___x_3891_);
return v___x_3892_;
}
else
{
if (v___x_3890_ == 0)
{
lean_object* v___x_3893_; lean_object* v___x_3894_; 
lean_del_object(v___x_3855_);
lean_dec(v_res_3853_);
v___x_3893_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
v___x_3894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3894_, 0, v_pos_3852_);
lean_ctor_set(v___x_3894_, 1, v___x_3893_);
return v___x_3894_;
}
else
{
lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3923_; 
lean_inc(v_idx_3885_);
lean_inc_ref(v_array_3884_);
v_isSharedCheck_3923_ = !lean_is_exclusive(v_pos_3852_);
if (v_isSharedCheck_3923_ == 0)
{
lean_object* v_unused_3924_; lean_object* v_unused_3925_; 
v_unused_3924_ = lean_ctor_get(v_pos_3852_, 1);
lean_dec(v_unused_3924_);
v_unused_3925_ = lean_ctor_get(v_pos_3852_, 0);
lean_dec(v_unused_3925_);
v___x_3896_ = v_pos_3852_;
v_isShared_3897_ = v_isSharedCheck_3923_;
goto v_resetjp_3895_;
}
else
{
lean_dec(v_pos_3852_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3923_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3901_; 
v___x_3898_ = lean_unsigned_to_nat(1u);
v___x_3899_ = lean_nat_add(v_idx_3885_, v___x_3898_);
lean_dec(v_idx_3885_);
lean_inc(v___x_3899_);
lean_inc_ref(v_array_3884_);
if (v_isShared_3897_ == 0)
{
lean_ctor_set(v___x_3896_, 1, v___x_3899_);
v___x_3901_ = v___x_3896_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_array_3884_);
lean_ctor_set(v_reuseFailAlloc_3922_, 1, v___x_3899_);
v___x_3901_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
uint8_t v___x_3902_; 
v___x_3902_ = lean_nat_dec_lt(v___x_3899_, v___x_3886_);
if (v___x_3902_ == 0)
{
v_pos_3876_ = v___x_3901_;
v_array_3877_ = v_array_3884_;
v_idx_3878_ = v___x_3899_;
goto v___jp_3875_;
}
else
{
uint8_t v___x_3903_; uint8_t v___x_3904_; uint8_t v___x_3905_; 
v___x_3903_ = lean_byte_array_fget(v_array_3884_, v___x_3899_);
v___x_3904_ = 48;
v___x_3905_ = lean_uint8_dec_le(v___x_3904_, v___x_3903_);
if (v___x_3905_ == 0)
{
v_pos_3876_ = v___x_3901_;
v_array_3877_ = v_array_3884_;
v_idx_3878_ = v___x_3899_;
goto v___jp_3875_;
}
else
{
uint8_t v___x_3906_; uint8_t v___x_3907_; 
v___x_3906_ = 57;
v___x_3907_ = lean_uint8_dec_le(v___x_3903_, v___x_3906_);
if (v___x_3907_ == 0)
{
v_pos_3876_ = v___x_3901_;
v_array_3877_ = v_array_3884_;
v_idx_3878_ = v___x_3899_;
goto v___jp_3875_;
}
else
{
lean_object* v___x_3908_; 
lean_dec(v___x_3899_);
lean_dec_ref(v_array_3884_);
v___x_3908_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_3901_);
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_object* v_pos_3909_; lean_object* v_res_3910_; lean_object* v___x_3911_; uint16_t v___x_3912_; 
v_pos_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_pos_3909_);
v_res_3910_ = lean_ctor_get(v___x_3908_, 1);
lean_inc(v_res_3910_);
lean_dec_ref_known(v___x_3908_, 2);
v___x_3911_ = lean_alloc_ctor(2, 0, 2);
v___x_3912_ = lean_unbox(v_res_3910_);
lean_dec(v_res_3910_);
lean_ctor_set_uint16(v___x_3911_, 0, v___x_3912_);
v_port_3858_ = v___x_3911_;
v___y_3859_ = v_pos_3909_;
goto v___jp_3857_;
}
else
{
lean_object* v_pos_3913_; lean_object* v_err_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3921_; 
lean_del_object(v___x_3855_);
lean_dec(v_res_3853_);
v_pos_3913_ = lean_ctor_get(v___x_3908_, 0);
v_err_3914_ = lean_ctor_get(v___x_3908_, 1);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3908_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3916_ = v___x_3908_;
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_err_3914_);
lean_inc(v_pos_3913_);
lean_dec(v___x_3908_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3917_ == 0)
{
v___x_3919_ = v___x_3916_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_pos_3913_);
lean_ctor_set(v_reuseFailAlloc_3920_, 1, v_err_3914_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
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
v___jp_3857_:
{
lean_object* v_array_3860_; lean_object* v_idx_3861_; lean_object* v___x_3862_; uint8_t v___x_3863_; 
v_array_3860_ = lean_ctor_get(v___y_3859_, 0);
v_idx_3861_ = lean_ctor_get(v___y_3859_, 1);
v___x_3862_ = lean_byte_array_size(v_array_3860_);
v___x_3863_ = lean_nat_dec_lt(v_idx_3861_, v___x_3862_);
if (v___x_3863_ == 0)
{
lean_object* v___x_3864_; lean_object* v___x_3866_; 
v___x_3864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3864_, 0, v_res_3853_);
lean_ctor_set(v___x_3864_, 1, v_port_3858_);
if (v_isShared_3856_ == 0)
{
lean_ctor_set(v___x_3855_, 1, v___x_3864_);
lean_ctor_set(v___x_3855_, 0, v___y_3859_);
v___x_3866_ = v___x_3855_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v___y_3859_);
lean_ctor_set(v_reuseFailAlloc_3867_, 1, v___x_3864_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
else
{
lean_object* v___x_3868_; lean_object* v___x_3870_; 
lean_dec(v_port_3858_);
lean_dec(v_res_3853_);
v___x_3868_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__1));
if (v_isShared_3856_ == 0)
{
lean_ctor_set_tag(v___x_3855_, 1);
lean_ctor_set(v___x_3855_, 1, v___x_3868_);
lean_ctor_set(v___x_3855_, 0, v___y_3859_);
v___x_3870_ = v___x_3855_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___y_3859_);
lean_ctor_set(v_reuseFailAlloc_3871_, 1, v___x_3868_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
v___jp_3872_:
{
lean_object* v___x_3874_; 
v___x_3874_ = lean_box(0);
v_port_3858_ = v___x_3874_;
v___y_3859_ = v_pos_3873_;
goto v___jp_3857_;
}
v___jp_3875_:
{
lean_object* v___x_3879_; uint8_t v___x_3880_; 
v___x_3879_ = lean_byte_array_size(v_array_3877_);
lean_dec_ref(v_array_3877_);
v___x_3880_ = lean_nat_dec_lt(v_idx_3878_, v___x_3879_);
lean_dec(v_idx_3878_);
if (v___x_3880_ == 0)
{
lean_object* v___x_3881_; 
v___x_3881_ = lean_box(1);
v_port_3858_ = v___x_3881_;
v___y_3859_ = v_pos_3876_;
goto v___jp_3857_;
}
else
{
lean_object* v___x_3882_; lean_object* v___x_3883_; 
lean_del_object(v___x_3855_);
lean_dec(v_res_3853_);
v___x_3882_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__3));
v___x_3883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3883_, 0, v_pos_3876_);
lean_ctor_set(v___x_3883_, 1, v___x_3882_);
return v___x_3883_;
}
}
}
}
else
{
lean_object* v_pos_3927_; lean_object* v_err_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
v_pos_3927_ = lean_ctor_get(v___x_3851_, 0);
v_err_3928_ = lean_ctor_get(v___x_3851_, 1);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3930_ = v___x_3851_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_err_3928_);
lean_inc(v_pos_3927_);
lean_dec(v___x_3851_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_pos_3927_);
lean_ctor_set(v_reuseFailAlloc_3934_, 1, v_err_3928_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader___boxed(lean_object* v_config_3936_, lean_object* v_a_3937_){
_start:
{
lean_object* v_res_3938_; 
v_res_3938_ = l_Std_Http_URI_Parser_parseHostHeader(v_config_3936_, v_a_3937_);
lean_dec_ref(v_config_3936_);
return v_res_3938_;
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
