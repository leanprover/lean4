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
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Http_URI_isValidDomainLabel(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_uv_pton_v4(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_uv_pton_v6(lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(lean_object*);
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
lean_object* v___y_154_; lean_object* v___y_155_; uint32_t v___y_159_; lean_object* v___x_171_; uint8_t v_decide_172_; 
v___x_171_ = lean_string_utf8_byte_size(v_s_151_);
v_decide_172_ = lean_nat_dec_eq(v_p_152_, v___x_171_);
if (v_decide_172_ == 0)
{
uint32_t v___x_173_; uint32_t v___x_174_; uint8_t v___x_175_; 
v___x_173_ = lean_string_utf8_get_fast(v_s_151_, v_p_152_);
v___x_174_ = 65;
v___x_175_ = lean_uint32_dec_le(v___x_174_, v___x_173_);
if (v___x_175_ == 0)
{
v___y_159_ = v___x_173_;
goto v___jp_158_;
}
else
{
uint32_t v___x_176_; uint8_t v___x_177_; 
v___x_176_ = 90;
v___x_177_ = lean_uint32_dec_le(v___x_173_, v___x_176_);
if (v___x_177_ == 0)
{
v___y_159_ = v___x_173_;
goto v___jp_158_;
}
else
{
uint32_t v___x_178_; uint32_t v___x_179_; 
v___x_178_ = 32;
v___x_179_ = lean_uint32_add(v___x_173_, v___x_178_);
v___y_159_ = v___x_179_;
goto v___jp_158_;
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
lean_object* v___x_156_; 
v___x_156_ = lean_nat_add(v_p_152_, v___y_155_);
lean_dec(v_p_152_);
v_s_151_ = v___y_154_;
v_p_152_ = v___x_156_;
goto _start;
}
v___jp_158_:
{
lean_object* v___x_160_; uint32_t v___x_161_; uint8_t v___x_162_; 
lean_inc(v_p_152_);
v___x_160_ = lean_string_utf8_set(v_s_151_, v_p_152_, v___y_159_);
v___x_161_ = 127;
v___x_162_ = lean_uint32_dec_le(v___y_159_, v___x_161_);
if (v___x_162_ == 0)
{
uint32_t v___x_163_; uint8_t v___x_164_; 
v___x_163_ = 2047;
v___x_164_ = lean_uint32_dec_le(v___y_159_, v___x_163_);
if (v___x_164_ == 0)
{
uint32_t v___x_165_; uint8_t v___x_166_; 
v___x_165_ = 65535;
v___x_166_ = lean_uint32_dec_le(v___y_159_, v___x_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; 
v___x_167_ = lean_unsigned_to_nat(4u);
v___y_154_ = v___x_160_;
v___y_155_ = v___x_167_;
goto v___jp_153_;
}
else
{
lean_object* v___x_168_; 
v___x_168_ = lean_unsigned_to_nat(3u);
v___y_154_ = v___x_160_;
v___y_155_ = v___x_168_;
goto v___jp_153_;
}
}
else
{
lean_object* v___x_169_; 
v___x_169_ = lean_unsigned_to_nat(2u);
v___y_154_ = v___x_160_;
v___y_155_ = v___x_169_;
goto v___jp_153_;
}
}
else
{
lean_object* v___x_170_; 
v___x_170_ = lean_unsigned_to_nat(1u);
v___y_154_ = v___x_160_;
v___y_155_ = v___x_170_;
goto v___jp_153_;
}
}
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_189_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6));
v___x_190_ = lean_unsigned_to_nat(46u);
v___x_191_ = lean_unsigned_to_nat(193u);
v___x_192_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5));
v___x_193_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__4));
v___x_194_ = l_mkPanicMessageWithDecl(v___x_193_, v___x_192_, v___x_191_, v___x_190_, v___x_189_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(lean_object* v_config_199_, lean_object* v_a_200_){
_start:
{
lean_object* v___y_205_; lean_object* v___y_209_; uint32_t v___y_210_; lean_object* v___y_211_; lean_object* v_maxSchemeLength_217_; lean_object* v___x_218_; lean_object* v___y_220_; lean_object* v___y_221_; uint8_t v___x_237_; lean_object* v___y_239_; lean_object* v___y_240_; uint8_t v___y_241_; lean_object* v_lower_242_; lean_object* v_upper_243_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_259_; uint8_t v___y_260_; lean_object* v___y_261_; 
v_maxSchemeLength_217_ = lean_ctor_get(v_config_199_, 0);
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_237_ = lean_nat_dec_eq(v_maxSchemeLength_217_, v___x_218_);
if (v___x_237_ == 0)
{
lean_object* v_array_263_; lean_object* v_idx_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v_array_263_ = lean_ctor_get(v_a_200_, 0);
v_idx_264_ = lean_ctor_get(v_a_200_, 1);
v___x_265_ = lean_byte_array_size(v_array_263_);
v___x_266_ = lean_nat_dec_lt(v_idx_264_, v___x_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_box(0);
v___x_268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_268_, 0, v_a_200_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
return v___x_268_;
}
else
{
lean_object* v___f_269_; lean_object* v_pos_271_; uint8_t v_res_272_; uint8_t v_c_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v_it_x27_287_; uint8_t v___x_293_; uint8_t v___x_294_; 
v___f_269_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__8));
v_c_284_ = lean_byte_array_fget(v_array_263_, v_idx_264_);
v___x_285_ = lean_unsigned_to_nat(1u);
v___x_286_ = lean_nat_add(v_idx_264_, v___x_285_);
lean_inc_ref(v_array_263_);
v_it_x27_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_287_, 0, v_array_263_);
lean_ctor_set(v_it_x27_287_, 1, v___x_286_);
v___x_293_ = 65;
v___x_294_ = lean_uint8_dec_le(v___x_293_, v_c_284_);
if (v___x_294_ == 0)
{
goto v___jp_288_;
}
else
{
uint8_t v___x_295_; uint8_t v___x_296_; 
v___x_295_ = 90;
v___x_296_ = lean_uint8_dec_le(v_c_284_, v___x_295_);
if (v___x_296_ == 0)
{
goto v___jp_288_;
}
else
{
lean_dec_ref(v_a_200_);
v_pos_271_ = v_it_x27_287_;
v_res_272_ = v_c_284_;
goto v___jp_270_;
}
}
v___jp_270_:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v_snd_276_; lean_object* v_fst_277_; lean_object* v_fst_278_; lean_object* v_array_279_; lean_object* v_idx_280_; lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_273_ = lean_unsigned_to_nat(1u);
v___x_274_ = lean_nat_sub(v_maxSchemeLength_217_, v___x_273_);
lean_inc_ref(v_pos_271_);
v___x_275_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_269_, v___x_274_, v___x_218_, v_pos_271_);
lean_dec(v___x_274_);
v_snd_276_ = lean_ctor_get(v___x_275_, 1);
lean_inc(v_snd_276_);
v_fst_277_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_fst_277_);
lean_dec_ref(v___x_275_);
v_fst_278_ = lean_ctor_get(v_snd_276_, 0);
lean_inc(v_fst_278_);
lean_dec(v_snd_276_);
v_array_279_ = lean_ctor_get(v_pos_271_, 0);
lean_inc_ref(v_array_279_);
v_idx_280_ = lean_ctor_get(v_pos_271_, 1);
lean_inc(v_idx_280_);
lean_dec_ref(v_pos_271_);
v___x_281_ = lean_nat_add(v_idx_280_, v_fst_277_);
lean_dec(v_fst_277_);
v___x_282_ = lean_byte_array_size(v_array_279_);
v___x_283_ = lean_nat_dec_le(v_idx_280_, v___x_218_);
if (v___x_283_ == 0)
{
v___y_256_ = v_fst_278_;
v___y_257_ = v___x_282_;
v___y_258_ = v_array_279_;
v___y_259_ = v___x_281_;
v___y_260_ = v_res_272_;
v___y_261_ = v_idx_280_;
goto v___jp_255_;
}
else
{
lean_dec(v_idx_280_);
v___y_256_ = v_fst_278_;
v___y_257_ = v___x_282_;
v___y_258_ = v_array_279_;
v___y_259_ = v___x_281_;
v___y_260_ = v_res_272_;
v___y_261_ = v___x_218_;
goto v___jp_255_;
}
}
v___jp_288_:
{
uint8_t v___x_289_; uint8_t v___x_290_; 
v___x_289_ = 97;
v___x_290_ = lean_uint8_dec_le(v___x_289_, v_c_284_);
if (v___x_290_ == 0)
{
lean_dec_ref_known(v_it_x27_287_, 2);
goto v___jp_201_;
}
else
{
uint8_t v___x_291_; uint8_t v___x_292_; 
v___x_291_ = 122;
v___x_292_ = lean_uint8_dec_le(v_c_284_, v___x_291_);
if (v___x_292_ == 0)
{
lean_dec_ref_known(v_it_x27_287_, 2);
goto v___jp_201_;
}
else
{
lean_dec_ref(v_a_200_);
v_pos_271_ = v_it_x27_287_;
v_res_272_ = v_c_284_;
goto v___jp_270_;
}
}
}
}
}
else
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10));
v___x_298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_298_, 0, v_a_200_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
return v___x_298_;
}
v___jp_201_:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__1));
v___x_203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_203_, 0, v_a_200_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
return v___x_203_;
}
v___jp_204_:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__3));
v___x_207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_207_, 0, v___y_205_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
return v___x_207_;
}
v___jp_208_:
{
uint32_t v___x_212_; uint8_t v___x_213_; 
v___x_212_ = 97;
v___x_213_ = lean_uint32_dec_le(v___x_212_, v___y_210_);
if (v___x_213_ == 0)
{
lean_dec_ref(v___y_211_);
v___y_205_ = v___y_209_;
goto v___jp_204_;
}
else
{
uint32_t v___x_214_; uint8_t v___x_215_; 
v___x_214_ = 122;
v___x_215_ = lean_uint32_dec_le(v___y_210_, v___x_214_);
if (v___x_215_ == 0)
{
lean_dec_ref(v___y_211_);
v___y_205_ = v___y_209_;
goto v___jp_204_;
}
else
{
lean_object* v___x_216_; 
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v___y_209_);
lean_ctor_set(v___x_216_, 1, v___y_211_);
return v___x_216_;
}
}
}
v___jp_219_:
{
lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_222_ = l_String_mapAux___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(v___y_221_, v___x_218_);
lean_inc_ref(v___x_222_);
v___x_223_ = l_Std_Http_Internal_instDecidableIsLowerCase(v___x_222_);
if (v___x_223_ == 0)
{
lean_dec_ref(v___x_222_);
v___y_205_ = v___y_220_;
goto v___jp_204_;
}
else
{
lean_object* v___x_224_; uint8_t v___x_225_; 
lean_inc_ref(v___x_222_);
v___x_224_ = l_String_toListImpl(v___x_222_);
v___x_225_ = l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(v___x_224_);
if (v___x_225_ == 0)
{
lean_dec(v___x_224_);
lean_dec_ref(v___x_222_);
v___y_205_ = v___y_220_;
goto v___jp_204_;
}
else
{
lean_object* v___x_226_; 
v___x_226_ = l_List_head_x3f___redArg(v___x_224_);
lean_dec(v___x_224_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_dec_ref(v___x_222_);
v___y_205_ = v___y_220_;
goto v___jp_204_;
}
else
{
lean_object* v_val_227_; uint32_t v___x_228_; uint32_t v___x_229_; uint8_t v___x_230_; 
v_val_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_val_227_);
lean_dec_ref_known(v___x_226_, 1);
v___x_228_ = 65;
v___x_229_ = lean_unbox_uint32(v_val_227_);
v___x_230_ = lean_uint32_dec_le(v___x_228_, v___x_229_);
if (v___x_230_ == 0)
{
uint32_t v___x_231_; 
v___x_231_ = lean_unbox_uint32(v_val_227_);
lean_dec(v_val_227_);
v___y_209_ = v___y_220_;
v___y_210_ = v___x_231_;
v___y_211_ = v___x_222_;
goto v___jp_208_;
}
else
{
uint32_t v___x_232_; uint32_t v___x_233_; uint8_t v___x_234_; 
v___x_232_ = 90;
v___x_233_ = lean_unbox_uint32(v_val_227_);
v___x_234_ = lean_uint32_dec_le(v___x_233_, v___x_232_);
if (v___x_234_ == 0)
{
uint32_t v___x_235_; 
v___x_235_ = lean_unbox_uint32(v_val_227_);
lean_dec(v_val_227_);
v___y_209_ = v___y_220_;
v___y_210_ = v___x_235_;
v___y_211_ = v___x_222_;
goto v___jp_208_;
}
else
{
lean_object* v___x_236_; 
lean_dec(v_val_227_);
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v___y_220_);
lean_ctor_set(v___x_236_, 1, v___x_222_);
return v___x_236_;
}
}
}
}
}
}
v___jp_238_:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_244_ = l_ByteArray_toByteSlice(v___y_240_, v_lower_242_, v_upper_243_);
v___x_245_ = l_ByteArray_empty;
v___x_246_ = lean_byte_array_push(v___x_245_, v___y_241_);
v___x_247_ = l_ByteSlice_toByteArray(v___x_244_);
v___x_248_ = lean_byte_array_size(v___x_246_);
v___x_249_ = lean_byte_array_size(v___x_247_);
v___x_250_ = lean_byte_array_copy_slice(v___x_247_, v___x_218_, v___x_246_, v___x_248_, v___x_249_, v___x_237_);
lean_dec_ref(v___x_247_);
v___x_251_ = lean_string_validate_utf8(v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; lean_object* v___x_253_; 
lean_dec_ref(v___x_250_);
v___x_252_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_253_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_252_);
v___y_220_ = v___y_239_;
v___y_221_ = v___x_253_;
goto v___jp_219_;
}
else
{
lean_object* v___x_254_; 
v___x_254_ = lean_string_from_utf8_unchecked(v___x_250_);
v___y_220_ = v___y_239_;
v___y_221_ = v___x_254_;
goto v___jp_219_;
}
}
v___jp_255_:
{
uint8_t v___x_262_; 
v___x_262_ = lean_nat_dec_le(v___y_259_, v___y_257_);
if (v___x_262_ == 0)
{
lean_dec(v___y_259_);
v___y_239_ = v___y_256_;
v___y_240_ = v___y_258_;
v___y_241_ = v___y_260_;
v_lower_242_ = v___y_261_;
v_upper_243_ = v___y_257_;
goto v___jp_238_;
}
else
{
lean_dec(v___y_257_);
v___y_239_ = v___y_256_;
v___y_240_ = v___y_258_;
v___y_241_ = v___y_260_;
v_lower_242_ = v___y_261_;
v_upper_243_ = v___y_259_;
goto v___jp_238_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___boxed(lean_object* v_config_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_299_, v_a_300_);
lean_dec_ref(v_config_299_);
return v_res_301_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0(uint8_t v___y_302_){
_start:
{
uint8_t v___x_303_; uint8_t v___x_304_; 
v___x_303_ = 48;
v___x_304_ = lean_uint8_dec_le(v___x_303_, v___y_302_);
if (v___x_304_ == 0)
{
return v___x_304_;
}
else
{
uint8_t v___x_305_; uint8_t v___x_306_; 
v___x_305_ = 57;
v___x_306_ = lean_uint8_dec_le(v___y_302_, v___x_305_);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0___boxed(lean_object* v___y_307_){
_start:
{
uint8_t v___y_560__boxed_308_; uint8_t v_res_309_; lean_object* v_r_310_; 
v___y_560__boxed_308_ = lean_unbox(v___y_307_);
v_res_309_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0(v___y_560__boxed_308_);
v_r_310_ = lean_box(v_res_309_);
return v_r_310_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(lean_object* v_a_314_){
_start:
{
lean_object* v___f_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v_snd_319_; lean_object* v_fst_320_; lean_object* v_fst_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_374_; 
v___f_315_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__0));
v___x_316_ = lean_unsigned_to_nat(5u);
v___x_317_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_314_);
v___x_318_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_315_, v___x_316_, v___x_317_, v_a_314_);
v_snd_319_ = lean_ctor_get(v___x_318_, 1);
lean_inc(v_snd_319_);
v_fst_320_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_fst_320_);
lean_dec_ref(v___x_318_);
v_fst_321_ = lean_ctor_get(v_snd_319_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v_snd_319_);
if (v_isSharedCheck_374_ == 0)
{
lean_object* v_unused_375_; 
v_unused_375_ = lean_ctor_get(v_snd_319_, 1);
lean_dec(v_unused_375_);
v___x_323_ = v_snd_319_;
v_isShared_324_ = v_isSharedCheck_374_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_fst_321_);
lean_dec(v_snd_319_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_374_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___y_326_; lean_object* v_array_357_; lean_object* v_idx_358_; lean_object* v_lower_360_; lean_object* v_upper_361_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___y_371_; uint8_t v___x_373_; 
v_array_357_ = lean_ctor_get(v_a_314_, 0);
lean_inc_ref(v_array_357_);
v_idx_358_ = lean_ctor_get(v_a_314_, 1);
lean_inc(v_idx_358_);
lean_dec_ref(v_a_314_);
v___x_368_ = lean_nat_add(v_idx_358_, v_fst_320_);
lean_dec(v_fst_320_);
v___x_369_ = lean_byte_array_size(v_array_357_);
v___x_373_ = lean_nat_dec_le(v_idx_358_, v___x_317_);
if (v___x_373_ == 0)
{
v___y_371_ = v_idx_358_;
goto v___jp_370_;
}
else
{
lean_dec(v_idx_358_);
v___y_371_ = v___x_317_;
goto v___jp_370_;
}
v___jp_325_:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_327_ = lean_string_utf8_byte_size(v___y_326_);
lean_inc_ref(v___y_326_);
v___x_328_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_328_, 0, v___y_326_);
lean_ctor_set(v___x_328_, 1, v___x_317_);
lean_ctor_set(v___x_328_, 2, v___x_327_);
v___x_329_ = l_String_Slice_toNat_x3f(v___x_328_);
lean_dec_ref_known(v___x_328_, 3);
if (lean_obj_tag(v___x_329_) == 1)
{
lean_object* v_val_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_350_; 
lean_dec_ref(v___y_326_);
v_val_330_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_350_ == 0)
{
v___x_332_ = v___x_329_;
v_isShared_333_ = v_isSharedCheck_350_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_val_330_);
lean_dec(v___x_329_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_350_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = lean_unsigned_to_nat(65535u);
v___x_335_ = lean_nat_dec_lt(v___x_334_, v_val_330_);
if (v___x_335_ == 0)
{
uint16_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_339_; 
lean_del_object(v___x_332_);
v___x_336_ = lean_uint16_of_nat(v_val_330_);
lean_dec(v_val_330_);
v___x_337_ = lean_box(v___x_336_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 1, v___x_337_);
v___x_339_ = v___x_323_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_fst_321_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
else
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_341_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__1));
v___x_342_ = l_Nat_reprFast(v_val_330_);
v___x_343_ = lean_string_append(v___x_341_, v___x_342_);
lean_dec_ref(v___x_342_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 0, v___x_343_);
v___x_345_ = v___x_332_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_349_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_object* v___x_347_; 
if (v_isShared_324_ == 0)
{
lean_ctor_set_tag(v___x_323_, 1);
lean_ctor_set(v___x_323_, 1, v___x_345_);
v___x_347_ = v___x_323_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_fst_321_);
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
}
}
else
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_355_; 
lean_dec(v___x_329_);
v___x_351_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__2));
v___x_352_ = lean_string_append(v___x_351_, v___y_326_);
lean_dec_ref(v___y_326_);
v___x_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
if (v_isShared_324_ == 0)
{
lean_ctor_set_tag(v___x_323_, 1);
lean_ctor_set(v___x_323_, 1, v___x_353_);
v___x_355_ = v___x_323_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_fst_321_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v___x_353_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
v___jp_359_:
{
lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_362_ = l_ByteArray_toByteSlice(v_array_357_, v_lower_360_, v_upper_361_);
v___x_363_ = l_ByteSlice_toByteArray(v___x_362_);
v___x_364_ = lean_string_validate_utf8(v___x_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; 
lean_dec_ref(v___x_363_);
v___x_365_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_366_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_365_);
v___y_326_ = v___x_366_;
goto v___jp_325_;
}
else
{
lean_object* v___x_367_; 
v___x_367_ = lean_string_from_utf8_unchecked(v___x_363_);
v___y_326_ = v___x_367_;
goto v___jp_325_;
}
}
v___jp_370_:
{
uint8_t v___x_372_; 
v___x_372_ = lean_nat_dec_le(v___x_368_, v___x_369_);
if (v___x_372_ == 0)
{
lean_dec(v___x_368_);
v_lower_360_ = v___y_371_;
v_upper_361_ = v___x_369_;
goto v___jp_359_;
}
else
{
v_lower_360_ = v___y_371_;
v_upper_361_ = v___x_368_;
goto v___jp_359_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0(uint8_t v_x_376_){
_start:
{
uint8_t v___x_422_; uint8_t v___x_423_; 
v___x_422_ = 58;
v___x_423_ = lean_uint8_dec_eq(v_x_376_, v___x_422_);
if (v___x_423_ == 0)
{
uint8_t v___x_424_; uint8_t v___x_425_; 
v___x_424_ = 48;
v___x_425_ = lean_uint8_dec_le(v___x_424_, v_x_376_);
if (v___x_425_ == 0)
{
goto v___jp_417_;
}
else
{
uint8_t v___x_426_; uint8_t v___x_427_; 
v___x_426_ = 57;
v___x_427_ = lean_uint8_dec_le(v_x_376_, v___x_426_);
if (v___x_427_ == 0)
{
goto v___jp_417_;
}
else
{
return v___x_427_;
}
}
}
else
{
uint8_t v___x_428_; 
v___x_428_ = 0;
return v___x_428_;
}
v___jp_377_:
{
uint8_t v___x_378_; uint8_t v___x_379_; 
v___x_378_ = 45;
v___x_379_ = lean_uint8_dec_eq(v_x_376_, v___x_378_);
if (v___x_379_ == 0)
{
uint8_t v___x_380_; uint8_t v___x_381_; 
v___x_380_ = 46;
v___x_381_ = lean_uint8_dec_eq(v_x_376_, v___x_380_);
if (v___x_381_ == 0)
{
uint8_t v___x_382_; uint8_t v___x_383_; 
v___x_382_ = 95;
v___x_383_ = lean_uint8_dec_eq(v_x_376_, v___x_382_);
if (v___x_383_ == 0)
{
uint8_t v___x_384_; uint8_t v___x_385_; 
v___x_384_ = 126;
v___x_385_ = lean_uint8_dec_eq(v_x_376_, v___x_384_);
if (v___x_385_ == 0)
{
uint8_t v___x_386_; uint8_t v___x_387_; 
v___x_386_ = 33;
v___x_387_ = lean_uint8_dec_eq(v_x_376_, v___x_386_);
if (v___x_387_ == 0)
{
uint8_t v___x_388_; uint8_t v___x_389_; 
v___x_388_ = 36;
v___x_389_ = lean_uint8_dec_eq(v_x_376_, v___x_388_);
if (v___x_389_ == 0)
{
uint8_t v___x_390_; uint8_t v___x_391_; 
v___x_390_ = 38;
v___x_391_ = lean_uint8_dec_eq(v_x_376_, v___x_390_);
if (v___x_391_ == 0)
{
uint8_t v___x_392_; uint8_t v___x_393_; 
v___x_392_ = 39;
v___x_393_ = lean_uint8_dec_eq(v_x_376_, v___x_392_);
if (v___x_393_ == 0)
{
uint8_t v___x_394_; uint8_t v___x_395_; 
v___x_394_ = 40;
v___x_395_ = lean_uint8_dec_eq(v_x_376_, v___x_394_);
if (v___x_395_ == 0)
{
uint8_t v___x_396_; uint8_t v___x_397_; 
v___x_396_ = 41;
v___x_397_ = lean_uint8_dec_eq(v_x_376_, v___x_396_);
if (v___x_397_ == 0)
{
uint8_t v___x_398_; uint8_t v___x_399_; 
v___x_398_ = 42;
v___x_399_ = lean_uint8_dec_eq(v_x_376_, v___x_398_);
if (v___x_399_ == 0)
{
uint8_t v___x_400_; uint8_t v___x_401_; 
v___x_400_ = 43;
v___x_401_ = lean_uint8_dec_eq(v_x_376_, v___x_400_);
if (v___x_401_ == 0)
{
uint8_t v___x_402_; uint8_t v___x_403_; 
v___x_402_ = 44;
v___x_403_ = lean_uint8_dec_eq(v_x_376_, v___x_402_);
if (v___x_403_ == 0)
{
uint8_t v___x_404_; uint8_t v___x_405_; 
v___x_404_ = 59;
v___x_405_ = lean_uint8_dec_eq(v_x_376_, v___x_404_);
if (v___x_405_ == 0)
{
uint8_t v___x_406_; uint8_t v___x_407_; 
v___x_406_ = 61;
v___x_407_ = lean_uint8_dec_eq(v_x_376_, v___x_406_);
if (v___x_407_ == 0)
{
uint8_t v___x_408_; uint8_t v___x_409_; 
v___x_408_ = 58;
v___x_409_ = lean_uint8_dec_eq(v_x_376_, v___x_408_);
if (v___x_409_ == 0)
{
uint8_t v___x_410_; uint8_t v___x_411_; 
v___x_410_ = 37;
v___x_411_ = lean_uint8_dec_eq(v_x_376_, v___x_410_);
return v___x_411_;
}
else
{
return v___x_409_;
}
}
else
{
return v___x_407_;
}
}
else
{
return v___x_405_;
}
}
else
{
return v___x_403_;
}
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
v___jp_412_:
{
uint8_t v___x_413_; uint8_t v___x_414_; 
v___x_413_ = 65;
v___x_414_ = lean_uint8_dec_le(v___x_413_, v_x_376_);
if (v___x_414_ == 0)
{
goto v___jp_377_;
}
else
{
uint8_t v___x_415_; uint8_t v___x_416_; 
v___x_415_ = 90;
v___x_416_ = lean_uint8_dec_le(v_x_376_, v___x_415_);
if (v___x_416_ == 0)
{
goto v___jp_377_;
}
else
{
return v___x_416_;
}
}
}
v___jp_417_:
{
uint8_t v___x_418_; uint8_t v___x_419_; 
v___x_418_ = 97;
v___x_419_ = lean_uint8_dec_le(v___x_418_, v_x_376_);
if (v___x_419_ == 0)
{
goto v___jp_412_;
}
else
{
uint8_t v___x_420_; uint8_t v___x_421_; 
v___x_420_ = 122;
v___x_421_ = lean_uint8_dec_le(v_x_376_, v___x_420_);
if (v___x_421_ == 0)
{
goto v___jp_412_;
}
else
{
return v___x_421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___boxed(lean_object* v_x_429_){
_start:
{
uint8_t v_x_boxed_430_; uint8_t v_res_431_; lean_object* v_r_432_; 
v_x_boxed_430_ = lean_unbox(v_x_429_);
v_res_431_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0(v_x_boxed_430_);
v_r_432_ = lean_box(v_res_431_);
return v_r_432_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1(uint8_t v___x_433_, uint8_t v___x_434_, uint8_t v_x_435_){
_start:
{
uint8_t v___x_480_; uint8_t v___x_481_; 
v___x_480_ = 48;
v___x_481_ = lean_uint8_dec_le(v___x_480_, v_x_435_);
if (v___x_481_ == 0)
{
goto v___jp_475_;
}
else
{
uint8_t v___x_482_; uint8_t v___x_483_; 
v___x_482_ = 57;
v___x_483_ = lean_uint8_dec_le(v_x_435_, v___x_482_);
if (v___x_483_ == 0)
{
goto v___jp_475_;
}
else
{
return v___x_434_;
}
}
v___jp_436_:
{
uint8_t v___x_437_; uint8_t v___x_438_; 
v___x_437_ = 45;
v___x_438_ = lean_uint8_dec_eq(v_x_435_, v___x_437_);
if (v___x_438_ == 0)
{
uint8_t v___x_439_; uint8_t v___x_440_; 
v___x_439_ = 46;
v___x_440_ = lean_uint8_dec_eq(v_x_435_, v___x_439_);
if (v___x_440_ == 0)
{
uint8_t v___x_441_; uint8_t v___x_442_; 
v___x_441_ = 95;
v___x_442_ = lean_uint8_dec_eq(v_x_435_, v___x_441_);
if (v___x_442_ == 0)
{
uint8_t v___x_443_; uint8_t v___x_444_; 
v___x_443_ = 126;
v___x_444_ = lean_uint8_dec_eq(v_x_435_, v___x_443_);
if (v___x_444_ == 0)
{
uint8_t v___x_445_; uint8_t v___x_446_; 
v___x_445_ = 33;
v___x_446_ = lean_uint8_dec_eq(v_x_435_, v___x_445_);
if (v___x_446_ == 0)
{
uint8_t v___x_447_; uint8_t v___x_448_; 
v___x_447_ = 36;
v___x_448_ = lean_uint8_dec_eq(v_x_435_, v___x_447_);
if (v___x_448_ == 0)
{
uint8_t v___x_449_; uint8_t v___x_450_; 
v___x_449_ = 38;
v___x_450_ = lean_uint8_dec_eq(v_x_435_, v___x_449_);
if (v___x_450_ == 0)
{
uint8_t v___x_451_; uint8_t v___x_452_; 
v___x_451_ = 39;
v___x_452_ = lean_uint8_dec_eq(v_x_435_, v___x_451_);
if (v___x_452_ == 0)
{
uint8_t v___x_453_; uint8_t v___x_454_; 
v___x_453_ = 40;
v___x_454_ = lean_uint8_dec_eq(v_x_435_, v___x_453_);
if (v___x_454_ == 0)
{
uint8_t v___x_455_; uint8_t v___x_456_; 
v___x_455_ = 41;
v___x_456_ = lean_uint8_dec_eq(v_x_435_, v___x_455_);
if (v___x_456_ == 0)
{
uint8_t v___x_457_; uint8_t v___x_458_; 
v___x_457_ = 42;
v___x_458_ = lean_uint8_dec_eq(v_x_435_, v___x_457_);
if (v___x_458_ == 0)
{
uint8_t v___x_459_; uint8_t v___x_460_; 
v___x_459_ = 43;
v___x_460_ = lean_uint8_dec_eq(v_x_435_, v___x_459_);
if (v___x_460_ == 0)
{
uint8_t v___x_461_; uint8_t v___x_462_; 
v___x_461_ = 44;
v___x_462_ = lean_uint8_dec_eq(v_x_435_, v___x_461_);
if (v___x_462_ == 0)
{
uint8_t v___x_463_; uint8_t v___x_464_; 
v___x_463_ = 59;
v___x_464_ = lean_uint8_dec_eq(v_x_435_, v___x_463_);
if (v___x_464_ == 0)
{
uint8_t v___x_465_; uint8_t v___x_466_; 
v___x_465_ = 61;
v___x_466_ = lean_uint8_dec_eq(v_x_435_, v___x_465_);
if (v___x_466_ == 0)
{
uint8_t v___x_467_; 
v___x_467_ = lean_uint8_dec_eq(v_x_435_, v___x_433_);
if (v___x_467_ == 0)
{
uint8_t v___x_468_; uint8_t v___x_469_; 
v___x_468_ = 37;
v___x_469_ = lean_uint8_dec_eq(v_x_435_, v___x_468_);
return v___x_469_;
}
else
{
return v___x_434_;
}
}
else
{
return v___x_434_;
}
}
else
{
return v___x_434_;
}
}
else
{
return v___x_434_;
}
}
else
{
return v___x_434_;
}
}
else
{
return v___x_434_;
}
}
else
{
return v___x_434_;
}
}
else
{
return v___x_434_;
}
}
else
{
return v___x_434_;
}
}
else
{
return v___x_434_;
}
}
else
{
return v___x_434_;
}
}
else
{
return v___x_434_;
}
}
else
{
return v___x_434_;
}
}
else
{
return v___x_434_;
}
}
else
{
return v___x_434_;
}
}
else
{
return v___x_434_;
}
}
v___jp_470_:
{
uint8_t v___x_471_; uint8_t v___x_472_; 
v___x_471_ = 65;
v___x_472_ = lean_uint8_dec_le(v___x_471_, v_x_435_);
if (v___x_472_ == 0)
{
goto v___jp_436_;
}
else
{
uint8_t v___x_473_; uint8_t v___x_474_; 
v___x_473_ = 90;
v___x_474_ = lean_uint8_dec_le(v_x_435_, v___x_473_);
if (v___x_474_ == 0)
{
goto v___jp_436_;
}
else
{
return v___x_434_;
}
}
}
v___jp_475_:
{
uint8_t v___x_476_; uint8_t v___x_477_; 
v___x_476_ = 97;
v___x_477_ = lean_uint8_dec_le(v___x_476_, v_x_435_);
if (v___x_477_ == 0)
{
goto v___jp_470_;
}
else
{
uint8_t v___x_478_; uint8_t v___x_479_; 
v___x_478_ = 122;
v___x_479_ = lean_uint8_dec_le(v_x_435_, v___x_478_);
if (v___x_479_ == 0)
{
goto v___jp_470_;
}
else
{
return v___x_434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1___boxed(lean_object* v___x_484_, lean_object* v___x_485_, lean_object* v_x_486_){
_start:
{
uint8_t v___x_4638__boxed_487_; uint8_t v___x_4639__boxed_488_; uint8_t v_x_boxed_489_; uint8_t v_res_490_; lean_object* v_r_491_; 
v___x_4638__boxed_487_ = lean_unbox(v___x_484_);
v___x_4639__boxed_488_ = lean_unbox(v___x_485_);
v_x_boxed_489_ = lean_unbox(v_x_486_);
v_res_490_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1(v___x_4638__boxed_487_, v___x_4639__boxed_488_, v_x_boxed_489_);
v_r_491_ = lean_box(v_res_490_);
return v_r_491_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(lean_object* v_config_496_, lean_object* v_a_497_){
_start:
{
lean_object* v___y_499_; lean_object* v_userPassEncoded_500_; lean_object* v___y_501_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v_lower_508_; lean_object* v_upper_509_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_524_; lean_object* v_pos_525_; lean_object* v_maxUserInfoLength_527_; lean_object* v___f_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v_snd_531_; lean_object* v_fst_532_; lean_object* v_fst_533_; lean_object* v_array_534_; lean_object* v_idx_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_583_; 
v_maxUserInfoLength_527_ = lean_ctor_get(v_config_496_, 2);
v___f_528_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__2));
v___x_529_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_497_);
v___x_530_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_528_, v_maxUserInfoLength_527_, v___x_529_, v_a_497_);
v_snd_531_ = lean_ctor_get(v___x_530_, 1);
lean_inc(v_snd_531_);
v_fst_532_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_fst_532_);
lean_dec_ref(v___x_530_);
v_fst_533_ = lean_ctor_get(v_snd_531_, 0);
lean_inc(v_fst_533_);
lean_dec(v_snd_531_);
v_array_534_ = lean_ctor_get(v_a_497_, 0);
v_idx_535_ = lean_ctor_get(v_a_497_, 1);
v_isSharedCheck_583_ = !lean_is_exclusive(v_a_497_);
if (v_isSharedCheck_583_ == 0)
{
v___x_537_ = v_a_497_;
v_isShared_538_ = v_isSharedCheck_583_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_idx_535_);
lean_inc(v_array_534_);
lean_dec(v_a_497_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_583_;
goto v_resetjp_536_;
}
v___jp_498_:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_502_, 0, v___y_499_);
lean_ctor_set(v___x_502_, 1, v_userPassEncoded_500_);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v___y_501_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
return v___x_503_;
}
v___jp_504_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_510_ = l_ByteArray_toByteSlice(v___y_505_, v_lower_508_, v_upper_509_);
v___x_511_ = l_ByteSlice_toByteArray(v___x_510_);
v___x_512_ = l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(v___x_511_);
if (lean_obj_tag(v___x_512_) == 1)
{
v___y_499_ = v___y_507_;
v_userPassEncoded_500_ = v___x_512_;
v___y_501_ = v___y_506_;
goto v___jp_498_;
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; 
lean_dec(v___x_512_);
lean_dec_ref(v___y_507_);
v___x_513_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1));
v___x_514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_514_, 0, v___y_506_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
return v___x_514_;
}
}
v___jp_515_:
{
uint8_t v___x_522_; 
v___x_522_ = lean_nat_dec_le(v___y_516_, v___y_520_);
if (v___x_522_ == 0)
{
lean_dec(v___y_516_);
v___y_505_ = v___y_517_;
v___y_506_ = v___y_518_;
v___y_507_ = v___y_519_;
v_lower_508_ = v___y_521_;
v_upper_509_ = v___y_520_;
goto v___jp_504_;
}
else
{
lean_dec(v___y_520_);
v___y_505_ = v___y_517_;
v___y_506_ = v___y_518_;
v___y_507_ = v___y_519_;
v_lower_508_ = v___y_521_;
v_upper_509_ = v___y_516_;
goto v___jp_504_;
}
}
v___jp_523_:
{
lean_object* v___x_526_; 
v___x_526_ = lean_box(0);
v___y_499_ = v___y_524_;
v_userPassEncoded_500_ = v___x_526_;
v___y_501_ = v_pos_525_;
goto v___jp_498_;
}
v_resetjp_536_:
{
lean_object* v_lower_540_; lean_object* v_upper_541_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___y_580_; uint8_t v___x_582_; 
v___x_577_ = lean_nat_add(v_idx_535_, v_fst_532_);
lean_dec(v_fst_532_);
v___x_578_ = lean_byte_array_size(v_array_534_);
v___x_582_ = lean_nat_dec_le(v_idx_535_, v___x_529_);
if (v___x_582_ == 0)
{
v___y_580_ = v_idx_535_;
goto v___jp_579_;
}
else
{
lean_dec(v_idx_535_);
v___y_580_ = v___x_529_;
goto v___jp_579_;
}
v___jp_539_:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_542_ = l_ByteArray_toByteSlice(v_array_534_, v_lower_540_, v_upper_541_);
v___x_543_ = l_ByteSlice_toByteArray(v___x_542_);
v___x_544_ = l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(v___x_543_);
if (lean_obj_tag(v___x_544_) == 1)
{
lean_object* v_val_545_; lean_object* v_array_546_; lean_object* v_idx_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
lean_del_object(v___x_537_);
v_val_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_val_545_);
lean_dec_ref_known(v___x_544_, 1);
v_array_546_ = lean_ctor_get(v_fst_533_, 0);
v_idx_547_ = lean_ctor_get(v_fst_533_, 1);
v___x_548_ = lean_byte_array_size(v_array_546_);
v___x_549_ = lean_nat_dec_lt(v_idx_547_, v___x_548_);
if (v___x_549_ == 0)
{
v___y_524_ = v_val_545_;
v_pos_525_ = v_fst_533_;
goto v___jp_523_;
}
else
{
uint8_t v___x_550_; uint8_t v___x_551_; uint8_t v___x_552_; 
v___x_550_ = lean_byte_array_fget(v_array_546_, v_idx_547_);
v___x_551_ = 58;
v___x_552_ = lean_uint8_dec_eq(v___x_550_, v___x_551_);
if (v___x_552_ == 0)
{
v___y_524_ = v_val_545_;
v_pos_525_ = v_fst_533_;
goto v___jp_523_;
}
else
{
lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_570_; 
lean_inc(v_idx_547_);
lean_inc_ref(v_array_546_);
v_isSharedCheck_570_ = !lean_is_exclusive(v_fst_533_);
if (v_isSharedCheck_570_ == 0)
{
lean_object* v_unused_571_; lean_object* v_unused_572_; 
v_unused_571_ = lean_ctor_get(v_fst_533_, 1);
lean_dec(v_unused_571_);
v_unused_572_ = lean_ctor_get(v_fst_533_, 0);
lean_dec(v_unused_572_);
v___x_554_ = v_fst_533_;
v_isShared_555_ = v_isSharedCheck_570_;
goto v_resetjp_553_;
}
else
{
lean_dec(v_fst_533_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_570_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___f_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_556_ = lean_box(v___x_551_);
v___x_557_ = lean_box(v___x_549_);
v___f_558_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1___boxed), 3, 2);
lean_closure_set(v___f_558_, 0, v___x_556_);
lean_closure_set(v___f_558_, 1, v___x_557_);
v___x_559_ = lean_unsigned_to_nat(1u);
v___x_560_ = lean_nat_add(v_idx_547_, v___x_559_);
lean_dec(v_idx_547_);
lean_inc(v___x_560_);
lean_inc_ref(v_array_546_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 1, v___x_560_);
v___x_562_ = v___x_554_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_array_546_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v___x_560_);
v___x_562_ = v_reuseFailAlloc_569_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_563_; lean_object* v_snd_564_; lean_object* v_fst_565_; lean_object* v_fst_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_563_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_558_, v_maxUserInfoLength_527_, v___x_529_, v___x_562_);
v_snd_564_ = lean_ctor_get(v___x_563_, 1);
lean_inc(v_snd_564_);
v_fst_565_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_fst_565_);
lean_dec_ref(v___x_563_);
v_fst_566_ = lean_ctor_get(v_snd_564_, 0);
lean_inc(v_fst_566_);
lean_dec(v_snd_564_);
v___x_567_ = lean_nat_add(v___x_560_, v_fst_565_);
lean_dec(v_fst_565_);
v___x_568_ = lean_nat_dec_le(v___x_560_, v___x_529_);
if (v___x_568_ == 0)
{
v___y_516_ = v___x_567_;
v___y_517_ = v_array_546_;
v___y_518_ = v_fst_566_;
v___y_519_ = v_val_545_;
v___y_520_ = v___x_548_;
v___y_521_ = v___x_560_;
goto v___jp_515_;
}
else
{
lean_dec(v___x_560_);
v___y_516_ = v___x_567_;
v___y_517_ = v_array_546_;
v___y_518_ = v_fst_566_;
v___y_519_ = v_val_545_;
v___y_520_ = v___x_548_;
v___y_521_ = v___x_529_;
goto v___jp_515_;
}
}
}
}
}
}
else
{
lean_object* v___x_573_; lean_object* v___x_575_; 
lean_dec(v___x_544_);
v___x_573_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1));
if (v_isShared_538_ == 0)
{
lean_ctor_set_tag(v___x_537_, 1);
lean_ctor_set(v___x_537_, 1, v___x_573_);
lean_ctor_set(v___x_537_, 0, v_fst_533_);
v___x_575_ = v___x_537_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_fst_533_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
v___jp_579_:
{
uint8_t v___x_581_; 
v___x_581_ = lean_nat_dec_le(v___x_577_, v___x_578_);
if (v___x_581_ == 0)
{
lean_dec(v___x_577_);
v_lower_540_ = v___y_580_;
v_upper_541_ = v___x_578_;
goto v___jp_539_;
}
else
{
v_lower_540_ = v___y_580_;
v_upper_541_ = v___x_577_;
goto v___jp_539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___boxed(lean_object* v_config_584_, lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(v_config_584_, v_a_585_);
lean_dec_ref(v_config_584_);
return v_res_586_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(uint8_t v_x_587_){
_start:
{
uint8_t v___x_598_; uint8_t v___x_599_; 
v___x_598_ = 58;
v___x_599_ = lean_uint8_dec_eq(v_x_587_, v___x_598_);
if (v___x_599_ == 0)
{
uint8_t v___x_600_; uint8_t v___x_601_; 
v___x_600_ = 46;
v___x_601_ = lean_uint8_dec_eq(v_x_587_, v___x_600_);
if (v___x_601_ == 0)
{
uint8_t v___x_602_; uint8_t v___x_603_; 
v___x_602_ = 48;
v___x_603_ = lean_uint8_dec_le(v___x_602_, v_x_587_);
if (v___x_603_ == 0)
{
goto v___jp_593_;
}
else
{
uint8_t v___x_604_; uint8_t v___x_605_; 
v___x_604_ = 57;
v___x_605_ = lean_uint8_dec_le(v_x_587_, v___x_604_);
if (v___x_605_ == 0)
{
goto v___jp_593_;
}
else
{
return v___x_605_;
}
}
}
else
{
return v___x_601_;
}
}
else
{
return v___x_599_;
}
v___jp_588_:
{
uint8_t v___x_589_; uint8_t v___x_590_; 
v___x_589_ = 65;
v___x_590_ = lean_uint8_dec_le(v___x_589_, v_x_587_);
if (v___x_590_ == 0)
{
return v___x_590_;
}
else
{
uint8_t v___x_591_; uint8_t v___x_592_; 
v___x_591_ = 70;
v___x_592_ = lean_uint8_dec_le(v_x_587_, v___x_591_);
return v___x_592_;
}
}
v___jp_593_:
{
uint8_t v___x_594_; uint8_t v___x_595_; 
v___x_594_ = 97;
v___x_595_ = lean_uint8_dec_le(v___x_594_, v_x_587_);
if (v___x_595_ == 0)
{
goto v___jp_588_;
}
else
{
uint8_t v___x_596_; uint8_t v___x_597_; 
v___x_596_ = 102;
v___x_597_ = lean_uint8_dec_le(v_x_587_, v___x_596_);
if (v___x_597_ == 0)
{
goto v___jp_588_;
}
else
{
return v___x_597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___boxed(lean_object* v_x_606_){
_start:
{
uint8_t v_x_boxed_607_; uint8_t v_res_608_; lean_object* v_r_609_; 
v_x_boxed_607_ = lean_unbox(v_x_606_);
v_res_608_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(v_x_boxed_607_);
v_r_609_ = lean_box(v_res_608_);
return v_r_609_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(lean_object* v_a_621_){
_start:
{
lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v_array_632_; lean_object* v_idx_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v_array_632_ = lean_ctor_get(v_a_621_, 0);
v_idx_633_ = lean_ctor_get(v_a_621_, 1);
v___x_634_ = lean_byte_array_size(v_array_632_);
v___x_635_ = lean_nat_dec_lt(v_idx_633_, v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_box(0);
v___x_637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_637_, 0, v_a_621_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
return v___x_637_;
}
else
{
uint8_t v___x_638_; uint8_t v_got_639_; uint8_t v___x_640_; 
v___x_638_ = 91;
v_got_639_ = lean_byte_array_fget(v_array_632_, v_idx_633_);
v___x_640_ = lean_uint8_dec_eq(v_got_639_, v___x_638_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_642_, 0, v_a_621_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
return v___x_642_;
}
else
{
lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_718_; 
lean_inc(v_idx_633_);
lean_inc_ref(v_array_632_);
v_isSharedCheck_718_ = !lean_is_exclusive(v_a_621_);
if (v_isSharedCheck_718_ == 0)
{
lean_object* v_unused_719_; lean_object* v_unused_720_; 
v_unused_719_ = lean_ctor_get(v_a_621_, 1);
lean_dec(v_unused_719_);
v_unused_720_ = lean_ctor_get(v_a_621_, 0);
lean_dec(v_unused_720_);
v___x_644_ = v_a_621_;
v_isShared_645_ = v_isSharedCheck_718_;
goto v_resetjp_643_;
}
else
{
lean_dec(v_a_621_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_718_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___f_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_650_; 
v___f_646_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3));
v___x_647_ = lean_unsigned_to_nat(1u);
v___x_648_ = lean_nat_add(v_idx_633_, v___x_647_);
lean_dec(v_idx_633_);
lean_inc(v___x_648_);
lean_inc_ref(v_array_632_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 1, v___x_648_);
v___x_650_ = v___x_644_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_array_632_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v___x_648_);
v___x_650_ = v_reuseFailAlloc_717_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v_snd_654_; lean_object* v_fst_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_716_; 
v___x_651_ = lean_unsigned_to_nat(256u);
v___x_652_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___x_650_);
v___x_653_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_646_, v___x_651_, v___x_652_, v___x_650_);
v_snd_654_ = lean_ctor_get(v___x_653_, 1);
v_fst_655_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_716_ == 0)
{
v___x_657_ = v___x_653_;
v_isShared_658_ = v_isSharedCheck_716_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_snd_654_);
lean_inc(v_fst_655_);
lean_dec(v___x_653_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_716_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v_fst_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_714_; 
v_fst_659_ = lean_ctor_get(v_snd_654_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v_snd_654_);
if (v_isSharedCheck_714_ == 0)
{
lean_object* v_unused_715_; 
v_unused_715_ = lean_ctor_get(v_snd_654_, 1);
lean_dec(v_unused_715_);
v___x_661_ = v_snd_654_;
v_isShared_662_ = v_isSharedCheck_714_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_fst_659_);
lean_dec(v_snd_654_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_714_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___y_664_; uint8_t v___x_698_; 
v___x_698_ = lean_nat_dec_eq(v_fst_655_, v___x_652_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; lean_object* v___y_701_; uint8_t v___x_709_; 
lean_dec_ref(v___x_650_);
v___x_699_ = lean_nat_add(v___x_648_, v_fst_655_);
lean_dec(v_fst_655_);
v___x_709_ = lean_nat_dec_le(v___x_648_, v___x_652_);
if (v___x_709_ == 0)
{
v___y_701_ = v___x_648_;
goto v___jp_700_;
}
else
{
lean_dec(v___x_648_);
v___y_701_ = v___x_652_;
goto v___jp_700_;
}
v___jp_700_:
{
uint8_t v___x_702_; 
v___x_702_ = lean_nat_dec_le(v___x_699_, v___x_634_);
if (v___x_702_ == 0)
{
lean_object* v___x_704_; 
lean_dec(v___x_699_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v___x_634_);
lean_ctor_set(v___x_657_, 0, v___y_701_);
v___x_704_ = v___x_657_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___y_701_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v___x_634_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
v___y_664_ = v___x_704_;
goto v___jp_663_;
}
}
else
{
lean_object* v___x_707_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v___x_699_);
lean_ctor_set(v___x_657_, 0, v___y_701_);
v___x_707_ = v___x_657_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___y_701_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v___x_699_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
v___y_664_ = v___x_707_;
goto v___jp_663_;
}
}
}
}
else
{
lean_object* v___x_710_; lean_object* v___x_712_; 
lean_del_object(v___x_661_);
lean_dec(v_fst_659_);
lean_dec(v_fst_655_);
lean_dec(v___x_648_);
lean_dec_ref(v_array_632_);
v___x_710_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7));
if (v_isShared_658_ == 0)
{
lean_ctor_set_tag(v___x_657_, 1);
lean_ctor_set(v___x_657_, 1, v___x_710_);
lean_ctor_set(v___x_657_, 0, v___x_650_);
v___x_712_ = v___x_657_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_650_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v___x_710_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
v___jp_663_:
{
lean_object* v_array_665_; lean_object* v_idx_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v_array_665_ = lean_ctor_get(v_fst_659_, 0);
v_idx_666_ = lean_ctor_get(v_fst_659_, 1);
v___x_667_ = lean_byte_array_size(v_array_665_);
v___x_668_ = lean_nat_dec_lt(v_idx_666_, v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; lean_object* v___x_671_; 
lean_dec_ref(v___y_664_);
lean_dec_ref(v_array_632_);
v___x_669_ = lean_box(0);
if (v_isShared_662_ == 0)
{
lean_ctor_set_tag(v___x_661_, 1);
lean_ctor_set(v___x_661_, 1, v___x_669_);
v___x_671_ = v___x_661_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_fst_659_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v___x_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
else
{
uint8_t v___x_673_; uint8_t v_got_674_; uint8_t v___x_675_; 
v___x_673_ = 93;
v_got_674_ = lean_byte_array_fget(v_array_665_, v_idx_666_);
v___x_675_ = lean_uint8_dec_eq(v_got_674_, v___x_673_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_678_; 
lean_dec_ref(v___y_664_);
lean_dec_ref(v_array_632_);
v___x_676_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5));
if (v_isShared_662_ == 0)
{
lean_ctor_set_tag(v___x_661_, 1);
lean_ctor_set(v___x_661_, 1, v___x_676_);
v___x_678_ = v___x_661_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_fst_659_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
else
{
lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_695_; 
lean_inc(v_idx_666_);
lean_inc_ref(v_array_665_);
lean_del_object(v___x_661_);
v_isSharedCheck_695_ = !lean_is_exclusive(v_fst_659_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; lean_object* v_unused_697_; 
v_unused_696_ = lean_ctor_get(v_fst_659_, 1);
lean_dec(v_unused_696_);
v_unused_697_ = lean_ctor_get(v_fst_659_, 0);
lean_dec(v_unused_697_);
v___x_681_ = v_fst_659_;
v_isShared_682_ = v_isSharedCheck_695_;
goto v_resetjp_680_;
}
else
{
lean_dec(v_fst_659_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_695_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v_lower_683_; lean_object* v_upper_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_688_; 
v_lower_683_ = lean_ctor_get(v___y_664_, 0);
lean_inc(v_lower_683_);
v_upper_684_ = lean_ctor_get(v___y_664_, 1);
lean_inc(v_upper_684_);
lean_dec_ref(v___y_664_);
v___x_685_ = l_ByteArray_toByteSlice(v_array_632_, v_lower_683_, v_upper_684_);
v___x_686_ = lean_nat_add(v_idx_666_, v___x_647_);
lean_dec(v_idx_666_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v___x_686_);
v___x_688_ = v___x_681_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_array_665_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v___x_686_);
v___x_688_ = v_reuseFailAlloc_694_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_689_ = l_ByteSlice_toByteArray(v___x_685_);
v___x_690_ = lean_string_validate_utf8(v___x_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; 
lean_dec_ref(v___x_689_);
v___x_691_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_692_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_691_);
v___y_623_ = v___x_688_;
v___y_624_ = v___x_692_;
goto v___jp_622_;
}
else
{
lean_object* v___x_693_; 
v___x_693_ = lean_string_from_utf8_unchecked(v___x_689_);
v___y_623_ = v___x_688_;
v___y_624_ = v___x_693_;
goto v___jp_622_;
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
v___jp_622_:
{
lean_object* v___x_625_; 
v___x_625_ = lean_uv_pton_v6(v___y_624_);
if (lean_obj_tag(v___x_625_) == 1)
{
lean_object* v_val_626_; lean_object* v___x_627_; 
lean_dec_ref(v___y_624_);
v_val_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_val_626_);
lean_dec_ref_known(v___x_625_, 1);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v___y_623_);
lean_ctor_set(v___x_627_, 1, v_val_626_);
return v___x_627_;
}
else
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
lean_dec(v___x_625_);
v___x_628_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__0));
v___x_629_ = lean_string_append(v___x_628_, v___y_624_);
lean_dec_ref(v___y_624_);
v___x_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
v___x_631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_631_, 0, v___y_623_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
return v___x_631_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0(uint8_t v_x_721_){
_start:
{
uint8_t v___x_722_; uint8_t v___x_723_; 
v___x_722_ = 46;
v___x_723_ = lean_uint8_dec_eq(v_x_721_, v___x_722_);
if (v___x_723_ == 0)
{
uint8_t v___x_724_; uint8_t v___x_725_; 
v___x_724_ = 48;
v___x_725_ = lean_uint8_dec_le(v___x_724_, v_x_721_);
if (v___x_725_ == 0)
{
return v___x_725_;
}
else
{
uint8_t v___x_726_; uint8_t v___x_727_; 
v___x_726_ = 57;
v___x_727_ = lean_uint8_dec_le(v_x_721_, v___x_726_);
return v___x_727_;
}
}
else
{
return v___x_723_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0___boxed(lean_object* v_x_728_){
_start:
{
uint8_t v_x_boxed_729_; uint8_t v_res_730_; lean_object* v_r_731_; 
v_x_boxed_729_ = lean_unbox(v_x_728_);
v_res_730_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0(v_x_boxed_729_);
v_r_731_ = lean_box(v_res_730_);
return v_r_731_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(lean_object* v_a_734_){
_start:
{
lean_object* v___f_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v_snd_739_; lean_object* v_fst_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_785_; 
v___f_735_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__0));
v___x_736_ = lean_unsigned_to_nat(256u);
v___x_737_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_734_);
v___x_738_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_735_, v___x_736_, v___x_737_, v_a_734_);
v_snd_739_ = lean_ctor_get(v___x_738_, 1);
v_fst_740_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_785_ == 0)
{
v___x_742_ = v___x_738_;
v_isShared_743_ = v_isSharedCheck_785_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_snd_739_);
lean_inc(v_fst_740_);
lean_dec(v___x_738_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_785_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v_fst_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_783_; 
v_fst_744_ = lean_ctor_get(v_snd_739_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v_snd_739_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; 
v_unused_784_ = lean_ctor_get(v_snd_739_, 1);
lean_dec(v_unused_784_);
v___x_746_ = v_snd_739_;
v_isShared_747_ = v_isSharedCheck_783_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_fst_744_);
lean_dec(v_snd_739_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_783_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___y_749_; uint8_t v___x_761_; 
v___x_761_ = lean_nat_dec_eq(v_fst_740_, v___x_737_);
if (v___x_761_ == 0)
{
lean_object* v_array_762_; lean_object* v_idx_763_; lean_object* v_lower_765_; lean_object* v_upper_766_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___y_776_; uint8_t v___x_778_; 
lean_del_object(v___x_742_);
v_array_762_ = lean_ctor_get(v_a_734_, 0);
lean_inc_ref(v_array_762_);
v_idx_763_ = lean_ctor_get(v_a_734_, 1);
lean_inc(v_idx_763_);
lean_dec_ref(v_a_734_);
v___x_773_ = lean_nat_add(v_idx_763_, v_fst_740_);
lean_dec(v_fst_740_);
v___x_774_ = lean_byte_array_size(v_array_762_);
v___x_778_ = lean_nat_dec_le(v_idx_763_, v___x_737_);
if (v___x_778_ == 0)
{
v___y_776_ = v_idx_763_;
goto v___jp_775_;
}
else
{
lean_dec(v_idx_763_);
v___y_776_ = v___x_737_;
goto v___jp_775_;
}
v___jp_764_:
{
lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_767_ = l_ByteArray_toByteSlice(v_array_762_, v_lower_765_, v_upper_766_);
v___x_768_ = l_ByteSlice_toByteArray(v___x_767_);
v___x_769_ = lean_string_validate_utf8(v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; lean_object* v___x_771_; 
lean_dec_ref(v___x_768_);
v___x_770_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_771_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_770_);
v___y_749_ = v___x_771_;
goto v___jp_748_;
}
else
{
lean_object* v___x_772_; 
v___x_772_ = lean_string_from_utf8_unchecked(v___x_768_);
v___y_749_ = v___x_772_;
goto v___jp_748_;
}
}
v___jp_775_:
{
uint8_t v___x_777_; 
v___x_777_ = lean_nat_dec_le(v___x_773_, v___x_774_);
if (v___x_777_ == 0)
{
lean_dec(v___x_773_);
v_lower_765_ = v___y_776_;
v_upper_766_ = v___x_774_;
goto v___jp_764_;
}
else
{
v_lower_765_ = v___y_776_;
v_upper_766_ = v___x_773_;
goto v___jp_764_;
}
}
}
else
{
lean_object* v___x_779_; lean_object* v___x_781_; 
lean_del_object(v___x_746_);
lean_dec(v_fst_744_);
lean_dec(v_fst_740_);
v___x_779_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7));
if (v_isShared_743_ == 0)
{
lean_ctor_set_tag(v___x_742_, 1);
lean_ctor_set(v___x_742_, 1, v___x_779_);
lean_ctor_set(v___x_742_, 0, v_a_734_);
v___x_781_ = v___x_742_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_734_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
v___jp_748_:
{
lean_object* v___x_750_; 
v___x_750_ = lean_uv_pton_v4(v___y_749_);
if (lean_obj_tag(v___x_750_) == 1)
{
lean_object* v_val_751_; lean_object* v___x_753_; 
lean_dec_ref(v___y_749_);
v_val_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_val_751_);
lean_dec_ref_known(v___x_750_, 1);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v_val_751_);
v___x_753_ = v___x_746_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_fst_744_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_val_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
else
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
lean_dec(v___x_750_);
v___x_755_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__1));
v___x_756_ = lean_string_append(v___x_755_, v___y_749_);
lean_dec_ref(v___y_749_);
v___x_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
if (v_isShared_747_ == 0)
{
lean_ctor_set_tag(v___x_746_, 1);
lean_ctor_set(v___x_746_, 1, v___x_757_);
v___x_759_ = v___x_746_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_fst_744_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
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
lean_object* v___x_789_; 
v___x_789_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0));
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___boxed(lean_object* v___dummy_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg();
return v_res_791_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0(void){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg();
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(lean_object* v_s_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___boxed(lean_object* v_s_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(v_s_795_);
lean_dec_ref(v_s_795_);
return v_res_796_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(uint8_t v___x_797_, uint8_t v_x_798_){
_start:
{
uint8_t v___x_814_; uint8_t v___x_815_; 
v___x_814_ = 48;
v___x_815_ = lean_uint8_dec_le(v___x_814_, v_x_798_);
if (v___x_815_ == 0)
{
goto v___jp_809_;
}
else
{
uint8_t v___x_816_; uint8_t v___x_817_; 
v___x_816_ = 57;
v___x_817_ = lean_uint8_dec_le(v_x_798_, v___x_816_);
if (v___x_817_ == 0)
{
goto v___jp_809_;
}
else
{
return v___x_797_;
}
}
v___jp_799_:
{
uint8_t v___x_800_; uint8_t v___x_801_; 
v___x_800_ = 45;
v___x_801_ = lean_uint8_dec_eq(v_x_798_, v___x_800_);
if (v___x_801_ == 0)
{
uint8_t v___x_802_; uint8_t v___x_803_; 
v___x_802_ = 46;
v___x_803_ = lean_uint8_dec_eq(v_x_798_, v___x_802_);
return v___x_803_;
}
else
{
return v___x_797_;
}
}
v___jp_804_:
{
uint8_t v___x_805_; uint8_t v___x_806_; 
v___x_805_ = 65;
v___x_806_ = lean_uint8_dec_le(v___x_805_, v_x_798_);
if (v___x_806_ == 0)
{
goto v___jp_799_;
}
else
{
uint8_t v___x_807_; uint8_t v___x_808_; 
v___x_807_ = 90;
v___x_808_ = lean_uint8_dec_le(v_x_798_, v___x_807_);
if (v___x_808_ == 0)
{
goto v___jp_799_;
}
else
{
return v___x_797_;
}
}
}
v___jp_809_:
{
uint8_t v___x_810_; uint8_t v___x_811_; 
v___x_810_ = 97;
v___x_811_ = lean_uint8_dec_le(v___x_810_, v_x_798_);
if (v___x_811_ == 0)
{
goto v___jp_804_;
}
else
{
uint8_t v___x_812_; uint8_t v___x_813_; 
v___x_812_ = 122;
v___x_813_ = lean_uint8_dec_le(v_x_798_, v___x_812_);
if (v___x_813_ == 0)
{
goto v___jp_804_;
}
else
{
return v___x_797_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed(lean_object* v___x_818_, lean_object* v_x_819_){
_start:
{
uint8_t v___x_12941__boxed_820_; uint8_t v_x_boxed_821_; uint8_t v_res_822_; lean_object* v_r_823_; 
v___x_12941__boxed_820_ = lean_unbox(v___x_818_);
v_x_boxed_821_ = lean_unbox(v_x_819_);
v_res_822_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(v___x_12941__boxed_820_, v_x_boxed_821_);
v_r_823_ = lean_box(v_res_822_);
return v_r_823_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(lean_object* v___x_824_, lean_object* v___x_825_, lean_object* v_a_826_, uint8_t v_b_827_){
_start:
{
if (lean_obj_tag(v_a_826_) == 0)
{
lean_object* v_currPos_828_; lean_object* v_searcher_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_843_; 
v_currPos_828_ = lean_ctor_get(v_a_826_, 0);
v_searcher_829_ = lean_ctor_get(v_a_826_, 1);
v_isSharedCheck_843_ = !lean_is_exclusive(v_a_826_);
if (v_isSharedCheck_843_ == 0)
{
v___x_831_ = v_a_826_;
v_isShared_832_ = v_isSharedCheck_843_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_searcher_829_);
lean_inc(v_currPos_828_);
lean_dec(v_a_826_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_843_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
uint8_t v___x_833_; uint8_t v_decide_834_; 
v___x_833_ = 0;
v_decide_834_ = lean_nat_dec_eq(v_searcher_829_, v___x_825_);
if (v_decide_834_ == 0)
{
uint32_t v___x_835_; uint32_t v___x_836_; uint8_t v___x_837_; 
v___x_835_ = 46;
v___x_836_ = lean_string_utf8_get_fast(v___x_824_, v_searcher_829_);
v___x_837_ = lean_uint32_dec_eq(v___x_836_, v___x_835_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_838_ = lean_string_utf8_next_fast(v___x_824_, v_searcher_829_);
lean_dec(v_searcher_829_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 1, v___x_838_);
v___x_840_ = v___x_831_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_currPos_828_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v___x_838_);
v___x_840_ = v_reuseFailAlloc_842_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
v_a_826_ = v___x_840_;
goto _start;
}
}
else
{
lean_del_object(v___x_831_);
lean_dec(v_searcher_829_);
lean_dec(v_currPos_828_);
return v___x_833_;
}
}
else
{
lean_del_object(v___x_831_);
lean_dec(v_searcher_829_);
lean_dec(v_currPos_828_);
return v___x_833_;
}
}
}
else
{
return v_b_827_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg___boxed(lean_object* v___x_844_, lean_object* v___x_845_, lean_object* v_a_846_, lean_object* v_b_847_){
_start:
{
uint8_t v_b_boxed_848_; uint8_t v_res_849_; lean_object* v_r_850_; 
v_b_boxed_848_ = lean_unbox(v_b_847_);
v_res_849_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_844_, v___x_845_, v_a_846_, v_b_boxed_848_);
lean_dec(v___x_845_);
lean_dec_ref(v___x_844_);
v_r_850_ = lean_box(v_res_849_);
return v_r_850_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(uint8_t v___x_851_, lean_object* v___x_852_, lean_object* v___x_853_, lean_object* v___x_854_, lean_object* v_a_855_, uint8_t v_b_856_){
_start:
{
uint8_t v___y_858_; lean_object* v_it_859_; lean_object* v_startInclusive_860_; lean_object* v_endExclusive_861_; uint8_t v___y_866_; 
if (v___x_851_ == 0)
{
uint8_t v___x_892_; 
v___x_892_ = 1;
v___y_866_ = v___x_892_;
goto v___jp_865_;
}
else
{
uint8_t v___x_893_; 
v___x_893_ = 0;
v___y_866_ = v___x_893_;
goto v___jp_865_;
}
v___jp_857_:
{
lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_862_ = lean_string_utf8_extract_fast(v___x_852_, v_startInclusive_860_, v_endExclusive_861_);
lean_dec(v_endExclusive_861_);
lean_dec(v_startInclusive_860_);
v___x_863_ = l_Std_Http_URI_isValidDomainLabel(v___x_862_);
if (v___x_863_ == 0)
{
lean_dec(v_it_859_);
lean_dec(v___x_854_);
return v___x_863_;
}
else
{
v_a_855_ = v_it_859_;
v_b_856_ = v___y_858_;
goto _start;
}
}
v___jp_865_:
{
if (lean_obj_tag(v_a_855_) == 0)
{
lean_object* v_currPos_867_; lean_object* v_searcher_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_891_; 
v_currPos_867_ = lean_ctor_get(v_a_855_, 0);
v_searcher_868_ = lean_ctor_get(v_a_855_, 1);
v_isSharedCheck_891_ = !lean_is_exclusive(v_a_855_);
if (v_isSharedCheck_891_ == 0)
{
v___x_870_ = v_a_855_;
v_isShared_871_ = v_isSharedCheck_891_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_searcher_868_);
lean_inc(v_currPos_867_);
lean_dec(v_a_855_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_891_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
uint8_t v_decide_872_; 
v_decide_872_ = lean_nat_dec_eq(v_searcher_868_, v___x_854_);
if (v_decide_872_ == 0)
{
uint32_t v___x_873_; uint32_t v___x_874_; uint8_t v___x_875_; 
v___x_873_ = 46;
v___x_874_ = lean_string_utf8_get_fast(v___x_852_, v_searcher_868_);
v___x_875_ = lean_uint32_dec_eq(v___x_874_, v___x_873_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_876_ = lean_string_utf8_next_fast(v___x_852_, v_searcher_868_);
lean_dec(v_searcher_868_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 1, v___x_876_);
v___x_878_ = v___x_870_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_currPos_867_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v___x_876_);
v___x_878_ = v_reuseFailAlloc_880_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
v_a_855_ = v___x_878_;
goto _start;
}
}
else
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v_slice_884_; lean_object* v_nextIt_886_; 
v___x_881_ = lean_string_utf8_next_fast(v___x_852_, v_searcher_868_);
v___x_882_ = lean_nat_sub(v___x_881_, v_searcher_868_);
v___x_883_ = lean_nat_add(v_searcher_868_, v___x_882_);
lean_dec(v___x_882_);
v_slice_884_ = l_String_Slice_subslice_x21(v___x_853_, v_currPos_867_, v_searcher_868_);
lean_inc(v___x_883_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 1, v___x_883_);
lean_ctor_set(v___x_870_, 0, v___x_883_);
v_nextIt_886_ = v___x_870_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v___x_883_);
v_nextIt_886_ = v_reuseFailAlloc_889_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v_startInclusive_887_; lean_object* v_endExclusive_888_; 
v_startInclusive_887_ = lean_ctor_get(v_slice_884_, 0);
lean_inc(v_startInclusive_887_);
v_endExclusive_888_ = lean_ctor_get(v_slice_884_, 1);
lean_inc(v_endExclusive_888_);
lean_dec_ref(v_slice_884_);
v___y_858_ = v___y_866_;
v_it_859_ = v_nextIt_886_;
v_startInclusive_860_ = v_startInclusive_887_;
v_endExclusive_861_ = v_endExclusive_888_;
goto v___jp_857_;
}
}
}
else
{
lean_object* v___x_890_; 
lean_del_object(v___x_870_);
lean_dec(v_searcher_868_);
v___x_890_ = lean_box(1);
lean_inc(v___x_854_);
v___y_858_ = v___y_866_;
v_it_859_ = v___x_890_;
v_startInclusive_860_ = v_currPos_867_;
v_endExclusive_861_ = v___x_854_;
goto v___jp_857_;
}
}
}
else
{
lean_dec(v___x_854_);
return v_b_856_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg___boxed(lean_object* v___x_894_, lean_object* v___x_895_, lean_object* v___x_896_, lean_object* v___x_897_, lean_object* v_a_898_, lean_object* v_b_899_){
_start:
{
uint8_t v___x_13020__boxed_900_; uint8_t v_b_boxed_901_; uint8_t v_res_902_; lean_object* v_r_903_; 
v___x_13020__boxed_900_ = lean_unbox(v___x_894_);
v_b_boxed_901_ = lean_unbox(v_b_899_);
v_res_902_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_13020__boxed_900_, v___x_895_, v___x_896_, v___x_897_, v_a_898_, v_b_boxed_901_);
lean_dec_ref(v___x_896_);
lean_dec_ref(v___x_895_);
v_r_903_ = lean_box(v_res_902_);
return v_r_903_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(lean_object* v_config_911_, lean_object* v_a_912_){
_start:
{
lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v_lower_924_; lean_object* v_upper_925_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_977_; lean_object* v_pos_978_; lean_object* v___y_1002_; lean_object* v_pos_1003_; lean_object* v_res_1004_; lean_object* v_array_1005_; lean_object* v_idx_1006_; lean_object* v_pos_1008_; lean_object* v_res_1009_; lean_object* v___x_1018_; uint8_t v___x_1019_; 
v_array_1005_ = lean_ctor_get(v_a_912_, 0);
v_idx_1006_ = lean_ctor_get(v_a_912_, 1);
v___x_1018_ = lean_byte_array_size(v_array_1005_);
v___x_1019_ = lean_nat_dec_lt(v_idx_1006_, v___x_1018_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; 
lean_inc(v_idx_1006_);
lean_inc_ref(v_array_1005_);
v___x_1020_ = lean_box(0);
v_pos_1008_ = v_a_912_;
v_res_1009_ = v___x_1020_;
goto v___jp_1007_;
}
else
{
uint8_t v___x_1021_; uint8_t v___x_1022_; uint8_t v___x_1023_; 
v___x_1021_ = lean_byte_array_fget(v_array_1005_, v_idx_1006_);
v___x_1022_ = 91;
v___x_1023_ = lean_uint8_dec_eq(v___x_1021_, v___x_1022_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; 
lean_inc(v_idx_1006_);
lean_inc_ref(v_array_1005_);
v___x_1024_ = lean_box(0);
v_pos_1008_ = v_a_912_;
v_res_1009_ = v___x_1024_;
goto v___jp_1007_;
}
else
{
lean_object* v___x_1025_; 
v___x_1025_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(v_a_912_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_pos_1026_; lean_object* v_res_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1035_; 
v_pos_1026_ = lean_ctor_get(v___x_1025_, 0);
v_res_1027_ = lean_ctor_get(v___x_1025_, 1);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1029_ = v___x_1025_;
v_isShared_1030_ = v_isSharedCheck_1035_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_res_1027_);
lean_inc(v_pos_1026_);
lean_dec(v___x_1025_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1035_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1031_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1031_, 0, v_res_1027_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 1, v___x_1031_);
v___x_1033_ = v___x_1029_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_pos_1026_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
else
{
lean_object* v_pos_1036_; lean_object* v_err_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
v_pos_1036_ = lean_ctor_get(v___x_1025_, 0);
v_err_1037_ = lean_ctor_get(v___x_1025_, 1);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1025_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_err_1037_);
lean_inc(v_pos_1036_);
lean_dec(v___x_1025_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_pos_1036_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_err_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
}
v___jp_913_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_916_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0));
v___x_917_ = lean_string_append(v___x_916_, v___y_914_);
lean_dec_ref(v___y_914_);
v___x_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
v___x_919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_919_, 0, v___y_915_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
return v___x_919_;
}
v___jp_920_:
{
lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_926_ = l_ByteArray_toByteSlice(v___y_921_, v_lower_924_, v_upper_925_);
v___x_927_ = l_ByteSlice_toByteArray(v___x_926_);
v___x_928_ = lean_string_validate_utf8(v___x_927_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; lean_object* v___x_930_; 
lean_dec_ref(v___x_927_);
lean_dec(v___y_922_);
v___x_929_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2));
v___x_930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_930_, 0, v___y_923_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
return v___x_930_;
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; uint8_t v___x_936_; 
v___x_931_ = lean_string_from_utf8_unchecked(v___x_927_);
lean_inc_n(v___y_922_, 2);
lean_inc_ref(v___x_931_);
v___x_932_ = l_String_mapAux___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(v___x_931_, v___y_922_);
v___x_933_ = lean_string_utf8_byte_size(v___x_932_);
lean_inc_ref(v___x_932_);
v___x_934_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_934_, 0, v___x_932_);
lean_ctor_set(v___x_934_, 1, v___y_922_);
lean_ctor_set(v___x_934_, 2, v___x_933_);
v___x_935_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0);
v___x_936_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_932_, v___x_933_, v___x_935_, v___x_928_);
if (v___x_936_ == 0)
{
uint8_t v___x_937_; 
v___x_937_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_936_, v___x_932_, v___x_934_, v___x_933_, v___x_935_, v___x_928_);
lean_dec_ref_known(v___x_934_, 3);
if (v___x_937_ == 0)
{
lean_dec_ref(v___x_932_);
lean_dec(v___y_922_);
v___y_914_ = v___x_931_;
v___y_915_ = v___y_923_;
goto v___jp_913_;
}
else
{
lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_938_ = lean_string_length(v___x_932_);
v___x_939_ = lean_unsigned_to_nat(255u);
v___x_940_ = lean_nat_dec_le(v___x_938_, v___x_939_);
if (v___x_940_ == 0)
{
lean_dec_ref(v___x_932_);
lean_dec(v___y_922_);
v___y_914_ = v___x_931_;
v___y_915_ = v___y_923_;
goto v___jp_913_;
}
else
{
uint8_t v___x_941_; 
v___x_941_ = lean_nat_dec_eq(v___x_933_, v___y_922_);
lean_dec(v___y_922_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; lean_object* v___x_943_; 
lean_dec_ref(v___x_931_);
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_932_);
v___x_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_943_, 0, v___y_923_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
return v___x_943_;
}
else
{
lean_dec_ref(v___x_932_);
v___y_914_ = v___x_931_;
v___y_915_ = v___y_923_;
goto v___jp_913_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_934_, 3);
lean_dec_ref(v___x_932_);
lean_dec(v___y_922_);
v___y_914_ = v___x_931_;
v___y_915_ = v___y_923_;
goto v___jp_913_;
}
}
}
v___jp_944_:
{
uint8_t v___x_951_; 
v___x_951_ = lean_nat_dec_le(v___y_947_, v___y_948_);
if (v___x_951_ == 0)
{
lean_dec(v___y_947_);
v___y_921_ = v___y_945_;
v___y_922_ = v___y_946_;
v___y_923_ = v___y_949_;
v_lower_924_ = v___y_950_;
v_upper_925_ = v___y_948_;
goto v___jp_920_;
}
else
{
lean_dec(v___y_948_);
v___y_921_ = v___y_945_;
v___y_922_ = v___y_946_;
v___y_923_ = v___y_949_;
v_lower_924_ = v___y_950_;
v_upper_925_ = v___y_947_;
goto v___jp_920_;
}
}
v___jp_952_:
{
lean_object* v_maxHostLength_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v_snd_958_; lean_object* v_fst_959_; lean_object* v_fst_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_974_; 
v_maxHostLength_955_ = lean_ctor_get(v_config_911_, 1);
v___x_956_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___y_954_);
lean_inc_ref(v___y_953_);
v___x_957_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___y_953_, v_maxHostLength_955_, v___x_956_, v___y_954_);
v_snd_958_ = lean_ctor_get(v___x_957_, 1);
lean_inc(v_snd_958_);
v_fst_959_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_fst_959_);
lean_dec_ref(v___x_957_);
v_fst_960_ = lean_ctor_get(v_snd_958_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v_snd_958_);
if (v_isSharedCheck_974_ == 0)
{
lean_object* v_unused_975_; 
v_unused_975_ = lean_ctor_get(v_snd_958_, 1);
lean_dec(v_unused_975_);
v___x_962_ = v_snd_958_;
v_isShared_963_ = v_isSharedCheck_974_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_fst_960_);
lean_dec(v_snd_958_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_974_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
uint8_t v___x_964_; 
v___x_964_ = lean_nat_dec_eq(v_fst_959_, v___x_956_);
if (v___x_964_ == 0)
{
lean_object* v_array_965_; lean_object* v_idx_966_; lean_object* v___x_967_; lean_object* v___x_968_; uint8_t v___x_969_; 
lean_del_object(v___x_962_);
v_array_965_ = lean_ctor_get(v___y_954_, 0);
lean_inc_ref(v_array_965_);
v_idx_966_ = lean_ctor_get(v___y_954_, 1);
lean_inc(v_idx_966_);
lean_dec_ref(v___y_954_);
v___x_967_ = lean_nat_add(v_idx_966_, v_fst_959_);
lean_dec(v_fst_959_);
v___x_968_ = lean_byte_array_size(v_array_965_);
v___x_969_ = lean_nat_dec_le(v_idx_966_, v___x_956_);
if (v___x_969_ == 0)
{
v___y_945_ = v_array_965_;
v___y_946_ = v___x_956_;
v___y_947_ = v___x_967_;
v___y_948_ = v___x_968_;
v___y_949_ = v_fst_960_;
v___y_950_ = v_idx_966_;
goto v___jp_944_;
}
else
{
lean_dec(v_idx_966_);
v___y_945_ = v_array_965_;
v___y_946_ = v___x_956_;
v___y_947_ = v___x_967_;
v___y_948_ = v___x_968_;
v___y_949_ = v_fst_960_;
v___y_950_ = v___x_956_;
goto v___jp_944_;
}
}
else
{
lean_object* v___x_970_; lean_object* v___x_972_; 
lean_dec(v_fst_960_);
lean_dec(v_fst_959_);
v___x_970_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7));
if (v_isShared_963_ == 0)
{
lean_ctor_set_tag(v___x_962_, 1);
lean_ctor_set(v___x_962_, 1, v___x_970_);
lean_ctor_set(v___x_962_, 0, v___y_954_);
v___x_972_ = v___x_962_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___y_954_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v___x_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
v___jp_976_:
{
lean_object* v___x_979_; 
lean_inc_ref(v_pos_978_);
v___x_979_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(v_pos_978_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_pos_980_; lean_object* v_res_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_989_; 
lean_dec_ref(v_pos_978_);
v_pos_980_ = lean_ctor_get(v___x_979_, 0);
v_res_981_ = lean_ctor_get(v___x_979_, 1);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_989_ == 0)
{
v___x_983_ = v___x_979_;
v_isShared_984_ = v_isSharedCheck_989_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_res_981_);
lean_inc(v_pos_980_);
lean_dec(v___x_979_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_989_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_985_, 0, v_res_981_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 1, v___x_985_);
v___x_987_ = v___x_983_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_pos_980_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
else
{
lean_object* v_err_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_999_; 
v_err_990_ = lean_ctor_get(v___x_979_, 1);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_999_ == 0)
{
lean_object* v_unused_1000_; 
v_unused_1000_ = lean_ctor_get(v___x_979_, 0);
lean_dec(v_unused_1000_);
v___x_992_ = v___x_979_;
v_isShared_993_ = v_isSharedCheck_999_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_err_990_);
lean_dec(v___x_979_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_999_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v_idx_994_; uint8_t v___x_995_; 
v_idx_994_ = lean_ctor_get(v_pos_978_, 1);
v___x_995_ = lean_nat_dec_eq(v_idx_994_, v_idx_994_);
if (v___x_995_ == 0)
{
lean_object* v___x_997_; 
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v_pos_978_);
v___x_997_ = v___x_992_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_pos_978_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_err_990_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
else
{
lean_del_object(v___x_992_);
lean_dec(v_err_990_);
v___y_953_ = v___y_977_;
v___y_954_ = v_pos_978_;
goto v___jp_952_;
}
}
}
}
v___jp_1001_:
{
v___y_953_ = v___y_1002_;
v___y_954_ = v_pos_1003_;
goto v___jp_952_;
}
v___jp_1007_:
{
lean_object* v___f_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v___f_1010_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3));
v___x_1011_ = lean_byte_array_size(v_array_1005_);
v___x_1012_ = lean_nat_dec_lt(v_idx_1006_, v___x_1011_);
if (v___x_1012_ == 0)
{
lean_dec(v_idx_1006_);
lean_dec_ref(v_array_1005_);
v___y_1002_ = v___f_1010_;
v_pos_1003_ = v_pos_1008_;
v_res_1004_ = v_res_1009_;
goto v___jp_1001_;
}
else
{
uint8_t v___x_1013_; uint8_t v___x_1014_; uint8_t v___x_1015_; 
v___x_1013_ = lean_byte_array_fget(v_array_1005_, v_idx_1006_);
lean_dec(v_idx_1006_);
lean_dec_ref(v_array_1005_);
v___x_1014_ = 48;
v___x_1015_ = lean_uint8_dec_le(v___x_1014_, v___x_1013_);
if (v___x_1015_ == 0)
{
v___y_1002_ = v___f_1010_;
v_pos_1003_ = v_pos_1008_;
v_res_1004_ = v_res_1009_;
goto v___jp_1001_;
}
else
{
uint8_t v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = 57;
v___x_1017_ = lean_uint8_dec_le(v___x_1013_, v___x_1016_);
if (v___x_1017_ == 0)
{
v___y_1002_ = v___f_1010_;
v_pos_1003_ = v_pos_1008_;
v_res_1004_ = v_res_1009_;
goto v___jp_1001_;
}
else
{
v___y_977_ = v___f_1010_;
v_pos_978_ = v_pos_1008_;
goto v___jp_976_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___boxed(lean_object* v_config_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_1045_, v_a_1046_);
lean_dec_ref(v_config_1045_);
return v_res_1047_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(lean_object* v___x_1048_, lean_object* v___x_1049_, lean_object* v___x_1050_, lean_object* v_inst_1051_, lean_object* v_R_1052_, lean_object* v_a_1053_, uint8_t v_b_1054_, lean_object* v_c_1055_){
_start:
{
uint8_t v___x_1056_; 
v___x_1056_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_1048_, v___x_1050_, v_a_1053_, v_b_1054_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___boxed(lean_object* v___x_1057_, lean_object* v___x_1058_, lean_object* v___x_1059_, lean_object* v_inst_1060_, lean_object* v_R_1061_, lean_object* v_a_1062_, lean_object* v_b_1063_, lean_object* v_c_1064_){
_start:
{
uint8_t v_b_boxed_1065_; uint8_t v_res_1066_; lean_object* v_r_1067_; 
v_b_boxed_1065_ = lean_unbox(v_b_1063_);
v_res_1066_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(v___x_1057_, v___x_1058_, v___x_1059_, v_inst_1060_, v_R_1061_, v_a_1062_, v_b_boxed_1065_, v_c_1064_);
lean_dec(v___x_1059_);
lean_dec_ref(v___x_1058_);
lean_dec_ref(v___x_1057_);
v_r_1067_ = lean_box(v_res_1066_);
return v_r_1067_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(uint8_t v___x_1068_, lean_object* v___x_1069_, lean_object* v___x_1070_, lean_object* v___x_1071_, lean_object* v_inst_1072_, lean_object* v_R_1073_, lean_object* v_a_1074_, uint8_t v_b_1075_, lean_object* v_c_1076_){
_start:
{
uint8_t v___x_1077_; 
v___x_1077_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_1068_, v___x_1069_, v___x_1070_, v___x_1071_, v_a_1074_, v_b_1075_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___boxed(lean_object* v___x_1078_, lean_object* v___x_1079_, lean_object* v___x_1080_, lean_object* v___x_1081_, lean_object* v_inst_1082_, lean_object* v_R_1083_, lean_object* v_a_1084_, lean_object* v_b_1085_, lean_object* v_c_1086_){
_start:
{
uint8_t v___x_13389__boxed_1087_; uint8_t v_b_boxed_1088_; uint8_t v_res_1089_; lean_object* v_r_1090_; 
v___x_13389__boxed_1087_ = lean_unbox(v___x_1078_);
v_b_boxed_1088_ = lean_unbox(v_b_1085_);
v_res_1089_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(v___x_13389__boxed_1087_, v___x_1079_, v___x_1080_, v___x_1081_, v_inst_1082_, v_R_1083_, v_a_1084_, v_b_boxed_1088_, v_c_1086_);
lean_dec_ref(v___x_1080_);
lean_dec_ref(v___x_1079_);
v_r_1090_ = lean_box(v_res_1089_);
return v_r_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(lean_object* v_config_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v_port_1105_; lean_object* v___y_1106_; lean_object* v___y_1110_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; uint8_t v_val_1122_; uint8_t v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v_pos_1133_; lean_object* v_array_1134_; lean_object* v_idx_1135_; lean_object* v_res_1136_; uint8_t v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v_pos_1151_; lean_object* v_pos_1154_; lean_object* v_res_1155_; lean_object* v_err_1220_; lean_object* v___x_1225_; 
lean_inc_ref(v_a_1101_);
v___x_1225_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(v_config_1100_, v_a_1101_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_pos_1226_; lean_object* v_res_1227_; lean_object* v_array_1228_; lean_object* v_idx_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1246_; 
v_pos_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_pos_1226_);
v_res_1227_ = lean_ctor_get(v___x_1225_, 1);
lean_inc(v_res_1227_);
lean_dec_ref_known(v___x_1225_, 2);
v_array_1228_ = lean_ctor_get(v_pos_1226_, 0);
v_idx_1229_ = lean_ctor_get(v_pos_1226_, 1);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_pos_1226_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1231_ = v_pos_1226_;
v_isShared_1232_ = v_isSharedCheck_1246_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_idx_1229_);
lean_inc(v_array_1228_);
lean_dec(v_pos_1226_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1246_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = lean_byte_array_size(v_array_1228_);
v___x_1234_ = lean_nat_dec_lt(v_idx_1229_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; 
lean_del_object(v___x_1231_);
lean_dec(v_idx_1229_);
lean_dec_ref(v_array_1228_);
lean_dec(v_res_1227_);
v___x_1235_ = lean_box(0);
v_err_1220_ = v___x_1235_;
goto v___jp_1219_;
}
else
{
uint8_t v___x_1236_; uint8_t v_got_1237_; uint8_t v___x_1238_; 
v___x_1236_ = 64;
v_got_1237_ = lean_byte_array_fget(v_array_1228_, v_idx_1229_);
v___x_1238_ = lean_uint8_dec_eq(v_got_1237_, v___x_1236_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; 
lean_del_object(v___x_1231_);
lean_dec(v_idx_1229_);
lean_dec_ref(v_array_1228_);
lean_dec(v_res_1227_);
v___x_1239_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5));
v_err_1220_ = v___x_1239_;
goto v___jp_1219_;
}
else
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1243_; 
lean_dec_ref(v_a_1101_);
v___x_1240_ = lean_unsigned_to_nat(1u);
v___x_1241_ = lean_nat_add(v_idx_1229_, v___x_1240_);
lean_dec(v_idx_1229_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v___x_1241_);
v___x_1243_ = v___x_1231_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_array_1228_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1244_; 
v___x_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1244_, 0, v_res_1227_);
v_pos_1154_ = v___x_1243_;
v_res_1155_ = v___x_1244_;
goto v___jp_1153_;
}
}
}
}
}
else
{
lean_object* v_err_1247_; 
v_err_1247_ = lean_ctor_get(v___x_1225_, 1);
lean_inc(v_err_1247_);
lean_dec_ref_known(v___x_1225_, 2);
v_err_1220_ = v_err_1247_;
goto v___jp_1219_;
}
v___jp_1102_:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1107_, 0, v___y_1103_);
lean_ctor_set(v___x_1107_, 1, v___y_1104_);
lean_ctor_set(v___x_1107_, 2, v_port_1105_);
v___x_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___y_1106_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
return v___x_1108_;
}
v___jp_1109_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__1));
v___x_1112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___y_1110_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
return v___x_1112_;
}
v___jp_1113_:
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_box(1);
v___y_1103_ = v___y_1114_;
v___y_1104_ = v___y_1116_;
v_port_1105_ = v___x_1117_;
v___y_1106_ = v___y_1115_;
goto v___jp_1102_;
}
v___jp_1118_:
{
uint8_t v___x_1123_; uint8_t v___x_1124_; 
v___x_1123_ = 47;
v___x_1124_ = lean_uint8_dec_eq(v_val_1122_, v___x_1123_);
if (v___x_1124_ == 0)
{
uint8_t v___x_1125_; uint8_t v___x_1126_; 
v___x_1125_ = 63;
v___x_1126_ = lean_uint8_dec_eq(v_val_1122_, v___x_1125_);
if (v___x_1126_ == 0)
{
uint8_t v___x_1127_; uint8_t v___x_1128_; 
v___x_1127_ = 35;
v___x_1128_ = lean_uint8_dec_eq(v_val_1122_, v___x_1127_);
if (v___x_1128_ == 0)
{
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1119_);
v___y_1110_ = v___y_1120_;
goto v___jp_1109_;
}
else
{
v___y_1114_ = v___y_1119_;
v___y_1115_ = v___y_1120_;
v___y_1116_ = v___y_1121_;
goto v___jp_1113_;
}
}
else
{
v___y_1114_ = v___y_1119_;
v___y_1115_ = v___y_1120_;
v___y_1116_ = v___y_1121_;
goto v___jp_1113_;
}
}
else
{
v___y_1114_ = v___y_1119_;
v___y_1115_ = v___y_1120_;
v___y_1116_ = v___y_1121_;
goto v___jp_1113_;
}
}
v___jp_1129_:
{
lean_object* v___x_1137_; uint8_t v___x_1138_; 
v___x_1137_ = lean_byte_array_size(v_array_1134_);
v___x_1138_ = lean_nat_dec_lt(v_idx_1135_, v___x_1137_);
if (v___x_1138_ == 0)
{
lean_dec(v_idx_1135_);
lean_dec_ref(v_array_1134_);
if (v___y_1130_ == 0)
{
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
v___y_1110_ = v_pos_1133_;
goto v___jp_1109_;
}
else
{
v___y_1114_ = v___y_1131_;
v___y_1115_ = v_pos_1133_;
v___y_1116_ = v___y_1132_;
goto v___jp_1113_;
}
}
else
{
uint8_t v___x_1139_; 
v___x_1139_ = lean_byte_array_fget(v_array_1134_, v_idx_1135_);
lean_dec(v_idx_1135_);
lean_dec_ref(v_array_1134_);
v___y_1119_ = v___y_1131_;
v___y_1120_ = v_pos_1133_;
v___y_1121_ = v___y_1132_;
v_val_1122_ = v___x_1139_;
goto v___jp_1118_;
}
}
v___jp_1140_:
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_box(0);
v___y_1130_ = v___y_1141_;
v___y_1131_ = v___y_1142_;
v___y_1132_ = v___y_1144_;
v_pos_1133_ = v___y_1145_;
v_array_1134_ = v___y_1146_;
v_idx_1135_ = v___y_1143_;
v_res_1136_ = v___x_1147_;
goto v___jp_1129_;
}
v___jp_1148_:
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_box(0);
v___y_1103_ = v___y_1149_;
v___y_1104_ = v___y_1150_;
v_port_1105_ = v___x_1152_;
v___y_1106_ = v_pos_1151_;
goto v___jp_1102_;
}
v___jp_1153_:
{
lean_object* v___x_1156_; 
v___x_1156_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_1100_, v_pos_1154_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_pos_1157_; lean_object* v_res_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1209_; 
v_pos_1157_ = lean_ctor_get(v___x_1156_, 0);
v_res_1158_ = lean_ctor_get(v___x_1156_, 1);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1160_ = v___x_1156_;
v_isShared_1161_ = v_isSharedCheck_1209_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_res_1158_);
lean_inc(v_pos_1157_);
lean_dec(v___x_1156_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1209_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v_array_1162_; lean_object* v_idx_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v_array_1162_ = lean_ctor_get(v_pos_1157_, 0);
v_idx_1163_ = lean_ctor_get(v_pos_1157_, 1);
v___x_1164_ = lean_byte_array_size(v_array_1162_);
v___x_1165_ = lean_nat_dec_lt(v_idx_1163_, v___x_1164_);
if (v___x_1165_ == 0)
{
lean_del_object(v___x_1160_);
v___y_1149_ = v_res_1155_;
v___y_1150_ = v_res_1158_;
v_pos_1151_ = v_pos_1157_;
goto v___jp_1148_;
}
else
{
uint8_t v___x_1166_; uint8_t v___x_1167_; uint8_t v___x_1168_; 
v___x_1166_ = lean_byte_array_fget(v_array_1162_, v_idx_1163_);
v___x_1167_ = 58;
v___x_1168_ = lean_uint8_dec_eq(v___x_1166_, v___x_1167_);
if (v___x_1168_ == 0)
{
lean_del_object(v___x_1160_);
v___y_1149_ = v_res_1155_;
v___y_1150_ = v_res_1158_;
v_pos_1151_ = v_pos_1157_;
goto v___jp_1148_;
}
else
{
if (v___x_1165_ == 0)
{
lean_object* v___x_1169_; lean_object* v___x_1171_; 
lean_dec(v_res_1158_);
lean_dec(v_res_1155_);
v___x_1169_ = lean_box(0);
if (v_isShared_1161_ == 0)
{
lean_ctor_set_tag(v___x_1160_, 1);
lean_ctor_set(v___x_1160_, 1, v___x_1169_);
v___x_1171_ = v___x_1160_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_pos_1157_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v___x_1169_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
else
{
if (v___x_1168_ == 0)
{
lean_object* v___x_1173_; lean_object* v___x_1175_; 
lean_dec(v_res_1158_);
lean_dec(v_res_1155_);
v___x_1173_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_1161_ == 0)
{
lean_ctor_set_tag(v___x_1160_, 1);
lean_ctor_set(v___x_1160_, 1, v___x_1173_);
v___x_1175_ = v___x_1160_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_pos_1157_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v___x_1173_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
else
{
lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1206_; 
lean_inc(v_idx_1163_);
lean_inc_ref(v_array_1162_);
lean_del_object(v___x_1160_);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_pos_1157_);
if (v_isSharedCheck_1206_ == 0)
{
lean_object* v_unused_1207_; lean_object* v_unused_1208_; 
v_unused_1207_ = lean_ctor_get(v_pos_1157_, 1);
lean_dec(v_unused_1207_);
v_unused_1208_ = lean_ctor_get(v_pos_1157_, 0);
lean_dec(v_unused_1208_);
v___x_1178_ = v_pos_1157_;
v_isShared_1179_ = v_isSharedCheck_1206_;
goto v_resetjp_1177_;
}
else
{
lean_dec(v_pos_1157_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1206_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1183_; 
v___x_1180_ = lean_unsigned_to_nat(1u);
v___x_1181_ = lean_nat_add(v_idx_1163_, v___x_1180_);
lean_dec(v_idx_1163_);
lean_inc(v___x_1181_);
lean_inc_ref(v_array_1162_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v___x_1181_);
v___x_1183_ = v___x_1178_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_array_1162_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
uint8_t v___x_1184_; 
v___x_1184_ = lean_nat_dec_lt(v___x_1181_, v___x_1164_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; 
v___x_1185_ = lean_box(0);
v___y_1130_ = v___x_1168_;
v___y_1131_ = v_res_1155_;
v___y_1132_ = v_res_1158_;
v_pos_1133_ = v___x_1183_;
v_array_1134_ = v_array_1162_;
v_idx_1135_ = v___x_1181_;
v_res_1136_ = v___x_1185_;
goto v___jp_1129_;
}
else
{
uint8_t v___x_1186_; uint8_t v___x_1187_; uint8_t v___x_1188_; 
v___x_1186_ = lean_byte_array_fget(v_array_1162_, v___x_1181_);
v___x_1187_ = 48;
v___x_1188_ = lean_uint8_dec_le(v___x_1187_, v___x_1186_);
if (v___x_1188_ == 0)
{
v___y_1141_ = v___x_1168_;
v___y_1142_ = v_res_1155_;
v___y_1143_ = v___x_1181_;
v___y_1144_ = v_res_1158_;
v___y_1145_ = v___x_1183_;
v___y_1146_ = v_array_1162_;
goto v___jp_1140_;
}
else
{
uint8_t v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = 57;
v___x_1190_ = lean_uint8_dec_le(v___x_1186_, v___x_1189_);
if (v___x_1190_ == 0)
{
v___y_1141_ = v___x_1168_;
v___y_1142_ = v_res_1155_;
v___y_1143_ = v___x_1181_;
v___y_1144_ = v_res_1158_;
v___y_1145_ = v___x_1183_;
v___y_1146_ = v_array_1162_;
goto v___jp_1140_;
}
else
{
lean_object* v___x_1191_; 
lean_dec(v___x_1181_);
lean_dec_ref(v_array_1162_);
v___x_1191_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_1183_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_pos_1192_; lean_object* v_res_1193_; lean_object* v___x_1194_; uint16_t v___x_1195_; 
v_pos_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_pos_1192_);
v_res_1193_ = lean_ctor_get(v___x_1191_, 1);
lean_inc(v_res_1193_);
lean_dec_ref_known(v___x_1191_, 2);
v___x_1194_ = lean_alloc_ctor(2, 0, 2);
v___x_1195_ = lean_unbox(v_res_1193_);
lean_dec(v_res_1193_);
lean_ctor_set_uint16(v___x_1194_, 0, v___x_1195_);
v___y_1103_ = v_res_1155_;
v___y_1104_ = v_res_1158_;
v_port_1105_ = v___x_1194_;
v___y_1106_ = v_pos_1192_;
goto v___jp_1102_;
}
else
{
lean_object* v_pos_1196_; lean_object* v_err_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_dec(v_res_1158_);
lean_dec(v_res_1155_);
v_pos_1196_ = lean_ctor_get(v___x_1191_, 0);
v_err_1197_ = lean_ctor_get(v___x_1191_, 1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1191_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_err_1197_);
lean_inc(v_pos_1196_);
lean_dec(v___x_1191_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_pos_1196_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_err_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
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
lean_object* v_pos_1210_; lean_object* v_err_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
lean_dec(v_res_1155_);
v_pos_1210_ = lean_ctor_get(v___x_1156_, 0);
v_err_1211_ = lean_ctor_get(v___x_1156_, 1);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1156_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_err_1211_);
lean_inc(v_pos_1210_);
lean_dec(v___x_1156_);
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
v___jp_1219_:
{
lean_object* v_idx_1221_; uint8_t v___x_1222_; 
v_idx_1221_ = lean_ctor_get(v_a_1101_, 1);
v___x_1222_ = lean_nat_dec_eq(v_idx_1221_, v_idx_1221_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; 
v___x_1223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1223_, 0, v_a_1101_);
lean_ctor_set(v___x_1223_, 1, v_err_1220_);
return v___x_1223_;
}
else
{
lean_object* v___x_1224_; 
lean_dec(v_err_1220_);
v___x_1224_ = lean_box(0);
v_pos_1154_ = v_a_1101_;
v_res_1155_ = v___x_1224_;
goto v___jp_1153_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___boxed(lean_object* v_config_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_1248_, v_a_1249_);
lean_dec_ref(v_config_1248_);
return v_res_1250_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(uint8_t v_c_1251_){
_start:
{
uint8_t v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = 48;
v___x_1300_ = lean_uint8_dec_le(v___x_1299_, v_c_1251_);
if (v___x_1300_ == 0)
{
goto v___jp_1294_;
}
else
{
uint8_t v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = 57;
v___x_1302_ = lean_uint8_dec_le(v_c_1251_, v___x_1301_);
if (v___x_1302_ == 0)
{
goto v___jp_1294_;
}
else
{
return v___x_1302_;
}
}
v___jp_1252_:
{
uint8_t v___x_1253_; uint8_t v___x_1254_; 
v___x_1253_ = 45;
v___x_1254_ = lean_uint8_dec_eq(v_c_1251_, v___x_1253_);
if (v___x_1254_ == 0)
{
uint8_t v___x_1255_; uint8_t v___x_1256_; 
v___x_1255_ = 46;
v___x_1256_ = lean_uint8_dec_eq(v_c_1251_, v___x_1255_);
if (v___x_1256_ == 0)
{
uint8_t v___x_1257_; uint8_t v___x_1258_; 
v___x_1257_ = 95;
v___x_1258_ = lean_uint8_dec_eq(v_c_1251_, v___x_1257_);
if (v___x_1258_ == 0)
{
uint8_t v___x_1259_; uint8_t v___x_1260_; 
v___x_1259_ = 126;
v___x_1260_ = lean_uint8_dec_eq(v_c_1251_, v___x_1259_);
if (v___x_1260_ == 0)
{
uint8_t v___x_1261_; uint8_t v___x_1262_; 
v___x_1261_ = 33;
v___x_1262_ = lean_uint8_dec_eq(v_c_1251_, v___x_1261_);
if (v___x_1262_ == 0)
{
uint8_t v___x_1263_; uint8_t v___x_1264_; 
v___x_1263_ = 36;
v___x_1264_ = lean_uint8_dec_eq(v_c_1251_, v___x_1263_);
if (v___x_1264_ == 0)
{
uint8_t v___x_1265_; uint8_t v___x_1266_; 
v___x_1265_ = 38;
v___x_1266_ = lean_uint8_dec_eq(v_c_1251_, v___x_1265_);
if (v___x_1266_ == 0)
{
uint8_t v___x_1267_; uint8_t v___x_1268_; 
v___x_1267_ = 39;
v___x_1268_ = lean_uint8_dec_eq(v_c_1251_, v___x_1267_);
if (v___x_1268_ == 0)
{
uint8_t v___x_1269_; uint8_t v___x_1270_; 
v___x_1269_ = 40;
v___x_1270_ = lean_uint8_dec_eq(v_c_1251_, v___x_1269_);
if (v___x_1270_ == 0)
{
uint8_t v___x_1271_; uint8_t v___x_1272_; 
v___x_1271_ = 41;
v___x_1272_ = lean_uint8_dec_eq(v_c_1251_, v___x_1271_);
if (v___x_1272_ == 0)
{
uint8_t v___x_1273_; uint8_t v___x_1274_; 
v___x_1273_ = 42;
v___x_1274_ = lean_uint8_dec_eq(v_c_1251_, v___x_1273_);
if (v___x_1274_ == 0)
{
uint8_t v___x_1275_; uint8_t v___x_1276_; 
v___x_1275_ = 43;
v___x_1276_ = lean_uint8_dec_eq(v_c_1251_, v___x_1275_);
if (v___x_1276_ == 0)
{
uint8_t v___x_1277_; uint8_t v___x_1278_; 
v___x_1277_ = 44;
v___x_1278_ = lean_uint8_dec_eq(v_c_1251_, v___x_1277_);
if (v___x_1278_ == 0)
{
uint8_t v___x_1279_; uint8_t v___x_1280_; 
v___x_1279_ = 59;
v___x_1280_ = lean_uint8_dec_eq(v_c_1251_, v___x_1279_);
if (v___x_1280_ == 0)
{
uint8_t v___x_1281_; uint8_t v___x_1282_; 
v___x_1281_ = 61;
v___x_1282_ = lean_uint8_dec_eq(v_c_1251_, v___x_1281_);
if (v___x_1282_ == 0)
{
uint8_t v___x_1283_; uint8_t v___x_1284_; 
v___x_1283_ = 58;
v___x_1284_ = lean_uint8_dec_eq(v_c_1251_, v___x_1283_);
if (v___x_1284_ == 0)
{
uint8_t v___x_1285_; uint8_t v___x_1286_; 
v___x_1285_ = 64;
v___x_1286_ = lean_uint8_dec_eq(v_c_1251_, v___x_1285_);
if (v___x_1286_ == 0)
{
uint8_t v___x_1287_; uint8_t v___x_1288_; 
v___x_1287_ = 37;
v___x_1288_ = lean_uint8_dec_eq(v_c_1251_, v___x_1287_);
return v___x_1288_;
}
else
{
return v___x_1286_;
}
}
else
{
return v___x_1284_;
}
}
else
{
return v___x_1282_;
}
}
else
{
return v___x_1280_;
}
}
else
{
return v___x_1278_;
}
}
else
{
return v___x_1276_;
}
}
else
{
return v___x_1274_;
}
}
else
{
return v___x_1272_;
}
}
else
{
return v___x_1270_;
}
}
else
{
return v___x_1268_;
}
}
else
{
return v___x_1266_;
}
}
else
{
return v___x_1264_;
}
}
else
{
return v___x_1262_;
}
}
else
{
return v___x_1260_;
}
}
else
{
return v___x_1258_;
}
}
else
{
return v___x_1256_;
}
}
else
{
return v___x_1254_;
}
}
v___jp_1289_:
{
uint8_t v___x_1290_; uint8_t v___x_1291_; 
v___x_1290_ = 65;
v___x_1291_ = lean_uint8_dec_le(v___x_1290_, v_c_1251_);
if (v___x_1291_ == 0)
{
goto v___jp_1252_;
}
else
{
uint8_t v___x_1292_; uint8_t v___x_1293_; 
v___x_1292_ = 90;
v___x_1293_ = lean_uint8_dec_le(v_c_1251_, v___x_1292_);
if (v___x_1293_ == 0)
{
goto v___jp_1252_;
}
else
{
return v___x_1293_;
}
}
}
v___jp_1294_:
{
uint8_t v___x_1295_; uint8_t v___x_1296_; 
v___x_1295_ = 97;
v___x_1296_ = lean_uint8_dec_le(v___x_1295_, v_c_1251_);
if (v___x_1296_ == 0)
{
goto v___jp_1289_;
}
else
{
uint8_t v___x_1297_; uint8_t v___x_1298_; 
v___x_1297_ = 122;
v___x_1298_ = lean_uint8_dec_le(v_c_1251_, v___x_1297_);
if (v___x_1298_ == 0)
{
goto v___jp_1289_;
}
else
{
return v___x_1298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0___boxed(lean_object* v_c_1303_){
_start:
{
uint8_t v_c_boxed_1304_; uint8_t v_res_1305_; lean_object* v_r_1306_; 
v_c_boxed_1304_ = lean_unbox(v_c_1303_);
v_res_1305_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(v_c_boxed_1304_);
v_r_1306_ = lean_box(v_res_1305_);
return v_r_1306_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(lean_object* v_config_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v_maxSegmentLength_1310_; lean_object* v___f_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v_snd_1314_; lean_object* v_fst_1315_; lean_object* v_fst_1316_; lean_object* v_array_1317_; lean_object* v_idx_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1335_; 
v_maxSegmentLength_1310_ = lean_ctor_get(v_config_1308_, 3);
v___f_1311_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___closed__0));
v___x_1312_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1309_);
v___x_1313_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1311_, v_maxSegmentLength_1310_, v___x_1312_, v_a_1309_);
v_snd_1314_ = lean_ctor_get(v___x_1313_, 1);
lean_inc(v_snd_1314_);
v_fst_1315_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_fst_1315_);
lean_dec_ref(v___x_1313_);
v_fst_1316_ = lean_ctor_get(v_snd_1314_, 0);
lean_inc(v_fst_1316_);
lean_dec(v_snd_1314_);
v_array_1317_ = lean_ctor_get(v_a_1309_, 0);
v_idx_1318_ = lean_ctor_get(v_a_1309_, 1);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_a_1309_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1320_ = v_a_1309_;
v_isShared_1321_ = v_isSharedCheck_1335_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_idx_1318_);
lean_inc(v_array_1317_);
lean_dec(v_a_1309_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1335_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v_lower_1323_; lean_object* v_upper_1324_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___y_1332_; uint8_t v___x_1334_; 
v___x_1329_ = lean_nat_add(v_idx_1318_, v_fst_1315_);
lean_dec(v_fst_1315_);
v___x_1330_ = lean_byte_array_size(v_array_1317_);
v___x_1334_ = lean_nat_dec_le(v_idx_1318_, v___x_1312_);
if (v___x_1334_ == 0)
{
v___y_1332_ = v_idx_1318_;
goto v___jp_1331_;
}
else
{
lean_dec(v_idx_1318_);
v___y_1332_ = v___x_1312_;
goto v___jp_1331_;
}
v___jp_1322_:
{
lean_object* v___x_1325_; lean_object* v___x_1327_; 
v___x_1325_ = l_ByteArray_toByteSlice(v_array_1317_, v_lower_1323_, v_upper_1324_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 1, v___x_1325_);
lean_ctor_set(v___x_1320_, 0, v_fst_1316_);
v___x_1327_ = v___x_1320_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_fst_1316_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v___x_1325_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
v___jp_1331_:
{
uint8_t v___x_1333_; 
v___x_1333_ = lean_nat_dec_le(v___x_1329_, v___x_1330_);
if (v___x_1333_ == 0)
{
lean_dec(v___x_1329_);
v_lower_1323_ = v___y_1332_;
v_upper_1324_ = v___x_1330_;
goto v___jp_1322_;
}
else
{
v_lower_1323_ = v___y_1332_;
v_upper_1324_ = v___x_1329_;
goto v___jp_1322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___boxed(lean_object* v_config_1336_, lean_object* v_a_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1336_, v_a_1337_);
lean_dec_ref(v_config_1336_);
return v_res_1338_;
}
}
LEAN_EXPORT uint8_t l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(uint8_t v_c_1339_){
_start:
{
uint8_t v___x_1340_; uint8_t v___x_1341_; 
v___x_1340_ = 63;
v___x_1341_ = lean_uint8_dec_eq(v_c_1339_, v___x_1340_);
if (v___x_1341_ == 0)
{
uint8_t v___x_1342_; uint8_t v___x_1343_; 
v___x_1342_ = 35;
v___x_1343_ = lean_uint8_dec_eq(v_c_1339_, v___x_1342_);
return v___x_1343_;
}
else
{
return v___x_1341_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0___boxed(lean_object* v_c_1344_){
_start:
{
uint8_t v_c_boxed_1345_; uint8_t v_res_1346_; lean_object* v_r_1347_; 
v_c_boxed_1345_ = lean_unbox(v_c_1344_);
v_res_1346_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v_c_boxed_1345_);
v_r_1347_ = lean_box(v_res_1346_);
return v_r_1347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(lean_object* v_config_1355_, lean_object* v_a_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v_array_1382_; lean_object* v_idx_1383_; lean_object* v_fst_1384_; lean_object* v_snd_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1550_; 
v_array_1382_ = lean_ctor_get(v___y_1357_, 0);
v_idx_1383_ = lean_ctor_get(v___y_1357_, 1);
v_fst_1384_ = lean_ctor_get(v_a_1356_, 0);
v_snd_1385_ = lean_ctor_get(v_a_1356_, 1);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_a_1356_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1387_ = v_a_1356_;
v_isShared_1388_ = v_isSharedCheck_1550_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_snd_1385_);
lean_inc(v_fst_1384_);
lean_dec(v_a_1356_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1550_;
goto v_resetjp_1386_;
}
v___jp_1358_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___y_1361_);
lean_ctor_set(v___x_1362_, 1, v___y_1359_);
v___x_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___y_1360_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
return v___x_1363_;
}
v___jp_1364_:
{
lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1369_ = lean_array_get_size(v___y_1367_);
v___x_1370_ = lean_nat_dec_le(v___y_1366_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
lean_dec(v___y_1366_);
v___x_1371_ = l_ByteArray_empty;
v___x_1372_ = lean_array_push(v___y_1367_, v___x_1371_);
v___x_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
lean_ctor_set(v___x_1373_, 1, v___y_1365_);
v_a_1356_ = v___x_1373_;
v___y_1357_ = v___y_1368_;
goto _start;
}
else
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1365_);
lean_dec_ref(v_config_1355_);
v___x_1375_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1376_ = l_Nat_reprFast(v___y_1366_);
v___x_1377_ = lean_string_append(v___x_1375_, v___x_1376_);
lean_dec_ref(v___x_1376_);
v___x_1378_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1379_ = lean_string_append(v___x_1377_, v___x_1378_);
v___x_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
v___x_1381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___y_1368_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
return v___x_1381_;
}
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; uint8_t v___x_1390_; 
v___x_1389_ = lean_byte_array_size(v_array_1382_);
v___x_1390_ = lean_nat_dec_lt(v_idx_1383_, v___x_1389_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1392_; 
lean_dec_ref(v_config_1355_);
if (v_isShared_1388_ == 0)
{
v___x_1392_ = v___x_1387_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_fst_1384_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_snd_1385_);
v___x_1392_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1393_; 
v___x_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___y_1357_);
lean_ctor_set(v___x_1393_, 1, v___x_1392_);
return v___x_1393_;
}
}
else
{
uint8_t v___x_1491_; uint8_t v___x_1541_; 
v___x_1491_ = lean_byte_array_fget(v_array_1382_, v_idx_1383_);
v___x_1541_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1491_);
if (v___x_1541_ == 0)
{
uint8_t v___x_1542_; uint8_t v___x_1543_; 
v___x_1542_ = 47;
v___x_1543_ = lean_uint8_dec_eq(v___x_1491_, v___x_1542_);
if (v___x_1543_ == 0)
{
uint8_t v___x_1544_; uint8_t v___x_1545_; 
v___x_1544_ = 48;
v___x_1545_ = lean_uint8_dec_le(v___x_1544_, v___x_1491_);
if (v___x_1545_ == 0)
{
goto v___jp_1536_;
}
else
{
uint8_t v___x_1546_; uint8_t v___x_1547_; 
v___x_1546_ = 57;
v___x_1547_ = lean_uint8_dec_le(v___x_1491_, v___x_1546_);
if (v___x_1547_ == 0)
{
goto v___jp_1536_;
}
else
{
goto v___jp_1395_;
}
}
}
else
{
goto v___jp_1395_;
}
}
else
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_del_object(v___x_1387_);
lean_dec_ref(v_config_1355_);
v___x_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1548_, 0, v_fst_1384_);
lean_ctor_set(v___x_1548_, 1, v_snd_1385_);
v___x_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___y_1357_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
return v___x_1549_;
}
v___jp_1395_:
{
lean_object* v_maxPathSegments_1396_; lean_object* v_maxTotalPathLength_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; 
v_maxPathSegments_1396_ = lean_ctor_get(v_config_1355_, 6);
v_maxTotalPathLength_1397_ = lean_ctor_get(v_config_1355_, 7);
v___x_1398_ = lean_array_get_size(v_fst_1384_);
v___x_1399_ = lean_nat_dec_le(v_maxPathSegments_1396_, v___x_1398_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; 
v___x_1400_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1355_, v___y_1357_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_pos_1401_; lean_object* v_res_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1474_; 
v_pos_1401_ = lean_ctor_get(v___x_1400_, 0);
v_res_1402_ = lean_ctor_get(v___x_1400_, 1);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1404_ = v___x_1400_;
v_isShared_1405_ = v_isSharedCheck_1474_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_res_1402_);
lean_inc(v_pos_1401_);
lean_dec(v___x_1400_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1474_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
lean_inc(v_res_1402_);
v___x_1406_ = l_ByteSlice_toByteArray(v_res_1402_);
v___x_1407_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_1406_);
if (lean_obj_tag(v___x_1407_) == 1)
{
lean_object* v_val_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1469_; 
v_val_1408_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1410_ = v___x_1407_;
v_isShared_1411_ = v_isSharedCheck_1469_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_val_1408_);
lean_dec(v___x_1407_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1469_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; 
v___x_1412_ = l_ByteSlice_size(v_res_1402_);
lean_dec(v_res_1402_);
v___x_1413_ = lean_nat_add(v_snd_1385_, v___x_1412_);
lean_dec(v___x_1412_);
lean_dec(v_snd_1385_);
v___x_1414_ = lean_nat_dec_lt(v_maxTotalPathLength_1397_, v___x_1413_);
if (v___x_1414_ == 0)
{
lean_object* v_array_1415_; lean_object* v_idx_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v_array_1415_ = lean_ctor_get(v_pos_1401_, 0);
v_idx_1416_ = lean_ctor_get(v_pos_1401_, 1);
v___x_1417_ = lean_array_push(v_fst_1384_, v_val_1408_);
v___x_1418_ = lean_byte_array_size(v_array_1415_);
v___x_1419_ = lean_nat_dec_lt(v_idx_1416_, v___x_1418_);
if (v___x_1419_ == 0)
{
lean_del_object(v___x_1410_);
lean_del_object(v___x_1404_);
lean_del_object(v___x_1387_);
lean_dec_ref(v_config_1355_);
v___y_1359_ = v___x_1413_;
v___y_1360_ = v_pos_1401_;
v___y_1361_ = v___x_1417_;
goto v___jp_1358_;
}
else
{
uint8_t v___x_1420_; uint8_t v___x_1421_; uint8_t v___x_1422_; 
v___x_1420_ = lean_byte_array_fget(v_array_1415_, v_idx_1416_);
v___x_1421_ = 47;
v___x_1422_ = lean_uint8_dec_eq(v___x_1420_, v___x_1421_);
if (v___x_1422_ == 0)
{
lean_del_object(v___x_1410_);
lean_del_object(v___x_1404_);
lean_del_object(v___x_1387_);
lean_dec_ref(v_config_1355_);
v___y_1359_ = v___x_1413_;
v___y_1360_ = v_pos_1401_;
v___y_1361_ = v___x_1417_;
goto v___jp_1358_;
}
else
{
lean_object* v___x_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; 
v___x_1423_ = lean_unsigned_to_nat(1u);
v___x_1424_ = lean_nat_add(v___x_1413_, v___x_1423_);
lean_dec(v___x_1413_);
v___x_1425_ = lean_nat_dec_lt(v_maxTotalPathLength_1397_, v___x_1424_);
if (v___x_1425_ == 0)
{
lean_del_object(v___x_1410_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1426_; lean_object* v___x_1428_; 
lean_dec(v___x_1424_);
lean_dec_ref(v___x_1417_);
lean_del_object(v___x_1387_);
lean_dec_ref(v_config_1355_);
v___x_1426_ = lean_box(0);
if (v_isShared_1405_ == 0)
{
lean_ctor_set_tag(v___x_1404_, 1);
lean_ctor_set(v___x_1404_, 1, v___x_1426_);
v___x_1428_ = v___x_1404_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_pos_1401_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
else
{
lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1444_; 
lean_inc(v_idx_1416_);
lean_inc_ref(v_array_1415_);
lean_del_object(v___x_1404_);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_pos_1401_);
if (v_isSharedCheck_1444_ == 0)
{
lean_object* v_unused_1445_; lean_object* v_unused_1446_; 
v_unused_1445_ = lean_ctor_get(v_pos_1401_, 1);
lean_dec(v_unused_1445_);
v_unused_1446_ = lean_ctor_get(v_pos_1401_, 0);
lean_dec(v_unused_1446_);
v___x_1431_ = v_pos_1401_;
v_isShared_1432_ = v_isSharedCheck_1444_;
goto v_resetjp_1430_;
}
else
{
lean_dec(v_pos_1401_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1444_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1433_; lean_object* v___x_1435_; 
v___x_1433_ = lean_nat_add(v_idx_1416_, v___x_1423_);
lean_dec(v_idx_1416_);
lean_inc(v___x_1433_);
lean_inc_ref(v_array_1415_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 1, v___x_1433_);
v___x_1435_ = v___x_1431_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_array_1415_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
uint8_t v___x_1436_; 
v___x_1436_ = lean_nat_dec_lt(v___x_1433_, v___x_1418_);
if (v___x_1436_ == 0)
{
lean_dec(v___x_1433_);
lean_dec_ref(v_array_1415_);
lean_del_object(v___x_1387_);
lean_inc(v_maxPathSegments_1396_);
v___y_1365_ = v___x_1424_;
v___y_1366_ = v_maxPathSegments_1396_;
v___y_1367_ = v___x_1417_;
v___y_1368_ = v___x_1435_;
goto v___jp_1364_;
}
else
{
uint8_t v___x_1437_; uint8_t v___x_1438_; 
v___x_1437_ = lean_byte_array_fget(v_array_1415_, v___x_1433_);
lean_dec(v___x_1433_);
lean_dec_ref(v_array_1415_);
v___x_1438_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1437_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1440_; 
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 1, v___x_1424_);
lean_ctor_set(v___x_1387_, 0, v___x_1417_);
v___x_1440_ = v___x_1387_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1417_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v___x_1424_);
v___x_1440_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
v_a_1356_ = v___x_1440_;
v___y_1357_ = v___x_1435_;
goto _start;
}
}
else
{
lean_del_object(v___x_1387_);
lean_inc(v_maxPathSegments_1396_);
v___y_1365_ = v___x_1424_;
v___y_1366_ = v_maxPathSegments_1396_;
v___y_1367_ = v___x_1417_;
v___y_1368_ = v___x_1435_;
goto v___jp_1364_;
}
}
}
}
}
}
else
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1453_; 
lean_inc(v_maxTotalPathLength_1397_);
lean_dec(v___x_1424_);
lean_dec_ref(v___x_1417_);
lean_del_object(v___x_1387_);
lean_dec_ref(v_config_1355_);
v___x_1447_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1448_ = l_Nat_reprFast(v_maxTotalPathLength_1397_);
v___x_1449_ = lean_string_append(v___x_1447_, v___x_1448_);
lean_dec_ref(v___x_1448_);
v___x_1450_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1451_ = lean_string_append(v___x_1449_, v___x_1450_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 0, v___x_1451_);
v___x_1453_ = v___x_1410_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1451_);
v___x_1453_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1455_; 
if (v_isShared_1405_ == 0)
{
lean_ctor_set_tag(v___x_1404_, 1);
lean_ctor_set(v___x_1404_, 1, v___x_1453_);
v___x_1455_ = v___x_1404_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_pos_1401_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v___x_1453_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
}
else
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1464_; 
lean_inc(v_maxTotalPathLength_1397_);
lean_dec(v___x_1413_);
lean_dec(v_val_1408_);
lean_del_object(v___x_1387_);
lean_dec(v_fst_1384_);
lean_dec_ref(v_config_1355_);
v___x_1458_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1459_ = l_Nat_reprFast(v_maxTotalPathLength_1397_);
v___x_1460_ = lean_string_append(v___x_1458_, v___x_1459_);
lean_dec_ref(v___x_1459_);
v___x_1461_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1462_ = lean_string_append(v___x_1460_, v___x_1461_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 0, v___x_1462_);
v___x_1464_ = v___x_1410_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
lean_object* v___x_1466_; 
if (v_isShared_1405_ == 0)
{
lean_ctor_set_tag(v___x_1404_, 1);
lean_ctor_set(v___x_1404_, 1, v___x_1464_);
v___x_1466_ = v___x_1404_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_pos_1401_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v___x_1464_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
else
{
lean_object* v___x_1470_; lean_object* v___x_1472_; 
lean_dec(v___x_1407_);
lean_dec(v_res_1402_);
lean_del_object(v___x_1387_);
lean_dec(v_snd_1385_);
lean_dec(v_fst_1384_);
lean_dec_ref(v_config_1355_);
v___x_1470_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5));
if (v_isShared_1405_ == 0)
{
lean_ctor_set_tag(v___x_1404_, 1);
lean_ctor_set(v___x_1404_, 1, v___x_1470_);
v___x_1472_ = v___x_1404_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_pos_1401_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v___x_1470_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
else
{
lean_object* v_pos_1475_; lean_object* v_err_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
lean_del_object(v___x_1387_);
lean_dec(v_snd_1385_);
lean_dec(v_fst_1384_);
lean_dec_ref(v_config_1355_);
v_pos_1475_ = lean_ctor_get(v___x_1400_, 0);
v_err_1476_ = lean_ctor_get(v___x_1400_, 1);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1400_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_err_1476_);
lean_inc(v_pos_1475_);
lean_dec(v___x_1400_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_pos_1475_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v_err_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
else
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
lean_inc(v_maxPathSegments_1396_);
lean_del_object(v___x_1387_);
lean_dec(v_snd_1385_);
lean_dec(v_fst_1384_);
lean_dec_ref(v_config_1355_);
v___x_1484_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1485_ = l_Nat_reprFast(v_maxPathSegments_1396_);
v___x_1486_ = lean_string_append(v___x_1484_, v___x_1485_);
lean_dec_ref(v___x_1485_);
v___x_1487_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1488_ = lean_string_append(v___x_1486_, v___x_1487_);
v___x_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
v___x_1490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___y_1357_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
return v___x_1490_;
}
}
v___jp_1492_:
{
uint8_t v___x_1493_; uint8_t v___x_1494_; 
v___x_1493_ = 45;
v___x_1494_ = lean_uint8_dec_eq(v___x_1491_, v___x_1493_);
if (v___x_1494_ == 0)
{
uint8_t v___x_1495_; uint8_t v___x_1496_; 
v___x_1495_ = 46;
v___x_1496_ = lean_uint8_dec_eq(v___x_1491_, v___x_1495_);
if (v___x_1496_ == 0)
{
uint8_t v___x_1497_; uint8_t v___x_1498_; 
v___x_1497_ = 95;
v___x_1498_ = lean_uint8_dec_eq(v___x_1491_, v___x_1497_);
if (v___x_1498_ == 0)
{
uint8_t v___x_1499_; uint8_t v___x_1500_; 
v___x_1499_ = 126;
v___x_1500_ = lean_uint8_dec_eq(v___x_1491_, v___x_1499_);
if (v___x_1500_ == 0)
{
uint8_t v___x_1501_; uint8_t v___x_1502_; 
v___x_1501_ = 33;
v___x_1502_ = lean_uint8_dec_eq(v___x_1491_, v___x_1501_);
if (v___x_1502_ == 0)
{
uint8_t v___x_1503_; uint8_t v___x_1504_; 
v___x_1503_ = 36;
v___x_1504_ = lean_uint8_dec_eq(v___x_1491_, v___x_1503_);
if (v___x_1504_ == 0)
{
uint8_t v___x_1505_; uint8_t v___x_1506_; 
v___x_1505_ = 38;
v___x_1506_ = lean_uint8_dec_eq(v___x_1491_, v___x_1505_);
if (v___x_1506_ == 0)
{
uint8_t v___x_1507_; uint8_t v___x_1508_; 
v___x_1507_ = 39;
v___x_1508_ = lean_uint8_dec_eq(v___x_1491_, v___x_1507_);
if (v___x_1508_ == 0)
{
uint8_t v___x_1509_; uint8_t v___x_1510_; 
v___x_1509_ = 40;
v___x_1510_ = lean_uint8_dec_eq(v___x_1491_, v___x_1509_);
if (v___x_1510_ == 0)
{
uint8_t v___x_1511_; uint8_t v___x_1512_; 
v___x_1511_ = 41;
v___x_1512_ = lean_uint8_dec_eq(v___x_1491_, v___x_1511_);
if (v___x_1512_ == 0)
{
uint8_t v___x_1513_; uint8_t v___x_1514_; 
v___x_1513_ = 42;
v___x_1514_ = lean_uint8_dec_eq(v___x_1491_, v___x_1513_);
if (v___x_1514_ == 0)
{
uint8_t v___x_1515_; uint8_t v___x_1516_; 
v___x_1515_ = 43;
v___x_1516_ = lean_uint8_dec_eq(v___x_1491_, v___x_1515_);
if (v___x_1516_ == 0)
{
uint8_t v___x_1517_; uint8_t v___x_1518_; 
v___x_1517_ = 44;
v___x_1518_ = lean_uint8_dec_eq(v___x_1491_, v___x_1517_);
if (v___x_1518_ == 0)
{
uint8_t v___x_1519_; uint8_t v___x_1520_; 
v___x_1519_ = 59;
v___x_1520_ = lean_uint8_dec_eq(v___x_1491_, v___x_1519_);
if (v___x_1520_ == 0)
{
uint8_t v___x_1521_; uint8_t v___x_1522_; 
v___x_1521_ = 61;
v___x_1522_ = lean_uint8_dec_eq(v___x_1491_, v___x_1521_);
if (v___x_1522_ == 0)
{
uint8_t v___x_1523_; uint8_t v___x_1524_; 
v___x_1523_ = 58;
v___x_1524_ = lean_uint8_dec_eq(v___x_1491_, v___x_1523_);
if (v___x_1524_ == 0)
{
uint8_t v___x_1525_; uint8_t v___x_1526_; 
v___x_1525_ = 64;
v___x_1526_ = lean_uint8_dec_eq(v___x_1491_, v___x_1525_);
if (v___x_1526_ == 0)
{
uint8_t v___x_1527_; uint8_t v___x_1528_; 
v___x_1527_ = 37;
v___x_1528_ = lean_uint8_dec_eq(v___x_1491_, v___x_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_del_object(v___x_1387_);
lean_dec_ref(v_config_1355_);
v___x_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1529_, 0, v_fst_1384_);
lean_ctor_set(v___x_1529_, 1, v_snd_1385_);
v___x_1530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___y_1357_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
return v___x_1530_;
}
else
{
goto v___jp_1395_;
}
}
else
{
goto v___jp_1395_;
}
}
else
{
goto v___jp_1395_;
}
}
else
{
goto v___jp_1395_;
}
}
else
{
goto v___jp_1395_;
}
}
else
{
goto v___jp_1395_;
}
}
else
{
goto v___jp_1395_;
}
}
else
{
goto v___jp_1395_;
}
}
else
{
goto v___jp_1395_;
}
}
else
{
goto v___jp_1395_;
}
}
else
{
goto v___jp_1395_;
}
}
else
{
goto v___jp_1395_;
}
}
else
{
goto v___jp_1395_;
}
}
else
{
goto v___jp_1395_;
}
}
else
{
goto v___jp_1395_;
}
}
else
{
goto v___jp_1395_;
}
}
else
{
goto v___jp_1395_;
}
}
else
{
goto v___jp_1395_;
}
}
v___jp_1531_:
{
uint8_t v___x_1532_; uint8_t v___x_1533_; 
v___x_1532_ = 65;
v___x_1533_ = lean_uint8_dec_le(v___x_1532_, v___x_1491_);
if (v___x_1533_ == 0)
{
goto v___jp_1492_;
}
else
{
uint8_t v___x_1534_; uint8_t v___x_1535_; 
v___x_1534_ = 90;
v___x_1535_ = lean_uint8_dec_le(v___x_1491_, v___x_1534_);
if (v___x_1535_ == 0)
{
goto v___jp_1492_;
}
else
{
goto v___jp_1395_;
}
}
}
v___jp_1536_:
{
uint8_t v___x_1537_; uint8_t v___x_1538_; 
v___x_1537_ = 97;
v___x_1538_ = lean_uint8_dec_le(v___x_1537_, v___x_1491_);
if (v___x_1538_ == 0)
{
goto v___jp_1531_;
}
else
{
uint8_t v___x_1539_; uint8_t v___x_1540_; 
v___x_1539_ = 122;
v___x_1540_ = lean_uint8_dec_le(v___x_1491_, v___x_1539_);
if (v___x_1540_ == 0)
{
goto v___jp_1531_;
}
else
{
goto v___jp_1395_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(lean_object* v_config_1551_, lean_object* v_a_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v_array_1578_; lean_object* v_idx_1579_; lean_object* v_fst_1580_; lean_object* v_snd_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1746_; 
v_array_1578_ = lean_ctor_get(v___y_1553_, 0);
v_idx_1579_ = lean_ctor_get(v___y_1553_, 1);
v_fst_1580_ = lean_ctor_get(v_a_1552_, 0);
v_snd_1581_ = lean_ctor_get(v_a_1552_, 1);
v_isSharedCheck_1746_ = !lean_is_exclusive(v_a_1552_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1583_ = v_a_1552_;
v_isShared_1584_ = v_isSharedCheck_1746_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_snd_1581_);
lean_inc(v_fst_1580_);
lean_dec(v_a_1552_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1746_;
goto v_resetjp_1582_;
}
v___jp_1554_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___y_1556_);
lean_ctor_set(v___x_1558_, 1, v___y_1557_);
v___x_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___y_1555_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
return v___x_1559_;
}
v___jp_1560_:
{
lean_object* v___x_1565_; uint8_t v___x_1566_; 
v___x_1565_ = lean_array_get_size(v___y_1563_);
v___x_1566_ = lean_nat_dec_le(v___y_1562_, v___x_1565_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
lean_dec(v___y_1562_);
v___x_1567_ = l_ByteArray_empty;
v___x_1568_ = lean_array_push(v___y_1563_, v___x_1567_);
v___x_1569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
lean_ctor_set(v___x_1569_, 1, v___y_1561_);
v___x_1570_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_1551_, v___x_1569_, v___y_1564_);
return v___x_1570_;
}
else
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1561_);
lean_dec_ref(v_config_1551_);
v___x_1571_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1572_ = l_Nat_reprFast(v___y_1562_);
v___x_1573_ = lean_string_append(v___x_1571_, v___x_1572_);
lean_dec_ref(v___x_1572_);
v___x_1574_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1575_ = lean_string_append(v___x_1573_, v___x_1574_);
v___x_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
v___x_1577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___y_1564_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
return v___x_1577_;
}
}
v_resetjp_1582_:
{
lean_object* v___x_1585_; uint8_t v___x_1586_; 
v___x_1585_ = lean_byte_array_size(v_array_1578_);
v___x_1586_ = lean_nat_dec_lt(v_idx_1579_, v___x_1585_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1588_; 
lean_dec_ref(v_config_1551_);
if (v_isShared_1584_ == 0)
{
v___x_1588_ = v___x_1583_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_fst_1580_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_snd_1581_);
v___x_1588_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v___x_1589_; 
v___x_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___y_1553_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
return v___x_1589_;
}
}
else
{
uint8_t v___x_1687_; uint8_t v___x_1737_; 
v___x_1687_ = lean_byte_array_fget(v_array_1578_, v_idx_1579_);
v___x_1737_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1687_);
if (v___x_1737_ == 0)
{
uint8_t v___x_1738_; uint8_t v___x_1739_; 
v___x_1738_ = 47;
v___x_1739_ = lean_uint8_dec_eq(v___x_1687_, v___x_1738_);
if (v___x_1739_ == 0)
{
uint8_t v___x_1740_; uint8_t v___x_1741_; 
v___x_1740_ = 48;
v___x_1741_ = lean_uint8_dec_le(v___x_1740_, v___x_1687_);
if (v___x_1741_ == 0)
{
goto v___jp_1732_;
}
else
{
uint8_t v___x_1742_; uint8_t v___x_1743_; 
v___x_1742_ = 57;
v___x_1743_ = lean_uint8_dec_le(v___x_1687_, v___x_1742_);
if (v___x_1743_ == 0)
{
goto v___jp_1732_;
}
else
{
goto v___jp_1591_;
}
}
}
else
{
goto v___jp_1591_;
}
}
else
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
lean_del_object(v___x_1583_);
lean_dec_ref(v_config_1551_);
v___x_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1744_, 0, v_fst_1580_);
lean_ctor_set(v___x_1744_, 1, v_snd_1581_);
v___x_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___y_1553_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
return v___x_1745_;
}
v___jp_1591_:
{
lean_object* v_maxPathSegments_1592_; lean_object* v_maxTotalPathLength_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; 
v_maxPathSegments_1592_ = lean_ctor_get(v_config_1551_, 6);
v_maxTotalPathLength_1593_ = lean_ctor_get(v_config_1551_, 7);
v___x_1594_ = lean_array_get_size(v_fst_1580_);
v___x_1595_ = lean_nat_dec_le(v_maxPathSegments_1592_, v___x_1594_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; 
v___x_1596_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1551_, v___y_1553_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_pos_1597_; lean_object* v_res_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1670_; 
v_pos_1597_ = lean_ctor_get(v___x_1596_, 0);
v_res_1598_ = lean_ctor_get(v___x_1596_, 1);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1600_ = v___x_1596_;
v_isShared_1601_ = v_isSharedCheck_1670_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_res_1598_);
lean_inc(v_pos_1597_);
lean_dec(v___x_1596_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1670_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_inc(v_res_1598_);
v___x_1602_ = l_ByteSlice_toByteArray(v_res_1598_);
v___x_1603_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_1602_);
if (lean_obj_tag(v___x_1603_) == 1)
{
lean_object* v_val_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1665_; 
v_val_1604_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1606_ = v___x_1603_;
v_isShared_1607_ = v_isSharedCheck_1665_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_val_1604_);
lean_dec(v___x_1603_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1665_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1608_ = l_ByteSlice_size(v_res_1598_);
lean_dec(v_res_1598_);
v___x_1609_ = lean_nat_add(v_snd_1581_, v___x_1608_);
lean_dec(v___x_1608_);
lean_dec(v_snd_1581_);
v___x_1610_ = lean_nat_dec_lt(v_maxTotalPathLength_1593_, v___x_1609_);
if (v___x_1610_ == 0)
{
lean_object* v_array_1611_; lean_object* v_idx_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
v_array_1611_ = lean_ctor_get(v_pos_1597_, 0);
v_idx_1612_ = lean_ctor_get(v_pos_1597_, 1);
v___x_1613_ = lean_array_push(v_fst_1580_, v_val_1604_);
v___x_1614_ = lean_byte_array_size(v_array_1611_);
v___x_1615_ = lean_nat_dec_lt(v_idx_1612_, v___x_1614_);
if (v___x_1615_ == 0)
{
lean_del_object(v___x_1606_);
lean_del_object(v___x_1600_);
lean_del_object(v___x_1583_);
lean_dec_ref(v_config_1551_);
v___y_1555_ = v_pos_1597_;
v___y_1556_ = v___x_1613_;
v___y_1557_ = v___x_1609_;
goto v___jp_1554_;
}
else
{
uint8_t v___x_1616_; uint8_t v___x_1617_; uint8_t v___x_1618_; 
v___x_1616_ = lean_byte_array_fget(v_array_1611_, v_idx_1612_);
v___x_1617_ = 47;
v___x_1618_ = lean_uint8_dec_eq(v___x_1616_, v___x_1617_);
if (v___x_1618_ == 0)
{
lean_del_object(v___x_1606_);
lean_del_object(v___x_1600_);
lean_del_object(v___x_1583_);
lean_dec_ref(v_config_1551_);
v___y_1555_ = v_pos_1597_;
v___y_1556_ = v___x_1613_;
v___y_1557_ = v___x_1609_;
goto v___jp_1554_;
}
else
{
lean_object* v___x_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; 
v___x_1619_ = lean_unsigned_to_nat(1u);
v___x_1620_ = lean_nat_add(v___x_1609_, v___x_1619_);
lean_dec(v___x_1609_);
v___x_1621_ = lean_nat_dec_lt(v_maxTotalPathLength_1593_, v___x_1620_);
if (v___x_1621_ == 0)
{
lean_del_object(v___x_1606_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1622_; lean_object* v___x_1624_; 
lean_dec(v___x_1620_);
lean_dec_ref(v___x_1613_);
lean_del_object(v___x_1583_);
lean_dec_ref(v_config_1551_);
v___x_1622_ = lean_box(0);
if (v_isShared_1601_ == 0)
{
lean_ctor_set_tag(v___x_1600_, 1);
lean_ctor_set(v___x_1600_, 1, v___x_1622_);
v___x_1624_ = v___x_1600_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_pos_1597_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v___x_1622_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
else
{
lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1640_; 
lean_inc(v_idx_1612_);
lean_inc_ref(v_array_1611_);
lean_del_object(v___x_1600_);
v_isSharedCheck_1640_ = !lean_is_exclusive(v_pos_1597_);
if (v_isSharedCheck_1640_ == 0)
{
lean_object* v_unused_1641_; lean_object* v_unused_1642_; 
v_unused_1641_ = lean_ctor_get(v_pos_1597_, 1);
lean_dec(v_unused_1641_);
v_unused_1642_ = lean_ctor_get(v_pos_1597_, 0);
lean_dec(v_unused_1642_);
v___x_1627_ = v_pos_1597_;
v_isShared_1628_ = v_isSharedCheck_1640_;
goto v_resetjp_1626_;
}
else
{
lean_dec(v_pos_1597_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1640_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1629_ = lean_nat_add(v_idx_1612_, v___x_1619_);
lean_dec(v_idx_1612_);
lean_inc(v___x_1629_);
lean_inc_ref(v_array_1611_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 1, v___x_1629_);
v___x_1631_ = v___x_1627_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_array_1611_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
uint8_t v___x_1632_; 
v___x_1632_ = lean_nat_dec_lt(v___x_1629_, v___x_1614_);
if (v___x_1632_ == 0)
{
lean_dec(v___x_1629_);
lean_dec_ref(v_array_1611_);
lean_del_object(v___x_1583_);
lean_inc(v_maxPathSegments_1592_);
v___y_1561_ = v___x_1620_;
v___y_1562_ = v_maxPathSegments_1592_;
v___y_1563_ = v___x_1613_;
v___y_1564_ = v___x_1631_;
goto v___jp_1560_;
}
else
{
uint8_t v___x_1633_; uint8_t v___x_1634_; 
v___x_1633_ = lean_byte_array_fget(v_array_1611_, v___x_1629_);
lean_dec(v___x_1629_);
lean_dec_ref(v_array_1611_);
v___x_1634_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1633_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1636_; 
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 1, v___x_1620_);
lean_ctor_set(v___x_1583_, 0, v___x_1613_);
v___x_1636_ = v___x_1583_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1613_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v___x_1620_);
v___x_1636_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1637_; 
v___x_1637_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_1551_, v___x_1636_, v___x_1631_);
return v___x_1637_;
}
}
else
{
lean_del_object(v___x_1583_);
lean_inc(v_maxPathSegments_1592_);
v___y_1561_ = v___x_1620_;
v___y_1562_ = v_maxPathSegments_1592_;
v___y_1563_ = v___x_1613_;
v___y_1564_ = v___x_1631_;
goto v___jp_1560_;
}
}
}
}
}
}
else
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1649_; 
lean_inc(v_maxTotalPathLength_1593_);
lean_dec(v___x_1620_);
lean_dec_ref(v___x_1613_);
lean_del_object(v___x_1583_);
lean_dec_ref(v_config_1551_);
v___x_1643_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1644_ = l_Nat_reprFast(v_maxTotalPathLength_1593_);
v___x_1645_ = lean_string_append(v___x_1643_, v___x_1644_);
lean_dec_ref(v___x_1644_);
v___x_1646_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1647_ = lean_string_append(v___x_1645_, v___x_1646_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v___x_1647_);
v___x_1649_ = v___x_1606_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
lean_object* v___x_1651_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set_tag(v___x_1600_, 1);
lean_ctor_set(v___x_1600_, 1, v___x_1649_);
v___x_1651_ = v___x_1600_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_pos_1597_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v___x_1649_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
}
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1660_; 
lean_inc(v_maxTotalPathLength_1593_);
lean_dec(v___x_1609_);
lean_dec(v_val_1604_);
lean_del_object(v___x_1583_);
lean_dec(v_fst_1580_);
lean_dec_ref(v_config_1551_);
v___x_1654_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1655_ = l_Nat_reprFast(v_maxTotalPathLength_1593_);
v___x_1656_ = lean_string_append(v___x_1654_, v___x_1655_);
lean_dec_ref(v___x_1655_);
v___x_1657_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1658_ = lean_string_append(v___x_1656_, v___x_1657_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v___x_1658_);
v___x_1660_ = v___x_1606_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1658_);
v___x_1660_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
lean_object* v___x_1662_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set_tag(v___x_1600_, 1);
lean_ctor_set(v___x_1600_, 1, v___x_1660_);
v___x_1662_ = v___x_1600_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_pos_1597_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v___x_1660_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
}
else
{
lean_object* v___x_1666_; lean_object* v___x_1668_; 
lean_dec(v___x_1603_);
lean_dec(v_res_1598_);
lean_del_object(v___x_1583_);
lean_dec(v_snd_1581_);
lean_dec(v_fst_1580_);
lean_dec_ref(v_config_1551_);
v___x_1666_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5));
if (v_isShared_1601_ == 0)
{
lean_ctor_set_tag(v___x_1600_, 1);
lean_ctor_set(v___x_1600_, 1, v___x_1666_);
v___x_1668_ = v___x_1600_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_pos_1597_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
else
{
lean_object* v_pos_1671_; lean_object* v_err_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_del_object(v___x_1583_);
lean_dec(v_snd_1581_);
lean_dec(v_fst_1580_);
lean_dec_ref(v_config_1551_);
v_pos_1671_ = lean_ctor_get(v___x_1596_, 0);
v_err_1672_ = lean_ctor_get(v___x_1596_, 1);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1596_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_err_1672_);
lean_inc(v_pos_1671_);
lean_dec(v___x_1596_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_pos_1671_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v_err_1672_);
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
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
lean_inc(v_maxPathSegments_1592_);
lean_del_object(v___x_1583_);
lean_dec(v_snd_1581_);
lean_dec(v_fst_1580_);
lean_dec_ref(v_config_1551_);
v___x_1680_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1681_ = l_Nat_reprFast(v_maxPathSegments_1592_);
v___x_1682_ = lean_string_append(v___x_1680_, v___x_1681_);
lean_dec_ref(v___x_1681_);
v___x_1683_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1684_ = lean_string_append(v___x_1682_, v___x_1683_);
v___x_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
v___x_1686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___y_1553_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
return v___x_1686_;
}
}
v___jp_1688_:
{
uint8_t v___x_1689_; uint8_t v___x_1690_; 
v___x_1689_ = 45;
v___x_1690_ = lean_uint8_dec_eq(v___x_1687_, v___x_1689_);
if (v___x_1690_ == 0)
{
uint8_t v___x_1691_; uint8_t v___x_1692_; 
v___x_1691_ = 46;
v___x_1692_ = lean_uint8_dec_eq(v___x_1687_, v___x_1691_);
if (v___x_1692_ == 0)
{
uint8_t v___x_1693_; uint8_t v___x_1694_; 
v___x_1693_ = 95;
v___x_1694_ = lean_uint8_dec_eq(v___x_1687_, v___x_1693_);
if (v___x_1694_ == 0)
{
uint8_t v___x_1695_; uint8_t v___x_1696_; 
v___x_1695_ = 126;
v___x_1696_ = lean_uint8_dec_eq(v___x_1687_, v___x_1695_);
if (v___x_1696_ == 0)
{
uint8_t v___x_1697_; uint8_t v___x_1698_; 
v___x_1697_ = 33;
v___x_1698_ = lean_uint8_dec_eq(v___x_1687_, v___x_1697_);
if (v___x_1698_ == 0)
{
uint8_t v___x_1699_; uint8_t v___x_1700_; 
v___x_1699_ = 36;
v___x_1700_ = lean_uint8_dec_eq(v___x_1687_, v___x_1699_);
if (v___x_1700_ == 0)
{
uint8_t v___x_1701_; uint8_t v___x_1702_; 
v___x_1701_ = 38;
v___x_1702_ = lean_uint8_dec_eq(v___x_1687_, v___x_1701_);
if (v___x_1702_ == 0)
{
uint8_t v___x_1703_; uint8_t v___x_1704_; 
v___x_1703_ = 39;
v___x_1704_ = lean_uint8_dec_eq(v___x_1687_, v___x_1703_);
if (v___x_1704_ == 0)
{
uint8_t v___x_1705_; uint8_t v___x_1706_; 
v___x_1705_ = 40;
v___x_1706_ = lean_uint8_dec_eq(v___x_1687_, v___x_1705_);
if (v___x_1706_ == 0)
{
uint8_t v___x_1707_; uint8_t v___x_1708_; 
v___x_1707_ = 41;
v___x_1708_ = lean_uint8_dec_eq(v___x_1687_, v___x_1707_);
if (v___x_1708_ == 0)
{
uint8_t v___x_1709_; uint8_t v___x_1710_; 
v___x_1709_ = 42;
v___x_1710_ = lean_uint8_dec_eq(v___x_1687_, v___x_1709_);
if (v___x_1710_ == 0)
{
uint8_t v___x_1711_; uint8_t v___x_1712_; 
v___x_1711_ = 43;
v___x_1712_ = lean_uint8_dec_eq(v___x_1687_, v___x_1711_);
if (v___x_1712_ == 0)
{
uint8_t v___x_1713_; uint8_t v___x_1714_; 
v___x_1713_ = 44;
v___x_1714_ = lean_uint8_dec_eq(v___x_1687_, v___x_1713_);
if (v___x_1714_ == 0)
{
uint8_t v___x_1715_; uint8_t v___x_1716_; 
v___x_1715_ = 59;
v___x_1716_ = lean_uint8_dec_eq(v___x_1687_, v___x_1715_);
if (v___x_1716_ == 0)
{
uint8_t v___x_1717_; uint8_t v___x_1718_; 
v___x_1717_ = 61;
v___x_1718_ = lean_uint8_dec_eq(v___x_1687_, v___x_1717_);
if (v___x_1718_ == 0)
{
uint8_t v___x_1719_; uint8_t v___x_1720_; 
v___x_1719_ = 58;
v___x_1720_ = lean_uint8_dec_eq(v___x_1687_, v___x_1719_);
if (v___x_1720_ == 0)
{
uint8_t v___x_1721_; uint8_t v___x_1722_; 
v___x_1721_ = 64;
v___x_1722_ = lean_uint8_dec_eq(v___x_1687_, v___x_1721_);
if (v___x_1722_ == 0)
{
uint8_t v___x_1723_; uint8_t v___x_1724_; 
v___x_1723_ = 37;
v___x_1724_ = lean_uint8_dec_eq(v___x_1687_, v___x_1723_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
lean_del_object(v___x_1583_);
lean_dec_ref(v_config_1551_);
v___x_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1725_, 0, v_fst_1580_);
lean_ctor_set(v___x_1725_, 1, v_snd_1581_);
v___x_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___y_1553_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
return v___x_1726_;
}
else
{
goto v___jp_1591_;
}
}
else
{
goto v___jp_1591_;
}
}
else
{
goto v___jp_1591_;
}
}
else
{
goto v___jp_1591_;
}
}
else
{
goto v___jp_1591_;
}
}
else
{
goto v___jp_1591_;
}
}
else
{
goto v___jp_1591_;
}
}
else
{
goto v___jp_1591_;
}
}
else
{
goto v___jp_1591_;
}
}
else
{
goto v___jp_1591_;
}
}
else
{
goto v___jp_1591_;
}
}
else
{
goto v___jp_1591_;
}
}
else
{
goto v___jp_1591_;
}
}
else
{
goto v___jp_1591_;
}
}
else
{
goto v___jp_1591_;
}
}
else
{
goto v___jp_1591_;
}
}
else
{
goto v___jp_1591_;
}
}
else
{
goto v___jp_1591_;
}
}
v___jp_1727_:
{
uint8_t v___x_1728_; uint8_t v___x_1729_; 
v___x_1728_ = 65;
v___x_1729_ = lean_uint8_dec_le(v___x_1728_, v___x_1687_);
if (v___x_1729_ == 0)
{
goto v___jp_1688_;
}
else
{
uint8_t v___x_1730_; uint8_t v___x_1731_; 
v___x_1730_ = 90;
v___x_1731_ = lean_uint8_dec_le(v___x_1687_, v___x_1730_);
if (v___x_1731_ == 0)
{
goto v___jp_1688_;
}
else
{
goto v___jp_1591_;
}
}
}
v___jp_1732_:
{
uint8_t v___x_1733_; uint8_t v___x_1734_; 
v___x_1733_ = 97;
v___x_1734_ = lean_uint8_dec_le(v___x_1733_, v___x_1687_);
if (v___x_1734_ == 0)
{
goto v___jp_1727_;
}
else
{
uint8_t v___x_1735_; uint8_t v___x_1736_; 
v___x_1735_ = 122;
v___x_1736_ = lean_uint8_dec_le(v___x_1687_, v___x_1735_);
if (v___x_1736_ == 0)
{
goto v___jp_1727_;
}
else
{
goto v___jp_1591_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath(lean_object* v_config_1758_, uint8_t v_forceAbsolute_1759_, uint8_t v_allowEmpty_1760_, lean_object* v_a_1761_){
_start:
{
lean_object* v___y_1763_; lean_object* v___y_1767_; lean_object* v_array_1770_; lean_object* v_idx_1771_; uint8_t v_isAbsolute_1772_; lean_object* v___x_1773_; lean_object* v_segments_1774_; uint8_t v_isAbsolute_1776_; lean_object* v_totalLength_1777_; lean_object* v___y_1778_; lean_object* v_pos_1802_; lean_object* v_array_1803_; lean_object* v_idx_1804_; lean_object* v___y_1813_; uint8_t v___y_1817_; lean_object* v_pos_1818_; uint8_t v_res_1819_; uint8_t v___y_1821_; lean_object* v_pos_1822_; uint8_t v_res_1823_; lean_object* v___y_1831_; uint8_t v___y_1832_; uint8_t v___y_1833_; uint8_t v___y_1842_; lean_object* v_pos_1843_; uint8_t v_res_1844_; lean_object* v_pos_1846_; lean_object* v_array_1847_; lean_object* v_idx_1848_; uint8_t v_res_1849_; lean_object* v___x_1853_; uint8_t v___x_1854_; 
v_array_1770_ = lean_ctor_get(v_a_1761_, 0);
lean_inc_ref(v_array_1770_);
v_idx_1771_ = lean_ctor_get(v_a_1761_, 1);
lean_inc(v_idx_1771_);
v_isAbsolute_1772_ = 0;
v___x_1773_ = lean_unsigned_to_nat(0u);
v_segments_1774_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__4));
v___x_1853_ = lean_byte_array_size(v_array_1770_);
v___x_1854_ = lean_nat_dec_lt(v_idx_1771_, v___x_1853_);
if (v___x_1854_ == 0)
{
v_pos_1846_ = v_a_1761_;
v_array_1847_ = v_array_1770_;
v_idx_1848_ = v_idx_1771_;
v_res_1849_ = v_isAbsolute_1772_;
goto v___jp_1845_;
}
else
{
uint8_t v___x_1855_; uint8_t v___x_1905_; uint8_t v___x_1906_; 
v___x_1855_ = lean_byte_array_fget(v_array_1770_, v_idx_1771_);
v___x_1905_ = 48;
v___x_1906_ = lean_uint8_dec_le(v___x_1905_, v___x_1855_);
if (v___x_1906_ == 0)
{
goto v___jp_1900_;
}
else
{
uint8_t v___x_1907_; uint8_t v___x_1908_; 
v___x_1907_ = 57;
v___x_1908_ = lean_uint8_dec_le(v___x_1855_, v___x_1907_);
if (v___x_1908_ == 0)
{
goto v___jp_1900_;
}
else
{
v_pos_1846_ = v_a_1761_;
v_array_1847_ = v_array_1770_;
v_idx_1848_ = v_idx_1771_;
v_res_1849_ = v___x_1908_;
goto v___jp_1845_;
}
}
v___jp_1856_:
{
uint8_t v___x_1857_; uint8_t v___x_1858_; 
v___x_1857_ = 45;
v___x_1858_ = lean_uint8_dec_eq(v___x_1855_, v___x_1857_);
if (v___x_1858_ == 0)
{
uint8_t v___x_1859_; uint8_t v___x_1860_; 
v___x_1859_ = 46;
v___x_1860_ = lean_uint8_dec_eq(v___x_1855_, v___x_1859_);
if (v___x_1860_ == 0)
{
uint8_t v___x_1861_; uint8_t v___x_1862_; 
v___x_1861_ = 95;
v___x_1862_ = lean_uint8_dec_eq(v___x_1855_, v___x_1861_);
if (v___x_1862_ == 0)
{
uint8_t v___x_1863_; uint8_t v___x_1864_; 
v___x_1863_ = 126;
v___x_1864_ = lean_uint8_dec_eq(v___x_1855_, v___x_1863_);
if (v___x_1864_ == 0)
{
uint8_t v___x_1865_; uint8_t v___x_1866_; 
v___x_1865_ = 33;
v___x_1866_ = lean_uint8_dec_eq(v___x_1855_, v___x_1865_);
if (v___x_1866_ == 0)
{
uint8_t v___x_1867_; uint8_t v___x_1868_; 
v___x_1867_ = 36;
v___x_1868_ = lean_uint8_dec_eq(v___x_1855_, v___x_1867_);
if (v___x_1868_ == 0)
{
uint8_t v___x_1869_; uint8_t v___x_1870_; 
v___x_1869_ = 38;
v___x_1870_ = lean_uint8_dec_eq(v___x_1855_, v___x_1869_);
if (v___x_1870_ == 0)
{
uint8_t v___x_1871_; uint8_t v___x_1872_; 
v___x_1871_ = 39;
v___x_1872_ = lean_uint8_dec_eq(v___x_1855_, v___x_1871_);
if (v___x_1872_ == 0)
{
uint8_t v___x_1873_; uint8_t v___x_1874_; 
v___x_1873_ = 40;
v___x_1874_ = lean_uint8_dec_eq(v___x_1855_, v___x_1873_);
if (v___x_1874_ == 0)
{
uint8_t v___x_1875_; uint8_t v___x_1876_; 
v___x_1875_ = 41;
v___x_1876_ = lean_uint8_dec_eq(v___x_1855_, v___x_1875_);
if (v___x_1876_ == 0)
{
uint8_t v___x_1877_; uint8_t v___x_1878_; 
v___x_1877_ = 42;
v___x_1878_ = lean_uint8_dec_eq(v___x_1855_, v___x_1877_);
if (v___x_1878_ == 0)
{
uint8_t v___x_1879_; uint8_t v___x_1880_; 
v___x_1879_ = 43;
v___x_1880_ = lean_uint8_dec_eq(v___x_1855_, v___x_1879_);
if (v___x_1880_ == 0)
{
uint8_t v___x_1881_; uint8_t v___x_1882_; 
v___x_1881_ = 44;
v___x_1882_ = lean_uint8_dec_eq(v___x_1855_, v___x_1881_);
if (v___x_1882_ == 0)
{
uint8_t v___x_1883_; uint8_t v___x_1884_; 
v___x_1883_ = 59;
v___x_1884_ = lean_uint8_dec_eq(v___x_1855_, v___x_1883_);
if (v___x_1884_ == 0)
{
uint8_t v___x_1885_; uint8_t v___x_1886_; 
v___x_1885_ = 61;
v___x_1886_ = lean_uint8_dec_eq(v___x_1855_, v___x_1885_);
if (v___x_1886_ == 0)
{
uint8_t v___x_1887_; uint8_t v___x_1888_; 
v___x_1887_ = 58;
v___x_1888_ = lean_uint8_dec_eq(v___x_1855_, v___x_1887_);
if (v___x_1888_ == 0)
{
uint8_t v___x_1889_; uint8_t v___x_1890_; 
v___x_1889_ = 64;
v___x_1890_ = lean_uint8_dec_eq(v___x_1855_, v___x_1889_);
if (v___x_1890_ == 0)
{
uint8_t v___x_1891_; uint8_t v___x_1892_; 
v___x_1891_ = 37;
v___x_1892_ = lean_uint8_dec_eq(v___x_1855_, v___x_1891_);
if (v___x_1892_ == 0)
{
uint8_t v___x_1893_; uint8_t v___x_1894_; 
v___x_1893_ = 47;
v___x_1894_ = lean_uint8_dec_eq(v___x_1855_, v___x_1893_);
if (v___x_1894_ == 0)
{
v_pos_1846_ = v_a_1761_;
v_array_1847_ = v_array_1770_;
v_idx_1848_ = v_idx_1771_;
v_res_1849_ = v_isAbsolute_1772_;
goto v___jp_1845_;
}
else
{
v_pos_1846_ = v_a_1761_;
v_array_1847_ = v_array_1770_;
v_idx_1848_ = v_idx_1771_;
v_res_1849_ = v___x_1894_;
goto v___jp_1845_;
}
}
else
{
v_pos_1846_ = v_a_1761_;
v_array_1847_ = v_array_1770_;
v_idx_1848_ = v_idx_1771_;
v_res_1849_ = v___x_1892_;
goto v___jp_1845_;
}
}
else
{
v_pos_1846_ = v_a_1761_;
v_array_1847_ = v_array_1770_;
v_idx_1848_ = v_idx_1771_;
v_res_1849_ = v___x_1890_;
goto v___jp_1845_;
}
}
else
{
v_pos_1846_ = v_a_1761_;
v_array_1847_ = v_array_1770_;
v_idx_1848_ = v_idx_1771_;
v_res_1849_ = v___x_1888_;
goto v___jp_1845_;
}
}
else
{
v_pos_1846_ = v_a_1761_;
v_array_1847_ = v_array_1770_;
v_idx_1848_ = v_idx_1771_;
v_res_1849_ = v___x_1886_;
goto v___jp_1845_;
}
}
else
{
v_pos_1846_ = v_a_1761_;
v_array_1847_ = v_array_1770_;
v_idx_1848_ = v_idx_1771_;
v_res_1849_ = v___x_1884_;
goto v___jp_1845_;
}
}
else
{
v_pos_1846_ = v_a_1761_;
v_array_1847_ = v_array_1770_;
v_idx_1848_ = v_idx_1771_;
v_res_1849_ = v___x_1882_;
goto v___jp_1845_;
}
}
else
{
v_pos_1846_ = v_a_1761_;
v_array_1847_ = v_array_1770_;
v_idx_1848_ = v_idx_1771_;
v_res_1849_ = v___x_1880_;
goto v___jp_1845_;
}
}
else
{
v_pos_1846_ = v_a_1761_;
v_array_1847_ = v_array_1770_;
v_idx_1848_ = v_idx_1771_;
v_res_1849_ = v___x_1878_;
goto v___jp_1845_;
}
}
else
{
v_pos_1846_ = v_a_1761_;
v_array_1847_ = v_array_1770_;
v_idx_1848_ = v_idx_1771_;
v_res_1849_ = v___x_1876_;
goto v___jp_1845_;
}
}
else
{
v_pos_1846_ = v_a_1761_;
v_array_1847_ = v_array_1770_;
v_idx_1848_ = v_idx_1771_;
v_res_1849_ = v___x_1874_;
goto v___jp_1845_;
}
}
else
{
v_pos_1846_ = v_a_1761_;
v_array_1847_ = v_array_1770_;
v_idx_1848_ = v_idx_1771_;
v_res_1849_ = v___x_1872_;
goto v___jp_1845_;
}
}
else
{
v_pos_1846_ = v_a_1761_;
v_array_1847_ = v_array_1770_;
v_idx_1848_ = v_idx_1771_;
v_res_1849_ = v___x_1870_;
goto v___jp_1845_;
}
}
else
{
v_pos_1846_ = v_a_1761_;
v_array_1847_ = v_array_1770_;
v_idx_1848_ = v_idx_1771_;
v_res_1849_ = v___x_1868_;
goto v___jp_1845_;
}
}
else
{
v_pos_1846_ = v_a_1761_;
v_array_1847_ = v_array_1770_;
v_idx_1848_ = v_idx_1771_;
v_res_1849_ = v___x_1866_;
goto v___jp_1845_;
}
}
else
{
v_pos_1846_ = v_a_1761_;
v_array_1847_ = v_array_1770_;
v_idx_1848_ = v_idx_1771_;
v_res_1849_ = v___x_1864_;
goto v___jp_1845_;
}
}
else
{
v_pos_1846_ = v_a_1761_;
v_array_1847_ = v_array_1770_;
v_idx_1848_ = v_idx_1771_;
v_res_1849_ = v___x_1862_;
goto v___jp_1845_;
}
}
else
{
v_pos_1846_ = v_a_1761_;
v_array_1847_ = v_array_1770_;
v_idx_1848_ = v_idx_1771_;
v_res_1849_ = v___x_1860_;
goto v___jp_1845_;
}
}
else
{
v_pos_1846_ = v_a_1761_;
v_array_1847_ = v_array_1770_;
v_idx_1848_ = v_idx_1771_;
v_res_1849_ = v___x_1858_;
goto v___jp_1845_;
}
}
v___jp_1895_:
{
uint8_t v___x_1896_; uint8_t v___x_1897_; 
v___x_1896_ = 65;
v___x_1897_ = lean_uint8_dec_le(v___x_1896_, v___x_1855_);
if (v___x_1897_ == 0)
{
goto v___jp_1856_;
}
else
{
uint8_t v___x_1898_; uint8_t v___x_1899_; 
v___x_1898_ = 90;
v___x_1899_ = lean_uint8_dec_le(v___x_1855_, v___x_1898_);
if (v___x_1899_ == 0)
{
goto v___jp_1856_;
}
else
{
v_pos_1846_ = v_a_1761_;
v_array_1847_ = v_array_1770_;
v_idx_1848_ = v_idx_1771_;
v_res_1849_ = v___x_1899_;
goto v___jp_1845_;
}
}
}
v___jp_1900_:
{
uint8_t v___x_1901_; uint8_t v___x_1902_; 
v___x_1901_ = 97;
v___x_1902_ = lean_uint8_dec_le(v___x_1901_, v___x_1855_);
if (v___x_1902_ == 0)
{
goto v___jp_1895_;
}
else
{
uint8_t v___x_1903_; uint8_t v___x_1904_; 
v___x_1903_ = 122;
v___x_1904_ = lean_uint8_dec_le(v___x_1855_, v___x_1903_);
if (v___x_1904_ == 0)
{
goto v___jp_1895_;
}
else
{
v_pos_1846_ = v_a_1761_;
v_array_1847_ = v_array_1770_;
v_idx_1848_ = v_idx_1771_;
v_res_1849_ = v___x_1904_;
goto v___jp_1845_;
}
}
}
}
v___jp_1762_:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1764_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__1));
v___x_1765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___y_1763_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
return v___x_1765_;
}
v___jp_1766_:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__3));
v___x_1769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___y_1767_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
return v___x_1769_;
}
v___jp_1775_:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1779_, 0, v_segments_1774_);
lean_ctor_set(v___x_1779_, 1, v_totalLength_1777_);
v___x_1780_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(v_config_1758_, v___x_1779_, v___y_1778_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_res_1781_; lean_object* v_pos_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1791_; 
v_res_1781_ = lean_ctor_get(v___x_1780_, 1);
v_pos_1782_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1784_ = v___x_1780_;
v_isShared_1785_ = v_isSharedCheck_1791_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_res_1781_);
lean_inc(v_pos_1782_);
lean_dec(v___x_1780_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1791_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v_fst_1786_; lean_object* v___x_1787_; lean_object* v___x_1789_; 
v_fst_1786_ = lean_ctor_get(v_res_1781_, 0);
lean_inc(v_fst_1786_);
lean_dec(v_res_1781_);
v___x_1787_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1787_, 0, v_fst_1786_);
lean_ctor_set_uint8(v___x_1787_, sizeof(void*)*1, v_isAbsolute_1776_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 1, v___x_1787_);
v___x_1789_ = v___x_1784_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_pos_1782_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
else
{
lean_object* v_pos_1792_; lean_object* v_err_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
v_pos_1792_ = lean_ctor_get(v___x_1780_, 0);
v_err_1793_ = lean_ctor_get(v___x_1780_, 1);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1780_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_err_1793_);
lean_inc(v_pos_1792_);
lean_dec(v___x_1780_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_pos_1792_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_err_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
v___jp_1801_:
{
lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1805_ = lean_byte_array_size(v_array_1803_);
v___x_1806_ = lean_nat_dec_lt(v_idx_1804_, v___x_1805_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
lean_dec(v_idx_1804_);
lean_dec_ref(v_array_1803_);
lean_dec_ref(v_config_1758_);
v___x_1807_ = lean_box(0);
v___x_1808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1808_, 0, v_pos_1802_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
return v___x_1808_;
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
lean_dec_ref(v_pos_1802_);
v___x_1809_ = lean_unsigned_to_nat(1u);
v___x_1810_ = lean_nat_add(v_idx_1804_, v___x_1809_);
lean_dec(v_idx_1804_);
v___x_1811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1811_, 0, v_array_1803_);
lean_ctor_set(v___x_1811_, 1, v___x_1810_);
v_isAbsolute_1776_ = v___x_1806_;
v_totalLength_1777_ = v___x_1809_;
v___y_1778_ = v___x_1811_;
goto v___jp_1775_;
}
}
v___jp_1812_:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__5));
v___x_1815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___y_1813_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
return v___x_1815_;
}
v___jp_1816_:
{
if (v_allowEmpty_1760_ == 0)
{
v___y_1763_ = v_pos_1818_;
goto v___jp_1762_;
}
else
{
if (v_res_1819_ == 0)
{
if (v___y_1817_ == 0)
{
v___y_1813_ = v_pos_1818_;
goto v___jp_1812_;
}
else
{
v___y_1763_ = v_pos_1818_;
goto v___jp_1762_;
}
}
else
{
v___y_1813_ = v_pos_1818_;
goto v___jp_1812_;
}
}
}
v___jp_1820_:
{
if (v_res_1823_ == 0)
{
if (v_forceAbsolute_1759_ == 0)
{
v_isAbsolute_1776_ = v_isAbsolute_1772_;
v_totalLength_1777_ = v___x_1773_;
v___y_1778_ = v_pos_1822_;
goto v___jp_1775_;
}
else
{
lean_object* v_array_1824_; lean_object* v_idx_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; 
lean_dec_ref(v_config_1758_);
v_array_1824_ = lean_ctor_get(v_pos_1822_, 0);
v_idx_1825_ = lean_ctor_get(v_pos_1822_, 1);
v___x_1826_ = lean_byte_array_size(v_array_1824_);
v___x_1827_ = lean_nat_dec_lt(v_idx_1825_, v___x_1826_);
if (v___x_1827_ == 0)
{
v___y_1817_ = v___y_1821_;
v_pos_1818_ = v_pos_1822_;
v_res_1819_ = v_forceAbsolute_1759_;
goto v___jp_1816_;
}
else
{
v___y_1817_ = v___y_1821_;
v_pos_1818_ = v_pos_1822_;
v_res_1819_ = v_res_1823_;
goto v___jp_1816_;
}
}
}
else
{
lean_object* v_array_1828_; lean_object* v_idx_1829_; 
v_array_1828_ = lean_ctor_get(v_pos_1822_, 0);
lean_inc_ref(v_array_1828_);
v_idx_1829_ = lean_ctor_get(v_pos_1822_, 1);
lean_inc(v_idx_1829_);
v_pos_1802_ = v_pos_1822_;
v_array_1803_ = v_array_1828_;
v_idx_1804_ = v_idx_1829_;
goto v___jp_1801_;
}
}
v___jp_1830_:
{
lean_object* v_array_1834_; lean_object* v_idx_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
v_array_1834_ = lean_ctor_get(v___y_1831_, 0);
v_idx_1835_ = lean_ctor_get(v___y_1831_, 1);
v___x_1836_ = lean_byte_array_size(v_array_1834_);
v___x_1837_ = lean_nat_dec_lt(v_idx_1835_, v___x_1836_);
if (v___x_1837_ == 0)
{
v___y_1821_ = v___y_1832_;
v_pos_1822_ = v___y_1831_;
v_res_1823_ = v___y_1833_;
goto v___jp_1820_;
}
else
{
uint8_t v___x_1838_; uint8_t v___x_1839_; uint8_t v___x_1840_; 
v___x_1838_ = lean_byte_array_fget(v_array_1834_, v_idx_1835_);
v___x_1839_ = 47;
v___x_1840_ = lean_uint8_dec_eq(v___x_1838_, v___x_1839_);
if (v___x_1840_ == 0)
{
v___y_1821_ = v___y_1832_;
v_pos_1822_ = v___y_1831_;
v_res_1823_ = v___y_1833_;
goto v___jp_1820_;
}
else
{
lean_inc(v_idx_1835_);
lean_inc_ref(v_array_1834_);
v_pos_1802_ = v___y_1831_;
v_array_1803_ = v_array_1834_;
v_idx_1804_ = v_idx_1835_;
goto v___jp_1801_;
}
}
}
v___jp_1841_:
{
if (v_allowEmpty_1760_ == 0)
{
if (v_res_1844_ == 0)
{
if (v___y_1842_ == 0)
{
lean_dec_ref(v_config_1758_);
v___y_1767_ = v_pos_1843_;
goto v___jp_1766_;
}
else
{
v___y_1831_ = v_pos_1843_;
v___y_1832_ = v___y_1842_;
v___y_1833_ = v_res_1844_;
goto v___jp_1830_;
}
}
else
{
lean_dec_ref(v_config_1758_);
v___y_1767_ = v_pos_1843_;
goto v___jp_1766_;
}
}
else
{
v___y_1831_ = v_pos_1843_;
v___y_1832_ = v___y_1842_;
v___y_1833_ = v_isAbsolute_1772_;
goto v___jp_1830_;
}
}
v___jp_1845_:
{
lean_object* v___x_1850_; uint8_t v___x_1851_; 
v___x_1850_ = lean_byte_array_size(v_array_1847_);
lean_dec_ref(v_array_1847_);
v___x_1851_ = lean_nat_dec_lt(v_idx_1848_, v___x_1850_);
lean_dec(v_idx_1848_);
if (v___x_1851_ == 0)
{
uint8_t v___x_1852_; 
v___x_1852_ = 1;
v___y_1842_ = v_res_1849_;
v_pos_1843_ = v_pos_1846_;
v_res_1844_ = v___x_1852_;
goto v___jp_1841_;
}
else
{
v___y_1842_ = v_res_1849_;
v_pos_1843_ = v_pos_1846_;
v_res_1844_ = v_isAbsolute_1772_;
goto v___jp_1841_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath___boxed(lean_object* v_config_1909_, lean_object* v_forceAbsolute_1910_, lean_object* v_allowEmpty_1911_, lean_object* v_a_1912_){
_start:
{
uint8_t v_forceAbsolute_boxed_1913_; uint8_t v_allowEmpty_boxed_1914_; lean_object* v_res_1915_; 
v_forceAbsolute_boxed_1913_ = lean_unbox(v_forceAbsolute_1910_);
v_allowEmpty_boxed_1914_ = lean_unbox(v_allowEmpty_1911_);
v_res_1915_ = l_Std_Http_URI_Parser_parsePath(v_config_1909_, v_forceAbsolute_boxed_1913_, v_allowEmpty_boxed_1914_, v_a_1912_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0(lean_object* v_config_1916_, lean_object* v_inst_1917_, lean_object* v_a_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(v_config_1916_, v_a_1918_, v___y_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0(lean_object* v_config_1921_, lean_object* v_inst_1922_, lean_object* v_a_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_1921_, v_a_1923_, v___y_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg(){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0));
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg___boxed(lean_object* v___dummy_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg();
return v_res_1929_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1930_; 
v___x_1930_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg();
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(lean_object* v_s_1931_){
_start:
{
lean_object* v___x_1932_; 
v___x_1932_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___boxed(lean_object* v_s_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(v_s_1933_);
lean_dec_ref(v_s_1933_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg(){
_start:
{
lean_object* v___x_1936_; 
v___x_1936_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0));
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg___boxed(lean_object* v___dummy_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg();
return v_res_1938_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1939_; 
v___x_1939_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg();
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(lean_object* v_s_1940_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___boxed(lean_object* v_s_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(v_s_1942_);
lean_dec_ref(v_s_1942_);
return v_res_1943_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(uint8_t v_c_1944_){
_start:
{
uint8_t v___x_1996_; uint8_t v___x_1997_; 
v___x_1996_ = 48;
v___x_1997_ = lean_uint8_dec_le(v___x_1996_, v_c_1944_);
if (v___x_1997_ == 0)
{
goto v___jp_1991_;
}
else
{
uint8_t v___x_1998_; uint8_t v___x_1999_; 
v___x_1998_ = 57;
v___x_1999_ = lean_uint8_dec_le(v_c_1944_, v___x_1998_);
if (v___x_1999_ == 0)
{
goto v___jp_1991_;
}
else
{
return v___x_1999_;
}
}
v___jp_1945_:
{
uint8_t v___x_1946_; uint8_t v___x_1947_; 
v___x_1946_ = 45;
v___x_1947_ = lean_uint8_dec_eq(v_c_1944_, v___x_1946_);
if (v___x_1947_ == 0)
{
uint8_t v___x_1948_; uint8_t v___x_1949_; 
v___x_1948_ = 46;
v___x_1949_ = lean_uint8_dec_eq(v_c_1944_, v___x_1948_);
if (v___x_1949_ == 0)
{
uint8_t v___x_1950_; uint8_t v___x_1951_; 
v___x_1950_ = 95;
v___x_1951_ = lean_uint8_dec_eq(v_c_1944_, v___x_1950_);
if (v___x_1951_ == 0)
{
uint8_t v___x_1952_; uint8_t v___x_1953_; 
v___x_1952_ = 126;
v___x_1953_ = lean_uint8_dec_eq(v_c_1944_, v___x_1952_);
if (v___x_1953_ == 0)
{
uint8_t v___x_1954_; uint8_t v___x_1955_; 
v___x_1954_ = 33;
v___x_1955_ = lean_uint8_dec_eq(v_c_1944_, v___x_1954_);
if (v___x_1955_ == 0)
{
uint8_t v___x_1956_; uint8_t v___x_1957_; 
v___x_1956_ = 36;
v___x_1957_ = lean_uint8_dec_eq(v_c_1944_, v___x_1956_);
if (v___x_1957_ == 0)
{
uint8_t v___x_1958_; uint8_t v___x_1959_; 
v___x_1958_ = 38;
v___x_1959_ = lean_uint8_dec_eq(v_c_1944_, v___x_1958_);
if (v___x_1959_ == 0)
{
uint8_t v___x_1960_; uint8_t v___x_1961_; 
v___x_1960_ = 39;
v___x_1961_ = lean_uint8_dec_eq(v_c_1944_, v___x_1960_);
if (v___x_1961_ == 0)
{
uint8_t v___x_1962_; uint8_t v___x_1963_; 
v___x_1962_ = 40;
v___x_1963_ = lean_uint8_dec_eq(v_c_1944_, v___x_1962_);
if (v___x_1963_ == 0)
{
uint8_t v___x_1964_; uint8_t v___x_1965_; 
v___x_1964_ = 41;
v___x_1965_ = lean_uint8_dec_eq(v_c_1944_, v___x_1964_);
if (v___x_1965_ == 0)
{
uint8_t v___x_1966_; uint8_t v___x_1967_; 
v___x_1966_ = 42;
v___x_1967_ = lean_uint8_dec_eq(v_c_1944_, v___x_1966_);
if (v___x_1967_ == 0)
{
uint8_t v___x_1968_; uint8_t v___x_1969_; 
v___x_1968_ = 43;
v___x_1969_ = lean_uint8_dec_eq(v_c_1944_, v___x_1968_);
if (v___x_1969_ == 0)
{
uint8_t v___x_1970_; uint8_t v___x_1971_; 
v___x_1970_ = 44;
v___x_1971_ = lean_uint8_dec_eq(v_c_1944_, v___x_1970_);
if (v___x_1971_ == 0)
{
uint8_t v___x_1972_; uint8_t v___x_1973_; 
v___x_1972_ = 59;
v___x_1973_ = lean_uint8_dec_eq(v_c_1944_, v___x_1972_);
if (v___x_1973_ == 0)
{
uint8_t v___x_1974_; uint8_t v___x_1975_; 
v___x_1974_ = 61;
v___x_1975_ = lean_uint8_dec_eq(v_c_1944_, v___x_1974_);
if (v___x_1975_ == 0)
{
uint8_t v___x_1976_; uint8_t v___x_1977_; 
v___x_1976_ = 58;
v___x_1977_ = lean_uint8_dec_eq(v_c_1944_, v___x_1976_);
if (v___x_1977_ == 0)
{
uint8_t v___x_1978_; uint8_t v___x_1979_; 
v___x_1978_ = 64;
v___x_1979_ = lean_uint8_dec_eq(v_c_1944_, v___x_1978_);
if (v___x_1979_ == 0)
{
uint8_t v___x_1980_; uint8_t v___x_1981_; 
v___x_1980_ = 47;
v___x_1981_ = lean_uint8_dec_eq(v_c_1944_, v___x_1980_);
if (v___x_1981_ == 0)
{
uint8_t v___x_1982_; uint8_t v___x_1983_; 
v___x_1982_ = 63;
v___x_1983_ = lean_uint8_dec_eq(v_c_1944_, v___x_1982_);
if (v___x_1983_ == 0)
{
uint8_t v___x_1984_; uint8_t v___x_1985_; 
v___x_1984_ = 37;
v___x_1985_ = lean_uint8_dec_eq(v_c_1944_, v___x_1984_);
return v___x_1985_;
}
else
{
return v___x_1983_;
}
}
else
{
return v___x_1981_;
}
}
else
{
return v___x_1979_;
}
}
else
{
return v___x_1977_;
}
}
else
{
return v___x_1975_;
}
}
else
{
return v___x_1973_;
}
}
else
{
return v___x_1971_;
}
}
else
{
return v___x_1969_;
}
}
else
{
return v___x_1967_;
}
}
else
{
return v___x_1965_;
}
}
else
{
return v___x_1963_;
}
}
else
{
return v___x_1961_;
}
}
else
{
return v___x_1959_;
}
}
else
{
return v___x_1957_;
}
}
else
{
return v___x_1955_;
}
}
else
{
return v___x_1953_;
}
}
else
{
return v___x_1951_;
}
}
else
{
return v___x_1949_;
}
}
else
{
return v___x_1947_;
}
}
v___jp_1986_:
{
uint8_t v___x_1987_; uint8_t v___x_1988_; 
v___x_1987_ = 65;
v___x_1988_ = lean_uint8_dec_le(v___x_1987_, v_c_1944_);
if (v___x_1988_ == 0)
{
goto v___jp_1945_;
}
else
{
uint8_t v___x_1989_; uint8_t v___x_1990_; 
v___x_1989_ = 90;
v___x_1990_ = lean_uint8_dec_le(v_c_1944_, v___x_1989_);
if (v___x_1990_ == 0)
{
goto v___jp_1945_;
}
else
{
return v___x_1990_;
}
}
}
v___jp_1991_:
{
uint8_t v___x_1992_; uint8_t v___x_1993_; 
v___x_1992_ = 97;
v___x_1993_ = lean_uint8_dec_le(v___x_1992_, v_c_1944_);
if (v___x_1993_ == 0)
{
goto v___jp_1986_;
}
else
{
uint8_t v___x_1994_; uint8_t v___x_1995_; 
v___x_1994_ = 122;
v___x_1995_ = lean_uint8_dec_le(v_c_1944_, v___x_1994_);
if (v___x_1995_ == 0)
{
goto v___jp_1986_;
}
else
{
return v___x_1995_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0___boxed(lean_object* v_c_2000_){
_start:
{
uint8_t v_c_boxed_2001_; uint8_t v_res_2002_; lean_object* v_r_2003_; 
v_c_boxed_2001_ = lean_unbox(v_c_2000_);
v_res_2002_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(v_c_boxed_2001_);
v_r_2003_ = lean_box(v_res_2002_);
return v_r_2003_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(lean_object* v___x_2004_, lean_object* v___x_2005_, lean_object* v_a_2006_, lean_object* v_b_2007_){
_start:
{
lean_object* v_it_2009_; 
if (lean_obj_tag(v_a_2006_) == 0)
{
lean_object* v_currPos_2013_; lean_object* v_searcher_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2040_; 
v_currPos_2013_ = lean_ctor_get(v_a_2006_, 0);
v_searcher_2014_ = lean_ctor_get(v_a_2006_, 1);
v_isSharedCheck_2040_ = !lean_is_exclusive(v_a_2006_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2016_ = v_a_2006_;
v_isShared_2017_ = v_isSharedCheck_2040_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_searcher_2014_);
lean_inc(v_currPos_2013_);
lean_dec(v_a_2006_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2040_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v_str_2018_; lean_object* v_startInclusive_2019_; lean_object* v_endExclusive_2020_; lean_object* v___x_2021_; uint8_t v_decide_2022_; 
v_str_2018_ = lean_ctor_get(v___x_2004_, 0);
v_startInclusive_2019_ = lean_ctor_get(v___x_2004_, 1);
v_endExclusive_2020_ = lean_ctor_get(v___x_2004_, 2);
v___x_2021_ = lean_nat_sub(v_endExclusive_2020_, v_startInclusive_2019_);
v_decide_2022_ = lean_nat_dec_eq(v_searcher_2014_, v___x_2021_);
lean_dec(v___x_2021_);
if (v_decide_2022_ == 0)
{
uint32_t v___x_2023_; lean_object* v___x_2024_; uint32_t v___x_2025_; uint8_t v___x_2026_; 
v___x_2023_ = 38;
v___x_2024_ = lean_nat_add(v_startInclusive_2019_, v_searcher_2014_);
v___x_2025_ = lean_string_utf8_get_fast(v_str_2018_, v___x_2024_);
v___x_2026_ = lean_uint32_dec_eq(v___x_2025_, v___x_2023_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2030_; 
lean_dec(v_searcher_2014_);
v___x_2027_ = lean_string_utf8_next_fast(v_str_2018_, v___x_2024_);
lean_dec(v___x_2024_);
v___x_2028_ = lean_nat_sub(v___x_2027_, v_startInclusive_2019_);
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 1, v___x_2028_);
v___x_2030_ = v___x_2016_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_currPos_2013_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
v_a_2006_ = v___x_2030_;
goto _start;
}
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v_nextIt_2037_; 
lean_dec(v_currPos_2013_);
v___x_2033_ = lean_string_utf8_next_fast(v_str_2018_, v___x_2024_);
v___x_2034_ = lean_nat_sub(v___x_2033_, v___x_2024_);
lean_dec(v___x_2024_);
v___x_2035_ = lean_nat_add(v_searcher_2014_, v___x_2034_);
lean_dec(v___x_2034_);
lean_dec(v_searcher_2014_);
lean_inc(v___x_2035_);
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 1, v___x_2035_);
lean_ctor_set(v___x_2016_, 0, v___x_2035_);
v_nextIt_2037_ = v___x_2016_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2038_, 1, v___x_2035_);
v_nextIt_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
v_it_2009_ = v_nextIt_2037_;
goto v___jp_2008_;
}
}
}
else
{
lean_object* v___x_2039_; 
lean_del_object(v___x_2016_);
lean_dec(v_searcher_2014_);
lean_dec(v_currPos_2013_);
v___x_2039_ = lean_box(1);
v_it_2009_ = v___x_2039_;
goto v___jp_2008_;
}
}
}
else
{
return v_b_2007_;
}
v___jp_2008_:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = lean_unsigned_to_nat(1u);
v___x_2011_ = lean_nat_add(v_b_2007_, v___x_2010_);
lean_dec(v_b_2007_);
v_a_2006_ = v_it_2009_;
v_b_2007_ = v___x_2011_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg___boxed(lean_object* v___x_2041_, lean_object* v___x_2042_, lean_object* v_a_2043_, lean_object* v_b_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2041_, v___x_2042_, v_a_2043_, v_b_2044_);
lean_dec(v___x_2042_);
lean_dec_ref(v___x_2041_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(lean_object* v___x_2046_, lean_object* v___x_2047_, lean_object* v___x_2048_, lean_object* v_a_2049_, lean_object* v_b_2050_){
_start:
{
lean_object* v_it_2052_; 
if (lean_obj_tag(v_a_2049_) == 0)
{
lean_object* v_currPos_2056_; lean_object* v_searcher_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2083_; 
v_currPos_2056_ = lean_ctor_get(v_a_2049_, 0);
v_searcher_2057_ = lean_ctor_get(v_a_2049_, 1);
v_isSharedCheck_2083_ = !lean_is_exclusive(v_a_2049_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2059_ = v_a_2049_;
v_isShared_2060_ = v_isSharedCheck_2083_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_searcher_2057_);
lean_inc(v_currPos_2056_);
lean_dec(v_a_2049_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2083_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v_str_2061_; lean_object* v_startInclusive_2062_; lean_object* v_endExclusive_2063_; lean_object* v___x_2064_; uint8_t v_decide_2065_; 
v_str_2061_ = lean_ctor_get(v___x_2047_, 0);
v_startInclusive_2062_ = lean_ctor_get(v___x_2047_, 1);
v_endExclusive_2063_ = lean_ctor_get(v___x_2047_, 2);
v___x_2064_ = lean_nat_sub(v_endExclusive_2063_, v_startInclusive_2062_);
v_decide_2065_ = lean_nat_dec_eq(v_searcher_2057_, v___x_2064_);
lean_dec(v___x_2064_);
if (v_decide_2065_ == 0)
{
lean_object* v___x_2066_; uint32_t v___x_2067_; uint32_t v___x_2068_; uint8_t v___x_2069_; 
v___x_2066_ = lean_nat_add(v_startInclusive_2062_, v_searcher_2057_);
v___x_2067_ = lean_string_utf8_get_fast(v_str_2061_, v___x_2066_);
v___x_2068_ = 38;
v___x_2069_ = lean_uint32_dec_eq(v___x_2067_, v___x_2068_);
if (v___x_2069_ == 0)
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2073_; 
lean_dec(v_searcher_2057_);
v___x_2070_ = lean_string_utf8_next_fast(v_str_2061_, v___x_2066_);
lean_dec(v___x_2066_);
v___x_2071_ = lean_nat_sub(v___x_2070_, v_startInclusive_2062_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 1, v___x_2071_);
v___x_2073_ = v___x_2059_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_currPos_2056_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v___x_2071_);
v___x_2073_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
lean_object* v___x_2074_; 
v___x_2074_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2047_, v___x_2048_, v___x_2073_, v_b_2050_);
return v___x_2074_;
}
}
else
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v_nextIt_2080_; 
lean_dec(v_currPos_2056_);
v___x_2076_ = lean_string_utf8_next_fast(v_str_2061_, v___x_2066_);
v___x_2077_ = lean_nat_sub(v___x_2076_, v___x_2066_);
lean_dec(v___x_2066_);
v___x_2078_ = lean_nat_add(v_searcher_2057_, v___x_2077_);
lean_dec(v___x_2077_);
lean_dec(v_searcher_2057_);
lean_inc(v___x_2078_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 1, v___x_2078_);
lean_ctor_set(v___x_2059_, 0, v___x_2078_);
v_nextIt_2080_ = v___x_2059_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2078_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v___x_2078_);
v_nextIt_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
v_it_2052_ = v_nextIt_2080_;
goto v___jp_2051_;
}
}
}
else
{
lean_object* v___x_2082_; 
lean_del_object(v___x_2059_);
lean_dec(v_searcher_2057_);
lean_dec(v_currPos_2056_);
v___x_2082_ = lean_box(1);
v_it_2052_ = v___x_2082_;
goto v___jp_2051_;
}
}
}
else
{
return v_b_2050_;
}
v___jp_2051_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2053_ = lean_unsigned_to_nat(1u);
v___x_2054_ = lean_nat_add(v_b_2050_, v___x_2053_);
lean_dec(v_b_2050_);
v___x_2055_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2047_, v___x_2048_, v_it_2052_, v___x_2054_);
return v___x_2055_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg___boxed(lean_object* v___x_2084_, lean_object* v___x_2085_, lean_object* v___x_2086_, lean_object* v_a_2087_, lean_object* v_b_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2084_, v___x_2085_, v___x_2086_, v_a_2087_, v_b_2088_);
lean_dec(v___x_2086_);
lean_dec_ref(v___x_2085_);
lean_dec_ref(v___x_2084_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(lean_object* v_out_2090_, lean_object* v_a_2091_, lean_object* v_b_2092_){
_start:
{
if (lean_obj_tag(v_a_2091_) == 0)
{
lean_object* v_currPos_2093_; lean_object* v_searcher_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2133_; 
v_currPos_2093_ = lean_ctor_get(v_a_2091_, 0);
v_searcher_2094_ = lean_ctor_get(v_a_2091_, 1);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_a_2091_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2096_ = v_a_2091_;
v_isShared_2097_ = v_isSharedCheck_2133_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_searcher_2094_);
lean_inc(v_currPos_2093_);
lean_dec(v_a_2091_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2133_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v_str_2098_; lean_object* v_startInclusive_2099_; lean_object* v_endExclusive_2100_; lean_object* v_it_2102_; lean_object* v_startInclusive_2103_; lean_object* v_endExclusive_2104_; lean_object* v___x_2111_; uint8_t v_decide_2112_; 
v_str_2098_ = lean_ctor_get(v_out_2090_, 0);
v_startInclusive_2099_ = lean_ctor_get(v_out_2090_, 1);
v_endExclusive_2100_ = lean_ctor_get(v_out_2090_, 2);
v___x_2111_ = lean_nat_sub(v_endExclusive_2100_, v_startInclusive_2099_);
v_decide_2112_ = lean_nat_dec_eq(v_searcher_2094_, v___x_2111_);
if (v_decide_2112_ == 0)
{
uint32_t v___x_2113_; lean_object* v___x_2114_; uint32_t v___x_2115_; uint8_t v___x_2116_; 
lean_dec(v___x_2111_);
v___x_2113_ = 61;
v___x_2114_ = lean_nat_add(v_startInclusive_2099_, v_searcher_2094_);
v___x_2115_ = lean_string_utf8_get_fast(v_str_2098_, v___x_2114_);
v___x_2116_ = lean_uint32_dec_eq(v___x_2115_, v___x_2113_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2120_; 
lean_dec(v_searcher_2094_);
v___x_2117_ = lean_string_utf8_next_fast(v_str_2098_, v___x_2114_);
lean_dec(v___x_2114_);
v___x_2118_ = lean_nat_sub(v___x_2117_, v_startInclusive_2099_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 1, v___x_2118_);
v___x_2120_ = v___x_2096_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_currPos_2093_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v___x_2118_);
v___x_2120_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
v_a_2091_ = v___x_2120_;
goto _start;
}
}
else
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v_slice_2126_; lean_object* v_nextIt_2128_; 
v___x_2123_ = lean_string_utf8_next_fast(v_str_2098_, v___x_2114_);
v___x_2124_ = lean_nat_sub(v___x_2123_, v___x_2114_);
lean_dec(v___x_2114_);
v___x_2125_ = lean_nat_add(v_searcher_2094_, v___x_2124_);
lean_dec(v___x_2124_);
v_slice_2126_ = l_String_Slice_subslice_x21(v_out_2090_, v_currPos_2093_, v_searcher_2094_);
lean_inc(v___x_2125_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 1, v___x_2125_);
lean_ctor_set(v___x_2096_, 0, v___x_2125_);
v_nextIt_2128_ = v___x_2096_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2125_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v___x_2125_);
v_nextIt_2128_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v_startInclusive_2129_; lean_object* v_endExclusive_2130_; 
v_startInclusive_2129_ = lean_ctor_get(v_slice_2126_, 0);
lean_inc(v_startInclusive_2129_);
v_endExclusive_2130_ = lean_ctor_get(v_slice_2126_, 1);
lean_inc(v_endExclusive_2130_);
lean_dec_ref(v_slice_2126_);
v_it_2102_ = v_nextIt_2128_;
v_startInclusive_2103_ = v_startInclusive_2129_;
v_endExclusive_2104_ = v_endExclusive_2130_;
goto v___jp_2101_;
}
}
}
else
{
lean_object* v___x_2132_; 
lean_del_object(v___x_2096_);
lean_dec(v_searcher_2094_);
v___x_2132_ = lean_box(1);
v_it_2102_ = v___x_2132_;
v_startInclusive_2103_ = v_currPos_2093_;
v_endExclusive_2104_ = v___x_2111_;
goto v___jp_2101_;
}
v___jp_2101_:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2105_ = lean_nat_add(v_startInclusive_2099_, v_startInclusive_2103_);
lean_dec(v_startInclusive_2103_);
v___x_2106_ = lean_nat_add(v_startInclusive_2099_, v_endExclusive_2104_);
lean_dec(v_endExclusive_2104_);
lean_inc_ref(v_str_2098_);
v___x_2107_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2107_, 0, v_str_2098_);
lean_ctor_set(v___x_2107_, 1, v___x_2105_);
lean_ctor_set(v___x_2107_, 2, v___x_2106_);
v___x_2108_ = l_String_Slice_toString(v___x_2107_);
lean_dec_ref_known(v___x_2107_, 3);
v___x_2109_ = lean_array_push(v_b_2092_, v___x_2108_);
v_a_2091_ = v_it_2102_;
v_b_2092_ = v___x_2109_;
goto _start;
}
}
}
else
{
return v_b_2092_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg___boxed(lean_object* v_out_2134_, lean_object* v_a_2135_, lean_object* v_b_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_2134_, v_a_2135_, v_b_2136_);
lean_dec_ref(v_out_2134_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(lean_object* v___x_2141_, lean_object* v___x_2142_, lean_object* v___x_2143_, lean_object* v_a_2144_, lean_object* v_b_2145_){
_start:
{
lean_object* v_it_2147_; lean_object* v_startInclusive_2148_; lean_object* v_endExclusive_2149_; 
if (lean_obj_tag(v_a_2144_) == 0)
{
lean_object* v_currPos_2174_; lean_object* v_searcher_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2204_; 
v_currPos_2174_ = lean_ctor_get(v_a_2144_, 0);
v_searcher_2175_ = lean_ctor_get(v_a_2144_, 1);
v_isSharedCheck_2204_ = !lean_is_exclusive(v_a_2144_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2177_ = v_a_2144_;
v_isShared_2178_ = v_isSharedCheck_2204_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_searcher_2175_);
lean_inc(v_currPos_2174_);
lean_dec(v_a_2144_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2204_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v_str_2179_; lean_object* v_startInclusive_2180_; lean_object* v_endExclusive_2181_; lean_object* v___x_2182_; uint8_t v_decide_2183_; 
v_str_2179_ = lean_ctor_get(v___x_2142_, 0);
v_startInclusive_2180_ = lean_ctor_get(v___x_2142_, 1);
v_endExclusive_2181_ = lean_ctor_get(v___x_2142_, 2);
v___x_2182_ = lean_nat_sub(v_endExclusive_2181_, v_startInclusive_2180_);
v_decide_2183_ = lean_nat_dec_eq(v_searcher_2175_, v___x_2182_);
lean_dec(v___x_2182_);
if (v_decide_2183_ == 0)
{
uint32_t v___x_2184_; lean_object* v___x_2185_; uint32_t v___x_2186_; uint8_t v___x_2187_; 
v___x_2184_ = 38;
v___x_2185_ = lean_nat_add(v_startInclusive_2180_, v_searcher_2175_);
v___x_2186_ = lean_string_utf8_get_fast(v_str_2179_, v___x_2185_);
v___x_2187_ = lean_uint32_dec_eq(v___x_2186_, v___x_2184_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2191_; 
lean_dec(v_searcher_2175_);
v___x_2188_ = lean_string_utf8_next_fast(v_str_2179_, v___x_2185_);
lean_dec(v___x_2185_);
v___x_2189_ = lean_nat_sub(v___x_2188_, v_startInclusive_2180_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 1, v___x_2189_);
v___x_2191_ = v___x_2177_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_currPos_2174_);
lean_ctor_set(v_reuseFailAlloc_2193_, 1, v___x_2189_);
v___x_2191_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
v_a_2144_ = v___x_2191_;
goto _start;
}
}
else
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v_slice_2197_; lean_object* v_nextIt_2199_; 
v___x_2194_ = lean_string_utf8_next_fast(v_str_2179_, v___x_2185_);
v___x_2195_ = lean_nat_sub(v___x_2194_, v___x_2185_);
lean_dec(v___x_2185_);
v___x_2196_ = lean_nat_add(v_searcher_2175_, v___x_2195_);
lean_dec(v___x_2195_);
v_slice_2197_ = l_String_Slice_subslice_x21(v___x_2142_, v_currPos_2174_, v_searcher_2175_);
lean_inc(v___x_2196_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 1, v___x_2196_);
lean_ctor_set(v___x_2177_, 0, v___x_2196_);
v_nextIt_2199_ = v___x_2177_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2196_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v___x_2196_);
v_nextIt_2199_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
lean_object* v_startInclusive_2200_; lean_object* v_endExclusive_2201_; 
v_startInclusive_2200_ = lean_ctor_get(v_slice_2197_, 0);
lean_inc(v_startInclusive_2200_);
v_endExclusive_2201_ = lean_ctor_get(v_slice_2197_, 1);
lean_inc(v_endExclusive_2201_);
lean_dec_ref(v_slice_2197_);
v_it_2147_ = v_nextIt_2199_;
v_startInclusive_2148_ = v_startInclusive_2200_;
v_endExclusive_2149_ = v_endExclusive_2201_;
goto v___jp_2146_;
}
}
}
else
{
lean_object* v___x_2203_; 
lean_del_object(v___x_2177_);
lean_dec(v_searcher_2175_);
v___x_2203_ = lean_box(1);
lean_inc(v___x_2143_);
v_it_2147_ = v___x_2203_;
v_startInclusive_2148_ = v_currPos_2174_;
v_endExclusive_2149_ = v___x_2143_;
goto v___jp_2146_;
}
}
}
else
{
lean_object* v___x_2205_; 
lean_dec(v___x_2143_);
lean_dec_ref(v___x_2141_);
v___x_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2205_, 0, v_b_2145_);
return v___x_2205_;
}
v___jp_2146_:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
lean_inc_ref(v___x_2141_);
v___x_2150_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2141_);
lean_ctor_set(v___x_2150_, 1, v_startInclusive_2148_);
lean_ctor_set(v___x_2150_, 2, v_endExclusive_2149_);
v___x_2151_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
v___x_2152_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0));
v___x_2153_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_2150_, v___x_2151_, v___x_2152_);
lean_dec_ref_known(v___x_2150_, 3);
v___x_2154_ = lean_array_to_list(v___x_2153_);
if (lean_obj_tag(v___x_2154_) == 0)
{
v_a_2144_ = v_it_2147_;
goto _start;
}
else
{
lean_object* v_tail_2156_; 
v_tail_2156_ = lean_ctor_get(v___x_2154_, 1);
if (lean_obj_tag(v_tail_2156_) == 0)
{
lean_object* v_head_2157_; lean_object* v___x_2158_; 
v_head_2157_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_head_2157_);
lean_dec_ref_known(v___x_2154_, 2);
v___x_2158_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2157_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v___x_2159_; 
lean_dec(v_it_2147_);
lean_dec_ref(v_b_2145_);
lean_dec(v___x_2143_);
lean_dec_ref(v___x_2141_);
v___x_2159_ = lean_box(0);
return v___x_2159_;
}
else
{
lean_object* v_val_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v_val_2160_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_val_2160_);
lean_dec_ref_known(v___x_2158_, 1);
v___x_2161_ = lean_box(0);
v___x_2162_ = l_Std_Http_URI_Query_insertEncoded(v_b_2145_, v_val_2160_, v___x_2161_);
v_a_2144_ = v_it_2147_;
v_b_2145_ = v___x_2162_;
goto _start;
}
}
else
{
lean_object* v_head_2164_; lean_object* v___x_2165_; 
lean_inc(v_tail_2156_);
v_head_2164_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_head_2164_);
lean_dec_ref_known(v___x_2154_, 2);
v___x_2165_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2164_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v___x_2166_; 
lean_dec(v_tail_2156_);
lean_dec(v_it_2147_);
lean_dec_ref(v_b_2145_);
lean_dec(v___x_2143_);
lean_dec_ref(v___x_2141_);
v___x_2166_ = lean_box(0);
return v___x_2166_;
}
else
{
lean_object* v_val_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v_val_2167_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_val_2167_);
lean_dec_ref_known(v___x_2165_, 1);
v___x_2168_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1));
v___x_2169_ = l_String_intercalate(v___x_2168_, v_tail_2156_);
v___x_2170_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2169_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v___x_2171_; 
lean_dec(v_val_2167_);
lean_dec(v_it_2147_);
lean_dec_ref(v_b_2145_);
lean_dec(v___x_2143_);
lean_dec_ref(v___x_2141_);
v___x_2171_ = lean_box(0);
return v___x_2171_;
}
else
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Std_Http_URI_Query_insertEncoded(v_b_2145_, v_val_2167_, v___x_2170_);
v_a_2144_ = v_it_2147_;
v_b_2145_ = v___x_2172_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___boxed(lean_object* v___x_2206_, lean_object* v___x_2207_, lean_object* v___x_2208_, lean_object* v_a_2209_, lean_object* v_b_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2206_, v___x_2207_, v___x_2208_, v_a_2209_, v_b_2210_);
lean_dec_ref(v___x_2207_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(lean_object* v___x_2212_, lean_object* v___x_2213_, lean_object* v___x_2214_, lean_object* v_a_2215_, lean_object* v_b_2216_){
_start:
{
lean_object* v_it_2218_; lean_object* v_startInclusive_2219_; lean_object* v_endExclusive_2220_; 
if (lean_obj_tag(v_a_2215_) == 0)
{
lean_object* v_currPos_2245_; lean_object* v_searcher_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2275_; 
v_currPos_2245_ = lean_ctor_get(v_a_2215_, 0);
v_searcher_2246_ = lean_ctor_get(v_a_2215_, 1);
v_isSharedCheck_2275_ = !lean_is_exclusive(v_a_2215_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2248_ = v_a_2215_;
v_isShared_2249_ = v_isSharedCheck_2275_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_searcher_2246_);
lean_inc(v_currPos_2245_);
lean_dec(v_a_2215_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2275_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v_str_2250_; lean_object* v_startInclusive_2251_; lean_object* v_endExclusive_2252_; lean_object* v___x_2253_; uint8_t v_decide_2254_; 
v_str_2250_ = lean_ctor_get(v___x_2213_, 0);
v_startInclusive_2251_ = lean_ctor_get(v___x_2213_, 1);
v_endExclusive_2252_ = lean_ctor_get(v___x_2213_, 2);
v___x_2253_ = lean_nat_sub(v_endExclusive_2252_, v_startInclusive_2251_);
v_decide_2254_ = lean_nat_dec_eq(v_searcher_2246_, v___x_2253_);
lean_dec(v___x_2253_);
if (v_decide_2254_ == 0)
{
lean_object* v___x_2255_; uint32_t v___x_2256_; uint32_t v___x_2257_; uint8_t v___x_2258_; 
v___x_2255_ = lean_nat_add(v_startInclusive_2251_, v_searcher_2246_);
v___x_2256_ = lean_string_utf8_get_fast(v_str_2250_, v___x_2255_);
v___x_2257_ = 38;
v___x_2258_ = lean_uint32_dec_eq(v___x_2256_, v___x_2257_);
if (v___x_2258_ == 0)
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2262_; 
lean_dec(v_searcher_2246_);
v___x_2259_ = lean_string_utf8_next_fast(v_str_2250_, v___x_2255_);
lean_dec(v___x_2255_);
v___x_2260_ = lean_nat_sub(v___x_2259_, v_startInclusive_2251_);
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 1, v___x_2260_);
v___x_2262_ = v___x_2248_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_currPos_2245_);
lean_ctor_set(v_reuseFailAlloc_2264_, 1, v___x_2260_);
v___x_2262_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
lean_object* v___x_2263_; 
v___x_2263_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2212_, v___x_2213_, v___x_2214_, v___x_2262_, v_b_2216_);
return v___x_2263_;
}
}
else
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v_slice_2268_; lean_object* v_nextIt_2270_; 
v___x_2265_ = lean_string_utf8_next_fast(v_str_2250_, v___x_2255_);
v___x_2266_ = lean_nat_sub(v___x_2265_, v___x_2255_);
lean_dec(v___x_2255_);
v___x_2267_ = lean_nat_add(v_searcher_2246_, v___x_2266_);
lean_dec(v___x_2266_);
v_slice_2268_ = l_String_Slice_subslice_x21(v___x_2213_, v_currPos_2245_, v_searcher_2246_);
lean_inc(v___x_2267_);
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 1, v___x_2267_);
lean_ctor_set(v___x_2248_, 0, v___x_2267_);
v_nextIt_2270_ = v___x_2248_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2267_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v___x_2267_);
v_nextIt_2270_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
lean_object* v_startInclusive_2271_; lean_object* v_endExclusive_2272_; 
v_startInclusive_2271_ = lean_ctor_get(v_slice_2268_, 0);
lean_inc(v_startInclusive_2271_);
v_endExclusive_2272_ = lean_ctor_get(v_slice_2268_, 1);
lean_inc(v_endExclusive_2272_);
lean_dec_ref(v_slice_2268_);
v_it_2218_ = v_nextIt_2270_;
v_startInclusive_2219_ = v_startInclusive_2271_;
v_endExclusive_2220_ = v_endExclusive_2272_;
goto v___jp_2217_;
}
}
}
else
{
lean_object* v___x_2274_; 
lean_del_object(v___x_2248_);
lean_dec(v_searcher_2246_);
v___x_2274_ = lean_box(1);
lean_inc(v___x_2214_);
v_it_2218_ = v___x_2274_;
v_startInclusive_2219_ = v_currPos_2245_;
v_endExclusive_2220_ = v___x_2214_;
goto v___jp_2217_;
}
}
}
else
{
lean_object* v___x_2276_; 
lean_dec(v___x_2214_);
lean_dec_ref(v___x_2212_);
v___x_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2276_, 0, v_b_2216_);
return v___x_2276_;
}
v___jp_2217_:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
lean_inc_ref(v___x_2212_);
v___x_2221_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2212_);
lean_ctor_set(v___x_2221_, 1, v_startInclusive_2219_);
lean_ctor_set(v___x_2221_, 2, v_endExclusive_2220_);
v___x_2222_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
v___x_2223_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0));
v___x_2224_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_2221_, v___x_2222_, v___x_2223_);
lean_dec_ref_known(v___x_2221_, 3);
v___x_2225_ = lean_array_to_list(v___x_2224_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v___x_2226_; 
v___x_2226_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2212_, v___x_2213_, v___x_2214_, v_it_2218_, v_b_2216_);
return v___x_2226_;
}
else
{
lean_object* v_tail_2227_; 
v_tail_2227_ = lean_ctor_get(v___x_2225_, 1);
if (lean_obj_tag(v_tail_2227_) == 0)
{
lean_object* v_head_2228_; lean_object* v___x_2229_; 
v_head_2228_ = lean_ctor_get(v___x_2225_, 0);
lean_inc(v_head_2228_);
lean_dec_ref_known(v___x_2225_, 2);
v___x_2229_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2228_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v___x_2230_; 
lean_dec(v_it_2218_);
lean_dec_ref(v_b_2216_);
lean_dec(v___x_2214_);
lean_dec_ref(v___x_2212_);
v___x_2230_ = lean_box(0);
return v___x_2230_;
}
else
{
lean_object* v_val_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v_val_2231_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_val_2231_);
lean_dec_ref_known(v___x_2229_, 1);
v___x_2232_ = lean_box(0);
v___x_2233_ = l_Std_Http_URI_Query_insertEncoded(v_b_2216_, v_val_2231_, v___x_2232_);
v___x_2234_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2212_, v___x_2213_, v___x_2214_, v_it_2218_, v___x_2233_);
return v___x_2234_;
}
}
else
{
lean_object* v_head_2235_; lean_object* v___x_2236_; 
lean_inc(v_tail_2227_);
v_head_2235_ = lean_ctor_get(v___x_2225_, 0);
lean_inc(v_head_2235_);
lean_dec_ref_known(v___x_2225_, 2);
v___x_2236_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2235_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v___x_2237_; 
lean_dec(v_tail_2227_);
lean_dec(v_it_2218_);
lean_dec_ref(v_b_2216_);
lean_dec(v___x_2214_);
lean_dec_ref(v___x_2212_);
v___x_2237_ = lean_box(0);
return v___x_2237_;
}
else
{
lean_object* v_val_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v_val_2238_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_val_2238_);
lean_dec_ref_known(v___x_2236_, 1);
v___x_2239_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1));
v___x_2240_ = l_String_intercalate(v___x_2239_, v_tail_2227_);
v___x_2241_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2240_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v___x_2242_; 
lean_dec(v_val_2238_);
lean_dec(v_it_2218_);
lean_dec_ref(v_b_2216_);
lean_dec(v___x_2214_);
lean_dec_ref(v___x_2212_);
v___x_2242_ = lean_box(0);
return v___x_2242_;
}
else
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = l_Std_Http_URI_Query_insertEncoded(v_b_2216_, v_val_2238_, v___x_2241_);
v___x_2244_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2212_, v___x_2213_, v___x_2214_, v_it_2218_, v___x_2243_);
return v___x_2244_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg___boxed(lean_object* v___x_2277_, lean_object* v___x_2278_, lean_object* v___x_2279_, lean_object* v_a_2280_, lean_object* v_b_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2277_, v___x_2278_, v___x_2279_, v_a_2280_, v_b_2281_);
lean_dec_ref(v___x_2278_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(lean_object* v_config_2288_, lean_object* v_a_2289_){
_start:
{
lean_object* v_maxQueryLength_2290_; lean_object* v_maxQueryParams_2291_; lean_object* v___f_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v_snd_2295_; lean_object* v_fst_2296_; lean_object* v_fst_2297_; lean_object* v_array_2298_; lean_object* v_idx_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2349_; 
v_maxQueryLength_2290_ = lean_ctor_get(v_config_2288_, 4);
lean_inc(v_maxQueryLength_2290_);
v_maxQueryParams_2291_ = lean_ctor_get(v_config_2288_, 8);
lean_inc(v_maxQueryParams_2291_);
lean_dec_ref(v_config_2288_);
v___f_2292_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2293_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2289_);
v___x_2294_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2292_, v_maxQueryLength_2290_, v___x_2293_, v_a_2289_);
lean_dec(v_maxQueryLength_2290_);
v_snd_2295_ = lean_ctor_get(v___x_2294_, 1);
lean_inc(v_snd_2295_);
v_fst_2296_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_fst_2296_);
lean_dec_ref(v___x_2294_);
v_fst_2297_ = lean_ctor_get(v_snd_2295_, 0);
lean_inc(v_fst_2297_);
lean_dec(v_snd_2295_);
v_array_2298_ = lean_ctor_get(v_a_2289_, 0);
v_idx_2299_ = lean_ctor_get(v_a_2289_, 1);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_a_2289_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2301_ = v_a_2289_;
v_isShared_2302_ = v_isSharedCheck_2349_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_idx_2299_);
lean_inc(v_array_2298_);
lean_dec(v_a_2289_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2349_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v_lower_2304_; lean_object* v_upper_2305_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___y_2346_; uint8_t v___x_2348_; 
v___x_2343_ = lean_nat_add(v_idx_2299_, v_fst_2296_);
lean_dec(v_fst_2296_);
v___x_2344_ = lean_byte_array_size(v_array_2298_);
v___x_2348_ = lean_nat_dec_le(v_idx_2299_, v___x_2293_);
if (v___x_2348_ == 0)
{
v___y_2346_ = v_idx_2299_;
goto v___jp_2345_;
}
else
{
lean_dec(v_idx_2299_);
v___y_2346_ = v___x_2293_;
goto v___jp_2345_;
}
v___jp_2303_:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; uint8_t v___x_2308_; 
v___x_2306_ = l_ByteArray_toByteSlice(v_array_2298_, v_lower_2304_, v_upper_2305_);
v___x_2307_ = l_ByteSlice_toByteArray(v___x_2306_);
v___x_2308_ = lean_string_validate_utf8(v___x_2307_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2309_; lean_object* v___x_2311_; 
lean_dec_ref(v___x_2307_);
lean_dec(v_maxQueryParams_2291_);
v___x_2309_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2302_ == 0)
{
lean_ctor_set_tag(v___x_2301_, 1);
lean_ctor_set(v___x_2301_, 1, v___x_2309_);
lean_ctor_set(v___x_2301_, 0, v_fst_2297_);
v___x_2311_ = v___x_2301_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_fst_2297_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v___x_2309_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
else
{
lean_object* v___x_2313_; lean_object* v___x_2314_; uint8_t v___x_2315_; 
v___x_2313_ = lean_string_from_utf8_unchecked(v___x_2307_);
v___x_2314_ = lean_string_utf8_byte_size(v___x_2313_);
v___x_2315_ = lean_nat_dec_eq(v___x_2314_, v___x_2293_);
if (v___x_2315_ == 0)
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; uint8_t v___x_2319_; 
lean_inc_ref(v___x_2313_);
v___x_2316_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2313_);
lean_ctor_set(v___x_2316_, 1, v___x_2293_);
lean_ctor_set(v___x_2316_, 2, v___x_2314_);
v___x_2317_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0);
v___x_2318_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2313_, v___x_2316_, v___x_2314_, v___x_2317_, v___x_2293_);
v___x_2319_ = lean_nat_dec_lt(v_maxQueryParams_2291_, v___x_2318_);
lean_dec(v___x_2318_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
lean_dec(v_maxQueryParams_2291_);
v___x_2320_ = l_Std_Http_URI_Query_empty;
v___x_2321_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2313_, v___x_2316_, v___x_2314_, v___x_2317_, v___x_2320_);
lean_dec_ref_known(v___x_2316_, 3);
if (lean_obj_tag(v___x_2321_) == 1)
{
lean_object* v_val_2322_; lean_object* v___x_2324_; 
v_val_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_val_2322_);
lean_dec_ref_known(v___x_2321_, 1);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 1, v_val_2322_);
lean_ctor_set(v___x_2301_, 0, v_fst_2297_);
v___x_2324_ = v___x_2301_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_fst_2297_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v_val_2322_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
else
{
lean_object* v___x_2326_; lean_object* v___x_2328_; 
lean_dec(v___x_2321_);
v___x_2326_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2302_ == 0)
{
lean_ctor_set_tag(v___x_2301_, 1);
lean_ctor_set(v___x_2301_, 1, v___x_2326_);
lean_ctor_set(v___x_2301_, 0, v_fst_2297_);
v___x_2328_ = v___x_2301_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_fst_2297_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v___x_2326_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
else
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2337_; 
lean_dec_ref_known(v___x_2316_, 3);
lean_dec_ref(v___x_2313_);
v___x_2330_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3));
v___x_2331_ = l_Nat_reprFast(v_maxQueryParams_2291_);
v___x_2332_ = lean_string_append(v___x_2330_, v___x_2331_);
lean_dec_ref(v___x_2331_);
v___x_2333_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_2334_ = lean_string_append(v___x_2332_, v___x_2333_);
v___x_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set_tag(v___x_2301_, 1);
lean_ctor_set(v___x_2301_, 1, v___x_2335_);
lean_ctor_set(v___x_2301_, 0, v_fst_2297_);
v___x_2337_ = v___x_2301_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_fst_2297_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v___x_2335_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
else
{
lean_object* v___x_2339_; lean_object* v___x_2341_; 
lean_dec_ref(v___x_2313_);
lean_dec(v_maxQueryParams_2291_);
v___x_2339_ = l_Std_Http_URI_Query_empty;
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 1, v___x_2339_);
lean_ctor_set(v___x_2301_, 0, v_fst_2297_);
v___x_2341_ = v___x_2301_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_fst_2297_);
lean_ctor_set(v_reuseFailAlloc_2342_, 1, v___x_2339_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
v___jp_2345_:
{
uint8_t v___x_2347_; 
v___x_2347_ = lean_nat_dec_le(v___x_2343_, v___x_2344_);
if (v___x_2347_ == 0)
{
lean_dec(v___x_2343_);
v_lower_2304_ = v___y_2346_;
v_upper_2305_ = v___x_2344_;
goto v___jp_2303_;
}
else
{
v_lower_2304_ = v___y_2346_;
v_upper_2305_ = v___x_2343_;
goto v___jp_2303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(lean_object* v___x_2350_, lean_object* v___x_2351_, lean_object* v___x_2352_, lean_object* v_inst_2353_, lean_object* v_R_2354_, lean_object* v_a_2355_, lean_object* v_b_2356_, lean_object* v_c_2357_){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2350_, v___x_2351_, v___x_2352_, v_a_2355_, v_b_2356_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___boxed(lean_object* v___x_2359_, lean_object* v___x_2360_, lean_object* v___x_2361_, lean_object* v_inst_2362_, lean_object* v_R_2363_, lean_object* v_a_2364_, lean_object* v_b_2365_, lean_object* v_c_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(v___x_2359_, v___x_2360_, v___x_2361_, v_inst_2362_, v_R_2363_, v_a_2364_, v_b_2365_, v_c_2366_);
lean_dec(v___x_2361_);
lean_dec_ref(v___x_2360_);
lean_dec_ref(v___x_2359_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(lean_object* v_out_2368_, lean_object* v_inst_2369_, lean_object* v_R_2370_, lean_object* v_a_2371_, lean_object* v_b_2372_){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_2368_, v_a_2371_, v_b_2372_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___boxed(lean_object* v_out_2374_, lean_object* v_inst_2375_, lean_object* v_R_2376_, lean_object* v_a_2377_, lean_object* v_b_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(v_out_2374_, v_inst_2375_, v_R_2376_, v_a_2377_, v_b_2378_);
lean_dec_ref(v_out_2374_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(lean_object* v___x_2380_, lean_object* v___x_2381_, lean_object* v___x_2382_, lean_object* v_inst_2383_, lean_object* v_R_2384_, lean_object* v_a_2385_, lean_object* v_b_2386_, lean_object* v_c_2387_){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2380_, v___x_2381_, v___x_2382_, v_a_2385_, v_b_2386_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___boxed(lean_object* v___x_2389_, lean_object* v___x_2390_, lean_object* v___x_2391_, lean_object* v_inst_2392_, lean_object* v_R_2393_, lean_object* v_a_2394_, lean_object* v_b_2395_, lean_object* v_c_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(v___x_2389_, v___x_2390_, v___x_2391_, v_inst_2392_, v_R_2393_, v_a_2394_, v_b_2395_, v_c_2396_);
lean_dec_ref(v___x_2390_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(lean_object* v___x_2398_, lean_object* v___x_2399_, lean_object* v___x_2400_, lean_object* v_inst_2401_, lean_object* v_R_2402_, lean_object* v_a_2403_, lean_object* v_b_2404_, lean_object* v_c_2405_){
_start:
{
lean_object* v___x_2406_; 
v___x_2406_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2399_, v___x_2400_, v_a_2403_, v_b_2404_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___boxed(lean_object* v___x_2407_, lean_object* v___x_2408_, lean_object* v___x_2409_, lean_object* v_inst_2410_, lean_object* v_R_2411_, lean_object* v_a_2412_, lean_object* v_b_2413_, lean_object* v_c_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(v___x_2407_, v___x_2408_, v___x_2409_, v_inst_2410_, v_R_2411_, v_a_2412_, v_b_2413_, v_c_2414_);
lean_dec(v___x_2409_);
lean_dec_ref(v___x_2408_);
lean_dec_ref(v___x_2407_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(lean_object* v___x_2416_, lean_object* v___x_2417_, lean_object* v___x_2418_, lean_object* v_inst_2419_, lean_object* v_R_2420_, lean_object* v_a_2421_, lean_object* v_b_2422_, lean_object* v_c_2423_){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2416_, v___x_2417_, v___x_2418_, v_a_2421_, v_b_2422_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___boxed(lean_object* v___x_2425_, lean_object* v___x_2426_, lean_object* v___x_2427_, lean_object* v_inst_2428_, lean_object* v_R_2429_, lean_object* v_a_2430_, lean_object* v_b_2431_, lean_object* v_c_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(v___x_2425_, v___x_2426_, v___x_2427_, v_inst_2428_, v_R_2429_, v_a_2430_, v_b_2431_, v_c_2432_);
lean_dec_ref(v___x_2426_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(lean_object* v_config_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v_maxFragmentLength_2439_; lean_object* v___f_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v_snd_2443_; lean_object* v_fst_2444_; lean_object* v_fst_2445_; lean_object* v_array_2446_; lean_object* v_idx_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2471_; 
v_maxFragmentLength_2439_ = lean_ctor_get(v_config_2437_, 5);
v___f_2440_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2441_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2438_);
v___x_2442_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2440_, v_maxFragmentLength_2439_, v___x_2441_, v_a_2438_);
v_snd_2443_ = lean_ctor_get(v___x_2442_, 1);
lean_inc(v_snd_2443_);
v_fst_2444_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_fst_2444_);
lean_dec_ref(v___x_2442_);
v_fst_2445_ = lean_ctor_get(v_snd_2443_, 0);
lean_inc(v_fst_2445_);
lean_dec(v_snd_2443_);
v_array_2446_ = lean_ctor_get(v_a_2438_, 0);
v_idx_2447_ = lean_ctor_get(v_a_2438_, 1);
v_isSharedCheck_2471_ = !lean_is_exclusive(v_a_2438_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2449_ = v_a_2438_;
v_isShared_2450_ = v_isSharedCheck_2471_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_idx_2447_);
lean_inc(v_array_2446_);
lean_dec(v_a_2438_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2471_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v_lower_2452_; lean_object* v_upper_2453_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___y_2468_; uint8_t v___x_2470_; 
v___x_2465_ = lean_nat_add(v_idx_2447_, v_fst_2444_);
lean_dec(v_fst_2444_);
v___x_2466_ = lean_byte_array_size(v_array_2446_);
v___x_2470_ = lean_nat_dec_le(v_idx_2447_, v___x_2441_);
if (v___x_2470_ == 0)
{
v___y_2468_ = v_idx_2447_;
goto v___jp_2467_;
}
else
{
lean_dec(v_idx_2447_);
v___y_2468_ = v___x_2441_;
goto v___jp_2467_;
}
v___jp_2451_:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2454_ = l_ByteArray_toByteSlice(v_array_2446_, v_lower_2452_, v_upper_2453_);
v___x_2455_ = l_ByteSlice_toByteArray(v___x_2454_);
v___x_2456_ = l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(v___x_2455_);
if (lean_obj_tag(v___x_2456_) == 1)
{
lean_object* v_val_2457_; lean_object* v___x_2459_; 
v_val_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_val_2457_);
lean_dec_ref_known(v___x_2456_, 1);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 1, v_val_2457_);
lean_ctor_set(v___x_2449_, 0, v_fst_2445_);
v___x_2459_ = v___x_2449_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_fst_2445_);
lean_ctor_set(v_reuseFailAlloc_2460_, 1, v_val_2457_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
else
{
lean_object* v___x_2461_; lean_object* v___x_2463_; 
lean_dec(v___x_2456_);
v___x_2461_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1));
if (v_isShared_2450_ == 0)
{
lean_ctor_set_tag(v___x_2449_, 1);
lean_ctor_set(v___x_2449_, 1, v___x_2461_);
lean_ctor_set(v___x_2449_, 0, v_fst_2445_);
v___x_2463_ = v___x_2449_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_fst_2445_);
lean_ctor_set(v_reuseFailAlloc_2464_, 1, v___x_2461_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
v___jp_2467_:
{
uint8_t v___x_2469_; 
v___x_2469_ = lean_nat_dec_le(v___x_2465_, v___x_2466_);
if (v___x_2469_ == 0)
{
lean_dec(v___x_2465_);
v_lower_2452_ = v___y_2468_;
v_upper_2453_ = v___x_2466_;
goto v___jp_2451_;
}
else
{
v_lower_2452_ = v___y_2468_;
v_upper_2453_ = v___x_2465_;
goto v___jp_2451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___boxed(lean_object* v_config_2472_, lean_object* v_a_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2472_, v_a_2473_);
lean_dec_ref(v_config_2472_);
return v_res_2474_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1(void){
_start:
{
lean_object* v___x_2476_; lean_object* v_utf8_2477_; 
v___x_2476_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0));
v_utf8_2477_ = lean_string_to_utf8(v___x_2476_);
return v_utf8_2477_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(lean_object* v_config_2478_, lean_object* v_a_2479_){
_start:
{
lean_object* v_utf8_2480_; lean_object* v___x_2481_; 
v_utf8_2480_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1);
lean_inc_ref(v_a_2479_);
v___x_2481_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_2480_, v_a_2479_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v_pos_2482_; uint8_t v___x_2483_; lean_object* v_pos_2485_; lean_object* v_res_2486_; lean_object* v___x_2507_; 
lean_dec_ref(v_a_2479_);
v_pos_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc_n(v_pos_2482_, 2);
lean_dec_ref_known(v___x_2481_, 2);
v___x_2483_ = 1;
v___x_2507_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_2478_, v_pos_2482_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_pos_2508_; lean_object* v_res_2509_; lean_object* v___x_2510_; 
lean_dec(v_pos_2482_);
v_pos_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_pos_2508_);
v_res_2509_ = lean_ctor_get(v___x_2507_, 1);
lean_inc(v_res_2509_);
lean_dec_ref_known(v___x_2507_, 2);
v___x_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2510_, 0, v_res_2509_);
v_pos_2485_ = v_pos_2508_;
v_res_2486_ = v___x_2510_;
goto v___jp_2484_;
}
else
{
lean_object* v_err_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2521_; 
v_err_2511_ = lean_ctor_get(v___x_2507_, 1);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2521_ == 0)
{
lean_object* v_unused_2522_; 
v_unused_2522_ = lean_ctor_get(v___x_2507_, 0);
lean_dec(v_unused_2522_);
v___x_2513_ = v___x_2507_;
v_isShared_2514_ = v_isSharedCheck_2521_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_err_2511_);
lean_dec(v___x_2507_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2521_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v_idx_2515_; uint8_t v___x_2516_; 
v_idx_2515_ = lean_ctor_get(v_pos_2482_, 1);
v___x_2516_ = lean_nat_dec_eq(v_idx_2515_, v_idx_2515_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2518_; 
lean_dec_ref(v_config_2478_);
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 0, v_pos_2482_);
v___x_2518_ = v___x_2513_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_pos_2482_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v_err_2511_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
else
{
lean_object* v___x_2520_; 
lean_del_object(v___x_2513_);
lean_dec(v_err_2511_);
v___x_2520_ = lean_box(0);
v_pos_2485_ = v_pos_2482_;
v_res_2486_ = v___x_2520_;
goto v___jp_2484_;
}
}
}
v___jp_2484_:
{
lean_object* v___x_2487_; 
v___x_2487_ = l_Std_Http_URI_Parser_parsePath(v_config_2478_, v___x_2483_, v___x_2483_, v_pos_2485_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_pos_2488_; lean_object* v_res_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2497_; 
v_pos_2488_ = lean_ctor_get(v___x_2487_, 0);
v_res_2489_ = lean_ctor_get(v___x_2487_, 1);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2491_ = v___x_2487_;
v_isShared_2492_ = v_isSharedCheck_2497_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_res_2489_);
lean_inc(v_pos_2488_);
lean_dec(v___x_2487_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2497_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2493_; lean_object* v___x_2495_; 
v___x_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2493_, 0, v_res_2486_);
lean_ctor_set(v___x_2493_, 1, v_res_2489_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 1, v___x_2493_);
v___x_2495_ = v___x_2491_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_pos_2488_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v___x_2493_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
else
{
lean_object* v_pos_2498_; lean_object* v_err_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
lean_dec(v_res_2486_);
v_pos_2498_ = lean_ctor_get(v___x_2487_, 0);
v_err_2499_ = lean_ctor_get(v___x_2487_, 1);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2487_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_err_2499_);
lean_inc(v_pos_2498_);
lean_dec(v___x_2487_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_pos_2498_);
lean_ctor_set(v_reuseFailAlloc_2505_, 1, v_err_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
}
else
{
lean_object* v_err_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2554_; 
v_err_2523_ = lean_ctor_get(v___x_2481_, 1);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2554_ == 0)
{
lean_object* v_unused_2555_; 
v_unused_2555_ = lean_ctor_get(v___x_2481_, 0);
lean_dec(v_unused_2555_);
v___x_2525_ = v___x_2481_;
v_isShared_2526_ = v_isSharedCheck_2554_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_err_2523_);
lean_dec(v___x_2481_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2554_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v_idx_2527_; uint8_t v___x_2528_; 
v_idx_2527_ = lean_ctor_get(v_a_2479_, 1);
v___x_2528_ = lean_nat_dec_eq(v_idx_2527_, v_idx_2527_);
if (v___x_2528_ == 0)
{
lean_object* v___x_2530_; 
lean_dec_ref(v_config_2478_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v_a_2479_);
v___x_2530_ = v___x_2525_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2479_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v_err_2523_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
else
{
uint8_t v___x_2532_; lean_object* v___x_2533_; 
lean_del_object(v___x_2525_);
lean_dec(v_err_2523_);
v___x_2532_ = 0;
v___x_2533_ = l_Std_Http_URI_Parser_parsePath(v_config_2478_, v___x_2532_, v___x_2528_, v_a_2479_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v_pos_2534_; lean_object* v_res_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2544_; 
v_pos_2534_ = lean_ctor_get(v___x_2533_, 0);
v_res_2535_ = lean_ctor_get(v___x_2533_, 1);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2537_ = v___x_2533_;
v_isShared_2538_ = v_isSharedCheck_2544_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_res_2535_);
lean_inc(v_pos_2534_);
lean_dec(v___x_2533_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2544_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2542_; 
v___x_2539_ = lean_box(0);
v___x_2540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2539_);
lean_ctor_set(v___x_2540_, 1, v_res_2535_);
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 1, v___x_2540_);
v___x_2542_ = v___x_2537_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_pos_2534_);
lean_ctor_set(v_reuseFailAlloc_2543_, 1, v___x_2540_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
else
{
lean_object* v_pos_2545_; lean_object* v_err_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
v_pos_2545_ = lean_ctor_get(v___x_2533_, 0);
v_err_2546_ = lean_ctor_get(v___x_2533_, 1);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2548_ = v___x_2533_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_err_2546_);
lean_inc(v_pos_2545_);
lean_dec(v___x_2533_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_pos_2545_);
lean_ctor_set(v_reuseFailAlloc_2552_, 1, v_err_2546_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURI(lean_object* v_config_2565_, lean_object* v_a_2566_){
_start:
{
lean_object* v___x_2567_; 
v___x_2567_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_2565_, v_a_2566_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_pos_2568_; lean_object* v_res_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2700_; 
v_pos_2568_ = lean_ctor_get(v___x_2567_, 0);
v_res_2569_ = lean_ctor_get(v___x_2567_, 1);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2571_ = v___x_2567_;
v_isShared_2572_ = v_isSharedCheck_2700_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_res_2569_);
lean_inc(v_pos_2568_);
lean_dec(v___x_2567_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2700_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v_array_2573_; lean_object* v_idx_2574_; lean_object* v___x_2575_; uint8_t v___x_2576_; 
v_array_2573_ = lean_ctor_get(v_pos_2568_, 0);
v_idx_2574_ = lean_ctor_get(v_pos_2568_, 1);
v___x_2575_ = lean_byte_array_size(v_array_2573_);
v___x_2576_ = lean_nat_dec_lt(v_idx_2574_, v___x_2575_);
if (v___x_2576_ == 0)
{
lean_object* v___x_2577_; lean_object* v___x_2579_; 
lean_dec(v_res_2569_);
lean_dec_ref(v_config_2565_);
v___x_2577_ = lean_box(0);
if (v_isShared_2572_ == 0)
{
lean_ctor_set_tag(v___x_2571_, 1);
lean_ctor_set(v___x_2571_, 1, v___x_2577_);
v___x_2579_ = v___x_2571_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_pos_2568_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
else
{
uint8_t v___x_2581_; uint8_t v_got_2582_; uint8_t v___x_2583_; 
v___x_2581_ = 58;
v_got_2582_ = lean_byte_array_fget(v_array_2573_, v_idx_2574_);
v___x_2583_ = lean_uint8_dec_eq(v_got_2582_, v___x_2581_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2584_; lean_object* v___x_2586_; 
lean_dec(v_res_2569_);
lean_dec_ref(v_config_2565_);
v___x_2584_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_2572_ == 0)
{
lean_ctor_set_tag(v___x_2571_, 1);
lean_ctor_set(v___x_2571_, 1, v___x_2584_);
v___x_2586_ = v___x_2571_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_pos_2568_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v___x_2584_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
else
{
lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2697_; 
lean_inc(v_idx_2574_);
lean_inc_ref(v_array_2573_);
v_isSharedCheck_2697_ = !lean_is_exclusive(v_pos_2568_);
if (v_isSharedCheck_2697_ == 0)
{
lean_object* v_unused_2698_; lean_object* v_unused_2699_; 
v_unused_2698_ = lean_ctor_get(v_pos_2568_, 1);
lean_dec(v_unused_2698_);
v_unused_2699_ = lean_ctor_get(v_pos_2568_, 0);
lean_dec(v_unused_2699_);
v___x_2589_ = v_pos_2568_;
v_isShared_2590_ = v_isSharedCheck_2697_;
goto v_resetjp_2588_;
}
else
{
lean_dec(v_pos_2568_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2697_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2594_; 
v___x_2591_ = lean_unsigned_to_nat(1u);
v___x_2592_ = lean_nat_add(v_idx_2574_, v___x_2591_);
lean_dec(v_idx_2574_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 1, v___x_2592_);
v___x_2594_ = v___x_2589_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_array_2573_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v___x_2592_);
v___x_2594_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
lean_object* v___x_2595_; 
lean_inc_ref(v_config_2565_);
v___x_2595_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2565_, v___x_2594_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_res_2596_; lean_object* v_pos_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2686_; 
v_res_2596_ = lean_ctor_get(v___x_2595_, 1);
v_pos_2597_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2599_ = v___x_2595_;
v_isShared_2600_ = v_isSharedCheck_2686_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_res_2596_);
lean_inc(v_pos_2597_);
lean_dec(v___x_2595_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2686_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v_fst_2601_; lean_object* v_snd_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2685_; 
v_fst_2601_ = lean_ctor_get(v_res_2596_, 0);
v_snd_2602_ = lean_ctor_get(v_res_2596_, 1);
v_isSharedCheck_2685_ = !lean_is_exclusive(v_res_2596_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2604_ = v_res_2596_;
v_isShared_2605_ = v_isSharedCheck_2685_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_snd_2602_);
lean_inc(v_fst_2601_);
lean_dec(v_res_2596_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2685_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___y_2607_; lean_object* v_pos_2608_; lean_object* v_res_2609_; lean_object* v_idx_2615_; lean_object* v___y_2616_; lean_object* v_pos_2617_; lean_object* v_err_2618_; lean_object* v_pos_2626_; lean_object* v_array_2627_; lean_object* v_idx_2628_; lean_object* v_res_2629_; lean_object* v_array_2648_; lean_object* v_idx_2649_; lean_object* v_pos_2651_; lean_object* v_array_2652_; lean_object* v_idx_2653_; lean_object* v_err_2654_; lean_object* v___x_2658_; uint8_t v___x_2659_; 
v_array_2648_ = lean_ctor_get(v_pos_2597_, 0);
lean_inc_ref(v_array_2648_);
v_idx_2649_ = lean_ctor_get(v_pos_2597_, 1);
lean_inc(v_idx_2649_);
v___x_2658_ = lean_byte_array_size(v_array_2648_);
v___x_2659_ = lean_nat_dec_lt(v_idx_2649_, v___x_2658_);
if (v___x_2659_ == 0)
{
lean_object* v___x_2660_; 
v___x_2660_ = lean_box(0);
lean_inc(v_idx_2649_);
v_pos_2651_ = v_pos_2597_;
v_array_2652_ = v_array_2648_;
v_idx_2653_ = v_idx_2649_;
v_err_2654_ = v___x_2660_;
goto v___jp_2650_;
}
else
{
uint8_t v___x_2661_; uint8_t v_got_2662_; uint8_t v___x_2663_; 
v___x_2661_ = 63;
v_got_2662_ = lean_byte_array_fget(v_array_2648_, v_idx_2649_);
v___x_2663_ = lean_uint8_dec_eq(v_got_2662_, v___x_2661_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; 
v___x_2664_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_2649_);
v_pos_2651_ = v_pos_2597_;
v_array_2652_ = v_array_2648_;
v_idx_2653_ = v_idx_2649_;
v_err_2654_ = v___x_2664_;
goto v___jp_2650_;
}
else
{
lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2682_; 
v_isSharedCheck_2682_ = !lean_is_exclusive(v_pos_2597_);
if (v_isSharedCheck_2682_ == 0)
{
lean_object* v_unused_2683_; lean_object* v_unused_2684_; 
v_unused_2683_ = lean_ctor_get(v_pos_2597_, 1);
lean_dec(v_unused_2683_);
v_unused_2684_ = lean_ctor_get(v_pos_2597_, 0);
lean_dec(v_unused_2684_);
v___x_2666_ = v_pos_2597_;
v_isShared_2667_ = v_isSharedCheck_2682_;
goto v_resetjp_2665_;
}
else
{
lean_dec(v_pos_2597_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2682_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2668_; lean_object* v___x_2670_; 
v___x_2668_ = lean_nat_add(v_idx_2649_, v___x_2591_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 1, v___x_2668_);
v___x_2670_ = v___x_2666_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_array_2648_);
lean_ctor_set(v_reuseFailAlloc_2681_, 1, v___x_2668_);
v___x_2670_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
lean_object* v___x_2671_; 
lean_inc_ref(v_config_2565_);
v___x_2671_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2565_, v___x_2670_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_pos_2672_; lean_object* v_res_2673_; lean_object* v_array_2674_; lean_object* v_idx_2675_; lean_object* v___x_2676_; 
lean_dec(v_idx_2649_);
v_pos_2672_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_pos_2672_);
v_res_2673_ = lean_ctor_get(v___x_2671_, 1);
lean_inc(v_res_2673_);
lean_dec_ref_known(v___x_2671_, 2);
v_array_2674_ = lean_ctor_get(v_pos_2672_, 0);
lean_inc_ref(v_array_2674_);
v_idx_2675_ = lean_ctor_get(v_pos_2672_, 1);
lean_inc(v_idx_2675_);
v___x_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2676_, 0, v_res_2673_);
v_pos_2626_ = v_pos_2672_;
v_array_2627_ = v_array_2674_;
v_idx_2628_ = v_idx_2675_;
v_res_2629_ = v___x_2676_;
goto v___jp_2625_;
}
else
{
lean_object* v_pos_2677_; lean_object* v_err_2678_; lean_object* v_array_2679_; lean_object* v_idx_2680_; 
v_pos_2677_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_pos_2677_);
v_err_2678_ = lean_ctor_get(v___x_2671_, 1);
lean_inc(v_err_2678_);
lean_dec_ref_known(v___x_2671_, 2);
v_array_2679_ = lean_ctor_get(v_pos_2677_, 0);
lean_inc_ref(v_array_2679_);
v_idx_2680_ = lean_ctor_get(v_pos_2677_, 1);
lean_inc(v_idx_2680_);
v_pos_2651_ = v_pos_2677_;
v_array_2652_ = v_array_2679_;
v_idx_2653_ = v_idx_2680_;
v_err_2654_ = v_err_2678_;
goto v___jp_2650_;
}
}
}
}
}
v___jp_2606_:
{
lean_object* v___x_2610_; lean_object* v___x_2612_; 
v___x_2610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2610_, 0, v_res_2569_);
lean_ctor_set(v___x_2610_, 1, v_fst_2601_);
lean_ctor_set(v___x_2610_, 2, v_snd_2602_);
lean_ctor_set(v___x_2610_, 3, v___y_2607_);
lean_ctor_set(v___x_2610_, 4, v_res_2609_);
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 1, v___x_2610_);
lean_ctor_set(v___x_2599_, 0, v_pos_2608_);
v___x_2612_ = v___x_2599_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_pos_2608_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v___x_2610_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
v___jp_2614_:
{
lean_object* v_idx_2619_; uint8_t v___x_2620_; 
v_idx_2619_ = lean_ctor_get(v_pos_2617_, 1);
v___x_2620_ = lean_nat_dec_eq(v_idx_2615_, v_idx_2619_);
lean_dec(v_idx_2615_);
if (v___x_2620_ == 0)
{
lean_object* v___x_2622_; 
lean_dec(v___y_2616_);
lean_dec(v_snd_2602_);
lean_dec(v_fst_2601_);
lean_del_object(v___x_2599_);
lean_dec(v_res_2569_);
if (v_isShared_2572_ == 0)
{
lean_ctor_set_tag(v___x_2571_, 1);
lean_ctor_set(v___x_2571_, 1, v_err_2618_);
lean_ctor_set(v___x_2571_, 0, v_pos_2617_);
v___x_2622_ = v___x_2571_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_pos_2617_);
lean_ctor_set(v_reuseFailAlloc_2623_, 1, v_err_2618_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
else
{
lean_object* v___x_2624_; 
lean_dec(v_err_2618_);
lean_del_object(v___x_2571_);
v___x_2624_ = lean_box(0);
v___y_2607_ = v___y_2616_;
v_pos_2608_ = v_pos_2617_;
v_res_2609_ = v___x_2624_;
goto v___jp_2606_;
}
}
v___jp_2625_:
{
lean_object* v___x_2630_; uint8_t v___x_2631_; 
v___x_2630_ = lean_byte_array_size(v_array_2627_);
v___x_2631_ = lean_nat_dec_lt(v_idx_2628_, v___x_2630_);
if (v___x_2631_ == 0)
{
lean_object* v___x_2632_; 
lean_dec_ref(v_array_2627_);
lean_del_object(v___x_2604_);
lean_dec_ref(v_config_2565_);
v___x_2632_ = lean_box(0);
v_idx_2615_ = v_idx_2628_;
v___y_2616_ = v_res_2629_;
v_pos_2617_ = v_pos_2626_;
v_err_2618_ = v___x_2632_;
goto v___jp_2614_;
}
else
{
uint8_t v___x_2633_; uint8_t v_got_2634_; uint8_t v___x_2635_; 
v___x_2633_ = 35;
v_got_2634_ = lean_byte_array_fget(v_array_2627_, v_idx_2628_);
v___x_2635_ = lean_uint8_dec_eq(v_got_2634_, v___x_2633_);
if (v___x_2635_ == 0)
{
lean_object* v___x_2636_; 
lean_dec_ref(v_array_2627_);
lean_del_object(v___x_2604_);
lean_dec_ref(v_config_2565_);
v___x_2636_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v_idx_2615_ = v_idx_2628_;
v___y_2616_ = v_res_2629_;
v_pos_2617_ = v_pos_2626_;
v_err_2618_ = v___x_2636_;
goto v___jp_2614_;
}
else
{
lean_object* v___x_2637_; lean_object* v___x_2639_; 
lean_dec_ref(v_pos_2626_);
v___x_2637_ = lean_nat_add(v_idx_2628_, v___x_2591_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 1, v___x_2637_);
lean_ctor_set(v___x_2604_, 0, v_array_2627_);
v___x_2639_ = v___x_2604_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_array_2627_);
lean_ctor_set(v_reuseFailAlloc_2647_, 1, v___x_2637_);
v___x_2639_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
lean_object* v___x_2640_; 
v___x_2640_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2565_, v___x_2639_);
lean_dec_ref(v_config_2565_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_pos_2641_; lean_object* v_res_2642_; lean_object* v___x_2643_; 
v_pos_2641_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_pos_2641_);
v_res_2642_ = lean_ctor_get(v___x_2640_, 1);
lean_inc(v_res_2642_);
lean_dec_ref_known(v___x_2640_, 2);
v___x_2643_ = l_Std_Http_URI_EncodedFragment_decode(v_res_2642_);
lean_dec(v_res_2642_);
if (lean_obj_tag(v___x_2643_) == 1)
{
lean_dec(v_idx_2628_);
lean_del_object(v___x_2571_);
v___y_2607_ = v_res_2629_;
v_pos_2608_ = v_pos_2641_;
v_res_2609_ = v___x_2643_;
goto v___jp_2606_;
}
else
{
lean_object* v___x_2644_; 
lean_dec(v___x_2643_);
v___x_2644_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__3));
v_idx_2615_ = v_idx_2628_;
v___y_2616_ = v_res_2629_;
v_pos_2617_ = v_pos_2641_;
v_err_2618_ = v___x_2644_;
goto v___jp_2614_;
}
}
else
{
lean_object* v_pos_2645_; lean_object* v_err_2646_; 
v_pos_2645_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_pos_2645_);
v_err_2646_ = lean_ctor_get(v___x_2640_, 1);
lean_inc(v_err_2646_);
lean_dec_ref_known(v___x_2640_, 2);
v_idx_2615_ = v_idx_2628_;
v___y_2616_ = v_res_2629_;
v_pos_2617_ = v_pos_2645_;
v_err_2618_ = v_err_2646_;
goto v___jp_2614_;
}
}
}
}
}
v___jp_2650_:
{
uint8_t v___x_2655_; 
v___x_2655_ = lean_nat_dec_eq(v_idx_2649_, v_idx_2653_);
lean_dec(v_idx_2649_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2656_; 
lean_dec(v_idx_2653_);
lean_dec_ref(v_array_2652_);
lean_del_object(v___x_2604_);
lean_dec(v_snd_2602_);
lean_dec(v_fst_2601_);
lean_del_object(v___x_2599_);
lean_del_object(v___x_2571_);
lean_dec(v_res_2569_);
lean_dec_ref(v_config_2565_);
v___x_2656_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2656_, 0, v_pos_2651_);
lean_ctor_set(v___x_2656_, 1, v_err_2654_);
return v___x_2656_;
}
else
{
lean_object* v___x_2657_; 
lean_dec(v_err_2654_);
v___x_2657_ = lean_box(0);
v_pos_2626_ = v_pos_2651_;
v_array_2627_ = v_array_2652_;
v_idx_2628_ = v_idx_2653_;
v_res_2629_ = v___x_2657_;
goto v___jp_2625_;
}
}
}
}
}
else
{
lean_object* v_pos_2687_; lean_object* v_err_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
lean_del_object(v___x_2571_);
lean_dec(v_res_2569_);
lean_dec_ref(v_config_2565_);
v_pos_2687_ = lean_ctor_get(v___x_2595_, 0);
v_err_2688_ = lean_ctor_get(v___x_2595_, 1);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2595_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_err_2688_);
lean_inc(v_pos_2687_);
lean_dec(v___x_2595_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_pos_2687_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v_err_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
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
lean_object* v_pos_2701_; lean_object* v_err_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
lean_dec_ref(v_config_2565_);
v_pos_2701_ = lean_ctor_get(v___x_2567_, 0);
v_err_2702_ = lean_ctor_get(v___x_2567_, 1);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2567_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_err_2702_);
lean_inc(v_pos_2701_);
lean_dec(v___x_2567_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_pos_2701_);
lean_ctor_set(v_reuseFailAlloc_2708_, 1, v_err_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(lean_object* v_a_2713_){
_start:
{
lean_object* v_array_2714_; lean_object* v_idx_2715_; lean_object* v___x_2716_; uint8_t v___x_2717_; 
v_array_2714_ = lean_ctor_get(v_a_2713_, 0);
v_idx_2715_ = lean_ctor_get(v_a_2713_, 1);
v___x_2716_ = lean_byte_array_size(v_array_2714_);
v___x_2717_ = lean_nat_dec_lt(v_idx_2715_, v___x_2716_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2718_ = lean_box(0);
v___x_2719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2719_, 0, v_a_2713_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
return v___x_2719_;
}
else
{
uint8_t v___x_2720_; uint8_t v_got_2721_; uint8_t v___x_2722_; 
v___x_2720_ = 42;
v_got_2721_ = lean_byte_array_fget(v_array_2714_, v_idx_2715_);
v___x_2722_ = lean_uint8_dec_eq(v_got_2721_, v___x_2720_);
if (v___x_2722_ == 0)
{
lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2723_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1));
v___x_2724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2724_, 0, v_a_2713_);
lean_ctor_set(v___x_2724_, 1, v___x_2723_);
return v___x_2724_;
}
else
{
lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2735_; 
lean_inc(v_idx_2715_);
lean_inc_ref(v_array_2714_);
v_isSharedCheck_2735_ = !lean_is_exclusive(v_a_2713_);
if (v_isSharedCheck_2735_ == 0)
{
lean_object* v_unused_2736_; lean_object* v_unused_2737_; 
v_unused_2736_ = lean_ctor_get(v_a_2713_, 1);
lean_dec(v_unused_2736_);
v_unused_2737_ = lean_ctor_get(v_a_2713_, 0);
lean_dec(v_unused_2737_);
v___x_2726_ = v_a_2713_;
v_isShared_2727_ = v_isSharedCheck_2735_;
goto v_resetjp_2725_;
}
else
{
lean_dec(v_a_2713_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2735_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2731_; 
v___x_2728_ = lean_unsigned_to_nat(1u);
v___x_2729_ = lean_nat_add(v_idx_2715_, v___x_2728_);
lean_dec(v_idx_2715_);
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 1, v___x_2729_);
v___x_2731_ = v___x_2726_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_array_2714_);
lean_ctor_set(v_reuseFailAlloc_2734_, 1, v___x_2729_);
v___x_2731_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2732_ = lean_box(3);
v___x_2733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2731_);
lean_ctor_set(v___x_2733_, 1, v___x_2732_);
return v___x_2733_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(lean_object* v_config_2741_, lean_object* v_a_2742_){
_start:
{
lean_object* v_array_2746_; lean_object* v_idx_2747_; lean_object* v___x_2748_; uint8_t v___x_2749_; 
v_array_2746_ = lean_ctor_get(v_a_2742_, 0);
v_idx_2747_ = lean_ctor_get(v_a_2742_, 1);
v___x_2748_ = lean_byte_array_size(v_array_2746_);
v___x_2749_ = lean_nat_dec_lt(v_idx_2747_, v___x_2748_);
if (v___x_2749_ == 0)
{
lean_dec_ref(v_config_2741_);
goto v___jp_2743_;
}
else
{
uint8_t v___x_2750_; uint8_t v___x_2751_; uint8_t v___x_2752_; 
v___x_2750_ = lean_byte_array_fget(v_array_2746_, v_idx_2747_);
v___x_2751_ = 47;
v___x_2752_ = lean_uint8_dec_eq(v___x_2750_, v___x_2751_);
if (v___x_2752_ == 0)
{
lean_dec_ref(v_config_2741_);
goto v___jp_2743_;
}
else
{
lean_object* v___x_2753_; 
lean_inc_ref(v_a_2742_);
lean_inc_ref(v_config_2741_);
v___x_2753_ = l_Std_Http_URI_Parser_parsePath(v_config_2741_, v___x_2752_, v___x_2752_, v_a_2742_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v_pos_2754_; lean_object* v_res_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2800_; 
v_pos_2754_ = lean_ctor_get(v___x_2753_, 0);
v_res_2755_ = lean_ctor_get(v___x_2753_, 1);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2757_ = v___x_2753_;
v_isShared_2758_ = v_isSharedCheck_2800_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_res_2755_);
lean_inc(v_pos_2754_);
lean_dec(v___x_2753_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2800_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v_pos_2760_; lean_object* v_res_2761_; lean_object* v_array_2766_; lean_object* v_idx_2767_; lean_object* v_pos_2769_; lean_object* v_idx_2770_; lean_object* v_err_2771_; lean_object* v___x_2775_; uint8_t v___x_2776_; 
v_array_2766_ = lean_ctor_get(v_pos_2754_, 0);
v_idx_2767_ = lean_ctor_get(v_pos_2754_, 1);
lean_inc(v_idx_2767_);
v___x_2775_ = lean_byte_array_size(v_array_2766_);
v___x_2776_ = lean_nat_dec_lt(v_idx_2767_, v___x_2775_);
if (v___x_2776_ == 0)
{
lean_object* v___x_2777_; 
lean_dec_ref(v_config_2741_);
v___x_2777_ = lean_box(0);
lean_inc(v_idx_2767_);
v_pos_2769_ = v_pos_2754_;
v_idx_2770_ = v_idx_2767_;
v_err_2771_ = v___x_2777_;
goto v___jp_2768_;
}
else
{
uint8_t v___x_2778_; uint8_t v_got_2779_; uint8_t v___x_2780_; 
v___x_2778_ = 63;
v_got_2779_ = lean_byte_array_fget(v_array_2766_, v_idx_2767_);
v___x_2780_ = lean_uint8_dec_eq(v_got_2779_, v___x_2778_);
if (v___x_2780_ == 0)
{
lean_object* v___x_2781_; 
lean_dec_ref(v_config_2741_);
v___x_2781_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_2767_);
v_pos_2769_ = v_pos_2754_;
v_idx_2770_ = v_idx_2767_;
v_err_2771_ = v___x_2781_;
goto v___jp_2768_;
}
else
{
lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2797_; 
lean_inc_ref(v_array_2766_);
v_isSharedCheck_2797_ = !lean_is_exclusive(v_pos_2754_);
if (v_isSharedCheck_2797_ == 0)
{
lean_object* v_unused_2798_; lean_object* v_unused_2799_; 
v_unused_2798_ = lean_ctor_get(v_pos_2754_, 1);
lean_dec(v_unused_2798_);
v_unused_2799_ = lean_ctor_get(v_pos_2754_, 0);
lean_dec(v_unused_2799_);
v___x_2783_ = v_pos_2754_;
v_isShared_2784_ = v_isSharedCheck_2797_;
goto v_resetjp_2782_;
}
else
{
lean_dec(v_pos_2754_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2797_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2788_; 
v___x_2785_ = lean_unsigned_to_nat(1u);
v___x_2786_ = lean_nat_add(v_idx_2767_, v___x_2785_);
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 1, v___x_2786_);
v___x_2788_ = v___x_2783_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_array_2766_);
lean_ctor_set(v_reuseFailAlloc_2796_, 1, v___x_2786_);
v___x_2788_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
lean_object* v___x_2789_; 
v___x_2789_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2741_, v___x_2788_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_pos_2790_; lean_object* v_res_2791_; lean_object* v___x_2792_; 
lean_dec(v_idx_2767_);
lean_dec_ref(v_a_2742_);
v_pos_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_pos_2790_);
v_res_2791_ = lean_ctor_get(v___x_2789_, 1);
lean_inc(v_res_2791_);
lean_dec_ref_known(v___x_2789_, 2);
v___x_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2792_, 0, v_res_2791_);
v_pos_2760_ = v_pos_2790_;
v_res_2761_ = v___x_2792_;
goto v___jp_2759_;
}
else
{
lean_object* v_pos_2793_; lean_object* v_err_2794_; lean_object* v_idx_2795_; 
v_pos_2793_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_pos_2793_);
v_err_2794_ = lean_ctor_get(v___x_2789_, 1);
lean_inc(v_err_2794_);
lean_dec_ref_known(v___x_2789_, 2);
v_idx_2795_ = lean_ctor_get(v_pos_2793_, 1);
lean_inc(v_idx_2795_);
v_pos_2769_ = v_pos_2793_;
v_idx_2770_ = v_idx_2795_;
v_err_2771_ = v_err_2794_;
goto v___jp_2768_;
}
}
}
}
}
v___jp_2759_:
{
lean_object* v___x_2762_; lean_object* v___x_2764_; 
v___x_2762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2762_, 0, v_res_2755_);
lean_ctor_set(v___x_2762_, 1, v_res_2761_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 1, v___x_2762_);
lean_ctor_set(v___x_2757_, 0, v_pos_2760_);
v___x_2764_ = v___x_2757_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_pos_2760_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v___x_2762_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
v___jp_2768_:
{
uint8_t v___x_2772_; 
v___x_2772_ = lean_nat_dec_eq(v_idx_2767_, v_idx_2770_);
lean_dec(v_idx_2770_);
lean_dec(v_idx_2767_);
if (v___x_2772_ == 0)
{
lean_object* v___x_2773_; 
lean_dec_ref(v_pos_2769_);
lean_del_object(v___x_2757_);
lean_dec(v_res_2755_);
v___x_2773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2773_, 0, v_a_2742_);
lean_ctor_set(v___x_2773_, 1, v_err_2771_);
return v___x_2773_;
}
else
{
lean_object* v___x_2774_; 
lean_dec(v_err_2771_);
lean_dec_ref(v_a_2742_);
v___x_2774_ = lean_box(0);
v_pos_2760_ = v_pos_2769_;
v_res_2761_ = v___x_2774_;
goto v___jp_2759_;
}
}
}
}
else
{
lean_object* v_err_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_dec_ref(v_config_2741_);
v_err_2801_ = lean_ctor_get(v___x_2753_, 1);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2808_ == 0)
{
lean_object* v_unused_2809_; 
v_unused_2809_ = lean_ctor_get(v___x_2753_, 0);
lean_dec(v_unused_2809_);
v___x_2803_ = v___x_2753_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_err_2801_);
lean_dec(v___x_2753_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 0, v_a_2742_);
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2742_);
lean_ctor_set(v_reuseFailAlloc_2807_, 1, v_err_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
}
v___jp_2743_:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2744_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1));
v___x_2745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2745_, 0, v_a_2742_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
return v___x_2745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(lean_object* v_config_2810_, lean_object* v_scheme_2811_, lean_object* v_a_2812_){
_start:
{
lean_object* v_array_2813_; lean_object* v_idx_2814_; lean_object* v___x_2815_; uint8_t v___x_2816_; 
v_array_2813_ = lean_ctor_get(v_a_2812_, 0);
v_idx_2814_ = lean_ctor_get(v_a_2812_, 1);
v___x_2815_ = lean_byte_array_size(v_array_2813_);
v___x_2816_ = lean_nat_dec_lt(v_idx_2814_, v___x_2815_);
if (v___x_2816_ == 0)
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
lean_dec_ref(v_scheme_2811_);
lean_dec_ref(v_config_2810_);
v___x_2817_ = lean_box(0);
v___x_2818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2818_, 0, v_a_2812_);
lean_ctor_set(v___x_2818_, 1, v___x_2817_);
return v___x_2818_;
}
else
{
uint8_t v___x_2819_; uint8_t v_got_2820_; uint8_t v___x_2821_; 
v___x_2819_ = 58;
v_got_2820_ = lean_byte_array_fget(v_array_2813_, v_idx_2814_);
v___x_2821_ = lean_uint8_dec_eq(v_got_2820_, v___x_2819_);
if (v___x_2821_ == 0)
{
lean_object* v___x_2822_; lean_object* v___x_2823_; 
lean_dec_ref(v_scheme_2811_);
lean_dec_ref(v_config_2810_);
v___x_2822_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
v___x_2823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2823_, 0, v_a_2812_);
lean_ctor_set(v___x_2823_, 1, v___x_2822_);
return v___x_2823_;
}
else
{
lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2898_; 
lean_inc(v_idx_2814_);
lean_inc_ref(v_array_2813_);
v_isSharedCheck_2898_ = !lean_is_exclusive(v_a_2812_);
if (v_isSharedCheck_2898_ == 0)
{
lean_object* v_unused_2899_; lean_object* v_unused_2900_; 
v_unused_2899_ = lean_ctor_get(v_a_2812_, 1);
lean_dec(v_unused_2899_);
v_unused_2900_ = lean_ctor_get(v_a_2812_, 0);
lean_dec(v_unused_2900_);
v___x_2825_ = v_a_2812_;
v_isShared_2826_ = v_isSharedCheck_2898_;
goto v_resetjp_2824_;
}
else
{
lean_dec(v_a_2812_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2898_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2830_; 
v___x_2827_ = lean_unsigned_to_nat(1u);
v___x_2828_ = lean_nat_add(v_idx_2814_, v___x_2827_);
lean_dec(v_idx_2814_);
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 1, v___x_2828_);
v___x_2830_ = v___x_2825_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_array_2813_);
lean_ctor_set(v_reuseFailAlloc_2897_, 1, v___x_2828_);
v___x_2830_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
lean_object* v___x_2831_; 
lean_inc_ref(v_config_2810_);
v___x_2831_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2810_, v___x_2830_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_res_2832_; lean_object* v_pos_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2887_; 
v_res_2832_ = lean_ctor_get(v___x_2831_, 1);
v_pos_2833_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2835_ = v___x_2831_;
v_isShared_2836_ = v_isSharedCheck_2887_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_res_2832_);
lean_inc(v_pos_2833_);
lean_dec(v___x_2831_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2887_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v_fst_2837_; lean_object* v_snd_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2886_; 
v_fst_2837_ = lean_ctor_get(v_res_2832_, 0);
v_snd_2838_ = lean_ctor_get(v_res_2832_, 1);
v_isSharedCheck_2886_ = !lean_is_exclusive(v_res_2832_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2840_ = v_res_2832_;
v_isShared_2841_ = v_isSharedCheck_2886_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_snd_2838_);
lean_inc(v_fst_2837_);
lean_dec(v_res_2832_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2886_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v_pos_2843_; lean_object* v_res_2844_; lean_object* v_array_2851_; lean_object* v_idx_2852_; lean_object* v_pos_2854_; lean_object* v_idx_2855_; lean_object* v_err_2856_; lean_object* v___x_2862_; uint8_t v___x_2863_; 
v_array_2851_ = lean_ctor_get(v_pos_2833_, 0);
v_idx_2852_ = lean_ctor_get(v_pos_2833_, 1);
lean_inc(v_idx_2852_);
v___x_2862_ = lean_byte_array_size(v_array_2851_);
v___x_2863_ = lean_nat_dec_lt(v_idx_2852_, v___x_2862_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2864_; 
lean_dec_ref(v_config_2810_);
v___x_2864_ = lean_box(0);
lean_inc(v_idx_2852_);
v_pos_2854_ = v_pos_2833_;
v_idx_2855_ = v_idx_2852_;
v_err_2856_ = v___x_2864_;
goto v___jp_2853_;
}
else
{
uint8_t v___x_2865_; uint8_t v_got_2866_; uint8_t v___x_2867_; 
v___x_2865_ = 63;
v_got_2866_ = lean_byte_array_fget(v_array_2851_, v_idx_2852_);
v___x_2867_ = lean_uint8_dec_eq(v_got_2866_, v___x_2865_);
if (v___x_2867_ == 0)
{
lean_object* v___x_2868_; 
lean_dec_ref(v_config_2810_);
v___x_2868_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_2852_);
v_pos_2854_ = v_pos_2833_;
v_idx_2855_ = v_idx_2852_;
v_err_2856_ = v___x_2868_;
goto v___jp_2853_;
}
else
{
lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2883_; 
lean_inc_ref(v_array_2851_);
v_isSharedCheck_2883_ = !lean_is_exclusive(v_pos_2833_);
if (v_isSharedCheck_2883_ == 0)
{
lean_object* v_unused_2884_; lean_object* v_unused_2885_; 
v_unused_2884_ = lean_ctor_get(v_pos_2833_, 1);
lean_dec(v_unused_2884_);
v_unused_2885_ = lean_ctor_get(v_pos_2833_, 0);
lean_dec(v_unused_2885_);
v___x_2870_ = v_pos_2833_;
v_isShared_2871_ = v_isSharedCheck_2883_;
goto v_resetjp_2869_;
}
else
{
lean_dec(v_pos_2833_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2883_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2872_; lean_object* v___x_2874_; 
v___x_2872_ = lean_nat_add(v_idx_2852_, v___x_2827_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 1, v___x_2872_);
v___x_2874_ = v___x_2870_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_array_2851_);
lean_ctor_set(v_reuseFailAlloc_2882_, 1, v___x_2872_);
v___x_2874_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
lean_object* v___x_2875_; 
v___x_2875_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2810_, v___x_2874_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_pos_2876_; lean_object* v_res_2877_; lean_object* v___x_2878_; 
lean_dec(v_idx_2852_);
lean_del_object(v___x_2840_);
v_pos_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_pos_2876_);
v_res_2877_ = lean_ctor_get(v___x_2875_, 1);
lean_inc(v_res_2877_);
lean_dec_ref_known(v___x_2875_, 2);
v___x_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2878_, 0, v_res_2877_);
v_pos_2843_ = v_pos_2876_;
v_res_2844_ = v___x_2878_;
goto v___jp_2842_;
}
else
{
lean_object* v_pos_2879_; lean_object* v_err_2880_; lean_object* v_idx_2881_; 
v_pos_2879_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_pos_2879_);
v_err_2880_ = lean_ctor_get(v___x_2875_, 1);
lean_inc(v_err_2880_);
lean_dec_ref_known(v___x_2875_, 2);
v_idx_2881_ = lean_ctor_get(v_pos_2879_, 1);
lean_inc(v_idx_2881_);
v_pos_2854_ = v_pos_2879_;
v_idx_2855_ = v_idx_2881_;
v_err_2856_ = v_err_2880_;
goto v___jp_2853_;
}
}
}
}
}
v___jp_2842_:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2849_; 
v___x_2845_ = lean_box(0);
v___x_2846_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2846_, 0, v_scheme_2811_);
lean_ctor_set(v___x_2846_, 1, v_fst_2837_);
lean_ctor_set(v___x_2846_, 2, v_snd_2838_);
lean_ctor_set(v___x_2846_, 3, v_res_2844_);
lean_ctor_set(v___x_2846_, 4, v___x_2845_);
v___x_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 1, v___x_2847_);
lean_ctor_set(v___x_2835_, 0, v_pos_2843_);
v___x_2849_ = v___x_2835_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_pos_2843_);
lean_ctor_set(v_reuseFailAlloc_2850_, 1, v___x_2847_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
v___jp_2853_:
{
uint8_t v___x_2857_; 
v___x_2857_ = lean_nat_dec_eq(v_idx_2852_, v_idx_2855_);
lean_dec(v_idx_2855_);
lean_dec(v_idx_2852_);
if (v___x_2857_ == 0)
{
lean_object* v___x_2859_; 
lean_dec(v_snd_2838_);
lean_dec(v_fst_2837_);
lean_del_object(v___x_2835_);
lean_dec_ref(v_scheme_2811_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set_tag(v___x_2840_, 1);
lean_ctor_set(v___x_2840_, 1, v_err_2856_);
lean_ctor_set(v___x_2840_, 0, v_pos_2854_);
v___x_2859_ = v___x_2840_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_pos_2854_);
lean_ctor_set(v_reuseFailAlloc_2860_, 1, v_err_2856_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
else
{
lean_object* v___x_2861_; 
lean_dec(v_err_2856_);
lean_del_object(v___x_2840_);
v___x_2861_ = lean_box(0);
v_pos_2843_ = v_pos_2854_;
v_res_2844_ = v___x_2861_;
goto v___jp_2842_;
}
}
}
}
}
else
{
lean_object* v_pos_2888_; lean_object* v_err_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
lean_dec_ref(v_scheme_2811_);
lean_dec_ref(v_config_2810_);
v_pos_2888_ = lean_ctor_get(v___x_2831_, 0);
v_err_2889_ = lean_ctor_get(v___x_2831_, 1);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2831_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_err_2889_);
lean_inc(v_pos_2888_);
lean_dec(v___x_2831_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_pos_2888_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v_err_2889_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(lean_object* v_config_2909_, lean_object* v_a_2910_){
_start:
{
lean_object* v___x_2914_; 
lean_inc_ref(v_a_2910_);
v___x_2914_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_2909_, v_a_2910_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_pos_2915_; lean_object* v_res_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_3012_; 
v_pos_2915_ = lean_ctor_get(v___x_2914_, 0);
v_res_2916_ = lean_ctor_get(v___x_2914_, 1);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_2918_ = v___x_2914_;
v_isShared_2919_ = v_isSharedCheck_3012_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_res_2916_);
lean_inc(v_pos_2915_);
lean_dec(v___x_2914_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_3012_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v_pos_2923_; lean_object* v_res_2924_; lean_object* v___y_2932_; lean_object* v_idx_2933_; lean_object* v___y_2934_; lean_object* v_pos_2935_; lean_object* v_idx_2936_; lean_object* v_err_2937_; lean_object* v___x_3006_; uint8_t v___x_3007_; 
v___x_3006_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2));
v___x_3007_ = lean_string_dec_eq(v_res_2916_, v___x_3006_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; uint8_t v___x_3009_; 
v___x_3008_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3));
v___x_3009_ = lean_string_dec_eq(v_res_2916_, v___x_3008_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; lean_object* v___x_3011_; 
lean_del_object(v___x_2918_);
lean_dec(v_res_2916_);
lean_dec(v_pos_2915_);
lean_dec_ref(v_config_2909_);
v___x_3010_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5));
v___x_3011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3011_, 0, v_a_2910_);
lean_ctor_set(v___x_3011_, 1, v___x_3010_);
return v___x_3011_;
}
else
{
goto v___jp_2941_;
}
}
else
{
goto v___jp_2941_;
}
v___jp_2920_:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2929_; 
v___x_2925_ = lean_box(0);
v___x_2926_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2926_, 0, v_res_2916_);
lean_ctor_set(v___x_2926_, 1, v___y_2921_);
lean_ctor_set(v___x_2926_, 2, v___y_2922_);
lean_ctor_set(v___x_2926_, 3, v_res_2924_);
lean_ctor_set(v___x_2926_, 4, v___x_2925_);
v___x_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 1, v___x_2927_);
lean_ctor_set(v___x_2918_, 0, v_pos_2923_);
v___x_2929_ = v___x_2918_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_pos_2923_);
lean_ctor_set(v_reuseFailAlloc_2930_, 1, v___x_2927_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
v___jp_2931_:
{
uint8_t v___x_2938_; 
v___x_2938_ = lean_nat_dec_eq(v_idx_2933_, v_idx_2936_);
lean_dec(v_idx_2936_);
lean_dec(v_idx_2933_);
if (v___x_2938_ == 0)
{
lean_object* v___x_2939_; 
lean_dec_ref(v_pos_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2932_);
lean_del_object(v___x_2918_);
lean_dec(v_res_2916_);
v___x_2939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2939_, 0, v_a_2910_);
lean_ctor_set(v___x_2939_, 1, v_err_2937_);
return v___x_2939_;
}
else
{
lean_object* v___x_2940_; 
lean_dec(v_err_2937_);
lean_dec_ref(v_a_2910_);
v___x_2940_ = lean_box(0);
v___y_2921_ = v___y_2932_;
v___y_2922_ = v___y_2934_;
v_pos_2923_ = v_pos_2935_;
v_res_2924_ = v___x_2940_;
goto v___jp_2920_;
}
}
v___jp_2941_:
{
lean_object* v_array_2942_; lean_object* v_idx_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_3005_; 
v_array_2942_ = lean_ctor_get(v_pos_2915_, 0);
v_idx_2943_ = lean_ctor_get(v_pos_2915_, 1);
v_isSharedCheck_3005_ = !lean_is_exclusive(v_pos_2915_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_2945_ = v_pos_2915_;
v_isShared_2946_ = v_isSharedCheck_3005_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_idx_2943_);
lean_inc(v_array_2942_);
lean_dec(v_pos_2915_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_3005_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2947_; uint8_t v___x_2948_; 
v___x_2947_ = lean_byte_array_size(v_array_2942_);
v___x_2948_ = lean_nat_dec_lt(v_idx_2943_, v___x_2947_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
lean_del_object(v___x_2945_);
lean_dec(v_idx_2943_);
lean_dec_ref(v_array_2942_);
lean_del_object(v___x_2918_);
lean_dec(v_res_2916_);
lean_dec_ref(v_config_2909_);
v___x_2949_ = lean_box(0);
v___x_2950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2950_, 0, v_a_2910_);
lean_ctor_set(v___x_2950_, 1, v___x_2949_);
return v___x_2950_;
}
else
{
uint8_t v___x_2951_; uint8_t v_got_2952_; uint8_t v___x_2953_; 
v___x_2951_ = 58;
v_got_2952_ = lean_byte_array_fget(v_array_2942_, v_idx_2943_);
v___x_2953_ = lean_uint8_dec_eq(v_got_2952_, v___x_2951_);
if (v___x_2953_ == 0)
{
lean_object* v___x_2954_; lean_object* v___x_2955_; 
lean_del_object(v___x_2945_);
lean_dec(v_idx_2943_);
lean_dec_ref(v_array_2942_);
lean_del_object(v___x_2918_);
lean_dec(v_res_2916_);
lean_dec_ref(v_config_2909_);
v___x_2954_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
v___x_2955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2955_, 0, v_a_2910_);
lean_ctor_set(v___x_2955_, 1, v___x_2954_);
return v___x_2955_;
}
else
{
lean_object* v___x_2956_; lean_object* v___x_2957_; uint8_t v___x_2958_; 
v___x_2956_ = lean_unsigned_to_nat(1u);
v___x_2957_ = lean_nat_add(v_idx_2943_, v___x_2956_);
lean_dec(v_idx_2943_);
v___x_2958_ = lean_nat_dec_lt(v___x_2957_, v___x_2947_);
if (v___x_2958_ == 0)
{
lean_dec(v___x_2957_);
lean_del_object(v___x_2945_);
lean_dec_ref(v_array_2942_);
lean_del_object(v___x_2918_);
lean_dec(v_res_2916_);
lean_dec_ref(v_config_2909_);
goto v___jp_2911_;
}
else
{
uint8_t v___x_2959_; uint8_t v___x_2960_; uint8_t v___x_2961_; 
v___x_2959_ = lean_byte_array_fget(v_array_2942_, v___x_2957_);
v___x_2960_ = 47;
v___x_2961_ = lean_uint8_dec_eq(v___x_2959_, v___x_2960_);
if (v___x_2961_ == 0)
{
lean_dec(v___x_2957_);
lean_del_object(v___x_2945_);
lean_dec_ref(v_array_2942_);
lean_del_object(v___x_2918_);
lean_dec(v_res_2916_);
lean_dec_ref(v_config_2909_);
goto v___jp_2911_;
}
else
{
lean_object* v___x_2963_; 
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 1, v___x_2957_);
v___x_2963_ = v___x_2945_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_array_2942_);
lean_ctor_set(v_reuseFailAlloc_3004_, 1, v___x_2957_);
v___x_2963_ = v_reuseFailAlloc_3004_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
lean_object* v___x_2964_; 
lean_inc_ref(v_config_2909_);
v___x_2964_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2909_, v___x_2963_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_res_2965_; lean_object* v_pos_2966_; lean_object* v_fst_2967_; lean_object* v_snd_2968_; lean_object* v_array_2969_; lean_object* v_idx_2970_; lean_object* v___x_2971_; uint8_t v___x_2972_; 
v_res_2965_ = lean_ctor_get(v___x_2964_, 1);
lean_inc(v_res_2965_);
v_pos_2966_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_pos_2966_);
lean_dec_ref_known(v___x_2964_, 2);
v_fst_2967_ = lean_ctor_get(v_res_2965_, 0);
lean_inc(v_fst_2967_);
v_snd_2968_ = lean_ctor_get(v_res_2965_, 1);
lean_inc(v_snd_2968_);
lean_dec(v_res_2965_);
v_array_2969_ = lean_ctor_get(v_pos_2966_, 0);
v_idx_2970_ = lean_ctor_get(v_pos_2966_, 1);
lean_inc(v_idx_2970_);
v___x_2971_ = lean_byte_array_size(v_array_2969_);
v___x_2972_ = lean_nat_dec_lt(v_idx_2970_, v___x_2971_);
if (v___x_2972_ == 0)
{
lean_object* v___x_2973_; 
lean_dec_ref(v_config_2909_);
v___x_2973_ = lean_box(0);
lean_inc(v_idx_2970_);
v___y_2932_ = v_fst_2967_;
v_idx_2933_ = v_idx_2970_;
v___y_2934_ = v_snd_2968_;
v_pos_2935_ = v_pos_2966_;
v_idx_2936_ = v_idx_2970_;
v_err_2937_ = v___x_2973_;
goto v___jp_2931_;
}
else
{
uint8_t v___x_2974_; uint8_t v_got_2975_; uint8_t v___x_2976_; 
v___x_2974_ = 63;
v_got_2975_ = lean_byte_array_fget(v_array_2969_, v_idx_2970_);
v___x_2976_ = lean_uint8_dec_eq(v_got_2975_, v___x_2974_);
if (v___x_2976_ == 0)
{
lean_object* v___x_2977_; 
lean_dec_ref(v_config_2909_);
v___x_2977_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_2970_);
v___y_2932_ = v_fst_2967_;
v_idx_2933_ = v_idx_2970_;
v___y_2934_ = v_snd_2968_;
v_pos_2935_ = v_pos_2966_;
v_idx_2936_ = v_idx_2970_;
v_err_2937_ = v___x_2977_;
goto v___jp_2931_;
}
else
{
lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2992_; 
lean_inc_ref(v_array_2969_);
v_isSharedCheck_2992_ = !lean_is_exclusive(v_pos_2966_);
if (v_isSharedCheck_2992_ == 0)
{
lean_object* v_unused_2993_; lean_object* v_unused_2994_; 
v_unused_2993_ = lean_ctor_get(v_pos_2966_, 1);
lean_dec(v_unused_2993_);
v_unused_2994_ = lean_ctor_get(v_pos_2966_, 0);
lean_dec(v_unused_2994_);
v___x_2979_ = v_pos_2966_;
v_isShared_2980_ = v_isSharedCheck_2992_;
goto v_resetjp_2978_;
}
else
{
lean_dec(v_pos_2966_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2992_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2981_; lean_object* v___x_2983_; 
v___x_2981_ = lean_nat_add(v_idx_2970_, v___x_2956_);
if (v_isShared_2980_ == 0)
{
lean_ctor_set(v___x_2979_, 1, v___x_2981_);
v___x_2983_ = v___x_2979_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_array_2969_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v___x_2981_);
v___x_2983_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
lean_object* v___x_2984_; 
v___x_2984_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2909_, v___x_2983_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v_pos_2985_; lean_object* v_res_2986_; lean_object* v___x_2987_; 
lean_dec(v_idx_2970_);
lean_dec_ref(v_a_2910_);
v_pos_2985_ = lean_ctor_get(v___x_2984_, 0);
lean_inc(v_pos_2985_);
v_res_2986_ = lean_ctor_get(v___x_2984_, 1);
lean_inc(v_res_2986_);
lean_dec_ref_known(v___x_2984_, 2);
v___x_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2987_, 0, v_res_2986_);
v___y_2921_ = v_fst_2967_;
v___y_2922_ = v_snd_2968_;
v_pos_2923_ = v_pos_2985_;
v_res_2924_ = v___x_2987_;
goto v___jp_2920_;
}
else
{
lean_object* v_pos_2988_; lean_object* v_err_2989_; lean_object* v_idx_2990_; 
v_pos_2988_ = lean_ctor_get(v___x_2984_, 0);
lean_inc(v_pos_2988_);
v_err_2989_ = lean_ctor_get(v___x_2984_, 1);
lean_inc(v_err_2989_);
lean_dec_ref_known(v___x_2984_, 2);
v_idx_2990_ = lean_ctor_get(v_pos_2988_, 1);
lean_inc(v_idx_2990_);
v___y_2932_ = v_fst_2967_;
v_idx_2933_ = v_idx_2970_;
v___y_2934_ = v_snd_2968_;
v_pos_2935_ = v_pos_2988_;
v_idx_2936_ = v_idx_2990_;
v_err_2937_ = v_err_2989_;
goto v___jp_2931_;
}
}
}
}
}
}
else
{
lean_object* v_err_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
lean_del_object(v___x_2918_);
lean_dec(v_res_2916_);
lean_dec_ref(v_config_2909_);
v_err_2995_ = lean_ctor_get(v___x_2964_, 1);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_3002_ == 0)
{
lean_object* v_unused_3003_; 
v_unused_3003_ = lean_ctor_get(v___x_2964_, 0);
lean_dec(v_unused_3003_);
v___x_2997_ = v___x_2964_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_err_2995_);
lean_dec(v___x_2964_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 0, v_a_2910_);
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2910_);
lean_ctor_set(v_reuseFailAlloc_3001_, 1, v_err_2995_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
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
lean_object* v_err_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
lean_dec_ref(v_config_2909_);
v_err_3013_ = lean_ctor_get(v___x_2914_, 1);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_3020_ == 0)
{
lean_object* v_unused_3021_; 
v_unused_3021_ = lean_ctor_get(v___x_2914_, 0);
lean_dec(v_unused_3021_);
v___x_3015_ = v___x_2914_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_err_3013_);
lean_dec(v___x_2914_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3018_; 
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 0, v_a_2910_);
v___x_3018_ = v___x_3015_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_2910_);
lean_ctor_set(v_reuseFailAlloc_3019_, 1, v_err_3013_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
v___jp_2911_:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2912_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1));
v___x_2913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2913_, 0, v_a_2910_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
return v___x_2913_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(lean_object* v_config_3022_, lean_object* v_a_3023_){
_start:
{
lean_object* v___x_3024_; 
lean_inc_ref(v_a_3023_);
v___x_3024_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3022_, v_a_3023_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_pos_3025_; lean_object* v_res_3026_; lean_object* v___x_3027_; 
v_pos_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_pos_3025_);
v_res_3026_ = lean_ctor_get(v___x_3024_, 1);
lean_inc(v_res_3026_);
lean_dec_ref_known(v___x_3024_, 2);
v___x_3027_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(v_config_3022_, v_res_3026_, v_pos_3025_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_dec_ref(v_a_3023_);
return v___x_3027_;
}
else
{
lean_object* v_err_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
v_err_3028_ = lean_ctor_get(v___x_3027_, 1);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3035_ == 0)
{
lean_object* v_unused_3036_; 
v_unused_3036_ = lean_ctor_get(v___x_3027_, 0);
lean_dec(v_unused_3036_);
v___x_3030_ = v___x_3027_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_err_3028_);
lean_dec(v___x_3027_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 0, v_a_3023_);
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3023_);
lean_ctor_set(v_reuseFailAlloc_3034_, 1, v_err_3028_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
}
else
{
lean_object* v_err_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec_ref(v_config_3022_);
v_err_3037_ = lean_ctor_get(v___x_3024_, 1);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3044_ == 0)
{
lean_object* v_unused_3045_; 
v_unused_3045_ = lean_ctor_get(v___x_3024_, 0);
lean_dec(v_unused_3045_);
v___x_3039_ = v___x_3024_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_err_3037_);
lean_dec(v___x_3024_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 0, v_a_3023_);
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3023_);
lean_ctor_set(v_reuseFailAlloc_3043_, 1, v_err_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(lean_object* v_config_3046_, lean_object* v_a_3047_){
_start:
{
lean_object* v___x_3048_; 
lean_inc_ref(v_a_3047_);
v___x_3048_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_3046_, v_a_3047_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_pos_3049_; lean_object* v_res_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3102_; 
v_pos_3049_ = lean_ctor_get(v___x_3048_, 0);
v_res_3050_ = lean_ctor_get(v___x_3048_, 1);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3052_ = v___x_3048_;
v_isShared_3053_ = v_isSharedCheck_3102_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_res_3050_);
lean_inc(v_pos_3049_);
lean_dec(v___x_3048_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3102_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v_array_3054_; lean_object* v_idx_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3101_; 
v_array_3054_ = lean_ctor_get(v_pos_3049_, 0);
v_idx_3055_ = lean_ctor_get(v_pos_3049_, 1);
v_isSharedCheck_3101_ = !lean_is_exclusive(v_pos_3049_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3057_ = v_pos_3049_;
v_isShared_3058_ = v_isSharedCheck_3101_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_idx_3055_);
lean_inc(v_array_3054_);
lean_dec(v_pos_3049_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3101_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3059_; uint8_t v___x_3060_; 
v___x_3059_ = lean_byte_array_size(v_array_3054_);
v___x_3060_ = lean_nat_dec_lt(v_idx_3055_, v___x_3059_);
if (v___x_3060_ == 0)
{
lean_object* v___x_3061_; lean_object* v___x_3063_; 
lean_del_object(v___x_3057_);
lean_dec(v_idx_3055_);
lean_dec_ref(v_array_3054_);
lean_dec(v_res_3050_);
v___x_3061_ = lean_box(0);
if (v_isShared_3053_ == 0)
{
lean_ctor_set_tag(v___x_3052_, 1);
lean_ctor_set(v___x_3052_, 1, v___x_3061_);
lean_ctor_set(v___x_3052_, 0, v_a_3047_);
v___x_3063_ = v___x_3052_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3047_);
lean_ctor_set(v_reuseFailAlloc_3064_, 1, v___x_3061_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
else
{
uint8_t v___x_3065_; uint8_t v_got_3066_; uint8_t v___x_3067_; 
v___x_3065_ = 58;
v_got_3066_ = lean_byte_array_fget(v_array_3054_, v_idx_3055_);
v___x_3067_ = lean_uint8_dec_eq(v_got_3066_, v___x_3065_);
if (v___x_3067_ == 0)
{
lean_object* v___x_3068_; lean_object* v___x_3070_; 
lean_del_object(v___x_3057_);
lean_dec(v_idx_3055_);
lean_dec_ref(v_array_3054_);
lean_dec(v_res_3050_);
v___x_3068_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_3053_ == 0)
{
lean_ctor_set_tag(v___x_3052_, 1);
lean_ctor_set(v___x_3052_, 1, v___x_3068_);
lean_ctor_set(v___x_3052_, 0, v_a_3047_);
v___x_3070_ = v___x_3052_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_a_3047_);
lean_ctor_set(v_reuseFailAlloc_3071_, 1, v___x_3068_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
else
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3075_; 
lean_del_object(v___x_3052_);
v___x_3072_ = lean_unsigned_to_nat(1u);
v___x_3073_ = lean_nat_add(v_idx_3055_, v___x_3072_);
lean_dec(v_idx_3055_);
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 1, v___x_3073_);
v___x_3075_ = v___x_3057_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_array_3054_);
lean_ctor_set(v_reuseFailAlloc_3100_, 1, v___x_3073_);
v___x_3075_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
lean_object* v___x_3076_; 
v___x_3076_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_3075_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v_pos_3077_; lean_object* v_res_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3090_; 
lean_dec_ref(v_a_3047_);
v_pos_3077_ = lean_ctor_get(v___x_3076_, 0);
v_res_3078_ = lean_ctor_get(v___x_3076_, 1);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3080_ = v___x_3076_;
v_isShared_3081_ = v_isSharedCheck_3090_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_res_3078_);
lean_inc(v_pos_3077_);
lean_dec(v___x_3076_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3090_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; uint16_t v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3088_; 
v___x_3082_ = lean_box(0);
v___x_3083_ = lean_alloc_ctor(2, 0, 2);
v___x_3084_ = lean_unbox(v_res_3078_);
lean_dec(v_res_3078_);
lean_ctor_set_uint16(v___x_3083_, 0, v___x_3084_);
v___x_3085_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3082_);
lean_ctor_set(v___x_3085_, 1, v_res_3050_);
lean_ctor_set(v___x_3085_, 2, v___x_3083_);
v___x_3086_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3085_);
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 1, v___x_3086_);
v___x_3088_ = v___x_3080_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_pos_3077_);
lean_ctor_set(v_reuseFailAlloc_3089_, 1, v___x_3086_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
else
{
lean_object* v_err_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
lean_dec(v_res_3050_);
v_err_3091_ = lean_ctor_get(v___x_3076_, 1);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3098_ == 0)
{
lean_object* v_unused_3099_; 
v_unused_3099_ = lean_ctor_get(v___x_3076_, 0);
lean_dec(v_unused_3099_);
v___x_3093_ = v___x_3076_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_err_3091_);
lean_dec(v___x_3076_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 0, v_a_3047_);
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3047_);
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
}
}
}
}
else
{
lean_object* v_err_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
v_err_3103_ = lean_ctor_get(v___x_3048_, 1);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3110_ == 0)
{
lean_object* v_unused_3111_; 
v_unused_3111_ = lean_ctor_get(v___x_3048_, 0);
lean_dec(v_unused_3111_);
v___x_3105_ = v___x_3048_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_err_3103_);
lean_dec(v___x_3048_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 0, v_a_3047_);
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3047_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v_err_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority___boxed(lean_object* v_config_3112_, lean_object* v_a_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3112_, v_a_3113_);
lean_dec_ref(v_config_3112_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object* v_config_3115_, lean_object* v_a_3116_){
_start:
{
lean_object* v___x_3117_; 
lean_inc_ref(v_a_3116_);
v___x_3117_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(v_a_3116_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_dec_ref(v_a_3116_);
lean_dec_ref(v_config_3115_);
return v___x_3117_;
}
else
{
lean_object* v_pos_3118_; lean_object* v_idx_3119_; lean_object* v_idx_3120_; uint8_t v___x_3121_; 
v_pos_3118_ = lean_ctor_get(v___x_3117_, 0);
v_idx_3119_ = lean_ctor_get(v_a_3116_, 1);
lean_inc(v_idx_3119_);
lean_dec_ref(v_a_3116_);
v_idx_3120_ = lean_ctor_get(v_pos_3118_, 1);
v___x_3121_ = lean_nat_dec_eq(v_idx_3119_, v_idx_3120_);
lean_dec(v_idx_3119_);
if (v___x_3121_ == 0)
{
lean_dec_ref(v_config_3115_);
return v___x_3117_;
}
else
{
lean_object* v___x_3122_; 
lean_inc(v_idx_3120_);
lean_inc(v_pos_3118_);
lean_dec_ref_known(v___x_3117_, 2);
lean_inc_ref(v_config_3115_);
v___x_3122_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(v_config_3115_, v_pos_3118_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_dec(v_idx_3120_);
lean_dec_ref(v_config_3115_);
return v___x_3122_;
}
else
{
lean_object* v_pos_3123_; lean_object* v_idx_3124_; uint8_t v___x_3125_; 
v_pos_3123_ = lean_ctor_get(v___x_3122_, 0);
v_idx_3124_ = lean_ctor_get(v_pos_3123_, 1);
v___x_3125_ = lean_nat_dec_eq(v_idx_3120_, v_idx_3124_);
lean_dec(v_idx_3120_);
if (v___x_3125_ == 0)
{
lean_dec_ref(v_config_3115_);
return v___x_3122_;
}
else
{
lean_object* v___x_3126_; 
lean_inc(v_idx_3124_);
lean_inc(v_pos_3123_);
lean_dec_ref_known(v___x_3122_, 2);
lean_inc_ref(v_config_3115_);
v___x_3126_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(v_config_3115_, v_pos_3123_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_dec(v_idx_3124_);
lean_dec_ref(v_config_3115_);
return v___x_3126_;
}
else
{
lean_object* v_pos_3127_; lean_object* v_idx_3128_; uint8_t v___x_3129_; 
v_pos_3127_ = lean_ctor_get(v___x_3126_, 0);
v_idx_3128_ = lean_ctor_get(v_pos_3127_, 1);
v___x_3129_ = lean_nat_dec_eq(v_idx_3124_, v_idx_3128_);
lean_dec(v_idx_3124_);
if (v___x_3129_ == 0)
{
lean_dec_ref(v_config_3115_);
return v___x_3126_;
}
else
{
lean_object* v___x_3130_; 
lean_inc(v_idx_3128_);
lean_inc(v_pos_3127_);
lean_dec_ref_known(v___x_3126_, 2);
v___x_3130_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3115_, v_pos_3127_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_dec(v_idx_3128_);
lean_dec_ref(v_config_3115_);
return v___x_3130_;
}
else
{
lean_object* v_pos_3131_; lean_object* v_idx_3132_; uint8_t v___x_3133_; 
v_pos_3131_ = lean_ctor_get(v___x_3130_, 0);
v_idx_3132_ = lean_ctor_get(v_pos_3131_, 1);
v___x_3133_ = lean_nat_dec_eq(v_idx_3128_, v_idx_3132_);
lean_dec(v_idx_3128_);
if (v___x_3133_ == 0)
{
lean_dec_ref(v_config_3115_);
return v___x_3130_;
}
else
{
lean_object* v___x_3134_; 
lean_inc(v_pos_3131_);
lean_dec_ref_known(v___x_3130_, 2);
v___x_3134_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(v_config_3115_, v_pos_3131_);
return v___x_3134_;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(lean_object* v_config_3138_, lean_object* v_a_3139_){
_start:
{
lean_object* v___x_3140_; 
v___x_3140_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_3138_, v_a_3139_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_pos_3141_; lean_object* v_res_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3155_; 
v_pos_3141_ = lean_ctor_get(v___x_3140_, 0);
v_res_3142_ = lean_ctor_get(v___x_3140_, 1);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3144_ = v___x_3140_;
v_isShared_3145_ = v_isSharedCheck_3155_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_res_3142_);
lean_inc(v_pos_3141_);
lean_dec(v___x_3140_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3155_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3146_; 
v___x_3146_ = l_Std_Http_URI_EncodedFragment_decode(v_res_3142_);
lean_dec(v_res_3142_);
if (lean_obj_tag(v___x_3146_) == 1)
{
lean_object* v_val_3147_; lean_object* v___x_3149_; 
v_val_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_val_3147_);
lean_dec_ref_known(v___x_3146_, 1);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 1, v_val_3147_);
v___x_3149_ = v___x_3144_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_pos_3141_);
lean_ctor_set(v_reuseFailAlloc_3150_, 1, v_val_3147_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
else
{
lean_object* v___x_3151_; lean_object* v___x_3153_; 
lean_dec(v___x_3146_);
v___x_3151_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___closed__1));
if (v_isShared_3145_ == 0)
{
lean_ctor_set_tag(v___x_3144_, 1);
lean_ctor_set(v___x_3144_, 1, v___x_3151_);
v___x_3153_ = v___x_3144_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_pos_3141_);
lean_ctor_set(v_reuseFailAlloc_3154_, 1, v___x_3151_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
else
{
lean_object* v_pos_3156_; lean_object* v_err_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3164_; 
v_pos_3156_ = lean_ctor_get(v___x_3140_, 0);
v_err_3157_ = lean_ctor_get(v___x_3140_, 1);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3159_ = v___x_3140_;
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_err_3157_);
lean_inc(v_pos_3156_);
lean_dec(v___x_3140_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3162_; 
if (v_isShared_3160_ == 0)
{
v___x_3162_ = v___x_3159_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_pos_3156_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___boxed(lean_object* v_config_3165_, lean_object* v_a_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3165_, v_a_3166_);
lean_dec_ref(v_config_3165_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_uri(lean_object* v_config_3168_, lean_object* v_a_3169_){
_start:
{
lean_object* v___x_3170_; 
lean_inc_ref(v_a_3169_);
v___x_3170_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3168_, v_a_3169_);
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_object* v_pos_3171_; lean_object* v_res_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3301_; 
v_pos_3171_ = lean_ctor_get(v___x_3170_, 0);
v_res_3172_ = lean_ctor_get(v___x_3170_, 1);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3174_ = v___x_3170_;
v_isShared_3175_ = v_isSharedCheck_3301_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_res_3172_);
lean_inc(v_pos_3171_);
lean_dec(v___x_3170_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3301_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v_array_3176_; lean_object* v_idx_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3300_; 
v_array_3176_ = lean_ctor_get(v_pos_3171_, 0);
v_idx_3177_ = lean_ctor_get(v_pos_3171_, 1);
v_isSharedCheck_3300_ = !lean_is_exclusive(v_pos_3171_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3179_ = v_pos_3171_;
v_isShared_3180_ = v_isSharedCheck_3300_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_idx_3177_);
lean_inc(v_array_3176_);
lean_dec(v_pos_3171_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3300_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3181_; uint8_t v___x_3182_; 
v___x_3181_ = lean_byte_array_size(v_array_3176_);
v___x_3182_ = lean_nat_dec_lt(v_idx_3177_, v___x_3181_);
if (v___x_3182_ == 0)
{
lean_object* v___x_3183_; lean_object* v___x_3185_; 
lean_del_object(v___x_3179_);
lean_dec(v_idx_3177_);
lean_dec_ref(v_array_3176_);
lean_dec(v_res_3172_);
lean_dec_ref(v_config_3168_);
v___x_3183_ = lean_box(0);
if (v_isShared_3175_ == 0)
{
lean_ctor_set_tag(v___x_3174_, 1);
lean_ctor_set(v___x_3174_, 1, v___x_3183_);
lean_ctor_set(v___x_3174_, 0, v_a_3169_);
v___x_3185_ = v___x_3174_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_a_3169_);
lean_ctor_set(v_reuseFailAlloc_3186_, 1, v___x_3183_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
else
{
uint8_t v___x_3187_; uint8_t v_got_3188_; uint8_t v___x_3189_; 
v___x_3187_ = 58;
v_got_3188_ = lean_byte_array_fget(v_array_3176_, v_idx_3177_);
v___x_3189_ = lean_uint8_dec_eq(v_got_3188_, v___x_3187_);
if (v___x_3189_ == 0)
{
lean_object* v___x_3190_; lean_object* v___x_3192_; 
lean_del_object(v___x_3179_);
lean_dec(v_idx_3177_);
lean_dec_ref(v_array_3176_);
lean_dec(v_res_3172_);
lean_dec_ref(v_config_3168_);
v___x_3190_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_3175_ == 0)
{
lean_ctor_set_tag(v___x_3174_, 1);
lean_ctor_set(v___x_3174_, 1, v___x_3190_);
lean_ctor_set(v___x_3174_, 0, v_a_3169_);
v___x_3192_ = v___x_3174_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3169_);
lean_ctor_set(v_reuseFailAlloc_3193_, 1, v___x_3190_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
else
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3197_; 
v___x_3194_ = lean_unsigned_to_nat(1u);
v___x_3195_ = lean_nat_add(v_idx_3177_, v___x_3194_);
lean_dec(v_idx_3177_);
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 1, v___x_3195_);
v___x_3197_ = v___x_3179_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_array_3176_);
lean_ctor_set(v_reuseFailAlloc_3299_, 1, v___x_3195_);
v___x_3197_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
lean_object* v___x_3198_; 
lean_inc_ref(v_config_3168_);
v___x_3198_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_3168_, v___x_3197_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_object* v_res_3199_; lean_object* v_pos_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3289_; 
v_res_3199_ = lean_ctor_get(v___x_3198_, 1);
v_pos_3200_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3202_ = v___x_3198_;
v_isShared_3203_ = v_isSharedCheck_3289_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_res_3199_);
lean_inc(v_pos_3200_);
lean_dec(v___x_3198_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3289_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v_fst_3204_; lean_object* v_snd_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3288_; 
v_fst_3204_ = lean_ctor_get(v_res_3199_, 0);
v_snd_3205_ = lean_ctor_get(v_res_3199_, 1);
v_isSharedCheck_3288_ = !lean_is_exclusive(v_res_3199_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3207_ = v_res_3199_;
v_isShared_3208_ = v_isSharedCheck_3288_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_snd_3205_);
lean_inc(v_fst_3204_);
lean_dec(v_res_3199_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3288_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___y_3210_; lean_object* v_pos_3211_; lean_object* v_res_3212_; lean_object* v_idx_3219_; lean_object* v___y_3220_; lean_object* v_pos_3221_; lean_object* v_err_3222_; lean_object* v_pos_3230_; lean_object* v_array_3231_; lean_object* v_idx_3232_; lean_object* v_res_3233_; lean_object* v_array_3251_; lean_object* v_idx_3252_; lean_object* v_pos_3254_; lean_object* v_array_3255_; lean_object* v_idx_3256_; lean_object* v_err_3257_; lean_object* v___x_3261_; uint8_t v___x_3262_; 
v_array_3251_ = lean_ctor_get(v_pos_3200_, 0);
lean_inc_ref(v_array_3251_);
v_idx_3252_ = lean_ctor_get(v_pos_3200_, 1);
lean_inc(v_idx_3252_);
v___x_3261_ = lean_byte_array_size(v_array_3251_);
v___x_3262_ = lean_nat_dec_lt(v_idx_3252_, v___x_3261_);
if (v___x_3262_ == 0)
{
lean_object* v___x_3263_; 
v___x_3263_ = lean_box(0);
lean_inc(v_idx_3252_);
v_pos_3254_ = v_pos_3200_;
v_array_3255_ = v_array_3251_;
v_idx_3256_ = v_idx_3252_;
v_err_3257_ = v___x_3263_;
goto v___jp_3253_;
}
else
{
uint8_t v___x_3264_; uint8_t v_got_3265_; uint8_t v___x_3266_; 
v___x_3264_ = 63;
v_got_3265_ = lean_byte_array_fget(v_array_3251_, v_idx_3252_);
v___x_3266_ = lean_uint8_dec_eq(v_got_3265_, v___x_3264_);
if (v___x_3266_ == 0)
{
lean_object* v___x_3267_; 
v___x_3267_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_3252_);
v_pos_3254_ = v_pos_3200_;
v_array_3255_ = v_array_3251_;
v_idx_3256_ = v_idx_3252_;
v_err_3257_ = v___x_3267_;
goto v___jp_3253_;
}
else
{
lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3285_; 
v_isSharedCheck_3285_ = !lean_is_exclusive(v_pos_3200_);
if (v_isSharedCheck_3285_ == 0)
{
lean_object* v_unused_3286_; lean_object* v_unused_3287_; 
v_unused_3286_ = lean_ctor_get(v_pos_3200_, 1);
lean_dec(v_unused_3286_);
v_unused_3287_ = lean_ctor_get(v_pos_3200_, 0);
lean_dec(v_unused_3287_);
v___x_3269_ = v_pos_3200_;
v_isShared_3270_ = v_isSharedCheck_3285_;
goto v_resetjp_3268_;
}
else
{
lean_dec(v_pos_3200_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3285_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3271_; lean_object* v___x_3273_; 
v___x_3271_ = lean_nat_add(v_idx_3252_, v___x_3194_);
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 1, v___x_3271_);
v___x_3273_ = v___x_3269_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_array_3251_);
lean_ctor_set(v_reuseFailAlloc_3284_, 1, v___x_3271_);
v___x_3273_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
lean_object* v___x_3274_; 
lean_inc_ref(v_config_3168_);
v___x_3274_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3168_, v___x_3273_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_pos_3275_; lean_object* v_res_3276_; lean_object* v_array_3277_; lean_object* v_idx_3278_; lean_object* v___x_3279_; 
lean_dec(v_idx_3252_);
v_pos_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_pos_3275_);
v_res_3276_ = lean_ctor_get(v___x_3274_, 1);
lean_inc(v_res_3276_);
lean_dec_ref_known(v___x_3274_, 2);
v_array_3277_ = lean_ctor_get(v_pos_3275_, 0);
lean_inc_ref(v_array_3277_);
v_idx_3278_ = lean_ctor_get(v_pos_3275_, 1);
lean_inc(v_idx_3278_);
v___x_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3279_, 0, v_res_3276_);
v_pos_3230_ = v_pos_3275_;
v_array_3231_ = v_array_3277_;
v_idx_3232_ = v_idx_3278_;
v_res_3233_ = v___x_3279_;
goto v___jp_3229_;
}
else
{
lean_object* v_pos_3280_; lean_object* v_err_3281_; lean_object* v_array_3282_; lean_object* v_idx_3283_; 
v_pos_3280_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_pos_3280_);
v_err_3281_ = lean_ctor_get(v___x_3274_, 1);
lean_inc(v_err_3281_);
lean_dec_ref_known(v___x_3274_, 2);
v_array_3282_ = lean_ctor_get(v_pos_3280_, 0);
lean_inc_ref(v_array_3282_);
v_idx_3283_ = lean_ctor_get(v_pos_3280_, 1);
lean_inc(v_idx_3283_);
v_pos_3254_ = v_pos_3280_;
v_array_3255_ = v_array_3282_;
v_idx_3256_ = v_idx_3283_;
v_err_3257_ = v_err_3281_;
goto v___jp_3253_;
}
}
}
}
}
v___jp_3209_:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3216_; 
v___x_3213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3213_, 0, v_res_3172_);
lean_ctor_set(v___x_3213_, 1, v_fst_3204_);
lean_ctor_set(v___x_3213_, 2, v_snd_3205_);
lean_ctor_set(v___x_3213_, 3, v___y_3210_);
lean_ctor_set(v___x_3213_, 4, v_res_3212_);
v___x_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 1, v___x_3214_);
lean_ctor_set(v___x_3202_, 0, v_pos_3211_);
v___x_3216_ = v___x_3202_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_pos_3211_);
lean_ctor_set(v_reuseFailAlloc_3217_, 1, v___x_3214_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
v___jp_3218_:
{
lean_object* v_idx_3223_; uint8_t v___x_3224_; 
v_idx_3223_ = lean_ctor_get(v_pos_3221_, 1);
v___x_3224_ = lean_nat_dec_eq(v_idx_3219_, v_idx_3223_);
lean_dec(v_idx_3219_);
if (v___x_3224_ == 0)
{
lean_object* v___x_3226_; 
lean_dec_ref(v_pos_3221_);
lean_dec(v___y_3220_);
lean_dec(v_snd_3205_);
lean_dec(v_fst_3204_);
lean_del_object(v___x_3202_);
lean_dec(v_res_3172_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set_tag(v___x_3174_, 1);
lean_ctor_set(v___x_3174_, 1, v_err_3222_);
lean_ctor_set(v___x_3174_, 0, v_a_3169_);
v___x_3226_ = v___x_3174_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3169_);
lean_ctor_set(v_reuseFailAlloc_3227_, 1, v_err_3222_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
else
{
lean_object* v___x_3228_; 
lean_dec(v_err_3222_);
lean_del_object(v___x_3174_);
lean_dec_ref(v_a_3169_);
v___x_3228_ = lean_box(0);
v___y_3210_ = v___y_3220_;
v_pos_3211_ = v_pos_3221_;
v_res_3212_ = v___x_3228_;
goto v___jp_3209_;
}
}
v___jp_3229_:
{
lean_object* v___x_3234_; uint8_t v___x_3235_; 
v___x_3234_ = lean_byte_array_size(v_array_3231_);
v___x_3235_ = lean_nat_dec_lt(v_idx_3232_, v___x_3234_);
if (v___x_3235_ == 0)
{
lean_object* v___x_3236_; 
lean_dec_ref(v_array_3231_);
lean_del_object(v___x_3207_);
lean_dec_ref(v_config_3168_);
v___x_3236_ = lean_box(0);
v_idx_3219_ = v_idx_3232_;
v___y_3220_ = v_res_3233_;
v_pos_3221_ = v_pos_3230_;
v_err_3222_ = v___x_3236_;
goto v___jp_3218_;
}
else
{
uint8_t v___x_3237_; uint8_t v_got_3238_; uint8_t v___x_3239_; 
v___x_3237_ = 35;
v_got_3238_ = lean_byte_array_fget(v_array_3231_, v_idx_3232_);
v___x_3239_ = lean_uint8_dec_eq(v_got_3238_, v___x_3237_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3240_; 
lean_dec_ref(v_array_3231_);
lean_del_object(v___x_3207_);
lean_dec_ref(v_config_3168_);
v___x_3240_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v_idx_3219_ = v_idx_3232_;
v___y_3220_ = v_res_3233_;
v_pos_3221_ = v_pos_3230_;
v_err_3222_ = v___x_3240_;
goto v___jp_3218_;
}
else
{
lean_object* v___x_3241_; lean_object* v___x_3243_; 
lean_dec_ref(v_pos_3230_);
v___x_3241_ = lean_nat_add(v_idx_3232_, v___x_3194_);
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 1, v___x_3241_);
lean_ctor_set(v___x_3207_, 0, v_array_3231_);
v___x_3243_ = v___x_3207_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_array_3231_);
lean_ctor_set(v_reuseFailAlloc_3250_, 1, v___x_3241_);
v___x_3243_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
lean_object* v___x_3244_; 
v___x_3244_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3168_, v___x_3243_);
lean_dec_ref(v_config_3168_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v_pos_3245_; lean_object* v_res_3246_; lean_object* v___x_3247_; 
lean_dec(v_idx_3232_);
lean_del_object(v___x_3174_);
lean_dec_ref(v_a_3169_);
v_pos_3245_ = lean_ctor_get(v___x_3244_, 0);
lean_inc(v_pos_3245_);
v_res_3246_ = lean_ctor_get(v___x_3244_, 1);
lean_inc(v_res_3246_);
lean_dec_ref_known(v___x_3244_, 2);
v___x_3247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3247_, 0, v_res_3246_);
v___y_3210_ = v_res_3233_;
v_pos_3211_ = v_pos_3245_;
v_res_3212_ = v___x_3247_;
goto v___jp_3209_;
}
else
{
lean_object* v_pos_3248_; lean_object* v_err_3249_; 
v_pos_3248_ = lean_ctor_get(v___x_3244_, 0);
lean_inc(v_pos_3248_);
v_err_3249_ = lean_ctor_get(v___x_3244_, 1);
lean_inc(v_err_3249_);
lean_dec_ref_known(v___x_3244_, 2);
v_idx_3219_ = v_idx_3232_;
v___y_3220_ = v_res_3233_;
v_pos_3221_ = v_pos_3248_;
v_err_3222_ = v_err_3249_;
goto v___jp_3218_;
}
}
}
}
}
v___jp_3253_:
{
uint8_t v___x_3258_; 
v___x_3258_ = lean_nat_dec_eq(v_idx_3252_, v_idx_3256_);
lean_dec(v_idx_3252_);
if (v___x_3258_ == 0)
{
lean_object* v___x_3259_; 
lean_dec(v_idx_3256_);
lean_dec_ref(v_array_3255_);
lean_dec_ref(v_pos_3254_);
lean_del_object(v___x_3207_);
lean_dec(v_snd_3205_);
lean_dec(v_fst_3204_);
lean_del_object(v___x_3202_);
lean_del_object(v___x_3174_);
lean_dec(v_res_3172_);
lean_dec_ref(v_config_3168_);
v___x_3259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3259_, 0, v_a_3169_);
lean_ctor_set(v___x_3259_, 1, v_err_3257_);
return v___x_3259_;
}
else
{
lean_object* v___x_3260_; 
lean_dec(v_err_3257_);
v___x_3260_ = lean_box(0);
v_pos_3230_ = v_pos_3254_;
v_array_3231_ = v_array_3255_;
v_idx_3232_ = v_idx_3256_;
v_res_3233_ = v___x_3260_;
goto v___jp_3229_;
}
}
}
}
}
else
{
lean_object* v_err_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3297_; 
lean_del_object(v___x_3174_);
lean_dec(v_res_3172_);
lean_dec_ref(v_config_3168_);
v_err_3290_ = lean_ctor_get(v___x_3198_, 1);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3297_ == 0)
{
lean_object* v_unused_3298_; 
v_unused_3298_ = lean_ctor_get(v___x_3198_, 0);
lean_dec(v_unused_3298_);
v___x_3292_ = v___x_3198_;
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_err_3290_);
lean_dec(v___x_3198_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3295_; 
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v_a_3169_);
v___x_3295_ = v___x_3292_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3169_);
lean_ctor_set(v_reuseFailAlloc_3296_, 1, v_err_3290_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
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
lean_object* v_err_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
lean_dec_ref(v_config_3168_);
v_err_3302_ = lean_ctor_get(v___x_3170_, 1);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3309_ == 0)
{
lean_object* v_unused_3310_; 
v_unused_3310_ = lean_ctor_get(v___x_3170_, 0);
lean_dec(v_unused_3310_);
v___x_3304_ = v___x_3170_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_err_3302_);
lean_dec(v___x_3170_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 0, v_a_3169_);
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3169_);
lean_ctor_set(v_reuseFailAlloc_3308_, 1, v_err_3302_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withAuthority(lean_object* v_config_3311_, lean_object* v_a_3312_){
_start:
{
lean_object* v_utf8_3313_; lean_object* v___x_3314_; 
v_utf8_3313_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1);
lean_inc_ref(v_a_3312_);
v___x_3314_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_3313_, v_a_3312_);
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_object* v_pos_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3433_; 
v_pos_3315_ = lean_ctor_get(v___x_3314_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3433_ == 0)
{
lean_object* v_unused_3434_; 
v_unused_3434_ = lean_ctor_get(v___x_3314_, 1);
lean_dec(v_unused_3434_);
v___x_3317_ = v___x_3314_;
v_isShared_3318_ = v_isSharedCheck_3433_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_pos_3315_);
lean_dec(v___x_3314_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3433_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
lean_object* v___x_3319_; 
v___x_3319_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_3311_, v_pos_3315_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_pos_3320_; lean_object* v_res_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3423_; 
v_pos_3320_ = lean_ctor_get(v___x_3319_, 0);
v_res_3321_ = lean_ctor_get(v___x_3319_, 1);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3323_ = v___x_3319_;
v_isShared_3324_ = v_isSharedCheck_3423_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_res_3321_);
lean_inc(v_pos_3320_);
lean_dec(v___x_3319_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3423_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
uint8_t v___x_3325_; lean_object* v___x_3326_; 
v___x_3325_ = 1;
lean_inc_ref(v_config_3311_);
v___x_3326_ = l_Std_Http_URI_Parser_parsePath(v_config_3311_, v___x_3325_, v___x_3325_, v_pos_3320_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_pos_3327_; lean_object* v_res_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3413_; 
v_pos_3327_ = lean_ctor_get(v___x_3326_, 0);
v_res_3328_ = lean_ctor_get(v___x_3326_, 1);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3330_ = v___x_3326_;
v_isShared_3331_ = v_isSharedCheck_3413_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_res_3328_);
lean_inc(v_pos_3327_);
lean_dec(v___x_3326_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3413_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___y_3333_; lean_object* v_pos_3334_; lean_object* v_res_3335_; lean_object* v_idx_3342_; lean_object* v___y_3343_; lean_object* v_pos_3344_; lean_object* v_err_3345_; lean_object* v_pos_3353_; lean_object* v_array_3354_; lean_object* v_idx_3355_; lean_object* v_res_3356_; lean_object* v_array_3373_; lean_object* v_idx_3374_; lean_object* v_pos_3376_; lean_object* v_array_3377_; lean_object* v_idx_3378_; lean_object* v_err_3379_; lean_object* v___x_3385_; uint8_t v___x_3386_; 
v_array_3373_ = lean_ctor_get(v_pos_3327_, 0);
lean_inc_ref(v_array_3373_);
v_idx_3374_ = lean_ctor_get(v_pos_3327_, 1);
lean_inc(v_idx_3374_);
v___x_3385_ = lean_byte_array_size(v_array_3373_);
v___x_3386_ = lean_nat_dec_lt(v_idx_3374_, v___x_3385_);
if (v___x_3386_ == 0)
{
lean_object* v___x_3387_; 
v___x_3387_ = lean_box(0);
lean_inc(v_idx_3374_);
v_pos_3376_ = v_pos_3327_;
v_array_3377_ = v_array_3373_;
v_idx_3378_ = v_idx_3374_;
v_err_3379_ = v___x_3387_;
goto v___jp_3375_;
}
else
{
uint8_t v___x_3388_; uint8_t v_got_3389_; uint8_t v___x_3390_; 
v___x_3388_ = 63;
v_got_3389_ = lean_byte_array_fget(v_array_3373_, v_idx_3374_);
v___x_3390_ = lean_uint8_dec_eq(v_got_3389_, v___x_3388_);
if (v___x_3390_ == 0)
{
lean_object* v___x_3391_; 
v___x_3391_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_3374_);
v_pos_3376_ = v_pos_3327_;
v_array_3377_ = v_array_3373_;
v_idx_3378_ = v_idx_3374_;
v_err_3379_ = v___x_3391_;
goto v___jp_3375_;
}
else
{
lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3410_; 
v_isSharedCheck_3410_ = !lean_is_exclusive(v_pos_3327_);
if (v_isSharedCheck_3410_ == 0)
{
lean_object* v_unused_3411_; lean_object* v_unused_3412_; 
v_unused_3411_ = lean_ctor_get(v_pos_3327_, 1);
lean_dec(v_unused_3411_);
v_unused_3412_ = lean_ctor_get(v_pos_3327_, 0);
lean_dec(v_unused_3412_);
v___x_3393_ = v_pos_3327_;
v_isShared_3394_ = v_isSharedCheck_3410_;
goto v_resetjp_3392_;
}
else
{
lean_dec(v_pos_3327_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3410_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3398_; 
v___x_3395_ = lean_unsigned_to_nat(1u);
v___x_3396_ = lean_nat_add(v_idx_3374_, v___x_3395_);
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 1, v___x_3396_);
v___x_3398_ = v___x_3393_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_array_3373_);
lean_ctor_set(v_reuseFailAlloc_3409_, 1, v___x_3396_);
v___x_3398_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
lean_object* v___x_3399_; 
lean_inc_ref(v_config_3311_);
v___x_3399_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3311_, v___x_3398_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v_pos_3400_; lean_object* v_res_3401_; lean_object* v_array_3402_; lean_object* v_idx_3403_; lean_object* v___x_3404_; 
lean_dec(v_idx_3374_);
lean_del_object(v___x_3317_);
v_pos_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_pos_3400_);
v_res_3401_ = lean_ctor_get(v___x_3399_, 1);
lean_inc(v_res_3401_);
lean_dec_ref_known(v___x_3399_, 2);
v_array_3402_ = lean_ctor_get(v_pos_3400_, 0);
lean_inc_ref(v_array_3402_);
v_idx_3403_ = lean_ctor_get(v_pos_3400_, 1);
lean_inc(v_idx_3403_);
v___x_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3404_, 0, v_res_3401_);
v_pos_3353_ = v_pos_3400_;
v_array_3354_ = v_array_3402_;
v_idx_3355_ = v_idx_3403_;
v_res_3356_ = v___x_3404_;
goto v___jp_3352_;
}
else
{
lean_object* v_pos_3405_; lean_object* v_err_3406_; lean_object* v_array_3407_; lean_object* v_idx_3408_; 
v_pos_3405_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_pos_3405_);
v_err_3406_ = lean_ctor_get(v___x_3399_, 1);
lean_inc(v_err_3406_);
lean_dec_ref_known(v___x_3399_, 2);
v_array_3407_ = lean_ctor_get(v_pos_3405_, 0);
lean_inc_ref(v_array_3407_);
v_idx_3408_ = lean_ctor_get(v_pos_3405_, 1);
lean_inc(v_idx_3408_);
v_pos_3376_ = v_pos_3405_;
v_array_3377_ = v_array_3407_;
v_idx_3378_ = v_idx_3408_;
v_err_3379_ = v_err_3406_;
goto v___jp_3375_;
}
}
}
}
}
v___jp_3332_:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3339_; 
v___x_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3336_, 0, v_res_3321_);
v___x_3337_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3336_);
lean_ctor_set(v___x_3337_, 1, v_res_3328_);
lean_ctor_set(v___x_3337_, 2, v___y_3333_);
lean_ctor_set(v___x_3337_, 3, v_res_3335_);
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 1, v___x_3337_);
lean_ctor_set(v___x_3330_, 0, v_pos_3334_);
v___x_3339_ = v___x_3330_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_pos_3334_);
lean_ctor_set(v_reuseFailAlloc_3340_, 1, v___x_3337_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
v___jp_3341_:
{
lean_object* v_idx_3346_; uint8_t v___x_3347_; 
v_idx_3346_ = lean_ctor_get(v_pos_3344_, 1);
v___x_3347_ = lean_nat_dec_eq(v_idx_3342_, v_idx_3346_);
lean_dec(v_idx_3342_);
if (v___x_3347_ == 0)
{
lean_object* v___x_3349_; 
lean_dec_ref(v_pos_3344_);
lean_dec(v___y_3343_);
lean_del_object(v___x_3330_);
lean_dec(v_res_3328_);
lean_dec(v_res_3321_);
if (v_isShared_3324_ == 0)
{
lean_ctor_set_tag(v___x_3323_, 1);
lean_ctor_set(v___x_3323_, 1, v_err_3345_);
lean_ctor_set(v___x_3323_, 0, v_a_3312_);
v___x_3349_ = v___x_3323_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_a_3312_);
lean_ctor_set(v_reuseFailAlloc_3350_, 1, v_err_3345_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
else
{
lean_object* v___x_3351_; 
lean_dec(v_err_3345_);
lean_del_object(v___x_3323_);
lean_dec_ref(v_a_3312_);
v___x_3351_ = lean_box(0);
v___y_3333_ = v___y_3343_;
v_pos_3334_ = v_pos_3344_;
v_res_3335_ = v___x_3351_;
goto v___jp_3332_;
}
}
v___jp_3352_:
{
lean_object* v___x_3357_; uint8_t v___x_3358_; 
v___x_3357_ = lean_byte_array_size(v_array_3354_);
v___x_3358_ = lean_nat_dec_lt(v_idx_3355_, v___x_3357_);
if (v___x_3358_ == 0)
{
lean_object* v___x_3359_; 
lean_dec_ref(v_array_3354_);
lean_dec_ref(v_config_3311_);
v___x_3359_ = lean_box(0);
v_idx_3342_ = v_idx_3355_;
v___y_3343_ = v_res_3356_;
v_pos_3344_ = v_pos_3353_;
v_err_3345_ = v___x_3359_;
goto v___jp_3341_;
}
else
{
uint8_t v___x_3360_; uint8_t v_got_3361_; uint8_t v___x_3362_; 
v___x_3360_ = 35;
v_got_3361_ = lean_byte_array_fget(v_array_3354_, v_idx_3355_);
v___x_3362_ = lean_uint8_dec_eq(v_got_3361_, v___x_3360_);
if (v___x_3362_ == 0)
{
lean_object* v___x_3363_; 
lean_dec_ref(v_array_3354_);
lean_dec_ref(v_config_3311_);
v___x_3363_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v_idx_3342_ = v_idx_3355_;
v___y_3343_ = v_res_3356_;
v_pos_3344_ = v_pos_3353_;
v_err_3345_ = v___x_3363_;
goto v___jp_3341_;
}
else
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
lean_dec_ref(v_pos_3353_);
v___x_3364_ = lean_unsigned_to_nat(1u);
v___x_3365_ = lean_nat_add(v_idx_3355_, v___x_3364_);
v___x_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3366_, 0, v_array_3354_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
v___x_3367_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3311_, v___x_3366_);
lean_dec_ref(v_config_3311_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_pos_3368_; lean_object* v_res_3369_; lean_object* v___x_3370_; 
lean_dec(v_idx_3355_);
lean_del_object(v___x_3323_);
lean_dec_ref(v_a_3312_);
v_pos_3368_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_pos_3368_);
v_res_3369_ = lean_ctor_get(v___x_3367_, 1);
lean_inc(v_res_3369_);
lean_dec_ref_known(v___x_3367_, 2);
v___x_3370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3370_, 0, v_res_3369_);
v___y_3333_ = v_res_3356_;
v_pos_3334_ = v_pos_3368_;
v_res_3335_ = v___x_3370_;
goto v___jp_3332_;
}
else
{
lean_object* v_pos_3371_; lean_object* v_err_3372_; 
v_pos_3371_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_pos_3371_);
v_err_3372_ = lean_ctor_get(v___x_3367_, 1);
lean_inc(v_err_3372_);
lean_dec_ref_known(v___x_3367_, 2);
v_idx_3342_ = v_idx_3355_;
v___y_3343_ = v_res_3356_;
v_pos_3344_ = v_pos_3371_;
v_err_3345_ = v_err_3372_;
goto v___jp_3341_;
}
}
}
}
v___jp_3375_:
{
uint8_t v___x_3380_; 
v___x_3380_ = lean_nat_dec_eq(v_idx_3374_, v_idx_3378_);
lean_dec(v_idx_3374_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3382_; 
lean_dec(v_idx_3378_);
lean_dec_ref(v_array_3377_);
lean_dec_ref(v_pos_3376_);
lean_del_object(v___x_3330_);
lean_dec(v_res_3328_);
lean_del_object(v___x_3323_);
lean_dec(v_res_3321_);
lean_dec_ref(v_config_3311_);
if (v_isShared_3318_ == 0)
{
lean_ctor_set_tag(v___x_3317_, 1);
lean_ctor_set(v___x_3317_, 1, v_err_3379_);
lean_ctor_set(v___x_3317_, 0, v_a_3312_);
v___x_3382_ = v___x_3317_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3312_);
lean_ctor_set(v_reuseFailAlloc_3383_, 1, v_err_3379_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
else
{
lean_object* v___x_3384_; 
lean_dec(v_err_3379_);
lean_del_object(v___x_3317_);
v___x_3384_ = lean_box(0);
v_pos_3353_ = v_pos_3376_;
v_array_3354_ = v_array_3377_;
v_idx_3355_ = v_idx_3378_;
v_res_3356_ = v___x_3384_;
goto v___jp_3352_;
}
}
}
}
else
{
lean_object* v_err_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3421_; 
lean_del_object(v___x_3323_);
lean_dec(v_res_3321_);
lean_del_object(v___x_3317_);
lean_dec_ref(v_config_3311_);
v_err_3414_ = lean_ctor_get(v___x_3326_, 1);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3421_ == 0)
{
lean_object* v_unused_3422_; 
v_unused_3422_ = lean_ctor_get(v___x_3326_, 0);
lean_dec(v_unused_3422_);
v___x_3416_ = v___x_3326_;
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_err_3414_);
lean_dec(v___x_3326_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 0, v_a_3312_);
v___x_3419_ = v___x_3416_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3312_);
lean_ctor_set(v_reuseFailAlloc_3420_, 1, v_err_3414_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
}
else
{
lean_object* v_err_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3431_; 
lean_del_object(v___x_3317_);
lean_dec_ref(v_config_3311_);
v_err_3424_ = lean_ctor_get(v___x_3319_, 1);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3431_ == 0)
{
lean_object* v_unused_3432_; 
v_unused_3432_ = lean_ctor_get(v___x_3319_, 0);
lean_dec(v_unused_3432_);
v___x_3426_ = v___x_3319_;
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_err_3424_);
lean_dec(v___x_3319_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3429_; 
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 0, v_a_3312_);
v___x_3429_ = v___x_3426_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3312_);
lean_ctor_set(v_reuseFailAlloc_3430_, 1, v_err_3424_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
}
else
{
lean_object* v_err_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3442_; 
lean_dec_ref(v_config_3311_);
v_err_3435_ = lean_ctor_get(v___x_3314_, 1);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3442_ == 0)
{
lean_object* v_unused_3443_; 
v_unused_3443_ = lean_ctor_get(v___x_3314_, 0);
lean_dec(v_unused_3443_);
v___x_3437_ = v___x_3314_;
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_err_3435_);
lean_dec(v___x_3314_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 0, v_a_3312_);
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3312_);
lean_ctor_set(v_reuseFailAlloc_3441_, 1, v_err_3435_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath(lean_object* v_config_3444_, lean_object* v_a_3445_){
_start:
{
uint8_t v___x_3446_; uint8_t v___x_3447_; lean_object* v___x_3448_; 
v___x_3446_ = 0;
v___x_3447_ = 1;
lean_inc_ref(v_config_3444_);
v___x_3448_ = l_Std_Http_URI_Parser_parsePath(v_config_3444_, v___x_3446_, v___x_3447_, v_a_3445_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_pos_3449_; lean_object* v_res_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3531_; 
v_pos_3449_ = lean_ctor_get(v___x_3448_, 0);
v_res_3450_ = lean_ctor_get(v___x_3448_, 1);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3452_ = v___x_3448_;
v_isShared_3453_ = v_isSharedCheck_3531_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_res_3450_);
lean_inc(v_pos_3449_);
lean_dec(v___x_3448_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3531_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___y_3455_; lean_object* v_pos_3456_; lean_object* v_res_3457_; lean_object* v_idx_3464_; lean_object* v___y_3465_; lean_object* v_pos_3466_; lean_object* v_err_3467_; lean_object* v_pos_3473_; lean_object* v_array_3474_; lean_object* v_idx_3475_; lean_object* v_res_3476_; lean_object* v_array_3493_; lean_object* v_idx_3494_; lean_object* v_pos_3496_; lean_object* v_array_3497_; lean_object* v_idx_3498_; lean_object* v_err_3499_; lean_object* v___x_3503_; uint8_t v___x_3504_; 
v_array_3493_ = lean_ctor_get(v_pos_3449_, 0);
lean_inc_ref(v_array_3493_);
v_idx_3494_ = lean_ctor_get(v_pos_3449_, 1);
lean_inc(v_idx_3494_);
v___x_3503_ = lean_byte_array_size(v_array_3493_);
v___x_3504_ = lean_nat_dec_lt(v_idx_3494_, v___x_3503_);
if (v___x_3504_ == 0)
{
lean_object* v___x_3505_; 
v___x_3505_ = lean_box(0);
lean_inc(v_idx_3494_);
v_pos_3496_ = v_pos_3449_;
v_array_3497_ = v_array_3493_;
v_idx_3498_ = v_idx_3494_;
v_err_3499_ = v___x_3505_;
goto v___jp_3495_;
}
else
{
uint8_t v___x_3506_; uint8_t v_got_3507_; uint8_t v___x_3508_; 
v___x_3506_ = 63;
v_got_3507_ = lean_byte_array_fget(v_array_3493_, v_idx_3494_);
v___x_3508_ = lean_uint8_dec_eq(v_got_3507_, v___x_3506_);
if (v___x_3508_ == 0)
{
lean_object* v___x_3509_; 
v___x_3509_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_3494_);
v_pos_3496_ = v_pos_3449_;
v_array_3497_ = v_array_3493_;
v_idx_3498_ = v_idx_3494_;
v_err_3499_ = v___x_3509_;
goto v___jp_3495_;
}
else
{
lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3528_; 
v_isSharedCheck_3528_ = !lean_is_exclusive(v_pos_3449_);
if (v_isSharedCheck_3528_ == 0)
{
lean_object* v_unused_3529_; lean_object* v_unused_3530_; 
v_unused_3529_ = lean_ctor_get(v_pos_3449_, 1);
lean_dec(v_unused_3529_);
v_unused_3530_ = lean_ctor_get(v_pos_3449_, 0);
lean_dec(v_unused_3530_);
v___x_3511_ = v_pos_3449_;
v_isShared_3512_ = v_isSharedCheck_3528_;
goto v_resetjp_3510_;
}
else
{
lean_dec(v_pos_3449_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3528_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3516_; 
v___x_3513_ = lean_unsigned_to_nat(1u);
v___x_3514_ = lean_nat_add(v_idx_3494_, v___x_3513_);
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 1, v___x_3514_);
v___x_3516_ = v___x_3511_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_array_3493_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v___x_3514_);
v___x_3516_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
lean_object* v___x_3517_; 
lean_inc_ref(v_config_3444_);
v___x_3517_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3444_, v___x_3516_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v_pos_3518_; lean_object* v_res_3519_; lean_object* v_array_3520_; lean_object* v_idx_3521_; lean_object* v___x_3522_; 
lean_dec(v_idx_3494_);
v_pos_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc(v_pos_3518_);
v_res_3519_ = lean_ctor_get(v___x_3517_, 1);
lean_inc(v_res_3519_);
lean_dec_ref_known(v___x_3517_, 2);
v_array_3520_ = lean_ctor_get(v_pos_3518_, 0);
lean_inc_ref(v_array_3520_);
v_idx_3521_ = lean_ctor_get(v_pos_3518_, 1);
lean_inc(v_idx_3521_);
v___x_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3522_, 0, v_res_3519_);
v_pos_3473_ = v_pos_3518_;
v_array_3474_ = v_array_3520_;
v_idx_3475_ = v_idx_3521_;
v_res_3476_ = v___x_3522_;
goto v___jp_3472_;
}
else
{
lean_object* v_pos_3523_; lean_object* v_err_3524_; lean_object* v_array_3525_; lean_object* v_idx_3526_; 
v_pos_3523_ = lean_ctor_get(v___x_3517_, 0);
lean_inc(v_pos_3523_);
v_err_3524_ = lean_ctor_get(v___x_3517_, 1);
lean_inc(v_err_3524_);
lean_dec_ref_known(v___x_3517_, 2);
v_array_3525_ = lean_ctor_get(v_pos_3523_, 0);
lean_inc_ref(v_array_3525_);
v_idx_3526_ = lean_ctor_get(v_pos_3523_, 1);
lean_inc(v_idx_3526_);
v_pos_3496_ = v_pos_3523_;
v_array_3497_ = v_array_3525_;
v_idx_3498_ = v_idx_3526_;
v_err_3499_ = v_err_3524_;
goto v___jp_3495_;
}
}
}
}
}
v___jp_3454_:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3461_; 
v___x_3458_ = lean_box(0);
v___x_3459_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3458_);
lean_ctor_set(v___x_3459_, 1, v_res_3450_);
lean_ctor_set(v___x_3459_, 2, v___y_3455_);
lean_ctor_set(v___x_3459_, 3, v_res_3457_);
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 1, v___x_3459_);
lean_ctor_set(v___x_3452_, 0, v_pos_3456_);
v___x_3461_ = v___x_3452_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_pos_3456_);
lean_ctor_set(v_reuseFailAlloc_3462_, 1, v___x_3459_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
v___jp_3463_:
{
lean_object* v_idx_3468_; uint8_t v___x_3469_; 
v_idx_3468_ = lean_ctor_get(v_pos_3466_, 1);
v___x_3469_ = lean_nat_dec_eq(v_idx_3464_, v_idx_3468_);
lean_dec(v_idx_3464_);
if (v___x_3469_ == 0)
{
lean_object* v___x_3470_; 
lean_dec(v___y_3465_);
lean_del_object(v___x_3452_);
lean_dec(v_res_3450_);
v___x_3470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3470_, 0, v_pos_3466_);
lean_ctor_set(v___x_3470_, 1, v_err_3467_);
return v___x_3470_;
}
else
{
lean_object* v___x_3471_; 
lean_dec(v_err_3467_);
v___x_3471_ = lean_box(0);
v___y_3455_ = v___y_3465_;
v_pos_3456_ = v_pos_3466_;
v_res_3457_ = v___x_3471_;
goto v___jp_3454_;
}
}
v___jp_3472_:
{
lean_object* v___x_3477_; uint8_t v___x_3478_; 
v___x_3477_ = lean_byte_array_size(v_array_3474_);
v___x_3478_ = lean_nat_dec_lt(v_idx_3475_, v___x_3477_);
if (v___x_3478_ == 0)
{
lean_object* v___x_3479_; 
lean_dec_ref(v_array_3474_);
lean_dec_ref(v_config_3444_);
v___x_3479_ = lean_box(0);
v_idx_3464_ = v_idx_3475_;
v___y_3465_ = v_res_3476_;
v_pos_3466_ = v_pos_3473_;
v_err_3467_ = v___x_3479_;
goto v___jp_3463_;
}
else
{
uint8_t v___x_3480_; uint8_t v_got_3481_; uint8_t v___x_3482_; 
v___x_3480_ = 35;
v_got_3481_ = lean_byte_array_fget(v_array_3474_, v_idx_3475_);
v___x_3482_ = lean_uint8_dec_eq(v_got_3481_, v___x_3480_);
if (v___x_3482_ == 0)
{
lean_object* v___x_3483_; 
lean_dec_ref(v_array_3474_);
lean_dec_ref(v_config_3444_);
v___x_3483_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v_idx_3464_ = v_idx_3475_;
v___y_3465_ = v_res_3476_;
v_pos_3466_ = v_pos_3473_;
v_err_3467_ = v___x_3483_;
goto v___jp_3463_;
}
else
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
lean_dec_ref(v_pos_3473_);
v___x_3484_ = lean_unsigned_to_nat(1u);
v___x_3485_ = lean_nat_add(v_idx_3475_, v___x_3484_);
v___x_3486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3486_, 0, v_array_3474_);
lean_ctor_set(v___x_3486_, 1, v___x_3485_);
v___x_3487_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3444_, v___x_3486_);
lean_dec_ref(v_config_3444_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_pos_3488_; lean_object* v_res_3489_; lean_object* v___x_3490_; 
lean_dec(v_idx_3475_);
v_pos_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_pos_3488_);
v_res_3489_ = lean_ctor_get(v___x_3487_, 1);
lean_inc(v_res_3489_);
lean_dec_ref_known(v___x_3487_, 2);
v___x_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3490_, 0, v_res_3489_);
v___y_3455_ = v_res_3476_;
v_pos_3456_ = v_pos_3488_;
v_res_3457_ = v___x_3490_;
goto v___jp_3454_;
}
else
{
lean_object* v_pos_3491_; lean_object* v_err_3492_; 
v_pos_3491_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_pos_3491_);
v_err_3492_ = lean_ctor_get(v___x_3487_, 1);
lean_inc(v_err_3492_);
lean_dec_ref_known(v___x_3487_, 2);
v_idx_3464_ = v_idx_3475_;
v___y_3465_ = v_res_3476_;
v_pos_3466_ = v_pos_3491_;
v_err_3467_ = v_err_3492_;
goto v___jp_3463_;
}
}
}
}
v___jp_3495_:
{
uint8_t v___x_3500_; 
v___x_3500_ = lean_nat_dec_eq(v_idx_3494_, v_idx_3498_);
lean_dec(v_idx_3494_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3501_; 
lean_dec(v_idx_3498_);
lean_dec_ref(v_array_3497_);
lean_del_object(v___x_3452_);
lean_dec(v_res_3450_);
lean_dec_ref(v_config_3444_);
v___x_3501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3501_, 0, v_pos_3496_);
lean_ctor_set(v___x_3501_, 1, v_err_3499_);
return v___x_3501_;
}
else
{
lean_object* v___x_3502_; 
lean_dec(v_err_3499_);
v___x_3502_ = lean_box(0);
v_pos_3473_ = v_pos_3496_;
v_array_3474_ = v_array_3497_;
v_idx_3475_ = v_idx_3498_;
v_res_3476_ = v___x_3502_;
goto v___jp_3472_;
}
}
}
}
else
{
lean_object* v_pos_3532_; lean_object* v_err_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
lean_dec_ref(v_config_3444_);
v_pos_3532_ = lean_ctor_get(v___x_3448_, 0);
v_err_3533_ = lean_ctor_get(v___x_3448_, 1);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3448_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_err_3533_);
lean_inc(v_pos_3532_);
lean_dec(v___x_3448_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_pos_3532_);
lean_ctor_set(v_reuseFailAlloc_3539_, 1, v_err_3533_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_relative(lean_object* v_config_3541_, lean_object* v_a_3542_){
_start:
{
lean_object* v_pos_3544_; lean_object* v_res_3545_; lean_object* v___x_3548_; 
lean_inc_ref(v_a_3542_);
lean_inc_ref(v_config_3541_);
v___x_3548_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withAuthority(v_config_3541_, v_a_3542_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v_pos_3549_; lean_object* v_res_3550_; 
lean_dec_ref(v_a_3542_);
lean_dec_ref(v_config_3541_);
v_pos_3549_ = lean_ctor_get(v___x_3548_, 0);
lean_inc(v_pos_3549_);
v_res_3550_ = lean_ctor_get(v___x_3548_, 1);
lean_inc(v_res_3550_);
lean_dec_ref_known(v___x_3548_, 2);
v_pos_3544_ = v_pos_3549_;
v_res_3545_ = v_res_3550_;
goto v___jp_3543_;
}
else
{
lean_object* v_pos_3551_; lean_object* v_err_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3574_; 
v_pos_3551_ = lean_ctor_get(v___x_3548_, 0);
v_err_3552_ = lean_ctor_get(v___x_3548_, 1);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3554_ = v___x_3548_;
v_isShared_3555_ = v_isSharedCheck_3574_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_err_3552_);
lean_inc(v_pos_3551_);
lean_dec(v___x_3548_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3574_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v_idx_3556_; lean_object* v_idx_3557_; uint8_t v___x_3558_; 
v_idx_3556_ = lean_ctor_get(v_a_3542_, 1);
lean_inc(v_idx_3556_);
lean_dec_ref(v_a_3542_);
v_idx_3557_ = lean_ctor_get(v_pos_3551_, 1);
v___x_3558_ = lean_nat_dec_eq(v_idx_3556_, v_idx_3557_);
lean_dec(v_idx_3556_);
if (v___x_3558_ == 0)
{
lean_object* v___x_3560_; 
lean_dec_ref(v_config_3541_);
if (v_isShared_3555_ == 0)
{
v___x_3560_ = v___x_3554_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_pos_3551_);
lean_ctor_set(v_reuseFailAlloc_3561_, 1, v_err_3552_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
else
{
lean_object* v___x_3562_; 
lean_del_object(v___x_3554_);
lean_dec(v_err_3552_);
v___x_3562_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath(v_config_3541_, v_pos_3551_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v_pos_3563_; lean_object* v_res_3564_; 
v_pos_3563_ = lean_ctor_get(v___x_3562_, 0);
lean_inc(v_pos_3563_);
v_res_3564_ = lean_ctor_get(v___x_3562_, 1);
lean_inc(v_res_3564_);
lean_dec_ref_known(v___x_3562_, 2);
v_pos_3544_ = v_pos_3563_;
v_res_3545_ = v_res_3564_;
goto v___jp_3543_;
}
else
{
lean_object* v_pos_3565_; lean_object* v_err_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3573_; 
v_pos_3565_ = lean_ctor_get(v___x_3562_, 0);
v_err_3566_ = lean_ctor_get(v___x_3562_, 1);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3568_ = v___x_3562_;
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_err_3566_);
lean_inc(v_pos_3565_);
lean_dec(v___x_3562_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___x_3571_; 
if (v_isShared_3569_ == 0)
{
v___x_3571_ = v___x_3568_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_pos_3565_);
lean_ctor_set(v_reuseFailAlloc_3572_, 1, v_err_3566_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
}
}
}
v___jp_3543_:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3546_, 0, v_res_3545_);
v___x_3547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3547_, 0, v_pos_3544_);
lean_ctor_set(v___x_3547_, 1, v___x_3546_);
return v___x_3547_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURIReference(lean_object* v_config_3575_, lean_object* v_a_3576_){
_start:
{
lean_object* v___x_3577_; 
lean_inc_ref(v_a_3576_);
lean_inc_ref(v_config_3575_);
v___x_3577_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_uri(v_config_3575_, v_a_3576_);
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_dec_ref(v_a_3576_);
lean_dec_ref(v_config_3575_);
return v___x_3577_;
}
else
{
lean_object* v_err_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3588_; 
v_err_3578_ = lean_ctor_get(v___x_3577_, 1);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3588_ == 0)
{
lean_object* v_unused_3589_; 
v_unused_3589_ = lean_ctor_get(v___x_3577_, 0);
lean_dec(v_unused_3589_);
v___x_3580_ = v___x_3577_;
v_isShared_3581_ = v_isSharedCheck_3588_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_err_3578_);
lean_dec(v___x_3577_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3588_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v_idx_3582_; uint8_t v___x_3583_; 
v_idx_3582_ = lean_ctor_get(v_a_3576_, 1);
v___x_3583_ = lean_nat_dec_eq(v_idx_3582_, v_idx_3582_);
if (v___x_3583_ == 0)
{
lean_object* v___x_3585_; 
lean_dec_ref(v_config_3575_);
if (v_isShared_3581_ == 0)
{
lean_ctor_set(v___x_3580_, 0, v_a_3576_);
v___x_3585_ = v___x_3580_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3576_);
lean_ctor_set(v_reuseFailAlloc_3586_, 1, v_err_3578_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
else
{
lean_object* v___x_3587_; 
lean_del_object(v___x_3580_);
lean_dec(v_err_3578_);
v___x_3587_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_relative(v_config_3575_, v_a_3576_);
return v___x_3587_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader(lean_object* v_config_3596_, lean_object* v_a_3597_){
_start:
{
lean_object* v___x_3598_; 
v___x_3598_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_3596_, v_a_3597_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_pos_3599_; lean_object* v_res_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3669_; 
v_pos_3599_ = lean_ctor_get(v___x_3598_, 0);
v_res_3600_ = lean_ctor_get(v___x_3598_, 1);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3602_ = v___x_3598_;
v_isShared_3603_ = v_isSharedCheck_3669_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_res_3600_);
lean_inc(v_pos_3599_);
lean_dec(v___x_3598_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3669_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v_port_3605_; lean_object* v___y_3606_; lean_object* v_pos_3620_; lean_object* v_pos_3623_; lean_object* v_array_3624_; lean_object* v_idx_3625_; lean_object* v_array_3631_; lean_object* v_idx_3632_; lean_object* v___x_3633_; uint8_t v___x_3634_; 
v_array_3631_ = lean_ctor_get(v_pos_3599_, 0);
v_idx_3632_ = lean_ctor_get(v_pos_3599_, 1);
v___x_3633_ = lean_byte_array_size(v_array_3631_);
v___x_3634_ = lean_nat_dec_lt(v_idx_3632_, v___x_3633_);
if (v___x_3634_ == 0)
{
v_pos_3620_ = v_pos_3599_;
goto v___jp_3619_;
}
else
{
uint8_t v___x_3635_; uint8_t v___x_3636_; uint8_t v___x_3637_; 
v___x_3635_ = lean_byte_array_fget(v_array_3631_, v_idx_3632_);
v___x_3636_ = 58;
v___x_3637_ = lean_uint8_dec_eq(v___x_3635_, v___x_3636_);
if (v___x_3637_ == 0)
{
v_pos_3620_ = v_pos_3599_;
goto v___jp_3619_;
}
else
{
lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3666_; 
lean_inc(v_idx_3632_);
lean_inc_ref(v_array_3631_);
v_isSharedCheck_3666_ = !lean_is_exclusive(v_pos_3599_);
if (v_isSharedCheck_3666_ == 0)
{
lean_object* v_unused_3667_; lean_object* v_unused_3668_; 
v_unused_3667_ = lean_ctor_get(v_pos_3599_, 1);
lean_dec(v_unused_3667_);
v_unused_3668_ = lean_ctor_get(v_pos_3599_, 0);
lean_dec(v_unused_3668_);
v___x_3639_ = v_pos_3599_;
v_isShared_3640_ = v_isSharedCheck_3666_;
goto v_resetjp_3638_;
}
else
{
lean_dec(v_pos_3599_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3666_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3644_; 
v___x_3641_ = lean_unsigned_to_nat(1u);
v___x_3642_ = lean_nat_add(v_idx_3632_, v___x_3641_);
lean_dec(v_idx_3632_);
lean_inc(v___x_3642_);
lean_inc_ref(v_array_3631_);
if (v_isShared_3640_ == 0)
{
lean_ctor_set(v___x_3639_, 1, v___x_3642_);
v___x_3644_ = v___x_3639_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_array_3631_);
lean_ctor_set(v_reuseFailAlloc_3665_, 1, v___x_3642_);
v___x_3644_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
uint8_t v___x_3645_; 
v___x_3645_ = lean_nat_dec_lt(v___x_3642_, v___x_3633_);
if (v___x_3645_ == 0)
{
v_pos_3623_ = v___x_3644_;
v_array_3624_ = v_array_3631_;
v_idx_3625_ = v___x_3642_;
goto v___jp_3622_;
}
else
{
uint8_t v___x_3646_; uint8_t v___x_3647_; uint8_t v___x_3648_; 
v___x_3646_ = lean_byte_array_fget(v_array_3631_, v___x_3642_);
v___x_3647_ = 48;
v___x_3648_ = lean_uint8_dec_le(v___x_3647_, v___x_3646_);
if (v___x_3648_ == 0)
{
v_pos_3623_ = v___x_3644_;
v_array_3624_ = v_array_3631_;
v_idx_3625_ = v___x_3642_;
goto v___jp_3622_;
}
else
{
uint8_t v___x_3649_; uint8_t v___x_3650_; 
v___x_3649_ = 57;
v___x_3650_ = lean_uint8_dec_le(v___x_3646_, v___x_3649_);
if (v___x_3650_ == 0)
{
v_pos_3623_ = v___x_3644_;
v_array_3624_ = v_array_3631_;
v_idx_3625_ = v___x_3642_;
goto v___jp_3622_;
}
else
{
lean_object* v___x_3651_; 
lean_dec(v___x_3642_);
lean_dec_ref(v_array_3631_);
v___x_3651_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_3644_);
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v_pos_3652_; lean_object* v_res_3653_; lean_object* v___x_3654_; uint16_t v___x_3655_; 
v_pos_3652_ = lean_ctor_get(v___x_3651_, 0);
lean_inc(v_pos_3652_);
v_res_3653_ = lean_ctor_get(v___x_3651_, 1);
lean_inc(v_res_3653_);
lean_dec_ref_known(v___x_3651_, 2);
v___x_3654_ = lean_alloc_ctor(2, 0, 2);
v___x_3655_ = lean_unbox(v_res_3653_);
lean_dec(v_res_3653_);
lean_ctor_set_uint16(v___x_3654_, 0, v___x_3655_);
v_port_3605_ = v___x_3654_;
v___y_3606_ = v_pos_3652_;
goto v___jp_3604_;
}
else
{
lean_object* v_pos_3656_; lean_object* v_err_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3664_; 
lean_del_object(v___x_3602_);
lean_dec(v_res_3600_);
v_pos_3656_ = lean_ctor_get(v___x_3651_, 0);
v_err_3657_ = lean_ctor_get(v___x_3651_, 1);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3659_ = v___x_3651_;
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_err_3657_);
lean_inc(v_pos_3656_);
lean_dec(v___x_3651_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3662_; 
if (v_isShared_3660_ == 0)
{
v___x_3662_ = v___x_3659_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_pos_3656_);
lean_ctor_set(v_reuseFailAlloc_3663_, 1, v_err_3657_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
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
v___jp_3604_:
{
lean_object* v_array_3607_; lean_object* v_idx_3608_; lean_object* v___x_3609_; uint8_t v___x_3610_; 
v_array_3607_ = lean_ctor_get(v___y_3606_, 0);
v_idx_3608_ = lean_ctor_get(v___y_3606_, 1);
v___x_3609_ = lean_byte_array_size(v_array_3607_);
v___x_3610_ = lean_nat_dec_lt(v_idx_3608_, v___x_3609_);
if (v___x_3610_ == 0)
{
lean_object* v___x_3611_; lean_object* v___x_3613_; 
v___x_3611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3611_, 0, v_res_3600_);
lean_ctor_set(v___x_3611_, 1, v_port_3605_);
if (v_isShared_3603_ == 0)
{
lean_ctor_set(v___x_3602_, 1, v___x_3611_);
lean_ctor_set(v___x_3602_, 0, v___y_3606_);
v___x_3613_ = v___x_3602_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v___y_3606_);
lean_ctor_set(v_reuseFailAlloc_3614_, 1, v___x_3611_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
else
{
lean_object* v___x_3615_; lean_object* v___x_3617_; 
lean_dec(v_port_3605_);
lean_dec(v_res_3600_);
v___x_3615_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__1));
if (v_isShared_3603_ == 0)
{
lean_ctor_set_tag(v___x_3602_, 1);
lean_ctor_set(v___x_3602_, 1, v___x_3615_);
lean_ctor_set(v___x_3602_, 0, v___y_3606_);
v___x_3617_ = v___x_3602_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___y_3606_);
lean_ctor_set(v_reuseFailAlloc_3618_, 1, v___x_3615_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
v___jp_3619_:
{
lean_object* v___x_3621_; 
v___x_3621_ = lean_box(0);
v_port_3605_ = v___x_3621_;
v___y_3606_ = v_pos_3620_;
goto v___jp_3604_;
}
v___jp_3622_:
{
lean_object* v___x_3626_; uint8_t v___x_3627_; 
v___x_3626_ = lean_byte_array_size(v_array_3624_);
lean_dec_ref(v_array_3624_);
v___x_3627_ = lean_nat_dec_lt(v_idx_3625_, v___x_3626_);
lean_dec(v_idx_3625_);
if (v___x_3627_ == 0)
{
lean_object* v___x_3628_; 
v___x_3628_ = lean_box(1);
v_port_3605_ = v___x_3628_;
v___y_3606_ = v_pos_3623_;
goto v___jp_3604_;
}
else
{
lean_object* v___x_3629_; lean_object* v___x_3630_; 
lean_del_object(v___x_3602_);
lean_dec(v_res_3600_);
v___x_3629_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__3));
v___x_3630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3630_, 0, v_pos_3623_);
lean_ctor_set(v___x_3630_, 1, v___x_3629_);
return v___x_3630_;
}
}
}
}
else
{
lean_object* v_pos_3670_; lean_object* v_err_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3678_; 
v_pos_3670_ = lean_ctor_get(v___x_3598_, 0);
v_err_3671_ = lean_ctor_get(v___x_3598_, 1);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3673_ = v___x_3598_;
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_err_3671_);
lean_inc(v_pos_3670_);
lean_dec(v___x_3598_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3676_; 
if (v_isShared_3674_ == 0)
{
v___x_3676_ = v___x_3673_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_pos_3670_);
lean_ctor_set(v_reuseFailAlloc_3677_, 1, v_err_3671_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader___boxed(lean_object* v_config_3679_, lean_object* v_a_3680_){
_start:
{
lean_object* v_res_3681_; 
v_res_3681_ = l_Std_Http_URI_Parser_parseHostHeader(v_config_3679_, v_a_3680_);
lean_dec_ref(v_config_3679_);
return v_res_3681_;
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
