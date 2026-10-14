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
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
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
lean_object* v___y_205_; lean_object* v___y_209_; lean_object* v___y_210_; uint8_t v___y_211_; lean_object* v___y_214_; uint32_t v___y_215_; lean_object* v___y_216_; lean_object* v_maxSchemeLength_221_; lean_object* v___x_222_; lean_object* v___y_224_; lean_object* v___y_225_; uint8_t v___x_241_; lean_object* v___y_243_; lean_object* v___y_244_; uint8_t v___y_245_; lean_object* v_lower_246_; lean_object* v_upper_247_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; uint8_t v___y_264_; lean_object* v___y_265_; 
v_maxSchemeLength_221_ = lean_ctor_get(v_config_199_, 0);
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_241_ = lean_nat_dec_eq(v_maxSchemeLength_221_, v___x_222_);
if (v___x_241_ == 0)
{
lean_object* v_array_267_; lean_object* v_idx_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
v_array_267_ = lean_ctor_get(v_a_200_, 0);
v_idx_268_ = lean_ctor_get(v_a_200_, 1);
v___x_269_ = lean_byte_array_size(v_array_267_);
v___x_270_ = lean_nat_dec_lt(v_idx_268_, v___x_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_box(0);
v___x_272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_272_, 0, v_a_200_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
return v___x_272_;
}
else
{
lean_object* v___f_273_; lean_object* v_pos_275_; uint8_t v_res_276_; uint8_t v_c_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v_it_x27_291_; uint8_t v___x_297_; uint8_t v___x_298_; 
v___f_273_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__8));
v_c_288_ = lean_byte_array_fget(v_array_267_, v_idx_268_);
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = lean_nat_add(v_idx_268_, v___x_289_);
lean_inc_ref(v_array_267_);
v_it_x27_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_291_, 0, v_array_267_);
lean_ctor_set(v_it_x27_291_, 1, v___x_290_);
v___x_297_ = 65;
v___x_298_ = lean_uint8_dec_le(v___x_297_, v_c_288_);
if (v___x_298_ == 0)
{
goto v___jp_292_;
}
else
{
uint8_t v___x_299_; uint8_t v___x_300_; 
v___x_299_ = 90;
v___x_300_ = lean_uint8_dec_le(v_c_288_, v___x_299_);
if (v___x_300_ == 0)
{
goto v___jp_292_;
}
else
{
lean_dec_ref(v_a_200_);
v_pos_275_ = v_it_x27_291_;
v_res_276_ = v_c_288_;
goto v___jp_274_;
}
}
v___jp_274_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v_snd_280_; lean_object* v_fst_281_; lean_object* v_fst_282_; lean_object* v_array_283_; lean_object* v_idx_284_; lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_277_ = lean_unsigned_to_nat(1u);
v___x_278_ = lean_nat_sub(v_maxSchemeLength_221_, v___x_277_);
lean_inc_ref(v_pos_275_);
v___x_279_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_273_, v___x_278_, v___x_222_, v_pos_275_);
lean_dec(v___x_278_);
v_snd_280_ = lean_ctor_get(v___x_279_, 1);
lean_inc(v_snd_280_);
v_fst_281_ = lean_ctor_get(v___x_279_, 0);
lean_inc(v_fst_281_);
lean_dec_ref(v___x_279_);
v_fst_282_ = lean_ctor_get(v_snd_280_, 0);
lean_inc(v_fst_282_);
lean_dec(v_snd_280_);
v_array_283_ = lean_ctor_get(v_pos_275_, 0);
lean_inc_ref(v_array_283_);
v_idx_284_ = lean_ctor_get(v_pos_275_, 1);
lean_inc(v_idx_284_);
lean_dec_ref(v_pos_275_);
v___x_285_ = lean_nat_add(v_idx_284_, v_fst_281_);
lean_dec(v_fst_281_);
v___x_286_ = lean_byte_array_size(v_array_283_);
v___x_287_ = lean_nat_dec_le(v_idx_284_, v___x_222_);
if (v___x_287_ == 0)
{
v___y_260_ = v_array_283_;
v___y_261_ = v_fst_282_;
v___y_262_ = v___x_286_;
v___y_263_ = v___x_285_;
v___y_264_ = v_res_276_;
v___y_265_ = v_idx_284_;
goto v___jp_259_;
}
else
{
lean_dec(v_idx_284_);
v___y_260_ = v_array_283_;
v___y_261_ = v_fst_282_;
v___y_262_ = v___x_286_;
v___y_263_ = v___x_285_;
v___y_264_ = v_res_276_;
v___y_265_ = v___x_222_;
goto v___jp_259_;
}
}
v___jp_292_:
{
uint8_t v___x_293_; uint8_t v___x_294_; 
v___x_293_ = 97;
v___x_294_ = lean_uint8_dec_le(v___x_293_, v_c_288_);
if (v___x_294_ == 0)
{
lean_dec_ref_known(v_it_x27_291_, 2);
goto v___jp_201_;
}
else
{
uint8_t v___x_295_; uint8_t v___x_296_; 
v___x_295_ = 122;
v___x_296_ = lean_uint8_dec_le(v_c_288_, v___x_295_);
if (v___x_296_ == 0)
{
lean_dec_ref_known(v_it_x27_291_, 2);
goto v___jp_201_;
}
else
{
lean_dec_ref(v_a_200_);
v_pos_275_ = v_it_x27_291_;
v_res_276_ = v_c_288_;
goto v___jp_274_;
}
}
}
}
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10));
v___x_302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_302_, 0, v_a_200_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
return v___x_302_;
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
if (v___y_211_ == 0)
{
lean_dec_ref(v___y_210_);
v___y_205_ = v___y_209_;
goto v___jp_204_;
}
else
{
lean_object* v___x_212_; 
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v___y_209_);
lean_ctor_set(v___x_212_, 1, v___y_210_);
return v___x_212_;
}
}
v___jp_213_:
{
uint32_t v___x_217_; uint8_t v___x_218_; 
v___x_217_ = 97;
v___x_218_ = lean_uint32_dec_le(v___x_217_, v___y_215_);
if (v___x_218_ == 0)
{
lean_dec_ref(v___y_216_);
v___y_205_ = v___y_214_;
goto v___jp_204_;
}
else
{
uint32_t v___x_219_; uint8_t v___x_220_; 
v___x_219_ = 122;
v___x_220_ = lean_uint32_dec_le(v___y_215_, v___x_219_);
v___y_209_ = v___y_214_;
v___y_210_ = v___y_216_;
v___y_211_ = v___x_220_;
goto v___jp_208_;
}
}
v___jp_223_:
{
lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_226_ = l_String_mapAux___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(v___y_225_, v___x_222_);
lean_inc_ref(v___x_226_);
v___x_227_ = l_Std_Http_Internal_instDecidableIsLowerCase(v___x_226_);
if (v___x_227_ == 0)
{
lean_dec_ref(v___x_226_);
v___y_205_ = v___y_224_;
goto v___jp_204_;
}
else
{
lean_object* v___x_228_; uint8_t v___x_229_; 
lean_inc_ref(v___x_226_);
v___x_228_ = l_String_toListImpl(v___x_226_);
v___x_229_ = l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(v___x_228_);
if (v___x_229_ == 0)
{
lean_dec(v___x_228_);
v___y_209_ = v___y_224_;
v___y_210_ = v___x_226_;
v___y_211_ = v___x_229_;
goto v___jp_208_;
}
else
{
lean_object* v___x_230_; 
v___x_230_ = l_List_head_x3f___redArg(v___x_228_);
lean_dec(v___x_228_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_dec_ref(v___x_226_);
v___y_205_ = v___y_224_;
goto v___jp_204_;
}
else
{
lean_object* v_val_231_; uint32_t v___x_232_; uint32_t v___x_233_; uint8_t v___x_234_; 
v_val_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_val_231_);
lean_dec_ref_known(v___x_230_, 1);
v___x_232_ = 65;
v___x_233_ = lean_unbox_uint32(v_val_231_);
v___x_234_ = lean_uint32_dec_le(v___x_232_, v___x_233_);
if (v___x_234_ == 0)
{
uint32_t v___x_235_; 
v___x_235_ = lean_unbox_uint32(v_val_231_);
lean_dec(v_val_231_);
v___y_214_ = v___y_224_;
v___y_215_ = v___x_235_;
v___y_216_ = v___x_226_;
goto v___jp_213_;
}
else
{
uint32_t v___x_236_; uint32_t v___x_237_; uint8_t v___x_238_; 
v___x_236_ = 90;
v___x_237_ = lean_unbox_uint32(v_val_231_);
v___x_238_ = lean_uint32_dec_le(v___x_237_, v___x_236_);
if (v___x_238_ == 0)
{
uint32_t v___x_239_; 
v___x_239_ = lean_unbox_uint32(v_val_231_);
lean_dec(v_val_231_);
v___y_214_ = v___y_224_;
v___y_215_ = v___x_239_;
v___y_216_ = v___x_226_;
goto v___jp_213_;
}
else
{
lean_object* v___x_240_; 
lean_dec(v_val_231_);
v___x_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_240_, 0, v___y_224_);
lean_ctor_set(v___x_240_, 1, v___x_226_);
return v___x_240_;
}
}
}
}
}
}
v___jp_242_:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_248_ = l_ByteArray_toByteSlice(v___y_243_, v_lower_246_, v_upper_247_);
v___x_249_ = l_ByteArray_empty;
v___x_250_ = lean_byte_array_push(v___x_249_, v___y_245_);
v___x_251_ = l_ByteSlice_toByteArray(v___x_248_);
v___x_252_ = lean_byte_array_size(v___x_250_);
v___x_253_ = lean_byte_array_size(v___x_251_);
v___x_254_ = lean_byte_array_copy_slice(v___x_251_, v___x_222_, v___x_250_, v___x_252_, v___x_253_, v___x_241_);
lean_dec_ref(v___x_251_);
v___x_255_ = lean_string_validate_utf8(v___x_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; 
lean_dec_ref(v___x_254_);
v___x_256_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_257_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_256_);
v___y_224_ = v___y_244_;
v___y_225_ = v___x_257_;
goto v___jp_223_;
}
else
{
lean_object* v___x_258_; 
v___x_258_ = lean_string_from_utf8_unchecked(v___x_254_);
v___y_224_ = v___y_244_;
v___y_225_ = v___x_258_;
goto v___jp_223_;
}
}
v___jp_259_:
{
uint8_t v___x_266_; 
v___x_266_ = lean_nat_dec_le(v___y_263_, v___y_262_);
if (v___x_266_ == 0)
{
lean_dec(v___y_263_);
v___y_243_ = v___y_260_;
v___y_244_ = v___y_261_;
v___y_245_ = v___y_264_;
v_lower_246_ = v___y_265_;
v_upper_247_ = v___y_262_;
goto v___jp_242_;
}
else
{
lean_dec(v___y_262_);
v___y_243_ = v___y_260_;
v___y_244_ = v___y_261_;
v___y_245_ = v___y_264_;
v_lower_246_ = v___y_265_;
v_upper_247_ = v___y_263_;
goto v___jp_242_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___boxed(lean_object* v_config_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_303_, v_a_304_);
lean_dec_ref(v_config_303_);
return v_res_305_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0(uint8_t v___y_306_){
_start:
{
uint8_t v___x_307_; uint8_t v___x_308_; 
v___x_307_ = 48;
v___x_308_ = lean_uint8_dec_le(v___x_307_, v___y_306_);
if (v___x_308_ == 0)
{
return v___x_308_;
}
else
{
uint8_t v___x_309_; uint8_t v___x_310_; 
v___x_309_ = 57;
v___x_310_ = lean_uint8_dec_le(v___y_306_, v___x_309_);
return v___x_310_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0___boxed(lean_object* v___y_311_){
_start:
{
uint8_t v___y_560__boxed_312_; uint8_t v_res_313_; lean_object* v_r_314_; 
v___y_560__boxed_312_ = lean_unbox(v___y_311_);
v_res_313_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0(v___y_560__boxed_312_);
v_r_314_ = lean_box(v_res_313_);
return v_r_314_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(lean_object* v_a_318_){
_start:
{
lean_object* v___f_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v_snd_323_; lean_object* v_fst_324_; lean_object* v_fst_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_378_; 
v___f_319_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__0));
v___x_320_ = lean_unsigned_to_nat(5u);
v___x_321_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_318_);
v___x_322_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_319_, v___x_320_, v___x_321_, v_a_318_);
v_snd_323_ = lean_ctor_get(v___x_322_, 1);
lean_inc(v_snd_323_);
v_fst_324_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_fst_324_);
lean_dec_ref(v___x_322_);
v_fst_325_ = lean_ctor_get(v_snd_323_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v_snd_323_);
if (v_isSharedCheck_378_ == 0)
{
lean_object* v_unused_379_; 
v_unused_379_ = lean_ctor_get(v_snd_323_, 1);
lean_dec(v_unused_379_);
v___x_327_ = v_snd_323_;
v_isShared_328_ = v_isSharedCheck_378_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_fst_325_);
lean_dec(v_snd_323_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_378_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___y_330_; lean_object* v_array_361_; lean_object* v_idx_362_; lean_object* v_lower_364_; lean_object* v_upper_365_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___y_375_; uint8_t v___x_377_; 
v_array_361_ = lean_ctor_get(v_a_318_, 0);
lean_inc_ref(v_array_361_);
v_idx_362_ = lean_ctor_get(v_a_318_, 1);
lean_inc(v_idx_362_);
lean_dec_ref(v_a_318_);
v___x_372_ = lean_nat_add(v_idx_362_, v_fst_324_);
lean_dec(v_fst_324_);
v___x_373_ = lean_byte_array_size(v_array_361_);
v___x_377_ = lean_nat_dec_le(v_idx_362_, v___x_321_);
if (v___x_377_ == 0)
{
v___y_375_ = v_idx_362_;
goto v___jp_374_;
}
else
{
lean_dec(v_idx_362_);
v___y_375_ = v___x_321_;
goto v___jp_374_;
}
v___jp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = lean_string_utf8_byte_size(v___y_330_);
lean_inc_ref(v___y_330_);
v___x_332_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_332_, 0, v___y_330_);
lean_ctor_set(v___x_332_, 1, v___x_321_);
lean_ctor_set(v___x_332_, 2, v___x_331_);
v___x_333_ = l_String_Slice_toNat_x3f(v___x_332_);
lean_dec_ref_known(v___x_332_, 3);
if (lean_obj_tag(v___x_333_) == 1)
{
lean_object* v_val_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_354_; 
lean_dec_ref(v___y_330_);
v_val_334_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_354_ == 0)
{
v___x_336_ = v___x_333_;
v_isShared_337_ = v_isSharedCheck_354_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_val_334_);
lean_dec(v___x_333_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_354_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_338_ = lean_unsigned_to_nat(65535u);
v___x_339_ = lean_nat_dec_lt(v___x_338_, v_val_334_);
if (v___x_339_ == 0)
{
uint16_t v___x_340_; lean_object* v___x_341_; lean_object* v___x_343_; 
lean_del_object(v___x_336_);
v___x_340_ = lean_uint16_of_nat(v_val_334_);
lean_dec(v_val_334_);
v___x_341_ = lean_box(v___x_340_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v___x_341_);
v___x_343_ = v___x_327_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_fst_325_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v___x_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
else
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_349_; 
v___x_345_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__1));
v___x_346_ = l_Nat_reprFast(v_val_334_);
v___x_347_ = lean_string_append(v___x_345_, v___x_346_);
lean_dec_ref(v___x_346_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_347_);
v___x_349_ = v___x_336_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_347_);
v___x_349_ = v_reuseFailAlloc_353_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_object* v___x_351_; 
if (v_isShared_328_ == 0)
{
lean_ctor_set_tag(v___x_327_, 1);
lean_ctor_set(v___x_327_, 1, v___x_349_);
v___x_351_ = v___x_327_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_fst_325_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v___x_349_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
else
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_359_; 
lean_dec(v___x_333_);
v___x_355_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__2));
v___x_356_ = lean_string_append(v___x_355_, v___y_330_);
lean_dec_ref(v___y_330_);
v___x_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
if (v_isShared_328_ == 0)
{
lean_ctor_set_tag(v___x_327_, 1);
lean_ctor_set(v___x_327_, 1, v___x_357_);
v___x_359_ = v___x_327_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_fst_325_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v___x_357_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
v___jp_363_:
{
lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_366_ = l_ByteArray_toByteSlice(v_array_361_, v_lower_364_, v_upper_365_);
v___x_367_ = l_ByteSlice_toByteArray(v___x_366_);
v___x_368_ = lean_string_validate_utf8(v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; lean_object* v___x_370_; 
lean_dec_ref(v___x_367_);
v___x_369_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_370_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_369_);
v___y_330_ = v___x_370_;
goto v___jp_329_;
}
else
{
lean_object* v___x_371_; 
v___x_371_ = lean_string_from_utf8_unchecked(v___x_367_);
v___y_330_ = v___x_371_;
goto v___jp_329_;
}
}
v___jp_374_:
{
uint8_t v___x_376_; 
v___x_376_ = lean_nat_dec_le(v___x_372_, v___x_373_);
if (v___x_376_ == 0)
{
lean_dec(v___x_372_);
v_lower_364_ = v___y_375_;
v_upper_365_ = v___x_373_;
goto v___jp_363_;
}
else
{
v_lower_364_ = v___y_375_;
v_upper_365_ = v___x_372_;
goto v___jp_363_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0(uint8_t v_x_380_){
_start:
{
uint8_t v___x_426_; uint8_t v___x_427_; 
v___x_426_ = 58;
v___x_427_ = lean_uint8_dec_eq(v_x_380_, v___x_426_);
if (v___x_427_ == 0)
{
uint8_t v___x_428_; uint8_t v___x_429_; 
v___x_428_ = 48;
v___x_429_ = lean_uint8_dec_le(v___x_428_, v_x_380_);
if (v___x_429_ == 0)
{
goto v___jp_421_;
}
else
{
uint8_t v___x_430_; uint8_t v___x_431_; 
v___x_430_ = 57;
v___x_431_ = lean_uint8_dec_le(v_x_380_, v___x_430_);
if (v___x_431_ == 0)
{
goto v___jp_421_;
}
else
{
return v___x_431_;
}
}
}
else
{
uint8_t v___x_432_; 
v___x_432_ = 0;
return v___x_432_;
}
v___jp_381_:
{
uint8_t v___x_382_; uint8_t v___x_383_; 
v___x_382_ = 45;
v___x_383_ = lean_uint8_dec_eq(v_x_380_, v___x_382_);
if (v___x_383_ == 0)
{
uint8_t v___x_384_; uint8_t v___x_385_; 
v___x_384_ = 46;
v___x_385_ = lean_uint8_dec_eq(v_x_380_, v___x_384_);
if (v___x_385_ == 0)
{
uint8_t v___x_386_; uint8_t v___x_387_; 
v___x_386_ = 95;
v___x_387_ = lean_uint8_dec_eq(v_x_380_, v___x_386_);
if (v___x_387_ == 0)
{
uint8_t v___x_388_; uint8_t v___x_389_; 
v___x_388_ = 126;
v___x_389_ = lean_uint8_dec_eq(v_x_380_, v___x_388_);
if (v___x_389_ == 0)
{
uint8_t v___x_390_; uint8_t v___x_391_; 
v___x_390_ = 33;
v___x_391_ = lean_uint8_dec_eq(v_x_380_, v___x_390_);
if (v___x_391_ == 0)
{
uint8_t v___x_392_; uint8_t v___x_393_; 
v___x_392_ = 36;
v___x_393_ = lean_uint8_dec_eq(v_x_380_, v___x_392_);
if (v___x_393_ == 0)
{
uint8_t v___x_394_; uint8_t v___x_395_; 
v___x_394_ = 38;
v___x_395_ = lean_uint8_dec_eq(v_x_380_, v___x_394_);
if (v___x_395_ == 0)
{
uint8_t v___x_396_; uint8_t v___x_397_; 
v___x_396_ = 39;
v___x_397_ = lean_uint8_dec_eq(v_x_380_, v___x_396_);
if (v___x_397_ == 0)
{
uint8_t v___x_398_; uint8_t v___x_399_; 
v___x_398_ = 40;
v___x_399_ = lean_uint8_dec_eq(v_x_380_, v___x_398_);
if (v___x_399_ == 0)
{
uint8_t v___x_400_; uint8_t v___x_401_; 
v___x_400_ = 41;
v___x_401_ = lean_uint8_dec_eq(v_x_380_, v___x_400_);
if (v___x_401_ == 0)
{
uint8_t v___x_402_; uint8_t v___x_403_; 
v___x_402_ = 42;
v___x_403_ = lean_uint8_dec_eq(v_x_380_, v___x_402_);
if (v___x_403_ == 0)
{
uint8_t v___x_404_; uint8_t v___x_405_; 
v___x_404_ = 43;
v___x_405_ = lean_uint8_dec_eq(v_x_380_, v___x_404_);
if (v___x_405_ == 0)
{
uint8_t v___x_406_; uint8_t v___x_407_; 
v___x_406_ = 44;
v___x_407_ = lean_uint8_dec_eq(v_x_380_, v___x_406_);
if (v___x_407_ == 0)
{
uint8_t v___x_408_; uint8_t v___x_409_; 
v___x_408_ = 59;
v___x_409_ = lean_uint8_dec_eq(v_x_380_, v___x_408_);
if (v___x_409_ == 0)
{
uint8_t v___x_410_; uint8_t v___x_411_; 
v___x_410_ = 61;
v___x_411_ = lean_uint8_dec_eq(v_x_380_, v___x_410_);
if (v___x_411_ == 0)
{
uint8_t v___x_412_; uint8_t v___x_413_; 
v___x_412_ = 58;
v___x_413_ = lean_uint8_dec_eq(v_x_380_, v___x_412_);
if (v___x_413_ == 0)
{
uint8_t v___x_414_; uint8_t v___x_415_; 
v___x_414_ = 37;
v___x_415_ = lean_uint8_dec_eq(v_x_380_, v___x_414_);
return v___x_415_;
}
else
{
return v___x_413_;
}
}
else
{
return v___x_411_;
}
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
v___jp_416_:
{
uint8_t v___x_417_; uint8_t v___x_418_; 
v___x_417_ = 65;
v___x_418_ = lean_uint8_dec_le(v___x_417_, v_x_380_);
if (v___x_418_ == 0)
{
goto v___jp_381_;
}
else
{
uint8_t v___x_419_; uint8_t v___x_420_; 
v___x_419_ = 90;
v___x_420_ = lean_uint8_dec_le(v_x_380_, v___x_419_);
if (v___x_420_ == 0)
{
goto v___jp_381_;
}
else
{
return v___x_420_;
}
}
}
v___jp_421_:
{
uint8_t v___x_422_; uint8_t v___x_423_; 
v___x_422_ = 97;
v___x_423_ = lean_uint8_dec_le(v___x_422_, v_x_380_);
if (v___x_423_ == 0)
{
goto v___jp_416_;
}
else
{
uint8_t v___x_424_; uint8_t v___x_425_; 
v___x_424_ = 122;
v___x_425_ = lean_uint8_dec_le(v_x_380_, v___x_424_);
if (v___x_425_ == 0)
{
goto v___jp_416_;
}
else
{
return v___x_425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___boxed(lean_object* v_x_433_){
_start:
{
uint8_t v_x_boxed_434_; uint8_t v_res_435_; lean_object* v_r_436_; 
v_x_boxed_434_ = lean_unbox(v_x_433_);
v_res_435_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0(v_x_boxed_434_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1(uint8_t v___x_437_, uint8_t v___x_438_, uint8_t v_x_439_){
_start:
{
uint8_t v___x_484_; uint8_t v___x_485_; 
v___x_484_ = 48;
v___x_485_ = lean_uint8_dec_le(v___x_484_, v_x_439_);
if (v___x_485_ == 0)
{
goto v___jp_479_;
}
else
{
uint8_t v___x_486_; uint8_t v___x_487_; 
v___x_486_ = 57;
v___x_487_ = lean_uint8_dec_le(v_x_439_, v___x_486_);
if (v___x_487_ == 0)
{
goto v___jp_479_;
}
else
{
return v___x_438_;
}
}
v___jp_440_:
{
uint8_t v___x_441_; uint8_t v___x_442_; 
v___x_441_ = 45;
v___x_442_ = lean_uint8_dec_eq(v_x_439_, v___x_441_);
if (v___x_442_ == 0)
{
uint8_t v___x_443_; uint8_t v___x_444_; 
v___x_443_ = 46;
v___x_444_ = lean_uint8_dec_eq(v_x_439_, v___x_443_);
if (v___x_444_ == 0)
{
uint8_t v___x_445_; uint8_t v___x_446_; 
v___x_445_ = 95;
v___x_446_ = lean_uint8_dec_eq(v_x_439_, v___x_445_);
if (v___x_446_ == 0)
{
uint8_t v___x_447_; uint8_t v___x_448_; 
v___x_447_ = 126;
v___x_448_ = lean_uint8_dec_eq(v_x_439_, v___x_447_);
if (v___x_448_ == 0)
{
uint8_t v___x_449_; uint8_t v___x_450_; 
v___x_449_ = 33;
v___x_450_ = lean_uint8_dec_eq(v_x_439_, v___x_449_);
if (v___x_450_ == 0)
{
uint8_t v___x_451_; uint8_t v___x_452_; 
v___x_451_ = 36;
v___x_452_ = lean_uint8_dec_eq(v_x_439_, v___x_451_);
if (v___x_452_ == 0)
{
uint8_t v___x_453_; uint8_t v___x_454_; 
v___x_453_ = 38;
v___x_454_ = lean_uint8_dec_eq(v_x_439_, v___x_453_);
if (v___x_454_ == 0)
{
uint8_t v___x_455_; uint8_t v___x_456_; 
v___x_455_ = 39;
v___x_456_ = lean_uint8_dec_eq(v_x_439_, v___x_455_);
if (v___x_456_ == 0)
{
uint8_t v___x_457_; uint8_t v___x_458_; 
v___x_457_ = 40;
v___x_458_ = lean_uint8_dec_eq(v_x_439_, v___x_457_);
if (v___x_458_ == 0)
{
uint8_t v___x_459_; uint8_t v___x_460_; 
v___x_459_ = 41;
v___x_460_ = lean_uint8_dec_eq(v_x_439_, v___x_459_);
if (v___x_460_ == 0)
{
uint8_t v___x_461_; uint8_t v___x_462_; 
v___x_461_ = 42;
v___x_462_ = lean_uint8_dec_eq(v_x_439_, v___x_461_);
if (v___x_462_ == 0)
{
uint8_t v___x_463_; uint8_t v___x_464_; 
v___x_463_ = 43;
v___x_464_ = lean_uint8_dec_eq(v_x_439_, v___x_463_);
if (v___x_464_ == 0)
{
uint8_t v___x_465_; uint8_t v___x_466_; 
v___x_465_ = 44;
v___x_466_ = lean_uint8_dec_eq(v_x_439_, v___x_465_);
if (v___x_466_ == 0)
{
uint8_t v___x_467_; uint8_t v___x_468_; 
v___x_467_ = 59;
v___x_468_ = lean_uint8_dec_eq(v_x_439_, v___x_467_);
if (v___x_468_ == 0)
{
uint8_t v___x_469_; uint8_t v___x_470_; 
v___x_469_ = 61;
v___x_470_ = lean_uint8_dec_eq(v_x_439_, v___x_469_);
if (v___x_470_ == 0)
{
uint8_t v___x_471_; 
v___x_471_ = lean_uint8_dec_eq(v_x_439_, v___x_437_);
if (v___x_471_ == 0)
{
uint8_t v___x_472_; uint8_t v___x_473_; 
v___x_472_ = 37;
v___x_473_ = lean_uint8_dec_eq(v_x_439_, v___x_472_);
return v___x_473_;
}
else
{
return v___x_438_;
}
}
else
{
return v___x_438_;
}
}
else
{
return v___x_438_;
}
}
else
{
return v___x_438_;
}
}
else
{
return v___x_438_;
}
}
else
{
return v___x_438_;
}
}
else
{
return v___x_438_;
}
}
else
{
return v___x_438_;
}
}
else
{
return v___x_438_;
}
}
else
{
return v___x_438_;
}
}
else
{
return v___x_438_;
}
}
else
{
return v___x_438_;
}
}
else
{
return v___x_438_;
}
}
else
{
return v___x_438_;
}
}
else
{
return v___x_438_;
}
}
else
{
return v___x_438_;
}
}
v___jp_474_:
{
uint8_t v___x_475_; uint8_t v___x_476_; 
v___x_475_ = 65;
v___x_476_ = lean_uint8_dec_le(v___x_475_, v_x_439_);
if (v___x_476_ == 0)
{
goto v___jp_440_;
}
else
{
uint8_t v___x_477_; uint8_t v___x_478_; 
v___x_477_ = 90;
v___x_478_ = lean_uint8_dec_le(v_x_439_, v___x_477_);
if (v___x_478_ == 0)
{
goto v___jp_440_;
}
else
{
return v___x_438_;
}
}
}
v___jp_479_:
{
uint8_t v___x_480_; uint8_t v___x_481_; 
v___x_480_ = 97;
v___x_481_ = lean_uint8_dec_le(v___x_480_, v_x_439_);
if (v___x_481_ == 0)
{
goto v___jp_474_;
}
else
{
uint8_t v___x_482_; uint8_t v___x_483_; 
v___x_482_ = 122;
v___x_483_ = lean_uint8_dec_le(v_x_439_, v___x_482_);
if (v___x_483_ == 0)
{
goto v___jp_474_;
}
else
{
return v___x_438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1___boxed(lean_object* v___x_488_, lean_object* v___x_489_, lean_object* v_x_490_){
_start:
{
uint8_t v___x_4626__boxed_491_; uint8_t v___x_4627__boxed_492_; uint8_t v_x_boxed_493_; uint8_t v_res_494_; lean_object* v_r_495_; 
v___x_4626__boxed_491_ = lean_unbox(v___x_488_);
v___x_4627__boxed_492_ = lean_unbox(v___x_489_);
v_x_boxed_493_ = lean_unbox(v_x_490_);
v_res_494_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1(v___x_4626__boxed_491_, v___x_4627__boxed_492_, v_x_boxed_493_);
v_r_495_ = lean_box(v_res_494_);
return v_r_495_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(lean_object* v_config_500_, lean_object* v_a_501_){
_start:
{
lean_object* v___y_503_; lean_object* v_userPassEncoded_504_; lean_object* v___y_505_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v_lower_512_; lean_object* v_upper_513_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_528_; lean_object* v_pos_529_; lean_object* v_maxUserInfoLength_531_; lean_object* v___f_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v_snd_535_; lean_object* v_fst_536_; lean_object* v_fst_537_; lean_object* v_array_538_; lean_object* v_idx_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_591_; 
v_maxUserInfoLength_531_ = lean_ctor_get(v_config_500_, 2);
v___f_532_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__2));
v___x_533_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_501_);
v___x_534_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_532_, v_maxUserInfoLength_531_, v___x_533_, v_a_501_);
v_snd_535_ = lean_ctor_get(v___x_534_, 1);
lean_inc(v_snd_535_);
v_fst_536_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_fst_536_);
lean_dec_ref(v___x_534_);
v_fst_537_ = lean_ctor_get(v_snd_535_, 0);
lean_inc(v_fst_537_);
lean_dec(v_snd_535_);
v_array_538_ = lean_ctor_get(v_a_501_, 0);
v_idx_539_ = lean_ctor_get(v_a_501_, 1);
v_isSharedCheck_591_ = !lean_is_exclusive(v_a_501_);
if (v_isSharedCheck_591_ == 0)
{
v___x_541_ = v_a_501_;
v_isShared_542_ = v_isSharedCheck_591_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_idx_539_);
lean_inc(v_array_538_);
lean_dec(v_a_501_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_591_;
goto v_resetjp_540_;
}
v___jp_502_:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_506_, 0, v___y_503_);
lean_ctor_set(v___x_506_, 1, v_userPassEncoded_504_);
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v___y_505_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
return v___x_507_;
}
v___jp_508_:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_514_ = l_ByteArray_toByteSlice(v___y_509_, v_lower_512_, v_upper_513_);
v___x_515_ = l_ByteSlice_toByteArray(v___x_514_);
v___x_516_ = l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(v___x_515_);
if (lean_obj_tag(v___x_516_) == 1)
{
v___y_503_ = v___y_511_;
v_userPassEncoded_504_ = v___x_516_;
v___y_505_ = v___y_510_;
goto v___jp_502_;
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; 
lean_dec(v___x_516_);
lean_dec_ref(v___y_511_);
v___x_517_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1));
v___x_518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_518_, 0, v___y_510_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
return v___x_518_;
}
}
v___jp_519_:
{
uint8_t v___x_526_; 
v___x_526_ = lean_nat_dec_le(v___y_521_, v___y_522_);
if (v___x_526_ == 0)
{
lean_dec(v___y_521_);
v___y_509_ = v___y_520_;
v___y_510_ = v___y_523_;
v___y_511_ = v___y_524_;
v_lower_512_ = v___y_525_;
v_upper_513_ = v___y_522_;
goto v___jp_508_;
}
else
{
lean_dec(v___y_522_);
v___y_509_ = v___y_520_;
v___y_510_ = v___y_523_;
v___y_511_ = v___y_524_;
v_lower_512_ = v___y_525_;
v_upper_513_ = v___y_521_;
goto v___jp_508_;
}
}
v___jp_527_:
{
lean_object* v___x_530_; 
v___x_530_ = lean_box(0);
v___y_503_ = v___y_528_;
v_userPassEncoded_504_ = v___x_530_;
v___y_505_ = v_pos_529_;
goto v___jp_502_;
}
v_resetjp_540_:
{
lean_object* v_lower_544_; lean_object* v_upper_545_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___y_588_; uint8_t v___x_590_; 
v___x_585_ = lean_nat_add(v_idx_539_, v_fst_536_);
lean_dec(v_fst_536_);
v___x_586_ = lean_byte_array_size(v_array_538_);
v___x_590_ = lean_nat_dec_le(v_idx_539_, v___x_533_);
if (v___x_590_ == 0)
{
v___y_588_ = v_idx_539_;
goto v___jp_587_;
}
else
{
lean_dec(v_idx_539_);
v___y_588_ = v___x_533_;
goto v___jp_587_;
}
v___jp_543_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_546_ = l_ByteArray_toByteSlice(v_array_538_, v_lower_544_, v_upper_545_);
v___x_547_ = l_ByteSlice_toByteArray(v___x_546_);
v___x_548_ = l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(v___x_547_);
if (lean_obj_tag(v___x_548_) == 1)
{
lean_object* v_val_549_; lean_object* v_array_550_; lean_object* v_idx_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v_val_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_val_549_);
lean_dec_ref_known(v___x_548_, 1);
v_array_550_ = lean_ctor_get(v_fst_537_, 0);
v_idx_551_ = lean_ctor_get(v_fst_537_, 1);
v___x_552_ = lean_byte_array_size(v_array_550_);
v___x_553_ = lean_nat_dec_lt(v_idx_551_, v___x_552_);
if (v___x_553_ == 0)
{
lean_del_object(v___x_541_);
v___y_528_ = v_val_549_;
v_pos_529_ = v_fst_537_;
goto v___jp_527_;
}
else
{
uint8_t v___x_554_; uint8_t v___x_555_; uint8_t v___x_556_; 
v___x_554_ = lean_byte_array_fget(v_array_550_, v_idx_551_);
v___x_555_ = 58;
v___x_556_ = lean_uint8_dec_eq(v___x_554_, v___x_555_);
if (v___x_556_ == 0)
{
lean_del_object(v___x_541_);
v___y_528_ = v_val_549_;
v_pos_529_ = v_fst_537_;
goto v___jp_527_;
}
else
{
if (v___x_553_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_559_; 
lean_dec(v_val_549_);
v___x_557_ = lean_box(0);
if (v_isShared_542_ == 0)
{
lean_ctor_set_tag(v___x_541_, 1);
lean_ctor_set(v___x_541_, 1, v___x_557_);
lean_ctor_set(v___x_541_, 0, v_fst_537_);
v___x_559_ = v___x_541_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_fst_537_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
else
{
lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_578_; 
lean_inc(v_idx_551_);
lean_inc_ref(v_array_550_);
lean_del_object(v___x_541_);
v_isSharedCheck_578_ = !lean_is_exclusive(v_fst_537_);
if (v_isSharedCheck_578_ == 0)
{
lean_object* v_unused_579_; lean_object* v_unused_580_; 
v_unused_579_ = lean_ctor_get(v_fst_537_, 1);
lean_dec(v_unused_579_);
v_unused_580_ = lean_ctor_get(v_fst_537_, 0);
lean_dec(v_unused_580_);
v___x_562_ = v_fst_537_;
v_isShared_563_ = v_isSharedCheck_578_;
goto v_resetjp_561_;
}
else
{
lean_dec(v_fst_537_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_578_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___f_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_564_ = lean_box(v___x_555_);
v___x_565_ = lean_box(v___x_553_);
v___f_566_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1___boxed), 3, 2);
lean_closure_set(v___f_566_, 0, v___x_564_);
lean_closure_set(v___f_566_, 1, v___x_565_);
v___x_567_ = lean_unsigned_to_nat(1u);
v___x_568_ = lean_nat_add(v_idx_551_, v___x_567_);
lean_dec(v_idx_551_);
lean_inc(v___x_568_);
lean_inc_ref(v_array_550_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 1, v___x_568_);
v___x_570_ = v___x_562_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_array_550_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v___x_568_);
v___x_570_ = v_reuseFailAlloc_577_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_571_; lean_object* v_snd_572_; lean_object* v_fst_573_; lean_object* v_fst_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_571_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_566_, v_maxUserInfoLength_531_, v___x_533_, v___x_570_);
v_snd_572_ = lean_ctor_get(v___x_571_, 1);
lean_inc(v_snd_572_);
v_fst_573_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_fst_573_);
lean_dec_ref(v___x_571_);
v_fst_574_ = lean_ctor_get(v_snd_572_, 0);
lean_inc(v_fst_574_);
lean_dec(v_snd_572_);
v___x_575_ = lean_nat_add(v___x_568_, v_fst_573_);
lean_dec(v_fst_573_);
v___x_576_ = lean_nat_dec_le(v___x_568_, v___x_533_);
if (v___x_576_ == 0)
{
v___y_520_ = v_array_550_;
v___y_521_ = v___x_575_;
v___y_522_ = v___x_552_;
v___y_523_ = v_fst_574_;
v___y_524_ = v_val_549_;
v___y_525_ = v___x_568_;
goto v___jp_519_;
}
else
{
lean_dec(v___x_568_);
v___y_520_ = v_array_550_;
v___y_521_ = v___x_575_;
v___y_522_ = v___x_552_;
v___y_523_ = v_fst_574_;
v___y_524_ = v_val_549_;
v___y_525_ = v___x_533_;
goto v___jp_519_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_581_; lean_object* v___x_583_; 
lean_dec(v___x_548_);
v___x_581_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1));
if (v_isShared_542_ == 0)
{
lean_ctor_set_tag(v___x_541_, 1);
lean_ctor_set(v___x_541_, 1, v___x_581_);
lean_ctor_set(v___x_541_, 0, v_fst_537_);
v___x_583_ = v___x_541_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_fst_537_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
v___jp_587_:
{
uint8_t v___x_589_; 
v___x_589_ = lean_nat_dec_le(v___x_585_, v___x_586_);
if (v___x_589_ == 0)
{
lean_dec(v___x_585_);
v_lower_544_ = v___y_588_;
v_upper_545_ = v___x_586_;
goto v___jp_543_;
}
else
{
v_lower_544_ = v___y_588_;
v_upper_545_ = v___x_585_;
goto v___jp_543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___boxed(lean_object* v_config_592_, lean_object* v_a_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(v_config_592_, v_a_593_);
lean_dec_ref(v_config_592_);
return v_res_594_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(uint8_t v_x_595_){
_start:
{
uint8_t v___x_606_; uint8_t v___x_607_; 
v___x_606_ = 58;
v___x_607_ = lean_uint8_dec_eq(v_x_595_, v___x_606_);
if (v___x_607_ == 0)
{
uint8_t v___x_608_; uint8_t v___x_609_; 
v___x_608_ = 46;
v___x_609_ = lean_uint8_dec_eq(v_x_595_, v___x_608_);
if (v___x_609_ == 0)
{
uint8_t v___x_610_; uint8_t v___x_611_; 
v___x_610_ = 48;
v___x_611_ = lean_uint8_dec_le(v___x_610_, v_x_595_);
if (v___x_611_ == 0)
{
goto v___jp_601_;
}
else
{
uint8_t v___x_612_; uint8_t v___x_613_; 
v___x_612_ = 57;
v___x_613_ = lean_uint8_dec_le(v_x_595_, v___x_612_);
if (v___x_613_ == 0)
{
goto v___jp_601_;
}
else
{
return v___x_613_;
}
}
}
else
{
return v___x_609_;
}
}
else
{
return v___x_607_;
}
v___jp_596_:
{
uint8_t v___x_597_; uint8_t v___x_598_; 
v___x_597_ = 65;
v___x_598_ = lean_uint8_dec_le(v___x_597_, v_x_595_);
if (v___x_598_ == 0)
{
return v___x_598_;
}
else
{
uint8_t v___x_599_; uint8_t v___x_600_; 
v___x_599_ = 70;
v___x_600_ = lean_uint8_dec_le(v_x_595_, v___x_599_);
return v___x_600_;
}
}
v___jp_601_:
{
uint8_t v___x_602_; uint8_t v___x_603_; 
v___x_602_ = 97;
v___x_603_ = lean_uint8_dec_le(v___x_602_, v_x_595_);
if (v___x_603_ == 0)
{
goto v___jp_596_;
}
else
{
uint8_t v___x_604_; uint8_t v___x_605_; 
v___x_604_ = 102;
v___x_605_ = lean_uint8_dec_le(v_x_595_, v___x_604_);
if (v___x_605_ == 0)
{
goto v___jp_596_;
}
else
{
return v___x_605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___boxed(lean_object* v_x_614_){
_start:
{
uint8_t v_x_boxed_615_; uint8_t v_res_616_; lean_object* v_r_617_; 
v_x_boxed_615_ = lean_unbox(v_x_614_);
v_res_616_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(v_x_boxed_615_);
v_r_617_ = lean_box(v_res_616_);
return v_r_617_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(lean_object* v_a_629_){
_start:
{
lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v_array_640_; lean_object* v_idx_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v_array_640_ = lean_ctor_get(v_a_629_, 0);
v_idx_641_ = lean_ctor_get(v_a_629_, 1);
v___x_642_ = lean_byte_array_size(v_array_640_);
v___x_643_ = lean_nat_dec_lt(v_idx_641_, v___x_642_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_box(0);
v___x_645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_645_, 0, v_a_629_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
return v___x_645_;
}
else
{
uint8_t v___x_646_; uint8_t v_got_647_; uint8_t v___x_648_; 
v___x_646_ = 91;
v_got_647_ = lean_byte_array_fget(v_array_640_, v_idx_641_);
v___x_648_ = lean_uint8_dec_eq(v_got_647_, v___x_646_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_650_, 0, v_a_629_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
return v___x_650_;
}
else
{
lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_726_; 
lean_inc(v_idx_641_);
lean_inc_ref(v_array_640_);
v_isSharedCheck_726_ = !lean_is_exclusive(v_a_629_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; lean_object* v_unused_728_; 
v_unused_727_ = lean_ctor_get(v_a_629_, 1);
lean_dec(v_unused_727_);
v_unused_728_ = lean_ctor_get(v_a_629_, 0);
lean_dec(v_unused_728_);
v___x_652_ = v_a_629_;
v_isShared_653_ = v_isSharedCheck_726_;
goto v_resetjp_651_;
}
else
{
lean_dec(v_a_629_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_726_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___f_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_658_; 
v___f_654_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3));
v___x_655_ = lean_unsigned_to_nat(1u);
v___x_656_ = lean_nat_add(v_idx_641_, v___x_655_);
lean_dec(v_idx_641_);
lean_inc(v___x_656_);
lean_inc_ref(v_array_640_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 1, v___x_656_);
v___x_658_ = v___x_652_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_array_640_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v___x_656_);
v___x_658_ = v_reuseFailAlloc_725_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v_snd_662_; lean_object* v_fst_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_724_; 
v___x_659_ = lean_unsigned_to_nat(256u);
v___x_660_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___x_658_);
v___x_661_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_654_, v___x_659_, v___x_660_, v___x_658_);
v_snd_662_ = lean_ctor_get(v___x_661_, 1);
v_fst_663_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_724_ == 0)
{
v___x_665_ = v___x_661_;
v_isShared_666_ = v_isSharedCheck_724_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_snd_662_);
lean_inc(v_fst_663_);
lean_dec(v___x_661_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_724_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v_fst_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_722_; 
v_fst_667_ = lean_ctor_get(v_snd_662_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v_snd_662_);
if (v_isSharedCheck_722_ == 0)
{
lean_object* v_unused_723_; 
v_unused_723_ = lean_ctor_get(v_snd_662_, 1);
lean_dec(v_unused_723_);
v___x_669_ = v_snd_662_;
v_isShared_670_ = v_isSharedCheck_722_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_fst_667_);
lean_dec(v_snd_662_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_722_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___y_672_; uint8_t v___x_706_; 
v___x_706_ = lean_nat_dec_eq(v_fst_663_, v___x_660_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v___y_709_; uint8_t v___x_717_; 
lean_dec_ref(v___x_658_);
v___x_707_ = lean_nat_add(v___x_656_, v_fst_663_);
lean_dec(v_fst_663_);
v___x_717_ = lean_nat_dec_le(v___x_656_, v___x_660_);
if (v___x_717_ == 0)
{
v___y_709_ = v___x_656_;
goto v___jp_708_;
}
else
{
lean_dec(v___x_656_);
v___y_709_ = v___x_660_;
goto v___jp_708_;
}
v___jp_708_:
{
uint8_t v___x_710_; 
v___x_710_ = lean_nat_dec_le(v___x_707_, v___x_642_);
if (v___x_710_ == 0)
{
lean_object* v___x_712_; 
lean_dec(v___x_707_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v___x_642_);
lean_ctor_set(v___x_665_, 0, v___y_709_);
v___x_712_ = v___x_665_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___y_709_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v___x_642_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
v___y_672_ = v___x_712_;
goto v___jp_671_;
}
}
else
{
lean_object* v___x_715_; 
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v___x_707_);
lean_ctor_set(v___x_665_, 0, v___y_709_);
v___x_715_ = v___x_665_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___y_709_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v___x_707_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
v___y_672_ = v___x_715_;
goto v___jp_671_;
}
}
}
}
else
{
lean_object* v___x_718_; lean_object* v___x_720_; 
lean_del_object(v___x_669_);
lean_dec(v_fst_667_);
lean_dec(v_fst_663_);
lean_dec(v___x_656_);
lean_dec_ref(v_array_640_);
v___x_718_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7));
if (v_isShared_666_ == 0)
{
lean_ctor_set_tag(v___x_665_, 1);
lean_ctor_set(v___x_665_, 1, v___x_718_);
lean_ctor_set(v___x_665_, 0, v___x_658_);
v___x_720_ = v___x_665_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_658_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v___x_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
v___jp_671_:
{
lean_object* v_array_673_; lean_object* v_idx_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v_array_673_ = lean_ctor_get(v_fst_667_, 0);
v_idx_674_ = lean_ctor_get(v_fst_667_, 1);
v___x_675_ = lean_byte_array_size(v_array_673_);
v___x_676_ = lean_nat_dec_lt(v_idx_674_, v___x_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_679_; 
lean_dec_ref(v___y_672_);
lean_dec_ref(v_array_640_);
v___x_677_ = lean_box(0);
if (v_isShared_670_ == 0)
{
lean_ctor_set_tag(v___x_669_, 1);
lean_ctor_set(v___x_669_, 1, v___x_677_);
v___x_679_ = v___x_669_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_fst_667_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
else
{
uint8_t v___x_681_; uint8_t v_got_682_; uint8_t v___x_683_; 
v___x_681_ = 93;
v_got_682_ = lean_byte_array_fget(v_array_673_, v_idx_674_);
v___x_683_ = lean_uint8_dec_eq(v_got_682_, v___x_681_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; lean_object* v___x_686_; 
lean_dec_ref(v___y_672_);
lean_dec_ref(v_array_640_);
v___x_684_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5));
if (v_isShared_670_ == 0)
{
lean_ctor_set_tag(v___x_669_, 1);
lean_ctor_set(v___x_669_, 1, v___x_684_);
v___x_686_ = v___x_669_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_fst_667_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
else
{
lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_703_; 
lean_inc(v_idx_674_);
lean_inc_ref(v_array_673_);
lean_del_object(v___x_669_);
v_isSharedCheck_703_ = !lean_is_exclusive(v_fst_667_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; lean_object* v_unused_705_; 
v_unused_704_ = lean_ctor_get(v_fst_667_, 1);
lean_dec(v_unused_704_);
v_unused_705_ = lean_ctor_get(v_fst_667_, 0);
lean_dec(v_unused_705_);
v___x_689_ = v_fst_667_;
v_isShared_690_ = v_isSharedCheck_703_;
goto v_resetjp_688_;
}
else
{
lean_dec(v_fst_667_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_703_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v_lower_691_; lean_object* v_upper_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_696_; 
v_lower_691_ = lean_ctor_get(v___y_672_, 0);
lean_inc(v_lower_691_);
v_upper_692_ = lean_ctor_get(v___y_672_, 1);
lean_inc(v_upper_692_);
lean_dec_ref(v___y_672_);
v___x_693_ = l_ByteArray_toByteSlice(v_array_640_, v_lower_691_, v_upper_692_);
v___x_694_ = lean_nat_add(v_idx_674_, v___x_655_);
lean_dec(v_idx_674_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 1, v___x_694_);
v___x_696_ = v___x_689_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_array_673_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v___x_694_);
v___x_696_ = v_reuseFailAlloc_702_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_697_ = l_ByteSlice_toByteArray(v___x_693_);
v___x_698_ = lean_string_validate_utf8(v___x_697_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; lean_object* v___x_700_; 
lean_dec_ref(v___x_697_);
v___x_699_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_700_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_699_);
v___y_631_ = v___x_696_;
v___y_632_ = v___x_700_;
goto v___jp_630_;
}
else
{
lean_object* v___x_701_; 
v___x_701_ = lean_string_from_utf8_unchecked(v___x_697_);
v___y_631_ = v___x_696_;
v___y_632_ = v___x_701_;
goto v___jp_630_;
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
v___jp_630_:
{
lean_object* v___x_633_; 
v___x_633_ = lean_uv_pton_v6(v___y_632_);
if (lean_obj_tag(v___x_633_) == 1)
{
lean_object* v_val_634_; lean_object* v___x_635_; 
lean_dec_ref(v___y_632_);
v_val_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_val_634_);
lean_dec_ref_known(v___x_633_, 1);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v___y_631_);
lean_ctor_set(v___x_635_, 1, v_val_634_);
return v___x_635_;
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
lean_dec(v___x_633_);
v___x_636_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__0));
v___x_637_ = lean_string_append(v___x_636_, v___y_632_);
lean_dec_ref(v___y_632_);
v___x_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
v___x_639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_639_, 0, v___y_631_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
return v___x_639_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0(uint8_t v_x_729_){
_start:
{
uint8_t v___x_730_; uint8_t v___x_731_; 
v___x_730_ = 46;
v___x_731_ = lean_uint8_dec_eq(v_x_729_, v___x_730_);
if (v___x_731_ == 0)
{
uint8_t v___x_732_; uint8_t v___x_733_; 
v___x_732_ = 48;
v___x_733_ = lean_uint8_dec_le(v___x_732_, v_x_729_);
if (v___x_733_ == 0)
{
return v___x_733_;
}
else
{
uint8_t v___x_734_; uint8_t v___x_735_; 
v___x_734_ = 57;
v___x_735_ = lean_uint8_dec_le(v_x_729_, v___x_734_);
return v___x_735_;
}
}
else
{
return v___x_731_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0___boxed(lean_object* v_x_736_){
_start:
{
uint8_t v_x_boxed_737_; uint8_t v_res_738_; lean_object* v_r_739_; 
v_x_boxed_737_ = lean_unbox(v_x_736_);
v_res_738_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0(v_x_boxed_737_);
v_r_739_ = lean_box(v_res_738_);
return v_r_739_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(lean_object* v_a_742_){
_start:
{
lean_object* v___f_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v_snd_747_; lean_object* v_fst_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_793_; 
v___f_743_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__0));
v___x_744_ = lean_unsigned_to_nat(256u);
v___x_745_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_742_);
v___x_746_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_743_, v___x_744_, v___x_745_, v_a_742_);
v_snd_747_ = lean_ctor_get(v___x_746_, 1);
v_fst_748_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_793_ == 0)
{
v___x_750_ = v___x_746_;
v_isShared_751_ = v_isSharedCheck_793_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_snd_747_);
lean_inc(v_fst_748_);
lean_dec(v___x_746_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_793_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v_fst_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_791_; 
v_fst_752_ = lean_ctor_get(v_snd_747_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v_snd_747_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; 
v_unused_792_ = lean_ctor_get(v_snd_747_, 1);
lean_dec(v_unused_792_);
v___x_754_ = v_snd_747_;
v_isShared_755_ = v_isSharedCheck_791_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_fst_752_);
lean_dec(v_snd_747_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_791_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___y_757_; uint8_t v___x_769_; 
v___x_769_ = lean_nat_dec_eq(v_fst_748_, v___x_745_);
if (v___x_769_ == 0)
{
lean_object* v_array_770_; lean_object* v_idx_771_; lean_object* v_lower_773_; lean_object* v_upper_774_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___y_784_; uint8_t v___x_786_; 
lean_del_object(v___x_750_);
v_array_770_ = lean_ctor_get(v_a_742_, 0);
lean_inc_ref(v_array_770_);
v_idx_771_ = lean_ctor_get(v_a_742_, 1);
lean_inc(v_idx_771_);
lean_dec_ref(v_a_742_);
v___x_781_ = lean_nat_add(v_idx_771_, v_fst_748_);
lean_dec(v_fst_748_);
v___x_782_ = lean_byte_array_size(v_array_770_);
v___x_786_ = lean_nat_dec_le(v_idx_771_, v___x_745_);
if (v___x_786_ == 0)
{
v___y_784_ = v_idx_771_;
goto v___jp_783_;
}
else
{
lean_dec(v_idx_771_);
v___y_784_ = v___x_745_;
goto v___jp_783_;
}
v___jp_772_:
{
lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_775_ = l_ByteArray_toByteSlice(v_array_770_, v_lower_773_, v_upper_774_);
v___x_776_ = l_ByteSlice_toByteArray(v___x_775_);
v___x_777_ = lean_string_validate_utf8(v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; lean_object* v___x_779_; 
lean_dec_ref(v___x_776_);
v___x_778_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_779_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_778_);
v___y_757_ = v___x_779_;
goto v___jp_756_;
}
else
{
lean_object* v___x_780_; 
v___x_780_ = lean_string_from_utf8_unchecked(v___x_776_);
v___y_757_ = v___x_780_;
goto v___jp_756_;
}
}
v___jp_783_:
{
uint8_t v___x_785_; 
v___x_785_ = lean_nat_dec_le(v___x_781_, v___x_782_);
if (v___x_785_ == 0)
{
lean_dec(v___x_781_);
v_lower_773_ = v___y_784_;
v_upper_774_ = v___x_782_;
goto v___jp_772_;
}
else
{
v_lower_773_ = v___y_784_;
v_upper_774_ = v___x_781_;
goto v___jp_772_;
}
}
}
else
{
lean_object* v___x_787_; lean_object* v___x_789_; 
lean_del_object(v___x_754_);
lean_dec(v_fst_752_);
lean_dec(v_fst_748_);
v___x_787_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7));
if (v_isShared_751_ == 0)
{
lean_ctor_set_tag(v___x_750_, 1);
lean_ctor_set(v___x_750_, 1, v___x_787_);
lean_ctor_set(v___x_750_, 0, v_a_742_);
v___x_789_ = v___x_750_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_742_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
v___jp_756_:
{
lean_object* v___x_758_; 
v___x_758_ = lean_uv_pton_v4(v___y_757_);
if (lean_obj_tag(v___x_758_) == 1)
{
lean_object* v_val_759_; lean_object* v___x_761_; 
lean_dec_ref(v___y_757_);
v_val_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_val_759_);
lean_dec_ref_known(v___x_758_, 1);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 1, v_val_759_);
v___x_761_ = v___x_754_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_fst_752_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_val_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_767_; 
lean_dec(v___x_758_);
v___x_763_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__1));
v___x_764_ = lean_string_append(v___x_763_, v___y_757_);
lean_dec_ref(v___y_757_);
v___x_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
if (v_isShared_755_ == 0)
{
lean_ctor_set_tag(v___x_754_, 1);
lean_ctor_set(v___x_754_, 1, v___x_765_);
v___x_767_ = v___x_754_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_fst_752_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v___x_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
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
lean_object* v___x_797_; 
v___x_797_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0));
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___boxed(lean_object* v___dummy_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg();
return v_res_799_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0(void){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg();
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(lean_object* v_s_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___boxed(lean_object* v_s_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(v_s_803_);
lean_dec_ref(v_s_803_);
return v_res_804_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(uint8_t v___x_805_, uint8_t v_x_806_){
_start:
{
uint8_t v___x_822_; uint8_t v___x_823_; 
v___x_822_ = 48;
v___x_823_ = lean_uint8_dec_le(v___x_822_, v_x_806_);
if (v___x_823_ == 0)
{
goto v___jp_817_;
}
else
{
uint8_t v___x_824_; uint8_t v___x_825_; 
v___x_824_ = 57;
v___x_825_ = lean_uint8_dec_le(v_x_806_, v___x_824_);
if (v___x_825_ == 0)
{
goto v___jp_817_;
}
else
{
return v___x_805_;
}
}
v___jp_807_:
{
uint8_t v___x_808_; uint8_t v___x_809_; 
v___x_808_ = 45;
v___x_809_ = lean_uint8_dec_eq(v_x_806_, v___x_808_);
if (v___x_809_ == 0)
{
uint8_t v___x_810_; uint8_t v___x_811_; 
v___x_810_ = 46;
v___x_811_ = lean_uint8_dec_eq(v_x_806_, v___x_810_);
return v___x_811_;
}
else
{
return v___x_805_;
}
}
v___jp_812_:
{
uint8_t v___x_813_; uint8_t v___x_814_; 
v___x_813_ = 65;
v___x_814_ = lean_uint8_dec_le(v___x_813_, v_x_806_);
if (v___x_814_ == 0)
{
goto v___jp_807_;
}
else
{
uint8_t v___x_815_; uint8_t v___x_816_; 
v___x_815_ = 90;
v___x_816_ = lean_uint8_dec_le(v_x_806_, v___x_815_);
if (v___x_816_ == 0)
{
goto v___jp_807_;
}
else
{
return v___x_805_;
}
}
}
v___jp_817_:
{
uint8_t v___x_818_; uint8_t v___x_819_; 
v___x_818_ = 97;
v___x_819_ = lean_uint8_dec_le(v___x_818_, v_x_806_);
if (v___x_819_ == 0)
{
goto v___jp_812_;
}
else
{
uint8_t v___x_820_; uint8_t v___x_821_; 
v___x_820_ = 122;
v___x_821_ = lean_uint8_dec_le(v_x_806_, v___x_820_);
if (v___x_821_ == 0)
{
goto v___jp_812_;
}
else
{
return v___x_805_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed(lean_object* v___x_826_, lean_object* v_x_827_){
_start:
{
uint8_t v___x_12906__boxed_828_; uint8_t v_x_boxed_829_; uint8_t v_res_830_; lean_object* v_r_831_; 
v___x_12906__boxed_828_ = lean_unbox(v___x_826_);
v_x_boxed_829_ = lean_unbox(v_x_827_);
v_res_830_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(v___x_12906__boxed_828_, v_x_boxed_829_);
v_r_831_ = lean_box(v_res_830_);
return v_r_831_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(lean_object* v___x_832_, lean_object* v___x_833_, lean_object* v_a_834_, uint8_t v_b_835_){
_start:
{
if (lean_obj_tag(v_a_834_) == 0)
{
lean_object* v_currPos_836_; lean_object* v_searcher_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_851_; 
v_currPos_836_ = lean_ctor_get(v_a_834_, 0);
v_searcher_837_ = lean_ctor_get(v_a_834_, 1);
v_isSharedCheck_851_ = !lean_is_exclusive(v_a_834_);
if (v_isSharedCheck_851_ == 0)
{
v___x_839_ = v_a_834_;
v_isShared_840_ = v_isSharedCheck_851_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_searcher_837_);
lean_inc(v_currPos_836_);
lean_dec(v_a_834_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_851_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
uint8_t v___x_841_; uint8_t v_decide_842_; 
v___x_841_ = 0;
v_decide_842_ = lean_nat_dec_eq(v_searcher_837_, v___x_833_);
if (v_decide_842_ == 0)
{
uint32_t v___x_843_; uint32_t v___x_844_; uint8_t v___x_845_; 
v___x_843_ = 46;
v___x_844_ = lean_string_utf8_get_fast(v___x_832_, v_searcher_837_);
v___x_845_ = lean_uint32_dec_eq(v___x_844_, v___x_843_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_846_ = lean_string_utf8_next_fast(v___x_832_, v_searcher_837_);
lean_dec(v_searcher_837_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 1, v___x_846_);
v___x_848_ = v___x_839_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_currPos_836_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v___x_846_);
v___x_848_ = v_reuseFailAlloc_850_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
v_a_834_ = v___x_848_;
goto _start;
}
}
else
{
lean_del_object(v___x_839_);
lean_dec(v_searcher_837_);
lean_dec(v_currPos_836_);
return v___x_841_;
}
}
else
{
lean_del_object(v___x_839_);
lean_dec(v_searcher_837_);
lean_dec(v_currPos_836_);
return v___x_841_;
}
}
}
else
{
return v_b_835_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg___boxed(lean_object* v___x_852_, lean_object* v___x_853_, lean_object* v_a_854_, lean_object* v_b_855_){
_start:
{
uint8_t v_b_boxed_856_; uint8_t v_res_857_; lean_object* v_r_858_; 
v_b_boxed_856_ = lean_unbox(v_b_855_);
v_res_857_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_852_, v___x_853_, v_a_854_, v_b_boxed_856_);
lean_dec(v___x_853_);
lean_dec_ref(v___x_852_);
v_r_858_ = lean_box(v_res_857_);
return v_r_858_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(uint8_t v___x_859_, lean_object* v___x_860_, lean_object* v___x_861_, lean_object* v___x_862_, lean_object* v_a_863_, uint8_t v_b_864_){
_start:
{
uint8_t v___y_866_; lean_object* v_it_867_; lean_object* v_startInclusive_868_; lean_object* v_endExclusive_869_; uint8_t v___y_874_; 
if (v___x_859_ == 0)
{
uint8_t v___x_900_; 
v___x_900_ = 1;
v___y_874_ = v___x_900_;
goto v___jp_873_;
}
else
{
uint8_t v___x_901_; 
v___x_901_ = 0;
v___y_874_ = v___x_901_;
goto v___jp_873_;
}
v___jp_865_:
{
lean_object* v___x_870_; uint8_t v___x_871_; 
v___x_870_ = lean_string_utf8_extract_fast(v___x_860_, v_startInclusive_868_, v_endExclusive_869_);
lean_dec(v_endExclusive_869_);
lean_dec(v_startInclusive_868_);
v___x_871_ = l_Std_Http_URI_isValidDomainLabel(v___x_870_);
if (v___x_871_ == 0)
{
lean_dec(v_it_867_);
lean_dec(v___x_862_);
return v___x_871_;
}
else
{
v_a_863_ = v_it_867_;
v_b_864_ = v___y_866_;
goto _start;
}
}
v___jp_873_:
{
if (lean_obj_tag(v_a_863_) == 0)
{
lean_object* v_currPos_875_; lean_object* v_searcher_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_899_; 
v_currPos_875_ = lean_ctor_get(v_a_863_, 0);
v_searcher_876_ = lean_ctor_get(v_a_863_, 1);
v_isSharedCheck_899_ = !lean_is_exclusive(v_a_863_);
if (v_isSharedCheck_899_ == 0)
{
v___x_878_ = v_a_863_;
v_isShared_879_ = v_isSharedCheck_899_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_searcher_876_);
lean_inc(v_currPos_875_);
lean_dec(v_a_863_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_899_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
uint8_t v_decide_880_; 
v_decide_880_ = lean_nat_dec_eq(v_searcher_876_, v___x_862_);
if (v_decide_880_ == 0)
{
uint32_t v___x_881_; uint32_t v___x_882_; uint8_t v___x_883_; 
v___x_881_ = 46;
v___x_882_ = lean_string_utf8_get_fast(v___x_860_, v_searcher_876_);
v___x_883_ = lean_uint32_dec_eq(v___x_882_, v___x_881_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = lean_string_utf8_next_fast(v___x_860_, v_searcher_876_);
lean_dec(v_searcher_876_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 1, v___x_884_);
v___x_886_ = v___x_878_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_currPos_875_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v___x_884_);
v___x_886_ = v_reuseFailAlloc_888_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
v_a_863_ = v___x_886_;
goto _start;
}
}
else
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v_slice_892_; lean_object* v_nextIt_894_; 
v___x_889_ = lean_string_utf8_next_fast(v___x_860_, v_searcher_876_);
v___x_890_ = lean_nat_sub(v___x_889_, v_searcher_876_);
v___x_891_ = lean_nat_add(v_searcher_876_, v___x_890_);
lean_dec(v___x_890_);
v_slice_892_ = l_String_Slice_subslice_x21(v___x_861_, v_currPos_875_, v_searcher_876_);
lean_inc(v___x_891_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 1, v___x_891_);
lean_ctor_set(v___x_878_, 0, v___x_891_);
v_nextIt_894_ = v___x_878_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_891_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v___x_891_);
v_nextIt_894_ = v_reuseFailAlloc_897_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v_startInclusive_895_; lean_object* v_endExclusive_896_; 
v_startInclusive_895_ = lean_ctor_get(v_slice_892_, 0);
lean_inc(v_startInclusive_895_);
v_endExclusive_896_ = lean_ctor_get(v_slice_892_, 1);
lean_inc(v_endExclusive_896_);
lean_dec_ref(v_slice_892_);
v___y_866_ = v___y_874_;
v_it_867_ = v_nextIt_894_;
v_startInclusive_868_ = v_startInclusive_895_;
v_endExclusive_869_ = v_endExclusive_896_;
goto v___jp_865_;
}
}
}
else
{
lean_object* v___x_898_; 
lean_del_object(v___x_878_);
lean_dec(v_searcher_876_);
v___x_898_ = lean_box(1);
lean_inc(v___x_862_);
v___y_866_ = v___y_874_;
v_it_867_ = v___x_898_;
v_startInclusive_868_ = v_currPos_875_;
v_endExclusive_869_ = v___x_862_;
goto v___jp_865_;
}
}
}
else
{
lean_dec(v___x_862_);
return v_b_864_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg___boxed(lean_object* v___x_902_, lean_object* v___x_903_, lean_object* v___x_904_, lean_object* v___x_905_, lean_object* v_a_906_, lean_object* v_b_907_){
_start:
{
uint8_t v___x_12985__boxed_908_; uint8_t v_b_boxed_909_; uint8_t v_res_910_; lean_object* v_r_911_; 
v___x_12985__boxed_908_ = lean_unbox(v___x_902_);
v_b_boxed_909_ = lean_unbox(v_b_907_);
v_res_910_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_12985__boxed_908_, v___x_903_, v___x_904_, v___x_905_, v_a_906_, v_b_boxed_909_);
lean_dec_ref(v___x_904_);
lean_dec_ref(v___x_903_);
v_r_911_ = lean_box(v_res_910_);
return v_r_911_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(lean_object* v_config_919_, lean_object* v_a_920_){
_start:
{
lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; uint8_t v___y_932_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; uint8_t v___y_940_; uint8_t v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; uint8_t v___y_945_; lean_object* v___y_952_; uint8_t v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v_lower_956_; lean_object* v_upper_957_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; uint8_t v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_1003_; lean_object* v_pos_1004_; lean_object* v___y_1028_; lean_object* v_pos_1029_; lean_object* v_res_1030_; lean_object* v_array_1031_; lean_object* v_idx_1032_; lean_object* v_pos_1034_; lean_object* v_res_1035_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v_array_1031_ = lean_ctor_get(v_a_920_, 0);
v_idx_1032_ = lean_ctor_get(v_a_920_, 1);
v___x_1044_ = lean_byte_array_size(v_array_1031_);
v___x_1045_ = lean_nat_dec_lt(v_idx_1032_, v___x_1044_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; 
lean_inc(v_idx_1032_);
lean_inc_ref(v_array_1031_);
v___x_1046_ = lean_box(0);
v_pos_1034_ = v_a_920_;
v_res_1035_ = v___x_1046_;
goto v___jp_1033_;
}
else
{
uint8_t v___x_1047_; uint8_t v___x_1048_; uint8_t v___x_1049_; 
v___x_1047_ = lean_byte_array_fget(v_array_1031_, v_idx_1032_);
v___x_1048_ = 91;
v___x_1049_ = lean_uint8_dec_eq(v___x_1047_, v___x_1048_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; 
lean_inc(v_idx_1032_);
lean_inc_ref(v_array_1031_);
v___x_1050_ = lean_box(0);
v_pos_1034_ = v_a_920_;
v_res_1035_ = v___x_1050_;
goto v___jp_1033_;
}
else
{
lean_object* v___x_1051_; 
v___x_1051_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(v_a_920_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_pos_1052_; lean_object* v_res_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1061_; 
v_pos_1052_ = lean_ctor_get(v___x_1051_, 0);
v_res_1053_ = lean_ctor_get(v___x_1051_, 1);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1055_ = v___x_1051_;
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_res_1053_);
lean_inc(v_pos_1052_);
lean_dec(v___x_1051_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1057_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1057_, 0, v_res_1053_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 1, v___x_1057_);
v___x_1059_ = v___x_1055_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_pos_1052_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
else
{
lean_object* v_pos_1062_; lean_object* v_err_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
v_pos_1062_ = lean_ctor_get(v___x_1051_, 0);
v_err_1063_ = lean_ctor_get(v___x_1051_, 1);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1051_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_err_1063_);
lean_inc(v_pos_1062_);
lean_dec(v___x_1051_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_pos_1062_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v_err_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
v___jp_921_:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_924_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0));
v___x_925_ = lean_string_append(v___x_924_, v___y_922_);
lean_dec_ref(v___y_922_);
v___x_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
v___x_927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_927_, 0, v___y_923_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
return v___x_927_;
}
v___jp_928_:
{
if (v___y_932_ == 0)
{
lean_dec_ref(v___y_929_);
v___y_922_ = v___y_930_;
v___y_923_ = v___y_931_;
goto v___jp_921_;
}
else
{
lean_object* v___x_933_; lean_object* v___x_934_; 
lean_dec_ref(v___y_930_);
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v___y_929_);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v___y_931_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
return v___x_934_;
}
}
v___jp_935_:
{
if (v___y_945_ == 0)
{
lean_dec(v___y_943_);
lean_dec(v___y_942_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec_ref(v___y_936_);
v___y_922_ = v___y_939_;
v___y_923_ = v___y_944_;
goto v___jp_921_;
}
else
{
uint8_t v___x_946_; 
lean_inc(v___y_938_);
v___x_946_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___y_940_, v___y_937_, v___y_936_, v___y_938_, v___y_943_, v___y_945_);
lean_dec_ref(v___y_936_);
if (v___x_946_ == 0)
{
lean_dec(v___y_942_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
v___y_922_ = v___y_939_;
v___y_923_ = v___y_944_;
goto v___jp_921_;
}
else
{
lean_object* v___x_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v___x_947_ = lean_string_length(v___y_937_);
v___x_948_ = lean_unsigned_to_nat(255u);
v___x_949_ = lean_nat_dec_le(v___x_947_, v___x_948_);
if (v___x_949_ == 0)
{
lean_dec(v___y_942_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
v___y_922_ = v___y_939_;
v___y_923_ = v___y_944_;
goto v___jp_921_;
}
else
{
uint8_t v___x_950_; 
v___x_950_ = lean_nat_dec_eq(v___y_938_, v___y_942_);
lean_dec(v___y_942_);
lean_dec(v___y_938_);
if (v___x_950_ == 0)
{
v___y_929_ = v___y_937_;
v___y_930_ = v___y_939_;
v___y_931_ = v___y_944_;
v___y_932_ = v___x_949_;
goto v___jp_928_;
}
else
{
v___y_929_ = v___y_937_;
v___y_930_ = v___y_939_;
v___y_931_ = v___y_944_;
v___y_932_ = v___y_941_;
goto v___jp_928_;
}
}
}
}
}
v___jp_951_:
{
lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_958_ = l_ByteArray_toByteSlice(v___y_952_, v_lower_956_, v_upper_957_);
v___x_959_ = l_ByteSlice_toByteArray(v___x_958_);
v___x_960_ = lean_string_validate_utf8(v___x_959_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; lean_object* v___x_962_; 
lean_dec_ref(v___x_959_);
lean_dec(v___y_954_);
v___x_961_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2));
v___x_962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_962_, 0, v___y_955_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
return v___x_962_;
}
else
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; uint8_t v___x_968_; 
v___x_963_ = lean_string_from_utf8_unchecked(v___x_959_);
lean_inc_n(v___y_954_, 2);
lean_inc_ref(v___x_963_);
v___x_964_ = l_String_mapAux___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(v___x_963_, v___y_954_);
v___x_965_ = lean_string_utf8_byte_size(v___x_964_);
lean_inc_ref(v___x_964_);
v___x_966_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___y_954_);
lean_ctor_set(v___x_966_, 2, v___x_965_);
v___x_967_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0);
v___x_968_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_964_, v___x_965_, v___x_967_, v___x_960_);
if (v___x_968_ == 0)
{
v___y_936_ = v___x_966_;
v___y_937_ = v___x_964_;
v___y_938_ = v___x_965_;
v___y_939_ = v___x_963_;
v___y_940_ = v___x_968_;
v___y_941_ = v___y_953_;
v___y_942_ = v___y_954_;
v___y_943_ = v___x_967_;
v___y_944_ = v___y_955_;
v___y_945_ = v___x_960_;
goto v___jp_935_;
}
else
{
v___y_936_ = v___x_966_;
v___y_937_ = v___x_964_;
v___y_938_ = v___x_965_;
v___y_939_ = v___x_963_;
v___y_940_ = v___x_968_;
v___y_941_ = v___y_953_;
v___y_942_ = v___y_954_;
v___y_943_ = v___x_967_;
v___y_944_ = v___y_955_;
v___y_945_ = v___y_953_;
goto v___jp_935_;
}
}
}
v___jp_969_:
{
uint8_t v___x_977_; 
v___x_977_ = lean_nat_dec_le(v___y_971_, v___y_970_);
if (v___x_977_ == 0)
{
lean_dec(v___y_971_);
v___y_952_ = v___y_972_;
v___y_953_ = v___y_973_;
v___y_954_ = v___y_974_;
v___y_955_ = v___y_975_;
v_lower_956_ = v___y_976_;
v_upper_957_ = v___y_970_;
goto v___jp_951_;
}
else
{
lean_dec(v___y_970_);
v___y_952_ = v___y_972_;
v___y_953_ = v___y_973_;
v___y_954_ = v___y_974_;
v___y_955_ = v___y_975_;
v_lower_956_ = v___y_976_;
v_upper_957_ = v___y_971_;
goto v___jp_951_;
}
}
v___jp_978_:
{
lean_object* v_maxHostLength_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v_snd_984_; lean_object* v_fst_985_; lean_object* v_fst_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1000_; 
v_maxHostLength_981_ = lean_ctor_get(v_config_919_, 1);
v___x_982_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___y_980_);
lean_inc_ref(v___y_979_);
v___x_983_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___y_979_, v_maxHostLength_981_, v___x_982_, v___y_980_);
v_snd_984_ = lean_ctor_get(v___x_983_, 1);
lean_inc(v_snd_984_);
v_fst_985_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_fst_985_);
lean_dec_ref(v___x_983_);
v_fst_986_ = lean_ctor_get(v_snd_984_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v_snd_984_);
if (v_isSharedCheck_1000_ == 0)
{
lean_object* v_unused_1001_; 
v_unused_1001_ = lean_ctor_get(v_snd_984_, 1);
lean_dec(v_unused_1001_);
v___x_988_ = v_snd_984_;
v_isShared_989_ = v_isSharedCheck_1000_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_fst_986_);
lean_dec(v_snd_984_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1000_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
uint8_t v___x_990_; 
v___x_990_ = lean_nat_dec_eq(v_fst_985_, v___x_982_);
if (v___x_990_ == 0)
{
lean_object* v_array_991_; lean_object* v_idx_992_; lean_object* v___x_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
lean_del_object(v___x_988_);
v_array_991_ = lean_ctor_get(v___y_980_, 0);
lean_inc_ref(v_array_991_);
v_idx_992_ = lean_ctor_get(v___y_980_, 1);
lean_inc(v_idx_992_);
lean_dec_ref(v___y_980_);
v___x_993_ = lean_nat_add(v_idx_992_, v_fst_985_);
lean_dec(v_fst_985_);
v___x_994_ = lean_byte_array_size(v_array_991_);
v___x_995_ = lean_nat_dec_le(v_idx_992_, v___x_982_);
if (v___x_995_ == 0)
{
v___y_970_ = v___x_994_;
v___y_971_ = v___x_993_;
v___y_972_ = v_array_991_;
v___y_973_ = v___x_990_;
v___y_974_ = v___x_982_;
v___y_975_ = v_fst_986_;
v___y_976_ = v_idx_992_;
goto v___jp_969_;
}
else
{
lean_dec(v_idx_992_);
v___y_970_ = v___x_994_;
v___y_971_ = v___x_993_;
v___y_972_ = v_array_991_;
v___y_973_ = v___x_990_;
v___y_974_ = v___x_982_;
v___y_975_ = v_fst_986_;
v___y_976_ = v___x_982_;
goto v___jp_969_;
}
}
else
{
lean_object* v___x_996_; lean_object* v___x_998_; 
lean_dec(v_fst_986_);
lean_dec(v_fst_985_);
v___x_996_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7));
if (v_isShared_989_ == 0)
{
lean_ctor_set_tag(v___x_988_, 1);
lean_ctor_set(v___x_988_, 1, v___x_996_);
lean_ctor_set(v___x_988_, 0, v___y_980_);
v___x_998_ = v___x_988_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___y_980_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v___x_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
v___jp_1002_:
{
lean_object* v___x_1005_; 
lean_inc_ref(v_pos_1004_);
v___x_1005_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(v_pos_1004_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_pos_1006_; lean_object* v_res_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1015_; 
lean_dec_ref(v_pos_1004_);
v_pos_1006_ = lean_ctor_get(v___x_1005_, 0);
v_res_1007_ = lean_ctor_get(v___x_1005_, 1);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1009_ = v___x_1005_;
v_isShared_1010_ = v_isSharedCheck_1015_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_res_1007_);
lean_inc(v_pos_1006_);
lean_dec(v___x_1005_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1015_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v___x_1013_; 
v___x_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1011_, 0, v_res_1007_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 1, v___x_1011_);
v___x_1013_ = v___x_1009_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_pos_1006_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
else
{
lean_object* v_err_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1025_; 
v_err_1016_ = lean_ctor_get(v___x_1005_, 1);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1025_ == 0)
{
lean_object* v_unused_1026_; 
v_unused_1026_ = lean_ctor_get(v___x_1005_, 0);
lean_dec(v_unused_1026_);
v___x_1018_ = v___x_1005_;
v_isShared_1019_ = v_isSharedCheck_1025_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_err_1016_);
lean_dec(v___x_1005_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1025_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v_idx_1020_; uint8_t v___x_1021_; 
v_idx_1020_ = lean_ctor_get(v_pos_1004_, 1);
v___x_1021_ = lean_nat_dec_eq(v_idx_1020_, v_idx_1020_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1023_; 
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v_pos_1004_);
v___x_1023_ = v___x_1018_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_pos_1004_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_err_1016_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
else
{
lean_del_object(v___x_1018_);
lean_dec(v_err_1016_);
v___y_979_ = v___y_1003_;
v___y_980_ = v_pos_1004_;
goto v___jp_978_;
}
}
}
}
v___jp_1027_:
{
v___y_979_ = v___y_1028_;
v___y_980_ = v_pos_1029_;
goto v___jp_978_;
}
v___jp_1033_:
{
lean_object* v___f_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; 
v___f_1036_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3));
v___x_1037_ = lean_byte_array_size(v_array_1031_);
v___x_1038_ = lean_nat_dec_lt(v_idx_1032_, v___x_1037_);
if (v___x_1038_ == 0)
{
lean_dec(v_idx_1032_);
lean_dec_ref(v_array_1031_);
v___y_1028_ = v___f_1036_;
v_pos_1029_ = v_pos_1034_;
v_res_1030_ = v_res_1035_;
goto v___jp_1027_;
}
else
{
uint8_t v___x_1039_; uint8_t v___x_1040_; uint8_t v___x_1041_; 
v___x_1039_ = lean_byte_array_fget(v_array_1031_, v_idx_1032_);
lean_dec(v_idx_1032_);
lean_dec_ref(v_array_1031_);
v___x_1040_ = 48;
v___x_1041_ = lean_uint8_dec_le(v___x_1040_, v___x_1039_);
if (v___x_1041_ == 0)
{
v___y_1028_ = v___f_1036_;
v_pos_1029_ = v_pos_1034_;
v_res_1030_ = v_res_1035_;
goto v___jp_1027_;
}
else
{
uint8_t v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = 57;
v___x_1043_ = lean_uint8_dec_le(v___x_1039_, v___x_1042_);
if (v___x_1043_ == 0)
{
v___y_1028_ = v___f_1036_;
v_pos_1029_ = v_pos_1034_;
v_res_1030_ = v_res_1035_;
goto v___jp_1027_;
}
else
{
v___y_1003_ = v___f_1036_;
v_pos_1004_ = v_pos_1034_;
goto v___jp_1002_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___boxed(lean_object* v_config_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_1071_, v_a_1072_);
lean_dec_ref(v_config_1071_);
return v_res_1073_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(lean_object* v___x_1074_, lean_object* v___x_1075_, lean_object* v___x_1076_, lean_object* v_inst_1077_, lean_object* v_R_1078_, lean_object* v_a_1079_, uint8_t v_b_1080_, lean_object* v_c_1081_){
_start:
{
uint8_t v___x_1082_; 
v___x_1082_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_1074_, v___x_1076_, v_a_1079_, v_b_1080_);
return v___x_1082_;
}
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
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(uint8_t v___x_1094_, lean_object* v___x_1095_, lean_object* v___x_1096_, lean_object* v___x_1097_, lean_object* v_inst_1098_, lean_object* v_R_1099_, lean_object* v_a_1100_, uint8_t v_b_1101_, lean_object* v_c_1102_){
_start:
{
uint8_t v___x_1103_; 
v___x_1103_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_1094_, v___x_1095_, v___x_1096_, v___x_1097_, v_a_1100_, v_b_1101_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___boxed(lean_object* v___x_1104_, lean_object* v___x_1105_, lean_object* v___x_1106_, lean_object* v___x_1107_, lean_object* v_inst_1108_, lean_object* v_R_1109_, lean_object* v_a_1110_, lean_object* v_b_1111_, lean_object* v_c_1112_){
_start:
{
uint8_t v___x_13390__boxed_1113_; uint8_t v_b_boxed_1114_; uint8_t v_res_1115_; lean_object* v_r_1116_; 
v___x_13390__boxed_1113_ = lean_unbox(v___x_1104_);
v_b_boxed_1114_ = lean_unbox(v_b_1111_);
v_res_1115_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(v___x_13390__boxed_1113_, v___x_1105_, v___x_1106_, v___x_1107_, v_inst_1108_, v_R_1109_, v_a_1110_, v_b_boxed_1114_, v_c_1112_);
lean_dec_ref(v___x_1106_);
lean_dec_ref(v___x_1105_);
v_r_1116_ = lean_box(v_res_1115_);
return v_r_1116_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(lean_object* v_config_1126_, lean_object* v_a_1127_){
_start:
{
lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v_port_1131_; lean_object* v___y_1132_; lean_object* v___y_1136_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1145_; lean_object* v___y_1146_; uint8_t v_val_1147_; lean_object* v___y_1148_; lean_object* v___y_1156_; lean_object* v___y_1157_; uint8_t v___y_1158_; lean_object* v_pos_1159_; lean_object* v_array_1160_; lean_object* v_idx_1161_; lean_object* v_res_1162_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; uint8_t v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v_pos_1177_; lean_object* v_pos_1180_; lean_object* v_res_1181_; lean_object* v_pos_1246_; lean_object* v_res_1247_; lean_object* v_err_1250_; lean_object* v___x_1255_; 
lean_inc_ref(v_a_1127_);
v___x_1255_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(v_config_1126_, v_a_1127_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_pos_1256_; lean_object* v_res_1257_; lean_object* v_array_1258_; lean_object* v_idx_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1275_; 
v_pos_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_pos_1256_);
v_res_1257_ = lean_ctor_get(v___x_1255_, 1);
lean_inc(v_res_1257_);
lean_dec_ref_known(v___x_1255_, 2);
v_array_1258_ = lean_ctor_get(v_pos_1256_, 0);
v_idx_1259_ = lean_ctor_get(v_pos_1256_, 1);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_pos_1256_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1261_ = v_pos_1256_;
v_isShared_1262_ = v_isSharedCheck_1275_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_idx_1259_);
lean_inc(v_array_1258_);
lean_dec(v_pos_1256_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1275_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_1263_ = lean_byte_array_size(v_array_1258_);
v___x_1264_ = lean_nat_dec_lt(v_idx_1259_, v___x_1263_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; 
lean_del_object(v___x_1261_);
lean_dec(v_idx_1259_);
lean_dec_ref(v_array_1258_);
lean_dec(v_res_1257_);
v___x_1265_ = lean_box(0);
v_err_1250_ = v___x_1265_;
goto v___jp_1249_;
}
else
{
uint8_t v___x_1266_; uint8_t v_got_1267_; uint8_t v___x_1268_; 
v___x_1266_ = 64;
v_got_1267_ = lean_byte_array_fget(v_array_1258_, v_idx_1259_);
v___x_1268_ = lean_uint8_dec_eq(v_got_1267_, v___x_1266_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; 
lean_del_object(v___x_1261_);
lean_dec(v_idx_1259_);
lean_dec_ref(v_array_1258_);
lean_dec(v_res_1257_);
v___x_1269_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5));
v_err_1250_ = v___x_1269_;
goto v___jp_1249_;
}
else
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1273_; 
lean_dec_ref(v_a_1127_);
v___x_1270_ = lean_unsigned_to_nat(1u);
v___x_1271_ = lean_nat_add(v_idx_1259_, v___x_1270_);
lean_dec(v_idx_1259_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 1, v___x_1271_);
v___x_1273_ = v___x_1261_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_array_1258_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
v_pos_1246_ = v___x_1273_;
v_res_1247_ = v_res_1257_;
goto v___jp_1245_;
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_pos_1276_; lean_object* v_res_1277_; 
lean_dec_ref(v_a_1127_);
v_pos_1276_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_pos_1276_);
v_res_1277_ = lean_ctor_get(v___x_1255_, 1);
lean_inc(v_res_1277_);
lean_dec_ref_known(v___x_1255_, 2);
v_pos_1246_ = v_pos_1276_;
v_res_1247_ = v_res_1277_;
goto v___jp_1245_;
}
else
{
lean_object* v_err_1278_; 
v_err_1278_ = lean_ctor_get(v___x_1255_, 1);
lean_inc(v_err_1278_);
lean_dec_ref_known(v___x_1255_, 2);
v_err_1250_ = v_err_1278_;
goto v___jp_1249_;
}
}
v___jp_1128_:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1133_, 0, v___y_1130_);
lean_ctor_set(v___x_1133_, 1, v___y_1129_);
lean_ctor_set(v___x_1133_, 2, v_port_1131_);
v___x_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___y_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
return v___x_1134_;
}
v___jp_1135_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__1));
v___x_1138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___y_1136_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
return v___x_1138_;
}
v___jp_1139_:
{
lean_object* v___x_1143_; 
v___x_1143_ = lean_box(1);
v___y_1129_ = v___y_1140_;
v___y_1130_ = v___y_1142_;
v_port_1131_ = v___x_1143_;
v___y_1132_ = v___y_1141_;
goto v___jp_1128_;
}
v___jp_1144_:
{
uint8_t v___x_1149_; uint8_t v___x_1150_; 
v___x_1149_ = 47;
v___x_1150_ = lean_uint8_dec_eq(v_val_1147_, v___x_1149_);
if (v___x_1150_ == 0)
{
uint8_t v___x_1151_; uint8_t v___x_1152_; 
v___x_1151_ = 63;
v___x_1152_ = lean_uint8_dec_eq(v_val_1147_, v___x_1151_);
if (v___x_1152_ == 0)
{
uint8_t v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = 35;
v___x_1154_ = lean_uint8_dec_eq(v_val_1147_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1145_);
v___y_1136_ = v___y_1146_;
goto v___jp_1135_;
}
else
{
v___y_1140_ = v___y_1145_;
v___y_1141_ = v___y_1146_;
v___y_1142_ = v___y_1148_;
goto v___jp_1139_;
}
}
else
{
v___y_1140_ = v___y_1145_;
v___y_1141_ = v___y_1146_;
v___y_1142_ = v___y_1148_;
goto v___jp_1139_;
}
}
else
{
v___y_1140_ = v___y_1145_;
v___y_1141_ = v___y_1146_;
v___y_1142_ = v___y_1148_;
goto v___jp_1139_;
}
}
v___jp_1155_:
{
lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = lean_byte_array_size(v_array_1160_);
v___x_1164_ = lean_nat_dec_lt(v_idx_1161_, v___x_1163_);
if (v___x_1164_ == 0)
{
lean_dec(v_idx_1161_);
lean_dec_ref(v_array_1160_);
if (v___y_1158_ == 0)
{
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
v___y_1136_ = v_pos_1159_;
goto v___jp_1135_;
}
else
{
v___y_1140_ = v___y_1156_;
v___y_1141_ = v_pos_1159_;
v___y_1142_ = v___y_1157_;
goto v___jp_1139_;
}
}
else
{
uint8_t v___x_1165_; 
v___x_1165_ = lean_byte_array_fget(v_array_1160_, v_idx_1161_);
lean_dec(v_idx_1161_);
lean_dec_ref(v_array_1160_);
v___y_1145_ = v___y_1156_;
v___y_1146_ = v_pos_1159_;
v_val_1147_ = v___x_1165_;
v___y_1148_ = v___y_1157_;
goto v___jp_1144_;
}
}
v___jp_1166_:
{
lean_object* v___x_1173_; 
v___x_1173_ = lean_box(0);
v___y_1156_ = v___y_1168_;
v___y_1157_ = v___y_1169_;
v___y_1158_ = v___y_1171_;
v_pos_1159_ = v___y_1170_;
v_array_1160_ = v___y_1172_;
v_idx_1161_ = v___y_1167_;
v_res_1162_ = v___x_1173_;
goto v___jp_1155_;
}
v___jp_1174_:
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_box(0);
v___y_1129_ = v___y_1175_;
v___y_1130_ = v___y_1176_;
v_port_1131_ = v___x_1178_;
v___y_1132_ = v_pos_1177_;
goto v___jp_1128_;
}
v___jp_1179_:
{
lean_object* v___x_1182_; 
v___x_1182_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_1126_, v_pos_1180_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_pos_1183_; lean_object* v_res_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1235_; 
v_pos_1183_ = lean_ctor_get(v___x_1182_, 0);
v_res_1184_ = lean_ctor_get(v___x_1182_, 1);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1186_ = v___x_1182_;
v_isShared_1187_ = v_isSharedCheck_1235_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_res_1184_);
lean_inc(v_pos_1183_);
lean_dec(v___x_1182_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1235_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v_array_1188_; lean_object* v_idx_1189_; lean_object* v___x_1190_; uint8_t v___x_1191_; 
v_array_1188_ = lean_ctor_get(v_pos_1183_, 0);
v_idx_1189_ = lean_ctor_get(v_pos_1183_, 1);
v___x_1190_ = lean_byte_array_size(v_array_1188_);
v___x_1191_ = lean_nat_dec_lt(v_idx_1189_, v___x_1190_);
if (v___x_1191_ == 0)
{
lean_del_object(v___x_1186_);
v___y_1175_ = v_res_1184_;
v___y_1176_ = v_res_1181_;
v_pos_1177_ = v_pos_1183_;
goto v___jp_1174_;
}
else
{
uint8_t v___x_1192_; uint8_t v___x_1193_; uint8_t v___x_1194_; 
v___x_1192_ = lean_byte_array_fget(v_array_1188_, v_idx_1189_);
v___x_1193_ = 58;
v___x_1194_ = lean_uint8_dec_eq(v___x_1192_, v___x_1193_);
if (v___x_1194_ == 0)
{
lean_del_object(v___x_1186_);
v___y_1175_ = v_res_1184_;
v___y_1176_ = v_res_1181_;
v_pos_1177_ = v_pos_1183_;
goto v___jp_1174_;
}
else
{
if (v___x_1194_ == 0)
{
lean_del_object(v___x_1186_);
v___y_1175_ = v_res_1184_;
v___y_1176_ = v_res_1181_;
v_pos_1177_ = v_pos_1183_;
goto v___jp_1174_;
}
else
{
if (v___x_1191_ == 0)
{
lean_object* v___x_1195_; lean_object* v___x_1197_; 
lean_dec(v_res_1184_);
lean_dec(v_res_1181_);
v___x_1195_ = lean_box(0);
if (v_isShared_1187_ == 0)
{
lean_ctor_set_tag(v___x_1186_, 1);
lean_ctor_set(v___x_1186_, 1, v___x_1195_);
v___x_1197_ = v___x_1186_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_pos_1183_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
else
{
if (v___x_1194_ == 0)
{
lean_object* v___x_1199_; lean_object* v___x_1201_; 
lean_dec(v_res_1184_);
lean_dec(v_res_1181_);
v___x_1199_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_1187_ == 0)
{
lean_ctor_set_tag(v___x_1186_, 1);
lean_ctor_set(v___x_1186_, 1, v___x_1199_);
v___x_1201_ = v___x_1186_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_pos_1183_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
else
{
lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1232_; 
lean_inc(v_idx_1189_);
lean_inc_ref(v_array_1188_);
lean_del_object(v___x_1186_);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_pos_1183_);
if (v_isSharedCheck_1232_ == 0)
{
lean_object* v_unused_1233_; lean_object* v_unused_1234_; 
v_unused_1233_ = lean_ctor_get(v_pos_1183_, 1);
lean_dec(v_unused_1233_);
v_unused_1234_ = lean_ctor_get(v_pos_1183_, 0);
lean_dec(v_unused_1234_);
v___x_1204_ = v_pos_1183_;
v_isShared_1205_ = v_isSharedCheck_1232_;
goto v_resetjp_1203_;
}
else
{
lean_dec(v_pos_1183_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1232_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1206_ = lean_unsigned_to_nat(1u);
v___x_1207_ = lean_nat_add(v_idx_1189_, v___x_1206_);
lean_dec(v_idx_1189_);
lean_inc(v___x_1207_);
lean_inc_ref(v_array_1188_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v___x_1207_);
v___x_1209_ = v___x_1204_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_array_1188_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
uint8_t v___x_1210_; 
v___x_1210_ = lean_nat_dec_lt(v___x_1207_, v___x_1190_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; 
v___x_1211_ = lean_box(0);
v___y_1156_ = v_res_1184_;
v___y_1157_ = v_res_1181_;
v___y_1158_ = v___x_1194_;
v_pos_1159_ = v___x_1209_;
v_array_1160_ = v_array_1188_;
v_idx_1161_ = v___x_1207_;
v_res_1162_ = v___x_1211_;
goto v___jp_1155_;
}
else
{
uint8_t v___x_1212_; uint8_t v___x_1213_; uint8_t v___x_1214_; 
v___x_1212_ = lean_byte_array_fget(v_array_1188_, v___x_1207_);
v___x_1213_ = 48;
v___x_1214_ = lean_uint8_dec_le(v___x_1213_, v___x_1212_);
if (v___x_1214_ == 0)
{
v___y_1167_ = v___x_1207_;
v___y_1168_ = v_res_1184_;
v___y_1169_ = v_res_1181_;
v___y_1170_ = v___x_1209_;
v___y_1171_ = v___x_1194_;
v___y_1172_ = v_array_1188_;
goto v___jp_1166_;
}
else
{
uint8_t v___x_1215_; uint8_t v___x_1216_; 
v___x_1215_ = 57;
v___x_1216_ = lean_uint8_dec_le(v___x_1212_, v___x_1215_);
if (v___x_1216_ == 0)
{
v___y_1167_ = v___x_1207_;
v___y_1168_ = v_res_1184_;
v___y_1169_ = v_res_1181_;
v___y_1170_ = v___x_1209_;
v___y_1171_ = v___x_1194_;
v___y_1172_ = v_array_1188_;
goto v___jp_1166_;
}
else
{
lean_object* v___x_1217_; 
lean_dec(v___x_1207_);
lean_dec_ref(v_array_1188_);
v___x_1217_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_1209_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_pos_1218_; lean_object* v_res_1219_; lean_object* v___x_1220_; uint16_t v___x_1221_; 
v_pos_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_pos_1218_);
v_res_1219_ = lean_ctor_get(v___x_1217_, 1);
lean_inc(v_res_1219_);
lean_dec_ref_known(v___x_1217_, 2);
v___x_1220_ = lean_alloc_ctor(2, 0, 2);
v___x_1221_ = lean_unbox(v_res_1219_);
lean_dec(v_res_1219_);
lean_ctor_set_uint16(v___x_1220_, 0, v___x_1221_);
v___y_1129_ = v_res_1184_;
v___y_1130_ = v_res_1181_;
v_port_1131_ = v___x_1220_;
v___y_1132_ = v_pos_1218_;
goto v___jp_1128_;
}
else
{
lean_object* v_pos_1222_; lean_object* v_err_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec(v_res_1184_);
lean_dec(v_res_1181_);
v_pos_1222_ = lean_ctor_get(v___x_1217_, 0);
v_err_1223_ = lean_ctor_get(v___x_1217_, 1);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1217_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_err_1223_);
lean_inc(v_pos_1222_);
lean_dec(v___x_1217_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_pos_1222_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_err_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
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
lean_object* v_pos_1236_; lean_object* v_err_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
lean_dec(v_res_1181_);
v_pos_1236_ = lean_ctor_get(v___x_1182_, 0);
v_err_1237_ = lean_ctor_get(v___x_1182_, 1);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1182_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_err_1237_);
lean_inc(v_pos_1236_);
lean_dec(v___x_1182_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_pos_1236_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_err_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
v___jp_1245_:
{
lean_object* v___x_1248_; 
v___x_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1248_, 0, v_res_1247_);
v_pos_1180_ = v_pos_1246_;
v_res_1181_ = v___x_1248_;
goto v___jp_1179_;
}
v___jp_1249_:
{
lean_object* v_idx_1251_; uint8_t v___x_1252_; 
v_idx_1251_ = lean_ctor_get(v_a_1127_, 1);
v___x_1252_ = lean_nat_dec_eq(v_idx_1251_, v_idx_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; 
v___x_1253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1253_, 0, v_a_1127_);
lean_ctor_set(v___x_1253_, 1, v_err_1250_);
return v___x_1253_;
}
else
{
lean_object* v___x_1254_; 
lean_dec(v_err_1250_);
v___x_1254_ = lean_box(0);
v_pos_1180_ = v_a_1127_;
v_res_1181_ = v___x_1254_;
goto v___jp_1179_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___boxed(lean_object* v_config_1279_, lean_object* v_a_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_1279_, v_a_1280_);
lean_dec_ref(v_config_1279_);
return v_res_1281_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(uint8_t v_c_1282_){
_start:
{
uint8_t v___x_1330_; uint8_t v___x_1331_; 
v___x_1330_ = 48;
v___x_1331_ = lean_uint8_dec_le(v___x_1330_, v_c_1282_);
if (v___x_1331_ == 0)
{
goto v___jp_1325_;
}
else
{
uint8_t v___x_1332_; uint8_t v___x_1333_; 
v___x_1332_ = 57;
v___x_1333_ = lean_uint8_dec_le(v_c_1282_, v___x_1332_);
if (v___x_1333_ == 0)
{
goto v___jp_1325_;
}
else
{
return v___x_1333_;
}
}
v___jp_1283_:
{
uint8_t v___x_1284_; uint8_t v___x_1285_; 
v___x_1284_ = 45;
v___x_1285_ = lean_uint8_dec_eq(v_c_1282_, v___x_1284_);
if (v___x_1285_ == 0)
{
uint8_t v___x_1286_; uint8_t v___x_1287_; 
v___x_1286_ = 46;
v___x_1287_ = lean_uint8_dec_eq(v_c_1282_, v___x_1286_);
if (v___x_1287_ == 0)
{
uint8_t v___x_1288_; uint8_t v___x_1289_; 
v___x_1288_ = 95;
v___x_1289_ = lean_uint8_dec_eq(v_c_1282_, v___x_1288_);
if (v___x_1289_ == 0)
{
uint8_t v___x_1290_; uint8_t v___x_1291_; 
v___x_1290_ = 126;
v___x_1291_ = lean_uint8_dec_eq(v_c_1282_, v___x_1290_);
if (v___x_1291_ == 0)
{
uint8_t v___x_1292_; uint8_t v___x_1293_; 
v___x_1292_ = 33;
v___x_1293_ = lean_uint8_dec_eq(v_c_1282_, v___x_1292_);
if (v___x_1293_ == 0)
{
uint8_t v___x_1294_; uint8_t v___x_1295_; 
v___x_1294_ = 36;
v___x_1295_ = lean_uint8_dec_eq(v_c_1282_, v___x_1294_);
if (v___x_1295_ == 0)
{
uint8_t v___x_1296_; uint8_t v___x_1297_; 
v___x_1296_ = 38;
v___x_1297_ = lean_uint8_dec_eq(v_c_1282_, v___x_1296_);
if (v___x_1297_ == 0)
{
uint8_t v___x_1298_; uint8_t v___x_1299_; 
v___x_1298_ = 39;
v___x_1299_ = lean_uint8_dec_eq(v_c_1282_, v___x_1298_);
if (v___x_1299_ == 0)
{
uint8_t v___x_1300_; uint8_t v___x_1301_; 
v___x_1300_ = 40;
v___x_1301_ = lean_uint8_dec_eq(v_c_1282_, v___x_1300_);
if (v___x_1301_ == 0)
{
uint8_t v___x_1302_; uint8_t v___x_1303_; 
v___x_1302_ = 41;
v___x_1303_ = lean_uint8_dec_eq(v_c_1282_, v___x_1302_);
if (v___x_1303_ == 0)
{
uint8_t v___x_1304_; uint8_t v___x_1305_; 
v___x_1304_ = 42;
v___x_1305_ = lean_uint8_dec_eq(v_c_1282_, v___x_1304_);
if (v___x_1305_ == 0)
{
uint8_t v___x_1306_; uint8_t v___x_1307_; 
v___x_1306_ = 43;
v___x_1307_ = lean_uint8_dec_eq(v_c_1282_, v___x_1306_);
if (v___x_1307_ == 0)
{
uint8_t v___x_1308_; uint8_t v___x_1309_; 
v___x_1308_ = 44;
v___x_1309_ = lean_uint8_dec_eq(v_c_1282_, v___x_1308_);
if (v___x_1309_ == 0)
{
uint8_t v___x_1310_; uint8_t v___x_1311_; 
v___x_1310_ = 59;
v___x_1311_ = lean_uint8_dec_eq(v_c_1282_, v___x_1310_);
if (v___x_1311_ == 0)
{
uint8_t v___x_1312_; uint8_t v___x_1313_; 
v___x_1312_ = 61;
v___x_1313_ = lean_uint8_dec_eq(v_c_1282_, v___x_1312_);
if (v___x_1313_ == 0)
{
uint8_t v___x_1314_; uint8_t v___x_1315_; 
v___x_1314_ = 58;
v___x_1315_ = lean_uint8_dec_eq(v_c_1282_, v___x_1314_);
if (v___x_1315_ == 0)
{
uint8_t v___x_1316_; uint8_t v___x_1317_; 
v___x_1316_ = 64;
v___x_1317_ = lean_uint8_dec_eq(v_c_1282_, v___x_1316_);
if (v___x_1317_ == 0)
{
uint8_t v___x_1318_; uint8_t v___x_1319_; 
v___x_1318_ = 37;
v___x_1319_ = lean_uint8_dec_eq(v_c_1282_, v___x_1318_);
return v___x_1319_;
}
else
{
return v___x_1317_;
}
}
else
{
return v___x_1315_;
}
}
else
{
return v___x_1313_;
}
}
else
{
return v___x_1311_;
}
}
else
{
return v___x_1309_;
}
}
else
{
return v___x_1307_;
}
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
v___jp_1320_:
{
uint8_t v___x_1321_; uint8_t v___x_1322_; 
v___x_1321_ = 65;
v___x_1322_ = lean_uint8_dec_le(v___x_1321_, v_c_1282_);
if (v___x_1322_ == 0)
{
goto v___jp_1283_;
}
else
{
uint8_t v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = 90;
v___x_1324_ = lean_uint8_dec_le(v_c_1282_, v___x_1323_);
if (v___x_1324_ == 0)
{
goto v___jp_1283_;
}
else
{
return v___x_1324_;
}
}
}
v___jp_1325_:
{
uint8_t v___x_1326_; uint8_t v___x_1327_; 
v___x_1326_ = 97;
v___x_1327_ = lean_uint8_dec_le(v___x_1326_, v_c_1282_);
if (v___x_1327_ == 0)
{
goto v___jp_1320_;
}
else
{
uint8_t v___x_1328_; uint8_t v___x_1329_; 
v___x_1328_ = 122;
v___x_1329_ = lean_uint8_dec_le(v_c_1282_, v___x_1328_);
if (v___x_1329_ == 0)
{
goto v___jp_1320_;
}
else
{
return v___x_1329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0___boxed(lean_object* v_c_1334_){
_start:
{
uint8_t v_c_boxed_1335_; uint8_t v_res_1336_; lean_object* v_r_1337_; 
v_c_boxed_1335_ = lean_unbox(v_c_1334_);
v_res_1336_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(v_c_boxed_1335_);
v_r_1337_ = lean_box(v_res_1336_);
return v_r_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(lean_object* v_config_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v_maxSegmentLength_1341_; lean_object* v___f_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v_snd_1345_; lean_object* v_fst_1346_; lean_object* v_fst_1347_; lean_object* v_array_1348_; lean_object* v_idx_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1366_; 
v_maxSegmentLength_1341_ = lean_ctor_get(v_config_1339_, 3);
v___f_1342_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___closed__0));
v___x_1343_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1340_);
v___x_1344_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1342_, v_maxSegmentLength_1341_, v___x_1343_, v_a_1340_);
v_snd_1345_ = lean_ctor_get(v___x_1344_, 1);
lean_inc(v_snd_1345_);
v_fst_1346_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_fst_1346_);
lean_dec_ref(v___x_1344_);
v_fst_1347_ = lean_ctor_get(v_snd_1345_, 0);
lean_inc(v_fst_1347_);
lean_dec(v_snd_1345_);
v_array_1348_ = lean_ctor_get(v_a_1340_, 0);
v_idx_1349_ = lean_ctor_get(v_a_1340_, 1);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_a_1340_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1351_ = v_a_1340_;
v_isShared_1352_ = v_isSharedCheck_1366_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_idx_1349_);
lean_inc(v_array_1348_);
lean_dec(v_a_1340_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1366_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v_lower_1354_; lean_object* v_upper_1355_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___y_1363_; uint8_t v___x_1365_; 
v___x_1360_ = lean_nat_add(v_idx_1349_, v_fst_1346_);
lean_dec(v_fst_1346_);
v___x_1361_ = lean_byte_array_size(v_array_1348_);
v___x_1365_ = lean_nat_dec_le(v_idx_1349_, v___x_1343_);
if (v___x_1365_ == 0)
{
v___y_1363_ = v_idx_1349_;
goto v___jp_1362_;
}
else
{
lean_dec(v_idx_1349_);
v___y_1363_ = v___x_1343_;
goto v___jp_1362_;
}
v___jp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1356_ = l_ByteArray_toByteSlice(v_array_1348_, v_lower_1354_, v_upper_1355_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 1, v___x_1356_);
lean_ctor_set(v___x_1351_, 0, v_fst_1347_);
v___x_1358_ = v___x_1351_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_fst_1347_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
v___jp_1362_:
{
uint8_t v___x_1364_; 
v___x_1364_ = lean_nat_dec_le(v___x_1360_, v___x_1361_);
if (v___x_1364_ == 0)
{
lean_dec(v___x_1360_);
v_lower_1354_ = v___y_1363_;
v_upper_1355_ = v___x_1361_;
goto v___jp_1353_;
}
else
{
v_lower_1354_ = v___y_1363_;
v_upper_1355_ = v___x_1360_;
goto v___jp_1353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___boxed(lean_object* v_config_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1367_, v_a_1368_);
lean_dec_ref(v_config_1367_);
return v_res_1369_;
}
}
LEAN_EXPORT uint8_t l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(uint8_t v_c_1370_){
_start:
{
uint8_t v___x_1371_; uint8_t v___x_1372_; 
v___x_1371_ = 63;
v___x_1372_ = lean_uint8_dec_eq(v_c_1370_, v___x_1371_);
if (v___x_1372_ == 0)
{
uint8_t v___x_1373_; uint8_t v___x_1374_; 
v___x_1373_ = 35;
v___x_1374_ = lean_uint8_dec_eq(v_c_1370_, v___x_1373_);
return v___x_1374_;
}
else
{
return v___x_1372_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0___boxed(lean_object* v_c_1375_){
_start:
{
uint8_t v_c_boxed_1376_; uint8_t v_res_1377_; lean_object* v_r_1378_; 
v_c_boxed_1376_ = lean_unbox(v_c_1375_);
v_res_1377_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v_c_boxed_1376_);
v_r_1378_ = lean_box(v_res_1377_);
return v_r_1378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(lean_object* v_config_1386_, lean_object* v_a_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v_array_1413_; lean_object* v_idx_1414_; lean_object* v_fst_1415_; lean_object* v_snd_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1588_; 
v_array_1413_ = lean_ctor_get(v___y_1388_, 0);
v_idx_1414_ = lean_ctor_get(v___y_1388_, 1);
v_fst_1415_ = lean_ctor_get(v_a_1387_, 0);
v_snd_1416_ = lean_ctor_get(v_a_1387_, 1);
v_isSharedCheck_1588_ = !lean_is_exclusive(v_a_1387_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1418_ = v_a_1387_;
v_isShared_1419_ = v_isSharedCheck_1588_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_snd_1416_);
lean_inc(v_fst_1415_);
lean_dec(v_a_1387_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1588_;
goto v_resetjp_1417_;
}
v___jp_1389_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___y_1390_);
lean_ctor_set(v___x_1393_, 1, v___y_1391_);
v___x_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___y_1392_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
return v___x_1394_;
}
v___jp_1395_:
{
lean_object* v___x_1400_; uint8_t v___x_1401_; 
v___x_1400_ = lean_array_get_size(v___y_1399_);
v___x_1401_ = lean_nat_dec_le(v___y_1398_, v___x_1400_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
lean_dec(v___y_1398_);
v___x_1402_ = l_ByteArray_empty;
v___x_1403_ = lean_array_push(v___y_1399_, v___x_1402_);
v___x_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
lean_ctor_set(v___x_1404_, 1, v___y_1397_);
v_a_1387_ = v___x_1404_;
v___y_1388_ = v___y_1396_;
goto _start;
}
else
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1397_);
lean_dec_ref(v_config_1386_);
v___x_1406_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1407_ = l_Nat_reprFast(v___y_1398_);
v___x_1408_ = lean_string_append(v___x_1406_, v___x_1407_);
lean_dec_ref(v___x_1407_);
v___x_1409_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1410_ = lean_string_append(v___x_1408_, v___x_1409_);
v___x_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
v___x_1412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___y_1396_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
return v___x_1412_;
}
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; uint8_t v___x_1421_; 
v___x_1420_ = lean_byte_array_size(v_array_1413_);
v___x_1421_ = lean_nat_dec_lt(v_idx_1414_, v___x_1420_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1423_; 
lean_dec_ref(v_config_1386_);
if (v_isShared_1419_ == 0)
{
v___x_1423_ = v___x_1418_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_fst_1415_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_snd_1416_);
v___x_1423_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
lean_object* v___x_1424_; 
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___y_1388_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
return v___x_1424_;
}
}
else
{
if (v___x_1421_ == 0)
{
lean_object* v___x_1427_; 
lean_dec_ref(v_config_1386_);
if (v_isShared_1419_ == 0)
{
v___x_1427_ = v___x_1418_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_fst_1415_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_snd_1416_);
v___x_1427_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v___x_1428_; 
v___x_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___y_1388_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
return v___x_1428_;
}
}
else
{
uint8_t v___y_1431_; uint8_t v___x_1531_; uint8_t v___x_1579_; 
v___x_1531_ = lean_byte_array_fget(v_array_1413_, v_idx_1414_);
v___x_1579_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1531_);
if (v___x_1579_ == 0)
{
uint8_t v___x_1580_; uint8_t v___x_1581_; 
v___x_1580_ = 47;
v___x_1581_ = lean_uint8_dec_eq(v___x_1531_, v___x_1580_);
if (v___x_1581_ == 0)
{
uint8_t v___x_1582_; uint8_t v___x_1583_; 
v___x_1582_ = 48;
v___x_1583_ = lean_uint8_dec_le(v___x_1582_, v___x_1531_);
if (v___x_1583_ == 0)
{
goto v___jp_1574_;
}
else
{
uint8_t v___x_1584_; uint8_t v___x_1585_; 
v___x_1584_ = 57;
v___x_1585_ = lean_uint8_dec_le(v___x_1531_, v___x_1584_);
if (v___x_1585_ == 0)
{
goto v___jp_1574_;
}
else
{
v___y_1431_ = v___x_1421_;
goto v___jp_1430_;
}
}
}
else
{
v___y_1431_ = v___x_1421_;
goto v___jp_1430_;
}
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
lean_del_object(v___x_1418_);
lean_dec_ref(v_config_1386_);
v___x_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1586_, 0, v_fst_1415_);
lean_ctor_set(v___x_1586_, 1, v_snd_1416_);
v___x_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___y_1388_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
return v___x_1587_;
}
v___jp_1430_:
{
if (v___y_1431_ == 0)
{
lean_object* v___x_1433_; 
lean_dec_ref(v_config_1386_);
if (v_isShared_1419_ == 0)
{
v___x_1433_ = v___x_1418_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_fst_1415_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_snd_1416_);
v___x_1433_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___y_1388_);
lean_ctor_set(v___x_1434_, 1, v___x_1433_);
return v___x_1434_;
}
}
else
{
lean_object* v_maxPathSegments_1436_; lean_object* v_maxTotalPathLength_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; 
v_maxPathSegments_1436_ = lean_ctor_get(v_config_1386_, 6);
v_maxTotalPathLength_1437_ = lean_ctor_get(v_config_1386_, 7);
v___x_1438_ = lean_array_get_size(v_fst_1415_);
v___x_1439_ = lean_nat_dec_le(v_maxPathSegments_1436_, v___x_1438_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; 
v___x_1440_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1386_, v___y_1388_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_pos_1441_; lean_object* v_res_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1514_; 
v_pos_1441_ = lean_ctor_get(v___x_1440_, 0);
v_res_1442_ = lean_ctor_get(v___x_1440_, 1);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1444_ = v___x_1440_;
v_isShared_1445_ = v_isSharedCheck_1514_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_res_1442_);
lean_inc(v_pos_1441_);
lean_dec(v___x_1440_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1514_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
lean_inc(v_res_1442_);
v___x_1446_ = l_ByteSlice_toByteArray(v_res_1442_);
v___x_1447_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_1446_);
if (lean_obj_tag(v___x_1447_) == 1)
{
lean_object* v_val_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1509_; 
v_val_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1509_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_val_1448_);
lean_dec(v___x_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1509_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
v___x_1452_ = l_ByteSlice_size(v_res_1442_);
lean_dec(v_res_1442_);
v___x_1453_ = lean_nat_add(v_snd_1416_, v___x_1452_);
lean_dec(v___x_1452_);
lean_dec(v_snd_1416_);
v___x_1454_ = lean_nat_dec_lt(v_maxTotalPathLength_1437_, v___x_1453_);
if (v___x_1454_ == 0)
{
lean_object* v_array_1455_; lean_object* v_idx_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; uint8_t v___x_1459_; 
v_array_1455_ = lean_ctor_get(v_pos_1441_, 0);
v_idx_1456_ = lean_ctor_get(v_pos_1441_, 1);
v___x_1457_ = lean_array_push(v_fst_1415_, v_val_1448_);
v___x_1458_ = lean_byte_array_size(v_array_1455_);
v___x_1459_ = lean_nat_dec_lt(v_idx_1456_, v___x_1458_);
if (v___x_1459_ == 0)
{
lean_del_object(v___x_1450_);
lean_del_object(v___x_1444_);
lean_del_object(v___x_1418_);
lean_dec_ref(v_config_1386_);
v___y_1390_ = v___x_1457_;
v___y_1391_ = v___x_1453_;
v___y_1392_ = v_pos_1441_;
goto v___jp_1389_;
}
else
{
uint8_t v___x_1460_; uint8_t v___x_1461_; uint8_t v___x_1462_; 
v___x_1460_ = lean_byte_array_fget(v_array_1455_, v_idx_1456_);
v___x_1461_ = 47;
v___x_1462_ = lean_uint8_dec_eq(v___x_1460_, v___x_1461_);
if (v___x_1462_ == 0)
{
lean_del_object(v___x_1450_);
lean_del_object(v___x_1444_);
lean_del_object(v___x_1418_);
lean_dec_ref(v_config_1386_);
v___y_1390_ = v___x_1457_;
v___y_1391_ = v___x_1453_;
v___y_1392_ = v_pos_1441_;
goto v___jp_1389_;
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; uint8_t v___x_1465_; 
v___x_1463_ = lean_unsigned_to_nat(1u);
v___x_1464_ = lean_nat_add(v___x_1453_, v___x_1463_);
lean_dec(v___x_1453_);
v___x_1465_ = lean_nat_dec_lt(v_maxTotalPathLength_1437_, v___x_1464_);
if (v___x_1465_ == 0)
{
lean_del_object(v___x_1450_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1468_; 
lean_dec(v___x_1464_);
lean_dec_ref(v___x_1457_);
lean_del_object(v___x_1418_);
lean_dec_ref(v_config_1386_);
v___x_1466_ = lean_box(0);
if (v_isShared_1445_ == 0)
{
lean_ctor_set_tag(v___x_1444_, 1);
lean_ctor_set(v___x_1444_, 1, v___x_1466_);
v___x_1468_ = v___x_1444_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_pos_1441_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v___x_1466_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
else
{
lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1484_; 
lean_inc(v_idx_1456_);
lean_inc_ref(v_array_1455_);
lean_del_object(v___x_1444_);
v_isSharedCheck_1484_ = !lean_is_exclusive(v_pos_1441_);
if (v_isSharedCheck_1484_ == 0)
{
lean_object* v_unused_1485_; lean_object* v_unused_1486_; 
v_unused_1485_ = lean_ctor_get(v_pos_1441_, 1);
lean_dec(v_unused_1485_);
v_unused_1486_ = lean_ctor_get(v_pos_1441_, 0);
lean_dec(v_unused_1486_);
v___x_1471_ = v_pos_1441_;
v_isShared_1472_ = v_isSharedCheck_1484_;
goto v_resetjp_1470_;
}
else
{
lean_dec(v_pos_1441_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1484_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1475_; 
v___x_1473_ = lean_nat_add(v_idx_1456_, v___x_1463_);
lean_dec(v_idx_1456_);
lean_inc(v___x_1473_);
lean_inc_ref(v_array_1455_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 1, v___x_1473_);
v___x_1475_ = v___x_1471_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_array_1455_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v___x_1473_);
v___x_1475_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
uint8_t v___x_1476_; 
v___x_1476_ = lean_nat_dec_lt(v___x_1473_, v___x_1458_);
if (v___x_1476_ == 0)
{
lean_dec(v___x_1473_);
lean_dec_ref(v_array_1455_);
lean_del_object(v___x_1418_);
lean_inc(v_maxPathSegments_1436_);
v___y_1396_ = v___x_1475_;
v___y_1397_ = v___x_1464_;
v___y_1398_ = v_maxPathSegments_1436_;
v___y_1399_ = v___x_1457_;
goto v___jp_1395_;
}
else
{
uint8_t v___x_1477_; uint8_t v___x_1478_; 
v___x_1477_ = lean_byte_array_fget(v_array_1455_, v___x_1473_);
lean_dec(v___x_1473_);
lean_dec_ref(v_array_1455_);
v___x_1478_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1477_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1480_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 1, v___x_1464_);
lean_ctor_set(v___x_1418_, 0, v___x_1457_);
v___x_1480_ = v___x_1418_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1457_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v___x_1464_);
v___x_1480_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
v_a_1387_ = v___x_1480_;
v___y_1388_ = v___x_1475_;
goto _start;
}
}
else
{
lean_del_object(v___x_1418_);
lean_inc(v_maxPathSegments_1436_);
v___y_1396_ = v___x_1475_;
v___y_1397_ = v___x_1464_;
v___y_1398_ = v_maxPathSegments_1436_;
v___y_1399_ = v___x_1457_;
goto v___jp_1395_;
}
}
}
}
}
}
else
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1493_; 
lean_inc(v_maxTotalPathLength_1437_);
lean_dec(v___x_1464_);
lean_dec_ref(v___x_1457_);
lean_del_object(v___x_1418_);
lean_dec_ref(v_config_1386_);
v___x_1487_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1488_ = l_Nat_reprFast(v_maxTotalPathLength_1437_);
v___x_1489_ = lean_string_append(v___x_1487_, v___x_1488_);
lean_dec_ref(v___x_1488_);
v___x_1490_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1491_ = lean_string_append(v___x_1489_, v___x_1490_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1491_);
v___x_1493_ = v___x_1450_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1495_; 
if (v_isShared_1445_ == 0)
{
lean_ctor_set_tag(v___x_1444_, 1);
lean_ctor_set(v___x_1444_, 1, v___x_1493_);
v___x_1495_ = v___x_1444_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_pos_1441_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
}
else
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1504_; 
lean_inc(v_maxTotalPathLength_1437_);
lean_dec(v___x_1453_);
lean_dec(v_val_1448_);
lean_del_object(v___x_1418_);
lean_dec(v_fst_1415_);
lean_dec_ref(v_config_1386_);
v___x_1498_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1499_ = l_Nat_reprFast(v_maxTotalPathLength_1437_);
v___x_1500_ = lean_string_append(v___x_1498_, v___x_1499_);
lean_dec_ref(v___x_1499_);
v___x_1501_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1502_ = lean_string_append(v___x_1500_, v___x_1501_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1502_);
v___x_1504_ = v___x_1450_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1502_);
v___x_1504_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1506_; 
if (v_isShared_1445_ == 0)
{
lean_ctor_set_tag(v___x_1444_, 1);
lean_ctor_set(v___x_1444_, 1, v___x_1504_);
v___x_1506_ = v___x_1444_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_pos_1441_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
}
else
{
lean_object* v___x_1510_; lean_object* v___x_1512_; 
lean_dec(v___x_1447_);
lean_dec(v_res_1442_);
lean_del_object(v___x_1418_);
lean_dec(v_snd_1416_);
lean_dec(v_fst_1415_);
lean_dec_ref(v_config_1386_);
v___x_1510_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5));
if (v_isShared_1445_ == 0)
{
lean_ctor_set_tag(v___x_1444_, 1);
lean_ctor_set(v___x_1444_, 1, v___x_1510_);
v___x_1512_ = v___x_1444_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_pos_1441_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
else
{
lean_object* v_pos_1515_; lean_object* v_err_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
lean_del_object(v___x_1418_);
lean_dec(v_snd_1416_);
lean_dec(v_fst_1415_);
lean_dec_ref(v_config_1386_);
v_pos_1515_ = lean_ctor_get(v___x_1440_, 0);
v_err_1516_ = lean_ctor_get(v___x_1440_, 1);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v___x_1440_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_err_1516_);
lean_inc(v_pos_1515_);
lean_dec(v___x_1440_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_pos_1515_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_err_1516_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
else
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_inc(v_maxPathSegments_1436_);
lean_del_object(v___x_1418_);
lean_dec(v_snd_1416_);
lean_dec(v_fst_1415_);
lean_dec_ref(v_config_1386_);
v___x_1524_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1525_ = l_Nat_reprFast(v_maxPathSegments_1436_);
v___x_1526_ = lean_string_append(v___x_1524_, v___x_1525_);
lean_dec_ref(v___x_1525_);
v___x_1527_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1528_ = lean_string_append(v___x_1526_, v___x_1527_);
v___x_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
v___x_1530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___y_1388_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
return v___x_1530_;
}
}
}
v___jp_1532_:
{
uint8_t v___x_1533_; uint8_t v___x_1534_; 
v___x_1533_ = 45;
v___x_1534_ = lean_uint8_dec_eq(v___x_1531_, v___x_1533_);
if (v___x_1534_ == 0)
{
uint8_t v___x_1535_; uint8_t v___x_1536_; 
v___x_1535_ = 46;
v___x_1536_ = lean_uint8_dec_eq(v___x_1531_, v___x_1535_);
if (v___x_1536_ == 0)
{
uint8_t v___x_1537_; uint8_t v___x_1538_; 
v___x_1537_ = 95;
v___x_1538_ = lean_uint8_dec_eq(v___x_1531_, v___x_1537_);
if (v___x_1538_ == 0)
{
uint8_t v___x_1539_; uint8_t v___x_1540_; 
v___x_1539_ = 126;
v___x_1540_ = lean_uint8_dec_eq(v___x_1531_, v___x_1539_);
if (v___x_1540_ == 0)
{
uint8_t v___x_1541_; uint8_t v___x_1542_; 
v___x_1541_ = 33;
v___x_1542_ = lean_uint8_dec_eq(v___x_1531_, v___x_1541_);
if (v___x_1542_ == 0)
{
uint8_t v___x_1543_; uint8_t v___x_1544_; 
v___x_1543_ = 36;
v___x_1544_ = lean_uint8_dec_eq(v___x_1531_, v___x_1543_);
if (v___x_1544_ == 0)
{
uint8_t v___x_1545_; uint8_t v___x_1546_; 
v___x_1545_ = 38;
v___x_1546_ = lean_uint8_dec_eq(v___x_1531_, v___x_1545_);
if (v___x_1546_ == 0)
{
uint8_t v___x_1547_; uint8_t v___x_1548_; 
v___x_1547_ = 39;
v___x_1548_ = lean_uint8_dec_eq(v___x_1531_, v___x_1547_);
if (v___x_1548_ == 0)
{
uint8_t v___x_1549_; uint8_t v___x_1550_; 
v___x_1549_ = 40;
v___x_1550_ = lean_uint8_dec_eq(v___x_1531_, v___x_1549_);
if (v___x_1550_ == 0)
{
uint8_t v___x_1551_; uint8_t v___x_1552_; 
v___x_1551_ = 41;
v___x_1552_ = lean_uint8_dec_eq(v___x_1531_, v___x_1551_);
if (v___x_1552_ == 0)
{
uint8_t v___x_1553_; uint8_t v___x_1554_; 
v___x_1553_ = 42;
v___x_1554_ = lean_uint8_dec_eq(v___x_1531_, v___x_1553_);
if (v___x_1554_ == 0)
{
uint8_t v___x_1555_; uint8_t v___x_1556_; 
v___x_1555_ = 43;
v___x_1556_ = lean_uint8_dec_eq(v___x_1531_, v___x_1555_);
if (v___x_1556_ == 0)
{
uint8_t v___x_1557_; uint8_t v___x_1558_; 
v___x_1557_ = 44;
v___x_1558_ = lean_uint8_dec_eq(v___x_1531_, v___x_1557_);
if (v___x_1558_ == 0)
{
uint8_t v___x_1559_; uint8_t v___x_1560_; 
v___x_1559_ = 59;
v___x_1560_ = lean_uint8_dec_eq(v___x_1531_, v___x_1559_);
if (v___x_1560_ == 0)
{
uint8_t v___x_1561_; uint8_t v___x_1562_; 
v___x_1561_ = 61;
v___x_1562_ = lean_uint8_dec_eq(v___x_1531_, v___x_1561_);
if (v___x_1562_ == 0)
{
uint8_t v___x_1563_; uint8_t v___x_1564_; 
v___x_1563_ = 58;
v___x_1564_ = lean_uint8_dec_eq(v___x_1531_, v___x_1563_);
if (v___x_1564_ == 0)
{
uint8_t v___x_1565_; uint8_t v___x_1566_; 
v___x_1565_ = 64;
v___x_1566_ = lean_uint8_dec_eq(v___x_1531_, v___x_1565_);
if (v___x_1566_ == 0)
{
uint8_t v___x_1567_; uint8_t v___x_1568_; 
v___x_1567_ = 37;
v___x_1568_ = lean_uint8_dec_eq(v___x_1531_, v___x_1567_);
v___y_1431_ = v___x_1568_;
goto v___jp_1430_;
}
else
{
v___y_1431_ = v___x_1421_;
goto v___jp_1430_;
}
}
else
{
v___y_1431_ = v___x_1421_;
goto v___jp_1430_;
}
}
else
{
v___y_1431_ = v___x_1421_;
goto v___jp_1430_;
}
}
else
{
v___y_1431_ = v___x_1421_;
goto v___jp_1430_;
}
}
else
{
v___y_1431_ = v___x_1421_;
goto v___jp_1430_;
}
}
else
{
v___y_1431_ = v___x_1421_;
goto v___jp_1430_;
}
}
else
{
v___y_1431_ = v___x_1421_;
goto v___jp_1430_;
}
}
else
{
v___y_1431_ = v___x_1421_;
goto v___jp_1430_;
}
}
else
{
v___y_1431_ = v___x_1421_;
goto v___jp_1430_;
}
}
else
{
v___y_1431_ = v___x_1421_;
goto v___jp_1430_;
}
}
else
{
v___y_1431_ = v___x_1421_;
goto v___jp_1430_;
}
}
else
{
v___y_1431_ = v___x_1421_;
goto v___jp_1430_;
}
}
else
{
v___y_1431_ = v___x_1421_;
goto v___jp_1430_;
}
}
else
{
v___y_1431_ = v___x_1421_;
goto v___jp_1430_;
}
}
else
{
v___y_1431_ = v___x_1421_;
goto v___jp_1430_;
}
}
else
{
v___y_1431_ = v___x_1421_;
goto v___jp_1430_;
}
}
else
{
v___y_1431_ = v___x_1421_;
goto v___jp_1430_;
}
}
v___jp_1569_:
{
uint8_t v___x_1570_; uint8_t v___x_1571_; 
v___x_1570_ = 65;
v___x_1571_ = lean_uint8_dec_le(v___x_1570_, v___x_1531_);
if (v___x_1571_ == 0)
{
goto v___jp_1532_;
}
else
{
uint8_t v___x_1572_; uint8_t v___x_1573_; 
v___x_1572_ = 90;
v___x_1573_ = lean_uint8_dec_le(v___x_1531_, v___x_1572_);
if (v___x_1573_ == 0)
{
goto v___jp_1532_;
}
else
{
v___y_1431_ = v___x_1421_;
goto v___jp_1430_;
}
}
}
v___jp_1574_:
{
uint8_t v___x_1575_; uint8_t v___x_1576_; 
v___x_1575_ = 97;
v___x_1576_ = lean_uint8_dec_le(v___x_1575_, v___x_1531_);
if (v___x_1576_ == 0)
{
goto v___jp_1569_;
}
else
{
uint8_t v___x_1577_; uint8_t v___x_1578_; 
v___x_1577_ = 122;
v___x_1578_ = lean_uint8_dec_le(v___x_1531_, v___x_1577_);
if (v___x_1578_ == 0)
{
goto v___jp_1569_;
}
else
{
v___y_1431_ = v___x_1421_;
goto v___jp_1430_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(lean_object* v_config_1589_, lean_object* v_a_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v_array_1616_; lean_object* v_idx_1617_; lean_object* v_fst_1618_; lean_object* v_snd_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1791_; 
v_array_1616_ = lean_ctor_get(v___y_1591_, 0);
v_idx_1617_ = lean_ctor_get(v___y_1591_, 1);
v_fst_1618_ = lean_ctor_get(v_a_1590_, 0);
v_snd_1619_ = lean_ctor_get(v_a_1590_, 1);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_a_1590_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1621_ = v_a_1590_;
v_isShared_1622_ = v_isSharedCheck_1791_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_snd_1619_);
lean_inc(v_fst_1618_);
lean_dec(v_a_1590_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1791_;
goto v_resetjp_1620_;
}
v___jp_1592_:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___y_1594_);
lean_ctor_set(v___x_1596_, 1, v___y_1593_);
v___x_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___y_1595_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
return v___x_1597_;
}
v___jp_1598_:
{
lean_object* v___x_1603_; uint8_t v___x_1604_; 
v___x_1603_ = lean_array_get_size(v___y_1600_);
v___x_1604_ = lean_nat_dec_le(v___y_1599_, v___x_1603_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
lean_dec(v___y_1599_);
v___x_1605_ = l_ByteArray_empty;
v___x_1606_ = lean_array_push(v___y_1600_, v___x_1605_);
v___x_1607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1606_);
lean_ctor_set(v___x_1607_, 1, v___y_1601_);
v___x_1608_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_1589_, v___x_1607_, v___y_1602_);
return v___x_1608_;
}
else
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec_ref(v_config_1589_);
v___x_1609_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1610_ = l_Nat_reprFast(v___y_1599_);
v___x_1611_ = lean_string_append(v___x_1609_, v___x_1610_);
lean_dec_ref(v___x_1610_);
v___x_1612_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1613_ = lean_string_append(v___x_1611_, v___x_1612_);
v___x_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
v___x_1615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___y_1602_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
return v___x_1615_;
}
}
v_resetjp_1620_:
{
lean_object* v___x_1623_; uint8_t v___x_1624_; 
v___x_1623_ = lean_byte_array_size(v_array_1616_);
v___x_1624_ = lean_nat_dec_lt(v_idx_1617_, v___x_1623_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1626_; 
lean_dec_ref(v_config_1589_);
if (v_isShared_1622_ == 0)
{
v___x_1626_ = v___x_1621_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_fst_1618_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v_snd_1619_);
v___x_1626_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
lean_object* v___x_1627_; 
v___x_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___y_1591_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
return v___x_1627_;
}
}
else
{
if (v___x_1624_ == 0)
{
lean_object* v___x_1630_; 
lean_dec_ref(v_config_1589_);
if (v_isShared_1622_ == 0)
{
v___x_1630_ = v___x_1621_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_fst_1618_);
lean_ctor_set(v_reuseFailAlloc_1632_, 1, v_snd_1619_);
v___x_1630_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1631_; 
v___x_1631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___y_1591_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
return v___x_1631_;
}
}
else
{
uint8_t v___y_1634_; uint8_t v___x_1734_; uint8_t v___x_1782_; 
v___x_1734_ = lean_byte_array_fget(v_array_1616_, v_idx_1617_);
v___x_1782_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1734_);
if (v___x_1782_ == 0)
{
uint8_t v___x_1783_; uint8_t v___x_1784_; 
v___x_1783_ = 47;
v___x_1784_ = lean_uint8_dec_eq(v___x_1734_, v___x_1783_);
if (v___x_1784_ == 0)
{
uint8_t v___x_1785_; uint8_t v___x_1786_; 
v___x_1785_ = 48;
v___x_1786_ = lean_uint8_dec_le(v___x_1785_, v___x_1734_);
if (v___x_1786_ == 0)
{
goto v___jp_1777_;
}
else
{
uint8_t v___x_1787_; uint8_t v___x_1788_; 
v___x_1787_ = 57;
v___x_1788_ = lean_uint8_dec_le(v___x_1734_, v___x_1787_);
if (v___x_1788_ == 0)
{
goto v___jp_1777_;
}
else
{
v___y_1634_ = v___x_1624_;
goto v___jp_1633_;
}
}
}
else
{
v___y_1634_ = v___x_1624_;
goto v___jp_1633_;
}
}
else
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_del_object(v___x_1621_);
lean_dec_ref(v_config_1589_);
v___x_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1789_, 0, v_fst_1618_);
lean_ctor_set(v___x_1789_, 1, v_snd_1619_);
v___x_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___y_1591_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
return v___x_1790_;
}
v___jp_1633_:
{
if (v___y_1634_ == 0)
{
lean_object* v___x_1636_; 
lean_dec_ref(v_config_1589_);
if (v_isShared_1622_ == 0)
{
v___x_1636_ = v___x_1621_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_fst_1618_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_snd_1619_);
v___x_1636_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1637_; 
v___x_1637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___y_1591_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
return v___x_1637_;
}
}
else
{
lean_object* v_maxPathSegments_1639_; lean_object* v_maxTotalPathLength_1640_; lean_object* v___x_1641_; uint8_t v___x_1642_; 
v_maxPathSegments_1639_ = lean_ctor_get(v_config_1589_, 6);
v_maxTotalPathLength_1640_ = lean_ctor_get(v_config_1589_, 7);
v___x_1641_ = lean_array_get_size(v_fst_1618_);
v___x_1642_ = lean_nat_dec_le(v_maxPathSegments_1639_, v___x_1641_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; 
v___x_1643_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1589_, v___y_1591_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_pos_1644_; lean_object* v_res_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1717_; 
v_pos_1644_ = lean_ctor_get(v___x_1643_, 0);
v_res_1645_ = lean_ctor_get(v___x_1643_, 1);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1647_ = v___x_1643_;
v_isShared_1648_ = v_isSharedCheck_1717_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_res_1645_);
lean_inc(v_pos_1644_);
lean_dec(v___x_1643_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1717_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_inc(v_res_1645_);
v___x_1649_ = l_ByteSlice_toByteArray(v_res_1645_);
v___x_1650_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_1649_);
if (lean_obj_tag(v___x_1650_) == 1)
{
lean_object* v_val_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1712_; 
v_val_1651_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1653_ = v___x_1650_;
v_isShared_1654_ = v_isSharedCheck_1712_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_val_1651_);
lean_dec(v___x_1650_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1712_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; uint8_t v___x_1657_; 
v___x_1655_ = l_ByteSlice_size(v_res_1645_);
lean_dec(v_res_1645_);
v___x_1656_ = lean_nat_add(v_snd_1619_, v___x_1655_);
lean_dec(v___x_1655_);
lean_dec(v_snd_1619_);
v___x_1657_ = lean_nat_dec_lt(v_maxTotalPathLength_1640_, v___x_1656_);
if (v___x_1657_ == 0)
{
lean_object* v_array_1658_; lean_object* v_idx_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; uint8_t v___x_1662_; 
v_array_1658_ = lean_ctor_get(v_pos_1644_, 0);
v_idx_1659_ = lean_ctor_get(v_pos_1644_, 1);
v___x_1660_ = lean_array_push(v_fst_1618_, v_val_1651_);
v___x_1661_ = lean_byte_array_size(v_array_1658_);
v___x_1662_ = lean_nat_dec_lt(v_idx_1659_, v___x_1661_);
if (v___x_1662_ == 0)
{
lean_del_object(v___x_1653_);
lean_del_object(v___x_1647_);
lean_del_object(v___x_1621_);
lean_dec_ref(v_config_1589_);
v___y_1593_ = v___x_1656_;
v___y_1594_ = v___x_1660_;
v___y_1595_ = v_pos_1644_;
goto v___jp_1592_;
}
else
{
uint8_t v___x_1663_; uint8_t v___x_1664_; uint8_t v___x_1665_; 
v___x_1663_ = lean_byte_array_fget(v_array_1658_, v_idx_1659_);
v___x_1664_ = 47;
v___x_1665_ = lean_uint8_dec_eq(v___x_1663_, v___x_1664_);
if (v___x_1665_ == 0)
{
lean_del_object(v___x_1653_);
lean_del_object(v___x_1647_);
lean_del_object(v___x_1621_);
lean_dec_ref(v_config_1589_);
v___y_1593_ = v___x_1656_;
v___y_1594_ = v___x_1660_;
v___y_1595_ = v_pos_1644_;
goto v___jp_1592_;
}
else
{
lean_object* v___x_1666_; lean_object* v___x_1667_; uint8_t v___x_1668_; 
v___x_1666_ = lean_unsigned_to_nat(1u);
v___x_1667_ = lean_nat_add(v___x_1656_, v___x_1666_);
lean_dec(v___x_1656_);
v___x_1668_ = lean_nat_dec_lt(v_maxTotalPathLength_1640_, v___x_1667_);
if (v___x_1668_ == 0)
{
lean_del_object(v___x_1653_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1669_; lean_object* v___x_1671_; 
lean_dec(v___x_1667_);
lean_dec_ref(v___x_1660_);
lean_del_object(v___x_1621_);
lean_dec_ref(v_config_1589_);
v___x_1669_ = lean_box(0);
if (v_isShared_1648_ == 0)
{
lean_ctor_set_tag(v___x_1647_, 1);
lean_ctor_set(v___x_1647_, 1, v___x_1669_);
v___x_1671_ = v___x_1647_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_pos_1644_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
else
{
lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1687_; 
lean_inc(v_idx_1659_);
lean_inc_ref(v_array_1658_);
lean_del_object(v___x_1647_);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_pos_1644_);
if (v_isSharedCheck_1687_ == 0)
{
lean_object* v_unused_1688_; lean_object* v_unused_1689_; 
v_unused_1688_ = lean_ctor_get(v_pos_1644_, 1);
lean_dec(v_unused_1688_);
v_unused_1689_ = lean_ctor_get(v_pos_1644_, 0);
lean_dec(v_unused_1689_);
v___x_1674_ = v_pos_1644_;
v_isShared_1675_ = v_isSharedCheck_1687_;
goto v_resetjp_1673_;
}
else
{
lean_dec(v_pos_1644_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1687_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; lean_object* v___x_1678_; 
v___x_1676_ = lean_nat_add(v_idx_1659_, v___x_1666_);
lean_dec(v_idx_1659_);
lean_inc(v___x_1676_);
lean_inc_ref(v_array_1658_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 1, v___x_1676_);
v___x_1678_ = v___x_1674_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_array_1658_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
uint8_t v___x_1679_; 
v___x_1679_ = lean_nat_dec_lt(v___x_1676_, v___x_1661_);
if (v___x_1679_ == 0)
{
lean_dec(v___x_1676_);
lean_dec_ref(v_array_1658_);
lean_del_object(v___x_1621_);
lean_inc(v_maxPathSegments_1639_);
v___y_1599_ = v_maxPathSegments_1639_;
v___y_1600_ = v___x_1660_;
v___y_1601_ = v___x_1667_;
v___y_1602_ = v___x_1678_;
goto v___jp_1598_;
}
else
{
uint8_t v___x_1680_; uint8_t v___x_1681_; 
v___x_1680_ = lean_byte_array_fget(v_array_1658_, v___x_1676_);
lean_dec(v___x_1676_);
lean_dec_ref(v_array_1658_);
v___x_1681_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1680_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1683_; 
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 1, v___x_1667_);
lean_ctor_set(v___x_1621_, 0, v___x_1660_);
v___x_1683_ = v___x_1621_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1660_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v___x_1667_);
v___x_1683_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1684_; 
v___x_1684_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_1589_, v___x_1683_, v___x_1678_);
return v___x_1684_;
}
}
else
{
lean_del_object(v___x_1621_);
lean_inc(v_maxPathSegments_1639_);
v___y_1599_ = v_maxPathSegments_1639_;
v___y_1600_ = v___x_1660_;
v___y_1601_ = v___x_1667_;
v___y_1602_ = v___x_1678_;
goto v___jp_1598_;
}
}
}
}
}
}
else
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1696_; 
lean_inc(v_maxTotalPathLength_1640_);
lean_dec(v___x_1667_);
lean_dec_ref(v___x_1660_);
lean_del_object(v___x_1621_);
lean_dec_ref(v_config_1589_);
v___x_1690_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1691_ = l_Nat_reprFast(v_maxTotalPathLength_1640_);
v___x_1692_ = lean_string_append(v___x_1690_, v___x_1691_);
lean_dec_ref(v___x_1691_);
v___x_1693_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1694_ = lean_string_append(v___x_1692_, v___x_1693_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 0, v___x_1694_);
v___x_1696_ = v___x_1653_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1694_);
v___x_1696_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
lean_object* v___x_1698_; 
if (v_isShared_1648_ == 0)
{
lean_ctor_set_tag(v___x_1647_, 1);
lean_ctor_set(v___x_1647_, 1, v___x_1696_);
v___x_1698_ = v___x_1647_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_pos_1644_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
}
else
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1707_; 
lean_inc(v_maxTotalPathLength_1640_);
lean_dec(v___x_1656_);
lean_dec(v_val_1651_);
lean_del_object(v___x_1621_);
lean_dec(v_fst_1618_);
lean_dec_ref(v_config_1589_);
v___x_1701_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1702_ = l_Nat_reprFast(v_maxTotalPathLength_1640_);
v___x_1703_ = lean_string_append(v___x_1701_, v___x_1702_);
lean_dec_ref(v___x_1702_);
v___x_1704_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1705_ = lean_string_append(v___x_1703_, v___x_1704_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 0, v___x_1705_);
v___x_1707_ = v___x_1653_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
lean_object* v___x_1709_; 
if (v_isShared_1648_ == 0)
{
lean_ctor_set_tag(v___x_1647_, 1);
lean_ctor_set(v___x_1647_, 1, v___x_1707_);
v___x_1709_ = v___x_1647_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_pos_1644_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
}
else
{
lean_object* v___x_1713_; lean_object* v___x_1715_; 
lean_dec(v___x_1650_);
lean_dec(v_res_1645_);
lean_del_object(v___x_1621_);
lean_dec(v_snd_1619_);
lean_dec(v_fst_1618_);
lean_dec_ref(v_config_1589_);
v___x_1713_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5));
if (v_isShared_1648_ == 0)
{
lean_ctor_set_tag(v___x_1647_, 1);
lean_ctor_set(v___x_1647_, 1, v___x_1713_);
v___x_1715_ = v___x_1647_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_pos_1644_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
else
{
lean_object* v_pos_1718_; lean_object* v_err_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
lean_del_object(v___x_1621_);
lean_dec(v_snd_1619_);
lean_dec(v_fst_1618_);
lean_dec_ref(v_config_1589_);
v_pos_1718_ = lean_ctor_get(v___x_1643_, 0);
v_err_1719_ = lean_ctor_get(v___x_1643_, 1);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1643_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_err_1719_);
lean_inc(v_pos_1718_);
lean_dec(v___x_1643_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_pos_1718_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_err_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
else
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
lean_inc(v_maxPathSegments_1639_);
lean_del_object(v___x_1621_);
lean_dec(v_snd_1619_);
lean_dec(v_fst_1618_);
lean_dec_ref(v_config_1589_);
v___x_1727_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1728_ = l_Nat_reprFast(v_maxPathSegments_1639_);
v___x_1729_ = lean_string_append(v___x_1727_, v___x_1728_);
lean_dec_ref(v___x_1728_);
v___x_1730_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1731_ = lean_string_append(v___x_1729_, v___x_1730_);
v___x_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
v___x_1733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___y_1591_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
return v___x_1733_;
}
}
}
v___jp_1735_:
{
uint8_t v___x_1736_; uint8_t v___x_1737_; 
v___x_1736_ = 45;
v___x_1737_ = lean_uint8_dec_eq(v___x_1734_, v___x_1736_);
if (v___x_1737_ == 0)
{
uint8_t v___x_1738_; uint8_t v___x_1739_; 
v___x_1738_ = 46;
v___x_1739_ = lean_uint8_dec_eq(v___x_1734_, v___x_1738_);
if (v___x_1739_ == 0)
{
uint8_t v___x_1740_; uint8_t v___x_1741_; 
v___x_1740_ = 95;
v___x_1741_ = lean_uint8_dec_eq(v___x_1734_, v___x_1740_);
if (v___x_1741_ == 0)
{
uint8_t v___x_1742_; uint8_t v___x_1743_; 
v___x_1742_ = 126;
v___x_1743_ = lean_uint8_dec_eq(v___x_1734_, v___x_1742_);
if (v___x_1743_ == 0)
{
uint8_t v___x_1744_; uint8_t v___x_1745_; 
v___x_1744_ = 33;
v___x_1745_ = lean_uint8_dec_eq(v___x_1734_, v___x_1744_);
if (v___x_1745_ == 0)
{
uint8_t v___x_1746_; uint8_t v___x_1747_; 
v___x_1746_ = 36;
v___x_1747_ = lean_uint8_dec_eq(v___x_1734_, v___x_1746_);
if (v___x_1747_ == 0)
{
uint8_t v___x_1748_; uint8_t v___x_1749_; 
v___x_1748_ = 38;
v___x_1749_ = lean_uint8_dec_eq(v___x_1734_, v___x_1748_);
if (v___x_1749_ == 0)
{
uint8_t v___x_1750_; uint8_t v___x_1751_; 
v___x_1750_ = 39;
v___x_1751_ = lean_uint8_dec_eq(v___x_1734_, v___x_1750_);
if (v___x_1751_ == 0)
{
uint8_t v___x_1752_; uint8_t v___x_1753_; 
v___x_1752_ = 40;
v___x_1753_ = lean_uint8_dec_eq(v___x_1734_, v___x_1752_);
if (v___x_1753_ == 0)
{
uint8_t v___x_1754_; uint8_t v___x_1755_; 
v___x_1754_ = 41;
v___x_1755_ = lean_uint8_dec_eq(v___x_1734_, v___x_1754_);
if (v___x_1755_ == 0)
{
uint8_t v___x_1756_; uint8_t v___x_1757_; 
v___x_1756_ = 42;
v___x_1757_ = lean_uint8_dec_eq(v___x_1734_, v___x_1756_);
if (v___x_1757_ == 0)
{
uint8_t v___x_1758_; uint8_t v___x_1759_; 
v___x_1758_ = 43;
v___x_1759_ = lean_uint8_dec_eq(v___x_1734_, v___x_1758_);
if (v___x_1759_ == 0)
{
uint8_t v___x_1760_; uint8_t v___x_1761_; 
v___x_1760_ = 44;
v___x_1761_ = lean_uint8_dec_eq(v___x_1734_, v___x_1760_);
if (v___x_1761_ == 0)
{
uint8_t v___x_1762_; uint8_t v___x_1763_; 
v___x_1762_ = 59;
v___x_1763_ = lean_uint8_dec_eq(v___x_1734_, v___x_1762_);
if (v___x_1763_ == 0)
{
uint8_t v___x_1764_; uint8_t v___x_1765_; 
v___x_1764_ = 61;
v___x_1765_ = lean_uint8_dec_eq(v___x_1734_, v___x_1764_);
if (v___x_1765_ == 0)
{
uint8_t v___x_1766_; uint8_t v___x_1767_; 
v___x_1766_ = 58;
v___x_1767_ = lean_uint8_dec_eq(v___x_1734_, v___x_1766_);
if (v___x_1767_ == 0)
{
uint8_t v___x_1768_; uint8_t v___x_1769_; 
v___x_1768_ = 64;
v___x_1769_ = lean_uint8_dec_eq(v___x_1734_, v___x_1768_);
if (v___x_1769_ == 0)
{
uint8_t v___x_1770_; uint8_t v___x_1771_; 
v___x_1770_ = 37;
v___x_1771_ = lean_uint8_dec_eq(v___x_1734_, v___x_1770_);
v___y_1634_ = v___x_1771_;
goto v___jp_1633_;
}
else
{
v___y_1634_ = v___x_1624_;
goto v___jp_1633_;
}
}
else
{
v___y_1634_ = v___x_1624_;
goto v___jp_1633_;
}
}
else
{
v___y_1634_ = v___x_1624_;
goto v___jp_1633_;
}
}
else
{
v___y_1634_ = v___x_1624_;
goto v___jp_1633_;
}
}
else
{
v___y_1634_ = v___x_1624_;
goto v___jp_1633_;
}
}
else
{
v___y_1634_ = v___x_1624_;
goto v___jp_1633_;
}
}
else
{
v___y_1634_ = v___x_1624_;
goto v___jp_1633_;
}
}
else
{
v___y_1634_ = v___x_1624_;
goto v___jp_1633_;
}
}
else
{
v___y_1634_ = v___x_1624_;
goto v___jp_1633_;
}
}
else
{
v___y_1634_ = v___x_1624_;
goto v___jp_1633_;
}
}
else
{
v___y_1634_ = v___x_1624_;
goto v___jp_1633_;
}
}
else
{
v___y_1634_ = v___x_1624_;
goto v___jp_1633_;
}
}
else
{
v___y_1634_ = v___x_1624_;
goto v___jp_1633_;
}
}
else
{
v___y_1634_ = v___x_1624_;
goto v___jp_1633_;
}
}
else
{
v___y_1634_ = v___x_1624_;
goto v___jp_1633_;
}
}
else
{
v___y_1634_ = v___x_1624_;
goto v___jp_1633_;
}
}
else
{
v___y_1634_ = v___x_1624_;
goto v___jp_1633_;
}
}
v___jp_1772_:
{
uint8_t v___x_1773_; uint8_t v___x_1774_; 
v___x_1773_ = 65;
v___x_1774_ = lean_uint8_dec_le(v___x_1773_, v___x_1734_);
if (v___x_1774_ == 0)
{
goto v___jp_1735_;
}
else
{
uint8_t v___x_1775_; uint8_t v___x_1776_; 
v___x_1775_ = 90;
v___x_1776_ = lean_uint8_dec_le(v___x_1734_, v___x_1775_);
if (v___x_1776_ == 0)
{
goto v___jp_1735_;
}
else
{
v___y_1634_ = v___x_1624_;
goto v___jp_1633_;
}
}
}
v___jp_1777_:
{
uint8_t v___x_1778_; uint8_t v___x_1779_; 
v___x_1778_ = 97;
v___x_1779_ = lean_uint8_dec_le(v___x_1778_, v___x_1734_);
if (v___x_1779_ == 0)
{
goto v___jp_1772_;
}
else
{
uint8_t v___x_1780_; uint8_t v___x_1781_; 
v___x_1780_ = 122;
v___x_1781_ = lean_uint8_dec_le(v___x_1734_, v___x_1780_);
if (v___x_1781_ == 0)
{
goto v___jp_1772_;
}
else
{
v___y_1634_ = v___x_1624_;
goto v___jp_1633_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath(lean_object* v_config_1803_, uint8_t v_forceAbsolute_1804_, uint8_t v_allowEmpty_1805_, lean_object* v_a_1806_){
_start:
{
lean_object* v___y_1808_; lean_object* v___y_1812_; lean_object* v_array_1815_; lean_object* v_idx_1816_; uint8_t v_isAbsolute_1817_; lean_object* v___x_1818_; lean_object* v_segments_1819_; uint8_t v_isAbsolute_1821_; lean_object* v_totalLength_1822_; lean_object* v___y_1823_; lean_object* v_pos_1847_; lean_object* v_array_1848_; lean_object* v_idx_1849_; lean_object* v___y_1858_; uint8_t v___y_1862_; lean_object* v_pos_1863_; uint8_t v_res_1864_; uint8_t v___y_1866_; lean_object* v_pos_1867_; uint8_t v_res_1868_; lean_object* v___y_1876_; uint8_t v___y_1877_; uint8_t v___y_1878_; uint8_t v___y_1887_; lean_object* v_pos_1888_; uint8_t v_res_1889_; lean_object* v_pos_1891_; lean_object* v_array_1892_; lean_object* v_idx_1893_; uint8_t v_res_1894_; lean_object* v___x_1898_; uint8_t v___x_1899_; 
v_array_1815_ = lean_ctor_get(v_a_1806_, 0);
lean_inc_ref(v_array_1815_);
v_idx_1816_ = lean_ctor_get(v_a_1806_, 1);
lean_inc(v_idx_1816_);
v_isAbsolute_1817_ = 0;
v___x_1818_ = lean_unsigned_to_nat(0u);
v_segments_1819_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__4));
v___x_1898_ = lean_byte_array_size(v_array_1815_);
v___x_1899_ = lean_nat_dec_lt(v_idx_1816_, v___x_1898_);
if (v___x_1899_ == 0)
{
v_pos_1891_ = v_a_1806_;
v_array_1892_ = v_array_1815_;
v_idx_1893_ = v_idx_1816_;
v_res_1894_ = v_isAbsolute_1817_;
goto v___jp_1890_;
}
else
{
uint8_t v___x_1900_; uint8_t v___x_1950_; uint8_t v___x_1951_; 
v___x_1900_ = lean_byte_array_fget(v_array_1815_, v_idx_1816_);
v___x_1950_ = 48;
v___x_1951_ = lean_uint8_dec_le(v___x_1950_, v___x_1900_);
if (v___x_1951_ == 0)
{
goto v___jp_1945_;
}
else
{
uint8_t v___x_1952_; uint8_t v___x_1953_; 
v___x_1952_ = 57;
v___x_1953_ = lean_uint8_dec_le(v___x_1900_, v___x_1952_);
if (v___x_1953_ == 0)
{
goto v___jp_1945_;
}
else
{
v_pos_1891_ = v_a_1806_;
v_array_1892_ = v_array_1815_;
v_idx_1893_ = v_idx_1816_;
v_res_1894_ = v___x_1953_;
goto v___jp_1890_;
}
}
v___jp_1901_:
{
uint8_t v___x_1902_; uint8_t v___x_1903_; 
v___x_1902_ = 45;
v___x_1903_ = lean_uint8_dec_eq(v___x_1900_, v___x_1902_);
if (v___x_1903_ == 0)
{
uint8_t v___x_1904_; uint8_t v___x_1905_; 
v___x_1904_ = 46;
v___x_1905_ = lean_uint8_dec_eq(v___x_1900_, v___x_1904_);
if (v___x_1905_ == 0)
{
uint8_t v___x_1906_; uint8_t v___x_1907_; 
v___x_1906_ = 95;
v___x_1907_ = lean_uint8_dec_eq(v___x_1900_, v___x_1906_);
if (v___x_1907_ == 0)
{
uint8_t v___x_1908_; uint8_t v___x_1909_; 
v___x_1908_ = 126;
v___x_1909_ = lean_uint8_dec_eq(v___x_1900_, v___x_1908_);
if (v___x_1909_ == 0)
{
uint8_t v___x_1910_; uint8_t v___x_1911_; 
v___x_1910_ = 33;
v___x_1911_ = lean_uint8_dec_eq(v___x_1900_, v___x_1910_);
if (v___x_1911_ == 0)
{
uint8_t v___x_1912_; uint8_t v___x_1913_; 
v___x_1912_ = 36;
v___x_1913_ = lean_uint8_dec_eq(v___x_1900_, v___x_1912_);
if (v___x_1913_ == 0)
{
uint8_t v___x_1914_; uint8_t v___x_1915_; 
v___x_1914_ = 38;
v___x_1915_ = lean_uint8_dec_eq(v___x_1900_, v___x_1914_);
if (v___x_1915_ == 0)
{
uint8_t v___x_1916_; uint8_t v___x_1917_; 
v___x_1916_ = 39;
v___x_1917_ = lean_uint8_dec_eq(v___x_1900_, v___x_1916_);
if (v___x_1917_ == 0)
{
uint8_t v___x_1918_; uint8_t v___x_1919_; 
v___x_1918_ = 40;
v___x_1919_ = lean_uint8_dec_eq(v___x_1900_, v___x_1918_);
if (v___x_1919_ == 0)
{
uint8_t v___x_1920_; uint8_t v___x_1921_; 
v___x_1920_ = 41;
v___x_1921_ = lean_uint8_dec_eq(v___x_1900_, v___x_1920_);
if (v___x_1921_ == 0)
{
uint8_t v___x_1922_; uint8_t v___x_1923_; 
v___x_1922_ = 42;
v___x_1923_ = lean_uint8_dec_eq(v___x_1900_, v___x_1922_);
if (v___x_1923_ == 0)
{
uint8_t v___x_1924_; uint8_t v___x_1925_; 
v___x_1924_ = 43;
v___x_1925_ = lean_uint8_dec_eq(v___x_1900_, v___x_1924_);
if (v___x_1925_ == 0)
{
uint8_t v___x_1926_; uint8_t v___x_1927_; 
v___x_1926_ = 44;
v___x_1927_ = lean_uint8_dec_eq(v___x_1900_, v___x_1926_);
if (v___x_1927_ == 0)
{
uint8_t v___x_1928_; uint8_t v___x_1929_; 
v___x_1928_ = 59;
v___x_1929_ = lean_uint8_dec_eq(v___x_1900_, v___x_1928_);
if (v___x_1929_ == 0)
{
uint8_t v___x_1930_; uint8_t v___x_1931_; 
v___x_1930_ = 61;
v___x_1931_ = lean_uint8_dec_eq(v___x_1900_, v___x_1930_);
if (v___x_1931_ == 0)
{
uint8_t v___x_1932_; uint8_t v___x_1933_; 
v___x_1932_ = 58;
v___x_1933_ = lean_uint8_dec_eq(v___x_1900_, v___x_1932_);
if (v___x_1933_ == 0)
{
uint8_t v___x_1934_; uint8_t v___x_1935_; 
v___x_1934_ = 64;
v___x_1935_ = lean_uint8_dec_eq(v___x_1900_, v___x_1934_);
if (v___x_1935_ == 0)
{
uint8_t v___x_1936_; uint8_t v___x_1937_; 
v___x_1936_ = 37;
v___x_1937_ = lean_uint8_dec_eq(v___x_1900_, v___x_1936_);
if (v___x_1937_ == 0)
{
uint8_t v___x_1938_; uint8_t v___x_1939_; 
v___x_1938_ = 47;
v___x_1939_ = lean_uint8_dec_eq(v___x_1900_, v___x_1938_);
if (v___x_1939_ == 0)
{
v_pos_1891_ = v_a_1806_;
v_array_1892_ = v_array_1815_;
v_idx_1893_ = v_idx_1816_;
v_res_1894_ = v_isAbsolute_1817_;
goto v___jp_1890_;
}
else
{
v_pos_1891_ = v_a_1806_;
v_array_1892_ = v_array_1815_;
v_idx_1893_ = v_idx_1816_;
v_res_1894_ = v___x_1939_;
goto v___jp_1890_;
}
}
else
{
v_pos_1891_ = v_a_1806_;
v_array_1892_ = v_array_1815_;
v_idx_1893_ = v_idx_1816_;
v_res_1894_ = v___x_1937_;
goto v___jp_1890_;
}
}
else
{
v_pos_1891_ = v_a_1806_;
v_array_1892_ = v_array_1815_;
v_idx_1893_ = v_idx_1816_;
v_res_1894_ = v___x_1935_;
goto v___jp_1890_;
}
}
else
{
v_pos_1891_ = v_a_1806_;
v_array_1892_ = v_array_1815_;
v_idx_1893_ = v_idx_1816_;
v_res_1894_ = v___x_1933_;
goto v___jp_1890_;
}
}
else
{
v_pos_1891_ = v_a_1806_;
v_array_1892_ = v_array_1815_;
v_idx_1893_ = v_idx_1816_;
v_res_1894_ = v___x_1931_;
goto v___jp_1890_;
}
}
else
{
v_pos_1891_ = v_a_1806_;
v_array_1892_ = v_array_1815_;
v_idx_1893_ = v_idx_1816_;
v_res_1894_ = v___x_1929_;
goto v___jp_1890_;
}
}
else
{
v_pos_1891_ = v_a_1806_;
v_array_1892_ = v_array_1815_;
v_idx_1893_ = v_idx_1816_;
v_res_1894_ = v___x_1927_;
goto v___jp_1890_;
}
}
else
{
v_pos_1891_ = v_a_1806_;
v_array_1892_ = v_array_1815_;
v_idx_1893_ = v_idx_1816_;
v_res_1894_ = v___x_1925_;
goto v___jp_1890_;
}
}
else
{
v_pos_1891_ = v_a_1806_;
v_array_1892_ = v_array_1815_;
v_idx_1893_ = v_idx_1816_;
v_res_1894_ = v___x_1923_;
goto v___jp_1890_;
}
}
else
{
v_pos_1891_ = v_a_1806_;
v_array_1892_ = v_array_1815_;
v_idx_1893_ = v_idx_1816_;
v_res_1894_ = v___x_1921_;
goto v___jp_1890_;
}
}
else
{
v_pos_1891_ = v_a_1806_;
v_array_1892_ = v_array_1815_;
v_idx_1893_ = v_idx_1816_;
v_res_1894_ = v___x_1919_;
goto v___jp_1890_;
}
}
else
{
v_pos_1891_ = v_a_1806_;
v_array_1892_ = v_array_1815_;
v_idx_1893_ = v_idx_1816_;
v_res_1894_ = v___x_1917_;
goto v___jp_1890_;
}
}
else
{
v_pos_1891_ = v_a_1806_;
v_array_1892_ = v_array_1815_;
v_idx_1893_ = v_idx_1816_;
v_res_1894_ = v___x_1915_;
goto v___jp_1890_;
}
}
else
{
v_pos_1891_ = v_a_1806_;
v_array_1892_ = v_array_1815_;
v_idx_1893_ = v_idx_1816_;
v_res_1894_ = v___x_1913_;
goto v___jp_1890_;
}
}
else
{
v_pos_1891_ = v_a_1806_;
v_array_1892_ = v_array_1815_;
v_idx_1893_ = v_idx_1816_;
v_res_1894_ = v___x_1911_;
goto v___jp_1890_;
}
}
else
{
v_pos_1891_ = v_a_1806_;
v_array_1892_ = v_array_1815_;
v_idx_1893_ = v_idx_1816_;
v_res_1894_ = v___x_1909_;
goto v___jp_1890_;
}
}
else
{
v_pos_1891_ = v_a_1806_;
v_array_1892_ = v_array_1815_;
v_idx_1893_ = v_idx_1816_;
v_res_1894_ = v___x_1907_;
goto v___jp_1890_;
}
}
else
{
v_pos_1891_ = v_a_1806_;
v_array_1892_ = v_array_1815_;
v_idx_1893_ = v_idx_1816_;
v_res_1894_ = v___x_1905_;
goto v___jp_1890_;
}
}
else
{
v_pos_1891_ = v_a_1806_;
v_array_1892_ = v_array_1815_;
v_idx_1893_ = v_idx_1816_;
v_res_1894_ = v___x_1903_;
goto v___jp_1890_;
}
}
v___jp_1940_:
{
uint8_t v___x_1941_; uint8_t v___x_1942_; 
v___x_1941_ = 65;
v___x_1942_ = lean_uint8_dec_le(v___x_1941_, v___x_1900_);
if (v___x_1942_ == 0)
{
goto v___jp_1901_;
}
else
{
uint8_t v___x_1943_; uint8_t v___x_1944_; 
v___x_1943_ = 90;
v___x_1944_ = lean_uint8_dec_le(v___x_1900_, v___x_1943_);
if (v___x_1944_ == 0)
{
goto v___jp_1901_;
}
else
{
v_pos_1891_ = v_a_1806_;
v_array_1892_ = v_array_1815_;
v_idx_1893_ = v_idx_1816_;
v_res_1894_ = v___x_1944_;
goto v___jp_1890_;
}
}
}
v___jp_1945_:
{
uint8_t v___x_1946_; uint8_t v___x_1947_; 
v___x_1946_ = 97;
v___x_1947_ = lean_uint8_dec_le(v___x_1946_, v___x_1900_);
if (v___x_1947_ == 0)
{
goto v___jp_1940_;
}
else
{
uint8_t v___x_1948_; uint8_t v___x_1949_; 
v___x_1948_ = 122;
v___x_1949_ = lean_uint8_dec_le(v___x_1900_, v___x_1948_);
if (v___x_1949_ == 0)
{
goto v___jp_1940_;
}
else
{
v_pos_1891_ = v_a_1806_;
v_array_1892_ = v_array_1815_;
v_idx_1893_ = v_idx_1816_;
v_res_1894_ = v___x_1949_;
goto v___jp_1890_;
}
}
}
}
v___jp_1807_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__1));
v___x_1810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___y_1808_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
return v___x_1810_;
}
v___jp_1811_:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__3));
v___x_1814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___y_1812_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
return v___x_1814_;
}
v___jp_1820_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1824_, 0, v_segments_1819_);
lean_ctor_set(v___x_1824_, 1, v_totalLength_1822_);
v___x_1825_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(v_config_1803_, v___x_1824_, v___y_1823_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_res_1826_; lean_object* v_pos_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1836_; 
v_res_1826_ = lean_ctor_get(v___x_1825_, 1);
v_pos_1827_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1829_ = v___x_1825_;
v_isShared_1830_ = v_isSharedCheck_1836_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_res_1826_);
lean_inc(v_pos_1827_);
lean_dec(v___x_1825_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1836_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v_fst_1831_; lean_object* v___x_1832_; lean_object* v___x_1834_; 
v_fst_1831_ = lean_ctor_get(v_res_1826_, 0);
lean_inc(v_fst_1831_);
lean_dec(v_res_1826_);
v___x_1832_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1832_, 0, v_fst_1831_);
lean_ctor_set_uint8(v___x_1832_, sizeof(void*)*1, v_isAbsolute_1821_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 1, v___x_1832_);
v___x_1834_ = v___x_1829_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_pos_1827_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v___x_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
else
{
lean_object* v_pos_1837_; lean_object* v_err_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
v_pos_1837_ = lean_ctor_get(v___x_1825_, 0);
v_err_1838_ = lean_ctor_get(v___x_1825_, 1);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1825_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_err_1838_);
lean_inc(v_pos_1837_);
lean_dec(v___x_1825_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_pos_1837_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v_err_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
v___jp_1846_:
{
lean_object* v___x_1850_; uint8_t v___x_1851_; 
v___x_1850_ = lean_byte_array_size(v_array_1848_);
v___x_1851_ = lean_nat_dec_lt(v_idx_1849_, v___x_1850_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
lean_dec(v_idx_1849_);
lean_dec_ref(v_array_1848_);
lean_dec_ref(v_config_1803_);
v___x_1852_ = lean_box(0);
v___x_1853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1853_, 0, v_pos_1847_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
return v___x_1853_;
}
else
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
lean_dec_ref(v_pos_1847_);
v___x_1854_ = lean_unsigned_to_nat(1u);
v___x_1855_ = lean_nat_add(v_idx_1849_, v___x_1854_);
lean_dec(v_idx_1849_);
v___x_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1856_, 0, v_array_1848_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
v_isAbsolute_1821_ = v___x_1851_;
v_totalLength_1822_ = v___x_1854_;
v___y_1823_ = v___x_1856_;
goto v___jp_1820_;
}
}
v___jp_1857_:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__5));
v___x_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___y_1858_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
return v___x_1860_;
}
v___jp_1861_:
{
if (v_allowEmpty_1805_ == 0)
{
v___y_1808_ = v_pos_1863_;
goto v___jp_1807_;
}
else
{
if (v_res_1864_ == 0)
{
if (v___y_1862_ == 0)
{
v___y_1858_ = v_pos_1863_;
goto v___jp_1857_;
}
else
{
v___y_1808_ = v_pos_1863_;
goto v___jp_1807_;
}
}
else
{
v___y_1858_ = v_pos_1863_;
goto v___jp_1857_;
}
}
}
v___jp_1865_:
{
if (v_res_1868_ == 0)
{
if (v_forceAbsolute_1804_ == 0)
{
v_isAbsolute_1821_ = v_isAbsolute_1817_;
v_totalLength_1822_ = v___x_1818_;
v___y_1823_ = v_pos_1867_;
goto v___jp_1820_;
}
else
{
lean_object* v_array_1869_; lean_object* v_idx_1870_; lean_object* v___x_1871_; uint8_t v___x_1872_; 
lean_dec_ref(v_config_1803_);
v_array_1869_ = lean_ctor_get(v_pos_1867_, 0);
v_idx_1870_ = lean_ctor_get(v_pos_1867_, 1);
v___x_1871_ = lean_byte_array_size(v_array_1869_);
v___x_1872_ = lean_nat_dec_lt(v_idx_1870_, v___x_1871_);
if (v___x_1872_ == 0)
{
v___y_1862_ = v___y_1866_;
v_pos_1863_ = v_pos_1867_;
v_res_1864_ = v_forceAbsolute_1804_;
goto v___jp_1861_;
}
else
{
v___y_1862_ = v___y_1866_;
v_pos_1863_ = v_pos_1867_;
v_res_1864_ = v_res_1868_;
goto v___jp_1861_;
}
}
}
else
{
lean_object* v_array_1873_; lean_object* v_idx_1874_; 
v_array_1873_ = lean_ctor_get(v_pos_1867_, 0);
lean_inc_ref(v_array_1873_);
v_idx_1874_ = lean_ctor_get(v_pos_1867_, 1);
lean_inc(v_idx_1874_);
v_pos_1847_ = v_pos_1867_;
v_array_1848_ = v_array_1873_;
v_idx_1849_ = v_idx_1874_;
goto v___jp_1846_;
}
}
v___jp_1875_:
{
lean_object* v_array_1879_; lean_object* v_idx_1880_; lean_object* v___x_1881_; uint8_t v___x_1882_; 
v_array_1879_ = lean_ctor_get(v___y_1876_, 0);
v_idx_1880_ = lean_ctor_get(v___y_1876_, 1);
v___x_1881_ = lean_byte_array_size(v_array_1879_);
v___x_1882_ = lean_nat_dec_lt(v_idx_1880_, v___x_1881_);
if (v___x_1882_ == 0)
{
v___y_1866_ = v___y_1877_;
v_pos_1867_ = v___y_1876_;
v_res_1868_ = v___y_1878_;
goto v___jp_1865_;
}
else
{
uint8_t v___x_1883_; uint8_t v___x_1884_; uint8_t v___x_1885_; 
v___x_1883_ = lean_byte_array_fget(v_array_1879_, v_idx_1880_);
v___x_1884_ = 47;
v___x_1885_ = lean_uint8_dec_eq(v___x_1883_, v___x_1884_);
if (v___x_1885_ == 0)
{
v___y_1866_ = v___y_1877_;
v_pos_1867_ = v___y_1876_;
v_res_1868_ = v___y_1878_;
goto v___jp_1865_;
}
else
{
lean_inc(v_idx_1880_);
lean_inc_ref(v_array_1879_);
v_pos_1847_ = v___y_1876_;
v_array_1848_ = v_array_1879_;
v_idx_1849_ = v_idx_1880_;
goto v___jp_1846_;
}
}
}
v___jp_1886_:
{
if (v_allowEmpty_1805_ == 0)
{
if (v_res_1889_ == 0)
{
if (v___y_1887_ == 0)
{
lean_dec_ref(v_config_1803_);
v___y_1812_ = v_pos_1888_;
goto v___jp_1811_;
}
else
{
v___y_1876_ = v_pos_1888_;
v___y_1877_ = v___y_1887_;
v___y_1878_ = v_res_1889_;
goto v___jp_1875_;
}
}
else
{
lean_dec_ref(v_config_1803_);
v___y_1812_ = v_pos_1888_;
goto v___jp_1811_;
}
}
else
{
v___y_1876_ = v_pos_1888_;
v___y_1877_ = v___y_1887_;
v___y_1878_ = v_isAbsolute_1817_;
goto v___jp_1875_;
}
}
v___jp_1890_:
{
lean_object* v___x_1895_; uint8_t v___x_1896_; 
v___x_1895_ = lean_byte_array_size(v_array_1892_);
lean_dec_ref(v_array_1892_);
v___x_1896_ = lean_nat_dec_lt(v_idx_1893_, v___x_1895_);
lean_dec(v_idx_1893_);
if (v___x_1896_ == 0)
{
uint8_t v___x_1897_; 
v___x_1897_ = 1;
v___y_1887_ = v_res_1894_;
v_pos_1888_ = v_pos_1891_;
v_res_1889_ = v___x_1897_;
goto v___jp_1886_;
}
else
{
v___y_1887_ = v_res_1894_;
v_pos_1888_ = v_pos_1891_;
v_res_1889_ = v_isAbsolute_1817_;
goto v___jp_1886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath___boxed(lean_object* v_config_1954_, lean_object* v_forceAbsolute_1955_, lean_object* v_allowEmpty_1956_, lean_object* v_a_1957_){
_start:
{
uint8_t v_forceAbsolute_boxed_1958_; uint8_t v_allowEmpty_boxed_1959_; lean_object* v_res_1960_; 
v_forceAbsolute_boxed_1958_ = lean_unbox(v_forceAbsolute_1955_);
v_allowEmpty_boxed_1959_ = lean_unbox(v_allowEmpty_1956_);
v_res_1960_ = l_Std_Http_URI_Parser_parsePath(v_config_1954_, v_forceAbsolute_boxed_1958_, v_allowEmpty_boxed_1959_, v_a_1957_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0(lean_object* v_config_1961_, lean_object* v_inst_1962_, lean_object* v_a_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(v_config_1961_, v_a_1963_, v___y_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0(lean_object* v_config_1966_, lean_object* v_inst_1967_, lean_object* v_a_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v___x_1970_; 
v___x_1970_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_1966_, v_a_1968_, v___y_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg(){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0));
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg___boxed(lean_object* v___dummy_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg();
return v_res_1974_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg();
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(lean_object* v_s_1976_){
_start:
{
lean_object* v___x_1977_; 
v___x_1977_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___boxed(lean_object* v_s_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(v_s_1978_);
lean_dec_ref(v_s_1978_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg(){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0));
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg___boxed(lean_object* v___dummy_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg();
return v_res_1983_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg();
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(lean_object* v_s_1985_){
_start:
{
lean_object* v___x_1986_; 
v___x_1986_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___boxed(lean_object* v_s_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(v_s_1987_);
lean_dec_ref(v_s_1987_);
return v_res_1988_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(uint8_t v_c_1989_){
_start:
{
uint8_t v___x_2041_; uint8_t v___x_2042_; 
v___x_2041_ = 48;
v___x_2042_ = lean_uint8_dec_le(v___x_2041_, v_c_1989_);
if (v___x_2042_ == 0)
{
goto v___jp_2036_;
}
else
{
uint8_t v___x_2043_; uint8_t v___x_2044_; 
v___x_2043_ = 57;
v___x_2044_ = lean_uint8_dec_le(v_c_1989_, v___x_2043_);
if (v___x_2044_ == 0)
{
goto v___jp_2036_;
}
else
{
return v___x_2044_;
}
}
v___jp_1990_:
{
uint8_t v___x_1991_; uint8_t v___x_1992_; 
v___x_1991_ = 45;
v___x_1992_ = lean_uint8_dec_eq(v_c_1989_, v___x_1991_);
if (v___x_1992_ == 0)
{
uint8_t v___x_1993_; uint8_t v___x_1994_; 
v___x_1993_ = 46;
v___x_1994_ = lean_uint8_dec_eq(v_c_1989_, v___x_1993_);
if (v___x_1994_ == 0)
{
uint8_t v___x_1995_; uint8_t v___x_1996_; 
v___x_1995_ = 95;
v___x_1996_ = lean_uint8_dec_eq(v_c_1989_, v___x_1995_);
if (v___x_1996_ == 0)
{
uint8_t v___x_1997_; uint8_t v___x_1998_; 
v___x_1997_ = 126;
v___x_1998_ = lean_uint8_dec_eq(v_c_1989_, v___x_1997_);
if (v___x_1998_ == 0)
{
uint8_t v___x_1999_; uint8_t v___x_2000_; 
v___x_1999_ = 33;
v___x_2000_ = lean_uint8_dec_eq(v_c_1989_, v___x_1999_);
if (v___x_2000_ == 0)
{
uint8_t v___x_2001_; uint8_t v___x_2002_; 
v___x_2001_ = 36;
v___x_2002_ = lean_uint8_dec_eq(v_c_1989_, v___x_2001_);
if (v___x_2002_ == 0)
{
uint8_t v___x_2003_; uint8_t v___x_2004_; 
v___x_2003_ = 38;
v___x_2004_ = lean_uint8_dec_eq(v_c_1989_, v___x_2003_);
if (v___x_2004_ == 0)
{
uint8_t v___x_2005_; uint8_t v___x_2006_; 
v___x_2005_ = 39;
v___x_2006_ = lean_uint8_dec_eq(v_c_1989_, v___x_2005_);
if (v___x_2006_ == 0)
{
uint8_t v___x_2007_; uint8_t v___x_2008_; 
v___x_2007_ = 40;
v___x_2008_ = lean_uint8_dec_eq(v_c_1989_, v___x_2007_);
if (v___x_2008_ == 0)
{
uint8_t v___x_2009_; uint8_t v___x_2010_; 
v___x_2009_ = 41;
v___x_2010_ = lean_uint8_dec_eq(v_c_1989_, v___x_2009_);
if (v___x_2010_ == 0)
{
uint8_t v___x_2011_; uint8_t v___x_2012_; 
v___x_2011_ = 42;
v___x_2012_ = lean_uint8_dec_eq(v_c_1989_, v___x_2011_);
if (v___x_2012_ == 0)
{
uint8_t v___x_2013_; uint8_t v___x_2014_; 
v___x_2013_ = 43;
v___x_2014_ = lean_uint8_dec_eq(v_c_1989_, v___x_2013_);
if (v___x_2014_ == 0)
{
uint8_t v___x_2015_; uint8_t v___x_2016_; 
v___x_2015_ = 44;
v___x_2016_ = lean_uint8_dec_eq(v_c_1989_, v___x_2015_);
if (v___x_2016_ == 0)
{
uint8_t v___x_2017_; uint8_t v___x_2018_; 
v___x_2017_ = 59;
v___x_2018_ = lean_uint8_dec_eq(v_c_1989_, v___x_2017_);
if (v___x_2018_ == 0)
{
uint8_t v___x_2019_; uint8_t v___x_2020_; 
v___x_2019_ = 61;
v___x_2020_ = lean_uint8_dec_eq(v_c_1989_, v___x_2019_);
if (v___x_2020_ == 0)
{
uint8_t v___x_2021_; uint8_t v___x_2022_; 
v___x_2021_ = 58;
v___x_2022_ = lean_uint8_dec_eq(v_c_1989_, v___x_2021_);
if (v___x_2022_ == 0)
{
uint8_t v___x_2023_; uint8_t v___x_2024_; 
v___x_2023_ = 64;
v___x_2024_ = lean_uint8_dec_eq(v_c_1989_, v___x_2023_);
if (v___x_2024_ == 0)
{
uint8_t v___x_2025_; uint8_t v___x_2026_; 
v___x_2025_ = 47;
v___x_2026_ = lean_uint8_dec_eq(v_c_1989_, v___x_2025_);
if (v___x_2026_ == 0)
{
uint8_t v___x_2027_; uint8_t v___x_2028_; 
v___x_2027_ = 63;
v___x_2028_ = lean_uint8_dec_eq(v_c_1989_, v___x_2027_);
if (v___x_2028_ == 0)
{
uint8_t v___x_2029_; uint8_t v___x_2030_; 
v___x_2029_ = 37;
v___x_2030_ = lean_uint8_dec_eq(v_c_1989_, v___x_2029_);
return v___x_2030_;
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
v___jp_2031_:
{
uint8_t v___x_2032_; uint8_t v___x_2033_; 
v___x_2032_ = 65;
v___x_2033_ = lean_uint8_dec_le(v___x_2032_, v_c_1989_);
if (v___x_2033_ == 0)
{
goto v___jp_1990_;
}
else
{
uint8_t v___x_2034_; uint8_t v___x_2035_; 
v___x_2034_ = 90;
v___x_2035_ = lean_uint8_dec_le(v_c_1989_, v___x_2034_);
if (v___x_2035_ == 0)
{
goto v___jp_1990_;
}
else
{
return v___x_2035_;
}
}
}
v___jp_2036_:
{
uint8_t v___x_2037_; uint8_t v___x_2038_; 
v___x_2037_ = 97;
v___x_2038_ = lean_uint8_dec_le(v___x_2037_, v_c_1989_);
if (v___x_2038_ == 0)
{
goto v___jp_2031_;
}
else
{
uint8_t v___x_2039_; uint8_t v___x_2040_; 
v___x_2039_ = 122;
v___x_2040_ = lean_uint8_dec_le(v_c_1989_, v___x_2039_);
if (v___x_2040_ == 0)
{
goto v___jp_2031_;
}
else
{
return v___x_2040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0___boxed(lean_object* v_c_2045_){
_start:
{
uint8_t v_c_boxed_2046_; uint8_t v_res_2047_; lean_object* v_r_2048_; 
v_c_boxed_2046_ = lean_unbox(v_c_2045_);
v_res_2047_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(v_c_boxed_2046_);
v_r_2048_ = lean_box(v_res_2047_);
return v_r_2048_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(lean_object* v___x_2049_, lean_object* v___x_2050_, lean_object* v_a_2051_, lean_object* v_b_2052_){
_start:
{
lean_object* v_it_2054_; 
if (lean_obj_tag(v_a_2051_) == 0)
{
lean_object* v_currPos_2058_; lean_object* v_searcher_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2085_; 
v_currPos_2058_ = lean_ctor_get(v_a_2051_, 0);
v_searcher_2059_ = lean_ctor_get(v_a_2051_, 1);
v_isSharedCheck_2085_ = !lean_is_exclusive(v_a_2051_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2061_ = v_a_2051_;
v_isShared_2062_ = v_isSharedCheck_2085_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_searcher_2059_);
lean_inc(v_currPos_2058_);
lean_dec(v_a_2051_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2085_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v_str_2063_; lean_object* v_startInclusive_2064_; lean_object* v_endExclusive_2065_; lean_object* v___x_2066_; uint8_t v_decide_2067_; 
v_str_2063_ = lean_ctor_get(v___x_2049_, 0);
v_startInclusive_2064_ = lean_ctor_get(v___x_2049_, 1);
v_endExclusive_2065_ = lean_ctor_get(v___x_2049_, 2);
v___x_2066_ = lean_nat_sub(v_endExclusive_2065_, v_startInclusive_2064_);
v_decide_2067_ = lean_nat_dec_eq(v_searcher_2059_, v___x_2066_);
lean_dec(v___x_2066_);
if (v_decide_2067_ == 0)
{
uint32_t v___x_2068_; lean_object* v___x_2069_; uint32_t v___x_2070_; uint8_t v___x_2071_; 
v___x_2068_ = 38;
v___x_2069_ = lean_nat_add(v_startInclusive_2064_, v_searcher_2059_);
v___x_2070_ = lean_string_utf8_get_fast(v_str_2063_, v___x_2069_);
v___x_2071_ = lean_uint32_dec_eq(v___x_2070_, v___x_2068_);
if (v___x_2071_ == 0)
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2075_; 
lean_dec(v_searcher_2059_);
v___x_2072_ = lean_string_utf8_next_fast(v_str_2063_, v___x_2069_);
lean_dec(v___x_2069_);
v___x_2073_ = lean_nat_sub(v___x_2072_, v_startInclusive_2064_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 1, v___x_2073_);
v___x_2075_ = v___x_2061_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_currPos_2058_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v___x_2073_);
v___x_2075_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
v_a_2051_ = v___x_2075_;
goto _start;
}
}
else
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v_nextIt_2082_; 
lean_dec(v_currPos_2058_);
v___x_2078_ = lean_string_utf8_next_fast(v_str_2063_, v___x_2069_);
v___x_2079_ = lean_nat_sub(v___x_2078_, v___x_2069_);
lean_dec(v___x_2069_);
v___x_2080_ = lean_nat_add(v_searcher_2059_, v___x_2079_);
lean_dec(v___x_2079_);
lean_dec(v_searcher_2059_);
lean_inc(v___x_2080_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 1, v___x_2080_);
lean_ctor_set(v___x_2061_, 0, v___x_2080_);
v_nextIt_2082_ = v___x_2061_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v___x_2080_);
v_nextIt_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
v_it_2054_ = v_nextIt_2082_;
goto v___jp_2053_;
}
}
}
else
{
lean_object* v___x_2084_; 
lean_del_object(v___x_2061_);
lean_dec(v_searcher_2059_);
lean_dec(v_currPos_2058_);
v___x_2084_ = lean_box(1);
v_it_2054_ = v___x_2084_;
goto v___jp_2053_;
}
}
}
else
{
return v_b_2052_;
}
v___jp_2053_:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = lean_unsigned_to_nat(1u);
v___x_2056_ = lean_nat_add(v_b_2052_, v___x_2055_);
lean_dec(v_b_2052_);
v_a_2051_ = v_it_2054_;
v_b_2052_ = v___x_2056_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg___boxed(lean_object* v___x_2086_, lean_object* v___x_2087_, lean_object* v_a_2088_, lean_object* v_b_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2086_, v___x_2087_, v_a_2088_, v_b_2089_);
lean_dec(v___x_2087_);
lean_dec_ref(v___x_2086_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(lean_object* v___x_2091_, lean_object* v___x_2092_, lean_object* v___x_2093_, lean_object* v_a_2094_, lean_object* v_b_2095_){
_start:
{
lean_object* v_it_2097_; 
if (lean_obj_tag(v_a_2094_) == 0)
{
lean_object* v_currPos_2101_; lean_object* v_searcher_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2128_; 
v_currPos_2101_ = lean_ctor_get(v_a_2094_, 0);
v_searcher_2102_ = lean_ctor_get(v_a_2094_, 1);
v_isSharedCheck_2128_ = !lean_is_exclusive(v_a_2094_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2104_ = v_a_2094_;
v_isShared_2105_ = v_isSharedCheck_2128_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_searcher_2102_);
lean_inc(v_currPos_2101_);
lean_dec(v_a_2094_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2128_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v_str_2106_; lean_object* v_startInclusive_2107_; lean_object* v_endExclusive_2108_; lean_object* v___x_2109_; uint8_t v_decide_2110_; 
v_str_2106_ = lean_ctor_get(v___x_2092_, 0);
v_startInclusive_2107_ = lean_ctor_get(v___x_2092_, 1);
v_endExclusive_2108_ = lean_ctor_get(v___x_2092_, 2);
v___x_2109_ = lean_nat_sub(v_endExclusive_2108_, v_startInclusive_2107_);
v_decide_2110_ = lean_nat_dec_eq(v_searcher_2102_, v___x_2109_);
lean_dec(v___x_2109_);
if (v_decide_2110_ == 0)
{
lean_object* v___x_2111_; uint32_t v___x_2112_; uint32_t v___x_2113_; uint8_t v___x_2114_; 
v___x_2111_ = lean_nat_add(v_startInclusive_2107_, v_searcher_2102_);
v___x_2112_ = lean_string_utf8_get_fast(v_str_2106_, v___x_2111_);
v___x_2113_ = 38;
v___x_2114_ = lean_uint32_dec_eq(v___x_2112_, v___x_2113_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2118_; 
lean_dec(v_searcher_2102_);
v___x_2115_ = lean_string_utf8_next_fast(v_str_2106_, v___x_2111_);
lean_dec(v___x_2111_);
v___x_2116_ = lean_nat_sub(v___x_2115_, v_startInclusive_2107_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 1, v___x_2116_);
v___x_2118_ = v___x_2104_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_currPos_2101_);
lean_ctor_set(v_reuseFailAlloc_2120_, 1, v___x_2116_);
v___x_2118_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
lean_object* v___x_2119_; 
v___x_2119_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2092_, v___x_2093_, v___x_2118_, v_b_2095_);
return v___x_2119_;
}
}
else
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v_nextIt_2125_; 
lean_dec(v_currPos_2101_);
v___x_2121_ = lean_string_utf8_next_fast(v_str_2106_, v___x_2111_);
v___x_2122_ = lean_nat_sub(v___x_2121_, v___x_2111_);
lean_dec(v___x_2111_);
v___x_2123_ = lean_nat_add(v_searcher_2102_, v___x_2122_);
lean_dec(v___x_2122_);
lean_dec(v_searcher_2102_);
lean_inc(v___x_2123_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 1, v___x_2123_);
lean_ctor_set(v___x_2104_, 0, v___x_2123_);
v_nextIt_2125_ = v___x_2104_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2123_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v___x_2123_);
v_nextIt_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
v_it_2097_ = v_nextIt_2125_;
goto v___jp_2096_;
}
}
}
else
{
lean_object* v___x_2127_; 
lean_del_object(v___x_2104_);
lean_dec(v_searcher_2102_);
lean_dec(v_currPos_2101_);
v___x_2127_ = lean_box(1);
v_it_2097_ = v___x_2127_;
goto v___jp_2096_;
}
}
}
else
{
return v_b_2095_;
}
v___jp_2096_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2098_ = lean_unsigned_to_nat(1u);
v___x_2099_ = lean_nat_add(v_b_2095_, v___x_2098_);
lean_dec(v_b_2095_);
v___x_2100_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2092_, v___x_2093_, v_it_2097_, v___x_2099_);
return v___x_2100_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg___boxed(lean_object* v___x_2129_, lean_object* v___x_2130_, lean_object* v___x_2131_, lean_object* v_a_2132_, lean_object* v_b_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2129_, v___x_2130_, v___x_2131_, v_a_2132_, v_b_2133_);
lean_dec(v___x_2131_);
lean_dec_ref(v___x_2130_);
lean_dec_ref(v___x_2129_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(lean_object* v_out_2135_, lean_object* v_a_2136_, lean_object* v_b_2137_){
_start:
{
if (lean_obj_tag(v_a_2136_) == 0)
{
lean_object* v_currPos_2138_; lean_object* v_searcher_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2178_; 
v_currPos_2138_ = lean_ctor_get(v_a_2136_, 0);
v_searcher_2139_ = lean_ctor_get(v_a_2136_, 1);
v_isSharedCheck_2178_ = !lean_is_exclusive(v_a_2136_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2141_ = v_a_2136_;
v_isShared_2142_ = v_isSharedCheck_2178_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_searcher_2139_);
lean_inc(v_currPos_2138_);
lean_dec(v_a_2136_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2178_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v_str_2143_; lean_object* v_startInclusive_2144_; lean_object* v_endExclusive_2145_; lean_object* v_it_2147_; lean_object* v_startInclusive_2148_; lean_object* v_endExclusive_2149_; lean_object* v___x_2156_; uint8_t v_decide_2157_; 
v_str_2143_ = lean_ctor_get(v_out_2135_, 0);
v_startInclusive_2144_ = lean_ctor_get(v_out_2135_, 1);
v_endExclusive_2145_ = lean_ctor_get(v_out_2135_, 2);
v___x_2156_ = lean_nat_sub(v_endExclusive_2145_, v_startInclusive_2144_);
v_decide_2157_ = lean_nat_dec_eq(v_searcher_2139_, v___x_2156_);
if (v_decide_2157_ == 0)
{
uint32_t v___x_2158_; lean_object* v___x_2159_; uint32_t v___x_2160_; uint8_t v___x_2161_; 
lean_dec(v___x_2156_);
v___x_2158_ = 61;
v___x_2159_ = lean_nat_add(v_startInclusive_2144_, v_searcher_2139_);
v___x_2160_ = lean_string_utf8_get_fast(v_str_2143_, v___x_2159_);
v___x_2161_ = lean_uint32_dec_eq(v___x_2160_, v___x_2158_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2165_; 
lean_dec(v_searcher_2139_);
v___x_2162_ = lean_string_utf8_next_fast(v_str_2143_, v___x_2159_);
lean_dec(v___x_2159_);
v___x_2163_ = lean_nat_sub(v___x_2162_, v_startInclusive_2144_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 1, v___x_2163_);
v___x_2165_ = v___x_2141_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_currPos_2138_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v___x_2163_);
v___x_2165_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
v_a_2136_ = v___x_2165_;
goto _start;
}
}
else
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v_slice_2171_; lean_object* v_nextIt_2173_; 
v___x_2168_ = lean_string_utf8_next_fast(v_str_2143_, v___x_2159_);
v___x_2169_ = lean_nat_sub(v___x_2168_, v___x_2159_);
lean_dec(v___x_2159_);
v___x_2170_ = lean_nat_add(v_searcher_2139_, v___x_2169_);
lean_dec(v___x_2169_);
v_slice_2171_ = l_String_Slice_subslice_x21(v_out_2135_, v_currPos_2138_, v_searcher_2139_);
lean_inc(v___x_2170_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 1, v___x_2170_);
lean_ctor_set(v___x_2141_, 0, v___x_2170_);
v_nextIt_2173_ = v___x_2141_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2170_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v___x_2170_);
v_nextIt_2173_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v_startInclusive_2174_; lean_object* v_endExclusive_2175_; 
v_startInclusive_2174_ = lean_ctor_get(v_slice_2171_, 0);
lean_inc(v_startInclusive_2174_);
v_endExclusive_2175_ = lean_ctor_get(v_slice_2171_, 1);
lean_inc(v_endExclusive_2175_);
lean_dec_ref(v_slice_2171_);
v_it_2147_ = v_nextIt_2173_;
v_startInclusive_2148_ = v_startInclusive_2174_;
v_endExclusive_2149_ = v_endExclusive_2175_;
goto v___jp_2146_;
}
}
}
else
{
lean_object* v___x_2177_; 
lean_del_object(v___x_2141_);
lean_dec(v_searcher_2139_);
v___x_2177_ = lean_box(1);
v_it_2147_ = v___x_2177_;
v_startInclusive_2148_ = v_currPos_2138_;
v_endExclusive_2149_ = v___x_2156_;
goto v___jp_2146_;
}
v___jp_2146_:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2150_ = lean_nat_add(v_startInclusive_2144_, v_startInclusive_2148_);
lean_dec(v_startInclusive_2148_);
v___x_2151_ = lean_nat_add(v_startInclusive_2144_, v_endExclusive_2149_);
lean_dec(v_endExclusive_2149_);
lean_inc_ref(v_str_2143_);
v___x_2152_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2152_, 0, v_str_2143_);
lean_ctor_set(v___x_2152_, 1, v___x_2150_);
lean_ctor_set(v___x_2152_, 2, v___x_2151_);
v___x_2153_ = l_String_Slice_toString(v___x_2152_);
lean_dec_ref_known(v___x_2152_, 3);
v___x_2154_ = lean_array_push(v_b_2137_, v___x_2153_);
v_a_2136_ = v_it_2147_;
v_b_2137_ = v___x_2154_;
goto _start;
}
}
}
else
{
return v_b_2137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg___boxed(lean_object* v_out_2179_, lean_object* v_a_2180_, lean_object* v_b_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_2179_, v_a_2180_, v_b_2181_);
lean_dec_ref(v_out_2179_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(lean_object* v___x_2186_, lean_object* v___x_2187_, lean_object* v___x_2188_, lean_object* v_a_2189_, lean_object* v_b_2190_){
_start:
{
lean_object* v_it_2192_; lean_object* v_startInclusive_2193_; lean_object* v_endExclusive_2194_; 
if (lean_obj_tag(v_a_2189_) == 0)
{
lean_object* v_currPos_2219_; lean_object* v_searcher_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2249_; 
v_currPos_2219_ = lean_ctor_get(v_a_2189_, 0);
v_searcher_2220_ = lean_ctor_get(v_a_2189_, 1);
v_isSharedCheck_2249_ = !lean_is_exclusive(v_a_2189_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2222_ = v_a_2189_;
v_isShared_2223_ = v_isSharedCheck_2249_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_searcher_2220_);
lean_inc(v_currPos_2219_);
lean_dec(v_a_2189_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2249_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v_str_2224_; lean_object* v_startInclusive_2225_; lean_object* v_endExclusive_2226_; lean_object* v___x_2227_; uint8_t v_decide_2228_; 
v_str_2224_ = lean_ctor_get(v___x_2187_, 0);
v_startInclusive_2225_ = lean_ctor_get(v___x_2187_, 1);
v_endExclusive_2226_ = lean_ctor_get(v___x_2187_, 2);
v___x_2227_ = lean_nat_sub(v_endExclusive_2226_, v_startInclusive_2225_);
v_decide_2228_ = lean_nat_dec_eq(v_searcher_2220_, v___x_2227_);
lean_dec(v___x_2227_);
if (v_decide_2228_ == 0)
{
uint32_t v___x_2229_; lean_object* v___x_2230_; uint32_t v___x_2231_; uint8_t v___x_2232_; 
v___x_2229_ = 38;
v___x_2230_ = lean_nat_add(v_startInclusive_2225_, v_searcher_2220_);
v___x_2231_ = lean_string_utf8_get_fast(v_str_2224_, v___x_2230_);
v___x_2232_ = lean_uint32_dec_eq(v___x_2231_, v___x_2229_);
if (v___x_2232_ == 0)
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2236_; 
lean_dec(v_searcher_2220_);
v___x_2233_ = lean_string_utf8_next_fast(v_str_2224_, v___x_2230_);
lean_dec(v___x_2230_);
v___x_2234_ = lean_nat_sub(v___x_2233_, v_startInclusive_2225_);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 1, v___x_2234_);
v___x_2236_ = v___x_2222_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_currPos_2219_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
v_a_2189_ = v___x_2236_;
goto _start;
}
}
else
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v_slice_2242_; lean_object* v_nextIt_2244_; 
v___x_2239_ = lean_string_utf8_next_fast(v_str_2224_, v___x_2230_);
v___x_2240_ = lean_nat_sub(v___x_2239_, v___x_2230_);
lean_dec(v___x_2230_);
v___x_2241_ = lean_nat_add(v_searcher_2220_, v___x_2240_);
lean_dec(v___x_2240_);
v_slice_2242_ = l_String_Slice_subslice_x21(v___x_2187_, v_currPos_2219_, v_searcher_2220_);
lean_inc(v___x_2241_);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 1, v___x_2241_);
lean_ctor_set(v___x_2222_, 0, v___x_2241_);
v_nextIt_2244_ = v___x_2222_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v___x_2241_);
lean_ctor_set(v_reuseFailAlloc_2247_, 1, v___x_2241_);
v_nextIt_2244_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
lean_object* v_startInclusive_2245_; lean_object* v_endExclusive_2246_; 
v_startInclusive_2245_ = lean_ctor_get(v_slice_2242_, 0);
lean_inc(v_startInclusive_2245_);
v_endExclusive_2246_ = lean_ctor_get(v_slice_2242_, 1);
lean_inc(v_endExclusive_2246_);
lean_dec_ref(v_slice_2242_);
v_it_2192_ = v_nextIt_2244_;
v_startInclusive_2193_ = v_startInclusive_2245_;
v_endExclusive_2194_ = v_endExclusive_2246_;
goto v___jp_2191_;
}
}
}
else
{
lean_object* v___x_2248_; 
lean_del_object(v___x_2222_);
lean_dec(v_searcher_2220_);
v___x_2248_ = lean_box(1);
lean_inc(v___x_2188_);
v_it_2192_ = v___x_2248_;
v_startInclusive_2193_ = v_currPos_2219_;
v_endExclusive_2194_ = v___x_2188_;
goto v___jp_2191_;
}
}
}
else
{
lean_object* v___x_2250_; 
lean_dec(v___x_2188_);
lean_dec_ref(v___x_2186_);
v___x_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2250_, 0, v_b_2190_);
return v___x_2250_;
}
v___jp_2191_:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
lean_inc_ref(v___x_2186_);
v___x_2195_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2186_);
lean_ctor_set(v___x_2195_, 1, v_startInclusive_2193_);
lean_ctor_set(v___x_2195_, 2, v_endExclusive_2194_);
v___x_2196_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
v___x_2197_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0));
v___x_2198_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_2195_, v___x_2196_, v___x_2197_);
lean_dec_ref_known(v___x_2195_, 3);
v___x_2199_ = lean_array_to_list(v___x_2198_);
if (lean_obj_tag(v___x_2199_) == 0)
{
v_a_2189_ = v_it_2192_;
goto _start;
}
else
{
lean_object* v_tail_2201_; 
v_tail_2201_ = lean_ctor_get(v___x_2199_, 1);
if (lean_obj_tag(v_tail_2201_) == 0)
{
lean_object* v_head_2202_; lean_object* v___x_2203_; 
v_head_2202_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_head_2202_);
lean_dec_ref_known(v___x_2199_, 2);
v___x_2203_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2202_);
lean_dec(v_head_2202_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v___x_2204_; 
lean_dec(v_it_2192_);
lean_dec_ref(v_b_2190_);
lean_dec(v___x_2188_);
lean_dec_ref(v___x_2186_);
v___x_2204_ = lean_box(0);
return v___x_2204_;
}
else
{
lean_object* v_val_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v_val_2205_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_val_2205_);
lean_dec_ref_known(v___x_2203_, 1);
v___x_2206_ = lean_box(0);
v___x_2207_ = l_Std_Http_URI_Query_insertEncoded(v_b_2190_, v_val_2205_, v___x_2206_);
v_a_2189_ = v_it_2192_;
v_b_2190_ = v___x_2207_;
goto _start;
}
}
else
{
lean_object* v_head_2209_; lean_object* v___x_2210_; 
lean_inc(v_tail_2201_);
v_head_2209_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_head_2209_);
lean_dec_ref_known(v___x_2199_, 2);
v___x_2210_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2209_);
lean_dec(v_head_2209_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v___x_2211_; 
lean_dec(v_tail_2201_);
lean_dec(v_it_2192_);
lean_dec_ref(v_b_2190_);
lean_dec(v___x_2188_);
lean_dec_ref(v___x_2186_);
v___x_2211_ = lean_box(0);
return v___x_2211_;
}
else
{
lean_object* v_val_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v_val_2212_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_val_2212_);
lean_dec_ref_known(v___x_2210_, 1);
v___x_2213_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1));
v___x_2214_ = l_String_intercalate(v___x_2213_, v_tail_2201_);
v___x_2215_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2214_);
lean_dec_ref(v___x_2214_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v___x_2216_; 
lean_dec(v_val_2212_);
lean_dec(v_it_2192_);
lean_dec_ref(v_b_2190_);
lean_dec(v___x_2188_);
lean_dec_ref(v___x_2186_);
v___x_2216_ = lean_box(0);
return v___x_2216_;
}
else
{
lean_object* v___x_2217_; 
v___x_2217_ = l_Std_Http_URI_Query_insertEncoded(v_b_2190_, v_val_2212_, v___x_2215_);
v_a_2189_ = v_it_2192_;
v_b_2190_ = v___x_2217_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___boxed(lean_object* v___x_2251_, lean_object* v___x_2252_, lean_object* v___x_2253_, lean_object* v_a_2254_, lean_object* v_b_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2251_, v___x_2252_, v___x_2253_, v_a_2254_, v_b_2255_);
lean_dec_ref(v___x_2252_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(lean_object* v___x_2257_, lean_object* v___x_2258_, lean_object* v___x_2259_, lean_object* v_a_2260_, lean_object* v_b_2261_){
_start:
{
lean_object* v_it_2263_; lean_object* v_startInclusive_2264_; lean_object* v_endExclusive_2265_; 
if (lean_obj_tag(v_a_2260_) == 0)
{
lean_object* v_currPos_2290_; lean_object* v_searcher_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2320_; 
v_currPos_2290_ = lean_ctor_get(v_a_2260_, 0);
v_searcher_2291_ = lean_ctor_get(v_a_2260_, 1);
v_isSharedCheck_2320_ = !lean_is_exclusive(v_a_2260_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2293_ = v_a_2260_;
v_isShared_2294_ = v_isSharedCheck_2320_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_searcher_2291_);
lean_inc(v_currPos_2290_);
lean_dec(v_a_2260_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2320_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v_str_2295_; lean_object* v_startInclusive_2296_; lean_object* v_endExclusive_2297_; lean_object* v___x_2298_; uint8_t v_decide_2299_; 
v_str_2295_ = lean_ctor_get(v___x_2258_, 0);
v_startInclusive_2296_ = lean_ctor_get(v___x_2258_, 1);
v_endExclusive_2297_ = lean_ctor_get(v___x_2258_, 2);
v___x_2298_ = lean_nat_sub(v_endExclusive_2297_, v_startInclusive_2296_);
v_decide_2299_ = lean_nat_dec_eq(v_searcher_2291_, v___x_2298_);
lean_dec(v___x_2298_);
if (v_decide_2299_ == 0)
{
lean_object* v___x_2300_; uint32_t v___x_2301_; uint32_t v___x_2302_; uint8_t v___x_2303_; 
v___x_2300_ = lean_nat_add(v_startInclusive_2296_, v_searcher_2291_);
v___x_2301_ = lean_string_utf8_get_fast(v_str_2295_, v___x_2300_);
v___x_2302_ = 38;
v___x_2303_ = lean_uint32_dec_eq(v___x_2301_, v___x_2302_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2307_; 
lean_dec(v_searcher_2291_);
v___x_2304_ = lean_string_utf8_next_fast(v_str_2295_, v___x_2300_);
lean_dec(v___x_2300_);
v___x_2305_ = lean_nat_sub(v___x_2304_, v_startInclusive_2296_);
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 1, v___x_2305_);
v___x_2307_ = v___x_2293_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_currPos_2290_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v___x_2305_);
v___x_2307_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2257_, v___x_2258_, v___x_2259_, v___x_2307_, v_b_2261_);
return v___x_2308_;
}
}
else
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v_slice_2313_; lean_object* v_nextIt_2315_; 
v___x_2310_ = lean_string_utf8_next_fast(v_str_2295_, v___x_2300_);
v___x_2311_ = lean_nat_sub(v___x_2310_, v___x_2300_);
lean_dec(v___x_2300_);
v___x_2312_ = lean_nat_add(v_searcher_2291_, v___x_2311_);
lean_dec(v___x_2311_);
v_slice_2313_ = l_String_Slice_subslice_x21(v___x_2258_, v_currPos_2290_, v_searcher_2291_);
lean_inc(v___x_2312_);
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 1, v___x_2312_);
lean_ctor_set(v___x_2293_, 0, v___x_2312_);
v_nextIt_2315_ = v___x_2293_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2312_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v___x_2312_);
v_nextIt_2315_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
lean_object* v_startInclusive_2316_; lean_object* v_endExclusive_2317_; 
v_startInclusive_2316_ = lean_ctor_get(v_slice_2313_, 0);
lean_inc(v_startInclusive_2316_);
v_endExclusive_2317_ = lean_ctor_get(v_slice_2313_, 1);
lean_inc(v_endExclusive_2317_);
lean_dec_ref(v_slice_2313_);
v_it_2263_ = v_nextIt_2315_;
v_startInclusive_2264_ = v_startInclusive_2316_;
v_endExclusive_2265_ = v_endExclusive_2317_;
goto v___jp_2262_;
}
}
}
else
{
lean_object* v___x_2319_; 
lean_del_object(v___x_2293_);
lean_dec(v_searcher_2291_);
v___x_2319_ = lean_box(1);
lean_inc(v___x_2259_);
v_it_2263_ = v___x_2319_;
v_startInclusive_2264_ = v_currPos_2290_;
v_endExclusive_2265_ = v___x_2259_;
goto v___jp_2262_;
}
}
}
else
{
lean_object* v___x_2321_; 
lean_dec(v___x_2259_);
lean_dec_ref(v___x_2257_);
v___x_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2321_, 0, v_b_2261_);
return v___x_2321_;
}
v___jp_2262_:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
lean_inc_ref(v___x_2257_);
v___x_2266_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2257_);
lean_ctor_set(v___x_2266_, 1, v_startInclusive_2264_);
lean_ctor_set(v___x_2266_, 2, v_endExclusive_2265_);
v___x_2267_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
v___x_2268_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0));
v___x_2269_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_2266_, v___x_2267_, v___x_2268_);
lean_dec_ref_known(v___x_2266_, 3);
v___x_2270_ = lean_array_to_list(v___x_2269_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v___x_2271_; 
v___x_2271_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2257_, v___x_2258_, v___x_2259_, v_it_2263_, v_b_2261_);
return v___x_2271_;
}
else
{
lean_object* v_tail_2272_; 
v_tail_2272_ = lean_ctor_get(v___x_2270_, 1);
if (lean_obj_tag(v_tail_2272_) == 0)
{
lean_object* v_head_2273_; lean_object* v___x_2274_; 
v_head_2273_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_head_2273_);
lean_dec_ref_known(v___x_2270_, 2);
v___x_2274_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2273_);
lean_dec(v_head_2273_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v___x_2275_; 
lean_dec(v_it_2263_);
lean_dec_ref(v_b_2261_);
lean_dec(v___x_2259_);
lean_dec_ref(v___x_2257_);
v___x_2275_ = lean_box(0);
return v___x_2275_;
}
else
{
lean_object* v_val_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v_val_2276_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_val_2276_);
lean_dec_ref_known(v___x_2274_, 1);
v___x_2277_ = lean_box(0);
v___x_2278_ = l_Std_Http_URI_Query_insertEncoded(v_b_2261_, v_val_2276_, v___x_2277_);
v___x_2279_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2257_, v___x_2258_, v___x_2259_, v_it_2263_, v___x_2278_);
return v___x_2279_;
}
}
else
{
lean_object* v_head_2280_; lean_object* v___x_2281_; 
lean_inc(v_tail_2272_);
v_head_2280_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_head_2280_);
lean_dec_ref_known(v___x_2270_, 2);
v___x_2281_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2280_);
lean_dec(v_head_2280_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v___x_2282_; 
lean_dec(v_tail_2272_);
lean_dec(v_it_2263_);
lean_dec_ref(v_b_2261_);
lean_dec(v___x_2259_);
lean_dec_ref(v___x_2257_);
v___x_2282_ = lean_box(0);
return v___x_2282_;
}
else
{
lean_object* v_val_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v_val_2283_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_val_2283_);
lean_dec_ref_known(v___x_2281_, 1);
v___x_2284_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1));
v___x_2285_ = l_String_intercalate(v___x_2284_, v_tail_2272_);
v___x_2286_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2285_);
lean_dec_ref(v___x_2285_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v___x_2287_; 
lean_dec(v_val_2283_);
lean_dec(v_it_2263_);
lean_dec_ref(v_b_2261_);
lean_dec(v___x_2259_);
lean_dec_ref(v___x_2257_);
v___x_2287_ = lean_box(0);
return v___x_2287_;
}
else
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = l_Std_Http_URI_Query_insertEncoded(v_b_2261_, v_val_2283_, v___x_2286_);
v___x_2289_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2257_, v___x_2258_, v___x_2259_, v_it_2263_, v___x_2288_);
return v___x_2289_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg___boxed(lean_object* v___x_2322_, lean_object* v___x_2323_, lean_object* v___x_2324_, lean_object* v_a_2325_, lean_object* v_b_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2322_, v___x_2323_, v___x_2324_, v_a_2325_, v_b_2326_);
lean_dec_ref(v___x_2323_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(lean_object* v_config_2333_, lean_object* v_a_2334_){
_start:
{
lean_object* v_maxQueryLength_2335_; lean_object* v_maxQueryParams_2336_; lean_object* v___f_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v_snd_2340_; lean_object* v_fst_2341_; lean_object* v_fst_2342_; lean_object* v_array_2343_; lean_object* v_idx_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2394_; 
v_maxQueryLength_2335_ = lean_ctor_get(v_config_2333_, 4);
lean_inc(v_maxQueryLength_2335_);
v_maxQueryParams_2336_ = lean_ctor_get(v_config_2333_, 8);
lean_inc(v_maxQueryParams_2336_);
lean_dec_ref(v_config_2333_);
v___f_2337_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2338_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2334_);
v___x_2339_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2337_, v_maxQueryLength_2335_, v___x_2338_, v_a_2334_);
lean_dec(v_maxQueryLength_2335_);
v_snd_2340_ = lean_ctor_get(v___x_2339_, 1);
lean_inc(v_snd_2340_);
v_fst_2341_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_fst_2341_);
lean_dec_ref(v___x_2339_);
v_fst_2342_ = lean_ctor_get(v_snd_2340_, 0);
lean_inc(v_fst_2342_);
lean_dec(v_snd_2340_);
v_array_2343_ = lean_ctor_get(v_a_2334_, 0);
v_idx_2344_ = lean_ctor_get(v_a_2334_, 1);
v_isSharedCheck_2394_ = !lean_is_exclusive(v_a_2334_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2346_ = v_a_2334_;
v_isShared_2347_ = v_isSharedCheck_2394_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_idx_2344_);
lean_inc(v_array_2343_);
lean_dec(v_a_2334_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2394_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v_lower_2349_; lean_object* v_upper_2350_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___y_2391_; uint8_t v___x_2393_; 
v___x_2388_ = lean_nat_add(v_idx_2344_, v_fst_2341_);
lean_dec(v_fst_2341_);
v___x_2389_ = lean_byte_array_size(v_array_2343_);
v___x_2393_ = lean_nat_dec_le(v_idx_2344_, v___x_2338_);
if (v___x_2393_ == 0)
{
v___y_2391_ = v_idx_2344_;
goto v___jp_2390_;
}
else
{
lean_dec(v_idx_2344_);
v___y_2391_ = v___x_2338_;
goto v___jp_2390_;
}
v___jp_2348_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; uint8_t v___x_2353_; 
v___x_2351_ = l_ByteArray_toByteSlice(v_array_2343_, v_lower_2349_, v_upper_2350_);
v___x_2352_ = l_ByteSlice_toByteArray(v___x_2351_);
v___x_2353_ = lean_string_validate_utf8(v___x_2352_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2354_; lean_object* v___x_2356_; 
lean_dec_ref(v___x_2352_);
lean_dec(v_maxQueryParams_2336_);
v___x_2354_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2347_ == 0)
{
lean_ctor_set_tag(v___x_2346_, 1);
lean_ctor_set(v___x_2346_, 1, v___x_2354_);
lean_ctor_set(v___x_2346_, 0, v_fst_2342_);
v___x_2356_ = v___x_2346_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_fst_2342_);
lean_ctor_set(v_reuseFailAlloc_2357_, 1, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
else
{
lean_object* v___x_2358_; lean_object* v___x_2359_; uint8_t v___x_2360_; 
v___x_2358_ = lean_string_from_utf8_unchecked(v___x_2352_);
v___x_2359_ = lean_string_utf8_byte_size(v___x_2358_);
v___x_2360_ = lean_nat_dec_eq(v___x_2359_, v___x_2338_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; uint8_t v___x_2364_; 
lean_inc_ref(v___x_2358_);
v___x_2361_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2358_);
lean_ctor_set(v___x_2361_, 1, v___x_2338_);
lean_ctor_set(v___x_2361_, 2, v___x_2359_);
v___x_2362_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0);
v___x_2363_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2358_, v___x_2361_, v___x_2359_, v___x_2362_, v___x_2338_);
v___x_2364_ = lean_nat_dec_lt(v_maxQueryParams_2336_, v___x_2363_);
lean_dec(v___x_2363_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
lean_dec(v_maxQueryParams_2336_);
v___x_2365_ = l_Std_Http_URI_Query_empty;
v___x_2366_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2358_, v___x_2361_, v___x_2359_, v___x_2362_, v___x_2365_);
lean_dec_ref_known(v___x_2361_, 3);
if (lean_obj_tag(v___x_2366_) == 1)
{
lean_object* v_val_2367_; lean_object* v___x_2369_; 
v_val_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_val_2367_);
lean_dec_ref_known(v___x_2366_, 1);
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 1, v_val_2367_);
lean_ctor_set(v___x_2346_, 0, v_fst_2342_);
v___x_2369_ = v___x_2346_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_fst_2342_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v_val_2367_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
else
{
lean_object* v___x_2371_; lean_object* v___x_2373_; 
lean_dec(v___x_2366_);
v___x_2371_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2347_ == 0)
{
lean_ctor_set_tag(v___x_2346_, 1);
lean_ctor_set(v___x_2346_, 1, v___x_2371_);
lean_ctor_set(v___x_2346_, 0, v_fst_2342_);
v___x_2373_ = v___x_2346_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_fst_2342_);
lean_ctor_set(v_reuseFailAlloc_2374_, 1, v___x_2371_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
else
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2382_; 
lean_dec_ref_known(v___x_2361_, 3);
lean_dec_ref(v___x_2358_);
v___x_2375_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3));
v___x_2376_ = l_Nat_reprFast(v_maxQueryParams_2336_);
v___x_2377_ = lean_string_append(v___x_2375_, v___x_2376_);
lean_dec_ref(v___x_2376_);
v___x_2378_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_2379_ = lean_string_append(v___x_2377_, v___x_2378_);
v___x_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
if (v_isShared_2347_ == 0)
{
lean_ctor_set_tag(v___x_2346_, 1);
lean_ctor_set(v___x_2346_, 1, v___x_2380_);
lean_ctor_set(v___x_2346_, 0, v_fst_2342_);
v___x_2382_ = v___x_2346_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_fst_2342_);
lean_ctor_set(v_reuseFailAlloc_2383_, 1, v___x_2380_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
else
{
lean_object* v___x_2384_; lean_object* v___x_2386_; 
lean_dec_ref(v___x_2358_);
lean_dec(v_maxQueryParams_2336_);
v___x_2384_ = l_Std_Http_URI_Query_empty;
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 1, v___x_2384_);
lean_ctor_set(v___x_2346_, 0, v_fst_2342_);
v___x_2386_ = v___x_2346_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_fst_2342_);
lean_ctor_set(v_reuseFailAlloc_2387_, 1, v___x_2384_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
v___jp_2390_:
{
uint8_t v___x_2392_; 
v___x_2392_ = lean_nat_dec_le(v___x_2388_, v___x_2389_);
if (v___x_2392_ == 0)
{
lean_dec(v___x_2388_);
v_lower_2349_ = v___y_2391_;
v_upper_2350_ = v___x_2389_;
goto v___jp_2348_;
}
else
{
v_lower_2349_ = v___y_2391_;
v_upper_2350_ = v___x_2388_;
goto v___jp_2348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(lean_object* v___x_2395_, lean_object* v___x_2396_, lean_object* v___x_2397_, lean_object* v_inst_2398_, lean_object* v_R_2399_, lean_object* v_a_2400_, lean_object* v_b_2401_, lean_object* v_c_2402_){
_start:
{
lean_object* v___x_2403_; 
v___x_2403_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2395_, v___x_2396_, v___x_2397_, v_a_2400_, v_b_2401_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___boxed(lean_object* v___x_2404_, lean_object* v___x_2405_, lean_object* v___x_2406_, lean_object* v_inst_2407_, lean_object* v_R_2408_, lean_object* v_a_2409_, lean_object* v_b_2410_, lean_object* v_c_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(v___x_2404_, v___x_2405_, v___x_2406_, v_inst_2407_, v_R_2408_, v_a_2409_, v_b_2410_, v_c_2411_);
lean_dec(v___x_2406_);
lean_dec_ref(v___x_2405_);
lean_dec_ref(v___x_2404_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(lean_object* v_out_2413_, lean_object* v_inst_2414_, lean_object* v_R_2415_, lean_object* v_a_2416_, lean_object* v_b_2417_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_2413_, v_a_2416_, v_b_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___boxed(lean_object* v_out_2419_, lean_object* v_inst_2420_, lean_object* v_R_2421_, lean_object* v_a_2422_, lean_object* v_b_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(v_out_2419_, v_inst_2420_, v_R_2421_, v_a_2422_, v_b_2423_);
lean_dec_ref(v_out_2419_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(lean_object* v___x_2425_, lean_object* v___x_2426_, lean_object* v___x_2427_, lean_object* v_inst_2428_, lean_object* v_R_2429_, lean_object* v_a_2430_, lean_object* v_b_2431_, lean_object* v_c_2432_){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2425_, v___x_2426_, v___x_2427_, v_a_2430_, v_b_2431_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___boxed(lean_object* v___x_2434_, lean_object* v___x_2435_, lean_object* v___x_2436_, lean_object* v_inst_2437_, lean_object* v_R_2438_, lean_object* v_a_2439_, lean_object* v_b_2440_, lean_object* v_c_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(v___x_2434_, v___x_2435_, v___x_2436_, v_inst_2437_, v_R_2438_, v_a_2439_, v_b_2440_, v_c_2441_);
lean_dec_ref(v___x_2435_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(lean_object* v___x_2443_, lean_object* v___x_2444_, lean_object* v___x_2445_, lean_object* v_inst_2446_, lean_object* v_R_2447_, lean_object* v_a_2448_, lean_object* v_b_2449_, lean_object* v_c_2450_){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2444_, v___x_2445_, v_a_2448_, v_b_2449_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___boxed(lean_object* v___x_2452_, lean_object* v___x_2453_, lean_object* v___x_2454_, lean_object* v_inst_2455_, lean_object* v_R_2456_, lean_object* v_a_2457_, lean_object* v_b_2458_, lean_object* v_c_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(v___x_2452_, v___x_2453_, v___x_2454_, v_inst_2455_, v_R_2456_, v_a_2457_, v_b_2458_, v_c_2459_);
lean_dec(v___x_2454_);
lean_dec_ref(v___x_2453_);
lean_dec_ref(v___x_2452_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(lean_object* v___x_2461_, lean_object* v___x_2462_, lean_object* v___x_2463_, lean_object* v_inst_2464_, lean_object* v_R_2465_, lean_object* v_a_2466_, lean_object* v_b_2467_, lean_object* v_c_2468_){
_start:
{
lean_object* v___x_2469_; 
v___x_2469_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2461_, v___x_2462_, v___x_2463_, v_a_2466_, v_b_2467_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___boxed(lean_object* v___x_2470_, lean_object* v___x_2471_, lean_object* v___x_2472_, lean_object* v_inst_2473_, lean_object* v_R_2474_, lean_object* v_a_2475_, lean_object* v_b_2476_, lean_object* v_c_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(v___x_2470_, v___x_2471_, v___x_2472_, v_inst_2473_, v_R_2474_, v_a_2475_, v_b_2476_, v_c_2477_);
lean_dec_ref(v___x_2471_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(lean_object* v_config_2482_, lean_object* v_a_2483_){
_start:
{
lean_object* v_maxFragmentLength_2484_; lean_object* v___f_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v_snd_2488_; lean_object* v_fst_2489_; lean_object* v_fst_2490_; lean_object* v_array_2491_; lean_object* v_idx_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2516_; 
v_maxFragmentLength_2484_ = lean_ctor_get(v_config_2482_, 5);
v___f_2485_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2486_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2483_);
v___x_2487_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2485_, v_maxFragmentLength_2484_, v___x_2486_, v_a_2483_);
v_snd_2488_ = lean_ctor_get(v___x_2487_, 1);
lean_inc(v_snd_2488_);
v_fst_2489_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_fst_2489_);
lean_dec_ref(v___x_2487_);
v_fst_2490_ = lean_ctor_get(v_snd_2488_, 0);
lean_inc(v_fst_2490_);
lean_dec(v_snd_2488_);
v_array_2491_ = lean_ctor_get(v_a_2483_, 0);
v_idx_2492_ = lean_ctor_get(v_a_2483_, 1);
v_isSharedCheck_2516_ = !lean_is_exclusive(v_a_2483_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2494_ = v_a_2483_;
v_isShared_2495_ = v_isSharedCheck_2516_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_idx_2492_);
lean_inc(v_array_2491_);
lean_dec(v_a_2483_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2516_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v_lower_2497_; lean_object* v_upper_2498_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___y_2513_; uint8_t v___x_2515_; 
v___x_2510_ = lean_nat_add(v_idx_2492_, v_fst_2489_);
lean_dec(v_fst_2489_);
v___x_2511_ = lean_byte_array_size(v_array_2491_);
v___x_2515_ = lean_nat_dec_le(v_idx_2492_, v___x_2486_);
if (v___x_2515_ == 0)
{
v___y_2513_ = v_idx_2492_;
goto v___jp_2512_;
}
else
{
lean_dec(v_idx_2492_);
v___y_2513_ = v___x_2486_;
goto v___jp_2512_;
}
v___jp_2496_:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2499_ = l_ByteArray_toByteSlice(v_array_2491_, v_lower_2497_, v_upper_2498_);
v___x_2500_ = l_ByteSlice_toByteArray(v___x_2499_);
v___x_2501_ = l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(v___x_2500_);
if (lean_obj_tag(v___x_2501_) == 1)
{
lean_object* v_val_2502_; lean_object* v___x_2504_; 
v_val_2502_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_val_2502_);
lean_dec_ref_known(v___x_2501_, 1);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 1, v_val_2502_);
lean_ctor_set(v___x_2494_, 0, v_fst_2490_);
v___x_2504_ = v___x_2494_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_fst_2490_);
lean_ctor_set(v_reuseFailAlloc_2505_, 1, v_val_2502_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
else
{
lean_object* v___x_2506_; lean_object* v___x_2508_; 
lean_dec(v___x_2501_);
v___x_2506_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1));
if (v_isShared_2495_ == 0)
{
lean_ctor_set_tag(v___x_2494_, 1);
lean_ctor_set(v___x_2494_, 1, v___x_2506_);
lean_ctor_set(v___x_2494_, 0, v_fst_2490_);
v___x_2508_ = v___x_2494_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_fst_2490_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v___x_2506_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
v___jp_2512_:
{
uint8_t v___x_2514_; 
v___x_2514_ = lean_nat_dec_le(v___x_2510_, v___x_2511_);
if (v___x_2514_ == 0)
{
lean_dec(v___x_2510_);
v_lower_2497_ = v___y_2513_;
v_upper_2498_ = v___x_2511_;
goto v___jp_2496_;
}
else
{
v_lower_2497_ = v___y_2513_;
v_upper_2498_ = v___x_2510_;
goto v___jp_2496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___boxed(lean_object* v_config_2517_, lean_object* v_a_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2517_, v_a_2518_);
lean_dec_ref(v_config_2517_);
return v_res_2519_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1(void){
_start:
{
lean_object* v___x_2521_; lean_object* v_utf8_2522_; 
v___x_2521_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0));
v_utf8_2522_ = lean_string_to_utf8(v___x_2521_);
return v_utf8_2522_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(lean_object* v_config_2523_, lean_object* v_a_2524_){
_start:
{
uint8_t v___y_2526_; lean_object* v_pos_2527_; lean_object* v_res_2528_; uint8_t v___y_2550_; lean_object* v___y_2551_; lean_object* v_err_2552_; lean_object* v_pos_2558_; lean_object* v_utf8_2566_; lean_object* v___x_2567_; 
v_utf8_2566_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1);
lean_inc_ref(v_a_2524_);
v___x_2567_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_2566_, v_a_2524_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_pos_2568_; 
lean_dec_ref(v_a_2524_);
v_pos_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc(v_pos_2568_);
lean_dec_ref_known(v___x_2567_, 2);
v_pos_2558_ = v_pos_2568_;
goto v___jp_2557_;
}
else
{
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_pos_2569_; 
lean_dec_ref(v_a_2524_);
v_pos_2569_ = lean_ctor_get(v___x_2567_, 0);
lean_inc(v_pos_2569_);
lean_dec_ref_known(v___x_2567_, 2);
v_pos_2558_ = v_pos_2569_;
goto v___jp_2557_;
}
else
{
lean_object* v_err_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2601_; 
v_err_2570_ = lean_ctor_get(v___x_2567_, 1);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2601_ == 0)
{
lean_object* v_unused_2602_; 
v_unused_2602_ = lean_ctor_get(v___x_2567_, 0);
lean_dec(v_unused_2602_);
v___x_2572_ = v___x_2567_;
v_isShared_2573_ = v_isSharedCheck_2601_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_err_2570_);
lean_dec(v___x_2567_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2601_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v_idx_2574_; uint8_t v___x_2575_; 
v_idx_2574_ = lean_ctor_get(v_a_2524_, 1);
v___x_2575_ = lean_nat_dec_eq(v_idx_2574_, v_idx_2574_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2577_; 
lean_dec_ref(v_config_2523_);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 0, v_a_2524_);
v___x_2577_ = v___x_2572_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2524_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v_err_2570_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
else
{
uint8_t v___x_2579_; lean_object* v___x_2580_; 
lean_del_object(v___x_2572_);
lean_dec(v_err_2570_);
v___x_2579_ = 0;
v___x_2580_ = l_Std_Http_URI_Parser_parsePath(v_config_2523_, v___x_2579_, v___x_2575_, v_a_2524_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_pos_2581_; lean_object* v_res_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2591_; 
v_pos_2581_ = lean_ctor_get(v___x_2580_, 0);
v_res_2582_ = lean_ctor_get(v___x_2580_, 1);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2584_ = v___x_2580_;
v_isShared_2585_ = v_isSharedCheck_2591_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_res_2582_);
lean_inc(v_pos_2581_);
lean_dec(v___x_2580_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2591_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2589_; 
v___x_2586_ = lean_box(0);
v___x_2587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2586_);
lean_ctor_set(v___x_2587_, 1, v_res_2582_);
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 1, v___x_2587_);
v___x_2589_ = v___x_2584_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_pos_2581_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v___x_2587_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
else
{
lean_object* v_pos_2592_; lean_object* v_err_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
v_pos_2592_ = lean_ctor_get(v___x_2580_, 0);
v_err_2593_ = lean_ctor_get(v___x_2580_, 1);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2595_ = v___x_2580_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_err_2593_);
lean_inc(v_pos_2592_);
lean_dec(v___x_2580_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2596_ == 0)
{
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_pos_2592_);
lean_ctor_set(v_reuseFailAlloc_2599_, 1, v_err_2593_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
}
}
}
v___jp_2525_:
{
lean_object* v___x_2529_; 
v___x_2529_ = l_Std_Http_URI_Parser_parsePath(v_config_2523_, v___y_2526_, v___y_2526_, v_pos_2527_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_pos_2530_; lean_object* v_res_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2539_; 
v_pos_2530_ = lean_ctor_get(v___x_2529_, 0);
v_res_2531_ = lean_ctor_get(v___x_2529_, 1);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2533_ = v___x_2529_;
v_isShared_2534_ = v_isSharedCheck_2539_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_res_2531_);
lean_inc(v_pos_2530_);
lean_dec(v___x_2529_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2539_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2535_; lean_object* v___x_2537_; 
v___x_2535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2535_, 0, v_res_2528_);
lean_ctor_set(v___x_2535_, 1, v_res_2531_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 1, v___x_2535_);
v___x_2537_ = v___x_2533_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_pos_2530_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v___x_2535_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
else
{
lean_object* v_pos_2540_; lean_object* v_err_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_dec(v_res_2528_);
v_pos_2540_ = lean_ctor_get(v___x_2529_, 0);
v_err_2541_ = lean_ctor_get(v___x_2529_, 1);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2529_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_err_2541_);
lean_inc(v_pos_2540_);
lean_dec(v___x_2529_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_pos_2540_);
lean_ctor_set(v_reuseFailAlloc_2547_, 1, v_err_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
v___jp_2549_:
{
lean_object* v_idx_2553_; uint8_t v___x_2554_; 
v_idx_2553_ = lean_ctor_get(v___y_2551_, 1);
v___x_2554_ = lean_nat_dec_eq(v_idx_2553_, v_idx_2553_);
if (v___x_2554_ == 0)
{
lean_object* v___x_2555_; 
lean_dec_ref(v_config_2523_);
v___x_2555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___y_2551_);
lean_ctor_set(v___x_2555_, 1, v_err_2552_);
return v___x_2555_;
}
else
{
lean_object* v___x_2556_; 
lean_dec(v_err_2552_);
v___x_2556_ = lean_box(0);
v___y_2526_ = v___y_2550_;
v_pos_2527_ = v___y_2551_;
v_res_2528_ = v___x_2556_;
goto v___jp_2525_;
}
}
v___jp_2557_:
{
uint8_t v___x_2559_; lean_object* v___x_2560_; 
v___x_2559_ = 1;
lean_inc_ref(v_pos_2558_);
v___x_2560_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_2523_, v_pos_2558_);
if (lean_obj_tag(v___x_2560_) == 0)
{
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v_pos_2561_; lean_object* v_res_2562_; lean_object* v___x_2563_; 
lean_dec_ref(v_pos_2558_);
v_pos_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc(v_pos_2561_);
v_res_2562_ = lean_ctor_get(v___x_2560_, 1);
lean_inc(v_res_2562_);
lean_dec_ref_known(v___x_2560_, 2);
v___x_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2563_, 0, v_res_2562_);
v___y_2526_ = v___x_2559_;
v_pos_2527_ = v_pos_2561_;
v_res_2528_ = v___x_2563_;
goto v___jp_2525_;
}
else
{
lean_object* v_err_2564_; 
v_err_2564_ = lean_ctor_get(v___x_2560_, 1);
lean_inc(v_err_2564_);
lean_dec_ref_known(v___x_2560_, 2);
v___y_2550_ = v___x_2559_;
v___y_2551_ = v_pos_2558_;
v_err_2552_ = v_err_2564_;
goto v___jp_2549_;
}
}
else
{
lean_object* v_err_2565_; 
v_err_2565_ = lean_ctor_get(v___x_2560_, 1);
lean_inc(v_err_2565_);
lean_dec_ref_known(v___x_2560_, 2);
v___y_2550_ = v___x_2559_;
v___y_2551_ = v_pos_2558_;
v_err_2552_ = v_err_2565_;
goto v___jp_2549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURI(lean_object* v_config_2612_, lean_object* v_a_2613_){
_start:
{
lean_object* v___x_2614_; 
v___x_2614_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_2612_, v_a_2613_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_pos_2615_; lean_object* v_res_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2747_; 
v_pos_2615_ = lean_ctor_get(v___x_2614_, 0);
v_res_2616_ = lean_ctor_get(v___x_2614_, 1);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2618_ = v___x_2614_;
v_isShared_2619_ = v_isSharedCheck_2747_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_res_2616_);
lean_inc(v_pos_2615_);
lean_dec(v___x_2614_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2747_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v_array_2620_; lean_object* v_idx_2621_; lean_object* v___x_2622_; uint8_t v___x_2623_; 
v_array_2620_ = lean_ctor_get(v_pos_2615_, 0);
v_idx_2621_ = lean_ctor_get(v_pos_2615_, 1);
v___x_2622_ = lean_byte_array_size(v_array_2620_);
v___x_2623_ = lean_nat_dec_lt(v_idx_2621_, v___x_2622_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2624_; lean_object* v___x_2626_; 
lean_dec(v_res_2616_);
lean_dec_ref(v_config_2612_);
v___x_2624_ = lean_box(0);
if (v_isShared_2619_ == 0)
{
lean_ctor_set_tag(v___x_2618_, 1);
lean_ctor_set(v___x_2618_, 1, v___x_2624_);
v___x_2626_ = v___x_2618_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_pos_2615_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v___x_2624_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
else
{
uint8_t v___x_2628_; uint8_t v_got_2629_; uint8_t v___x_2630_; 
v___x_2628_ = 58;
v_got_2629_ = lean_byte_array_fget(v_array_2620_, v_idx_2621_);
v___x_2630_ = lean_uint8_dec_eq(v_got_2629_, v___x_2628_);
if (v___x_2630_ == 0)
{
lean_object* v___x_2631_; lean_object* v___x_2633_; 
lean_dec(v_res_2616_);
lean_dec_ref(v_config_2612_);
v___x_2631_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_2619_ == 0)
{
lean_ctor_set_tag(v___x_2618_, 1);
lean_ctor_set(v___x_2618_, 1, v___x_2631_);
v___x_2633_ = v___x_2618_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_pos_2615_);
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
lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2744_; 
lean_inc(v_idx_2621_);
lean_inc_ref(v_array_2620_);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_pos_2615_);
if (v_isSharedCheck_2744_ == 0)
{
lean_object* v_unused_2745_; lean_object* v_unused_2746_; 
v_unused_2745_ = lean_ctor_get(v_pos_2615_, 1);
lean_dec(v_unused_2745_);
v_unused_2746_ = lean_ctor_get(v_pos_2615_, 0);
lean_dec(v_unused_2746_);
v___x_2636_ = v_pos_2615_;
v_isShared_2637_ = v_isSharedCheck_2744_;
goto v_resetjp_2635_;
}
else
{
lean_dec(v_pos_2615_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2744_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2641_; 
v___x_2638_ = lean_unsigned_to_nat(1u);
v___x_2639_ = lean_nat_add(v_idx_2621_, v___x_2638_);
lean_dec(v_idx_2621_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 1, v___x_2639_);
v___x_2641_ = v___x_2636_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_array_2620_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v___x_2639_);
v___x_2641_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
lean_object* v___x_2642_; 
lean_inc_ref(v_config_2612_);
v___x_2642_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2612_, v___x_2641_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_res_2643_; lean_object* v_pos_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2733_; 
v_res_2643_ = lean_ctor_get(v___x_2642_, 1);
v_pos_2644_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2646_ = v___x_2642_;
v_isShared_2647_ = v_isSharedCheck_2733_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_res_2643_);
lean_inc(v_pos_2644_);
lean_dec(v___x_2642_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2733_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v_fst_2648_; lean_object* v_snd_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2732_; 
v_fst_2648_ = lean_ctor_get(v_res_2643_, 0);
v_snd_2649_ = lean_ctor_get(v_res_2643_, 1);
v_isSharedCheck_2732_ = !lean_is_exclusive(v_res_2643_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2651_ = v_res_2643_;
v_isShared_2652_ = v_isSharedCheck_2732_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_snd_2649_);
lean_inc(v_fst_2648_);
lean_dec(v_res_2643_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2732_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___y_2654_; lean_object* v_pos_2655_; lean_object* v_res_2656_; lean_object* v_idx_2662_; lean_object* v___y_2663_; lean_object* v_pos_2664_; lean_object* v_err_2665_; lean_object* v_pos_2673_; lean_object* v_array_2674_; lean_object* v_idx_2675_; lean_object* v_res_2676_; lean_object* v_array_2695_; lean_object* v_idx_2696_; lean_object* v_pos_2698_; lean_object* v_array_2699_; lean_object* v_idx_2700_; lean_object* v_err_2701_; lean_object* v___x_2705_; uint8_t v___x_2706_; 
v_array_2695_ = lean_ctor_get(v_pos_2644_, 0);
lean_inc_ref(v_array_2695_);
v_idx_2696_ = lean_ctor_get(v_pos_2644_, 1);
lean_inc(v_idx_2696_);
v___x_2705_ = lean_byte_array_size(v_array_2695_);
v___x_2706_ = lean_nat_dec_lt(v_idx_2696_, v___x_2705_);
if (v___x_2706_ == 0)
{
lean_object* v___x_2707_; 
v___x_2707_ = lean_box(0);
lean_inc(v_idx_2696_);
v_pos_2698_ = v_pos_2644_;
v_array_2699_ = v_array_2695_;
v_idx_2700_ = v_idx_2696_;
v_err_2701_ = v___x_2707_;
goto v___jp_2697_;
}
else
{
uint8_t v___x_2708_; uint8_t v_got_2709_; uint8_t v___x_2710_; 
v___x_2708_ = 63;
v_got_2709_ = lean_byte_array_fget(v_array_2695_, v_idx_2696_);
v___x_2710_ = lean_uint8_dec_eq(v_got_2709_, v___x_2708_);
if (v___x_2710_ == 0)
{
lean_object* v___x_2711_; 
v___x_2711_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_2696_);
v_pos_2698_ = v_pos_2644_;
v_array_2699_ = v_array_2695_;
v_idx_2700_ = v_idx_2696_;
v_err_2701_ = v___x_2711_;
goto v___jp_2697_;
}
else
{
lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2729_; 
v_isSharedCheck_2729_ = !lean_is_exclusive(v_pos_2644_);
if (v_isSharedCheck_2729_ == 0)
{
lean_object* v_unused_2730_; lean_object* v_unused_2731_; 
v_unused_2730_ = lean_ctor_get(v_pos_2644_, 1);
lean_dec(v_unused_2730_);
v_unused_2731_ = lean_ctor_get(v_pos_2644_, 0);
lean_dec(v_unused_2731_);
v___x_2713_ = v_pos_2644_;
v_isShared_2714_ = v_isSharedCheck_2729_;
goto v_resetjp_2712_;
}
else
{
lean_dec(v_pos_2644_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2729_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2715_; lean_object* v___x_2717_; 
v___x_2715_ = lean_nat_add(v_idx_2696_, v___x_2638_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 1, v___x_2715_);
v___x_2717_ = v___x_2713_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_array_2695_);
lean_ctor_set(v_reuseFailAlloc_2728_, 1, v___x_2715_);
v___x_2717_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
lean_object* v___x_2718_; 
lean_inc_ref(v_config_2612_);
v___x_2718_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2612_, v___x_2717_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v_pos_2719_; lean_object* v_res_2720_; lean_object* v_array_2721_; lean_object* v_idx_2722_; lean_object* v___x_2723_; 
lean_dec(v_idx_2696_);
v_pos_2719_ = lean_ctor_get(v___x_2718_, 0);
lean_inc(v_pos_2719_);
v_res_2720_ = lean_ctor_get(v___x_2718_, 1);
lean_inc(v_res_2720_);
lean_dec_ref_known(v___x_2718_, 2);
v_array_2721_ = lean_ctor_get(v_pos_2719_, 0);
lean_inc_ref(v_array_2721_);
v_idx_2722_ = lean_ctor_get(v_pos_2719_, 1);
lean_inc(v_idx_2722_);
v___x_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2723_, 0, v_res_2720_);
v_pos_2673_ = v_pos_2719_;
v_array_2674_ = v_array_2721_;
v_idx_2675_ = v_idx_2722_;
v_res_2676_ = v___x_2723_;
goto v___jp_2672_;
}
else
{
lean_object* v_pos_2724_; lean_object* v_err_2725_; lean_object* v_array_2726_; lean_object* v_idx_2727_; 
v_pos_2724_ = lean_ctor_get(v___x_2718_, 0);
lean_inc(v_pos_2724_);
v_err_2725_ = lean_ctor_get(v___x_2718_, 1);
lean_inc(v_err_2725_);
lean_dec_ref_known(v___x_2718_, 2);
v_array_2726_ = lean_ctor_get(v_pos_2724_, 0);
lean_inc_ref(v_array_2726_);
v_idx_2727_ = lean_ctor_get(v_pos_2724_, 1);
lean_inc(v_idx_2727_);
v_pos_2698_ = v_pos_2724_;
v_array_2699_ = v_array_2726_;
v_idx_2700_ = v_idx_2727_;
v_err_2701_ = v_err_2725_;
goto v___jp_2697_;
}
}
}
}
}
v___jp_2653_:
{
lean_object* v___x_2657_; lean_object* v___x_2659_; 
v___x_2657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2657_, 0, v_res_2616_);
lean_ctor_set(v___x_2657_, 1, v_fst_2648_);
lean_ctor_set(v___x_2657_, 2, v_snd_2649_);
lean_ctor_set(v___x_2657_, 3, v___y_2654_);
lean_ctor_set(v___x_2657_, 4, v_res_2656_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 1, v___x_2657_);
lean_ctor_set(v___x_2646_, 0, v_pos_2655_);
v___x_2659_ = v___x_2646_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_pos_2655_);
lean_ctor_set(v_reuseFailAlloc_2660_, 1, v___x_2657_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
v___jp_2661_:
{
lean_object* v_idx_2666_; uint8_t v___x_2667_; 
v_idx_2666_ = lean_ctor_get(v_pos_2664_, 1);
v___x_2667_ = lean_nat_dec_eq(v_idx_2662_, v_idx_2666_);
lean_dec(v_idx_2662_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2669_; 
lean_dec(v___y_2663_);
lean_dec(v_snd_2649_);
lean_dec(v_fst_2648_);
lean_del_object(v___x_2646_);
lean_dec(v_res_2616_);
if (v_isShared_2619_ == 0)
{
lean_ctor_set_tag(v___x_2618_, 1);
lean_ctor_set(v___x_2618_, 1, v_err_2665_);
lean_ctor_set(v___x_2618_, 0, v_pos_2664_);
v___x_2669_ = v___x_2618_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_pos_2664_);
lean_ctor_set(v_reuseFailAlloc_2670_, 1, v_err_2665_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
else
{
lean_object* v___x_2671_; 
lean_dec(v_err_2665_);
lean_del_object(v___x_2618_);
v___x_2671_ = lean_box(0);
v___y_2654_ = v___y_2663_;
v_pos_2655_ = v_pos_2664_;
v_res_2656_ = v___x_2671_;
goto v___jp_2653_;
}
}
v___jp_2672_:
{
lean_object* v___x_2677_; uint8_t v___x_2678_; 
v___x_2677_ = lean_byte_array_size(v_array_2674_);
v___x_2678_ = lean_nat_dec_lt(v_idx_2675_, v___x_2677_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2679_; 
lean_dec_ref(v_array_2674_);
lean_del_object(v___x_2651_);
lean_dec_ref(v_config_2612_);
v___x_2679_ = lean_box(0);
v_idx_2662_ = v_idx_2675_;
v___y_2663_ = v_res_2676_;
v_pos_2664_ = v_pos_2673_;
v_err_2665_ = v___x_2679_;
goto v___jp_2661_;
}
else
{
uint8_t v___x_2680_; uint8_t v_got_2681_; uint8_t v___x_2682_; 
v___x_2680_ = 35;
v_got_2681_ = lean_byte_array_fget(v_array_2674_, v_idx_2675_);
v___x_2682_ = lean_uint8_dec_eq(v_got_2681_, v___x_2680_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; 
lean_dec_ref(v_array_2674_);
lean_del_object(v___x_2651_);
lean_dec_ref(v_config_2612_);
v___x_2683_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v_idx_2662_ = v_idx_2675_;
v___y_2663_ = v_res_2676_;
v_pos_2664_ = v_pos_2673_;
v_err_2665_ = v___x_2683_;
goto v___jp_2661_;
}
else
{
lean_object* v___x_2684_; lean_object* v___x_2686_; 
lean_dec_ref(v_pos_2673_);
v___x_2684_ = lean_nat_add(v_idx_2675_, v___x_2638_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 1, v___x_2684_);
lean_ctor_set(v___x_2651_, 0, v_array_2674_);
v___x_2686_ = v___x_2651_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_array_2674_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v___x_2684_);
v___x_2686_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
lean_object* v___x_2687_; 
v___x_2687_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2612_, v___x_2686_);
lean_dec_ref(v_config_2612_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v_pos_2688_; lean_object* v_res_2689_; lean_object* v___x_2690_; 
v_pos_2688_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_pos_2688_);
v_res_2689_ = lean_ctor_get(v___x_2687_, 1);
lean_inc(v_res_2689_);
lean_dec_ref_known(v___x_2687_, 2);
v___x_2690_ = l_Std_Http_URI_EncodedFragment_decode(v_res_2689_);
lean_dec(v_res_2689_);
if (lean_obj_tag(v___x_2690_) == 1)
{
lean_dec(v_idx_2675_);
lean_del_object(v___x_2618_);
v___y_2654_ = v_res_2676_;
v_pos_2655_ = v_pos_2688_;
v_res_2656_ = v___x_2690_;
goto v___jp_2653_;
}
else
{
lean_object* v___x_2691_; 
lean_dec(v___x_2690_);
v___x_2691_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__3));
v_idx_2662_ = v_idx_2675_;
v___y_2663_ = v_res_2676_;
v_pos_2664_ = v_pos_2688_;
v_err_2665_ = v___x_2691_;
goto v___jp_2661_;
}
}
else
{
lean_object* v_pos_2692_; lean_object* v_err_2693_; 
v_pos_2692_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_pos_2692_);
v_err_2693_ = lean_ctor_get(v___x_2687_, 1);
lean_inc(v_err_2693_);
lean_dec_ref_known(v___x_2687_, 2);
v_idx_2662_ = v_idx_2675_;
v___y_2663_ = v_res_2676_;
v_pos_2664_ = v_pos_2692_;
v_err_2665_ = v_err_2693_;
goto v___jp_2661_;
}
}
}
}
}
v___jp_2697_:
{
uint8_t v___x_2702_; 
v___x_2702_ = lean_nat_dec_eq(v_idx_2696_, v_idx_2700_);
lean_dec(v_idx_2696_);
if (v___x_2702_ == 0)
{
lean_object* v___x_2703_; 
lean_dec(v_idx_2700_);
lean_dec_ref(v_array_2699_);
lean_del_object(v___x_2651_);
lean_dec(v_snd_2649_);
lean_dec(v_fst_2648_);
lean_del_object(v___x_2646_);
lean_del_object(v___x_2618_);
lean_dec(v_res_2616_);
lean_dec_ref(v_config_2612_);
v___x_2703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2703_, 0, v_pos_2698_);
lean_ctor_set(v___x_2703_, 1, v_err_2701_);
return v___x_2703_;
}
else
{
lean_object* v___x_2704_; 
lean_dec(v_err_2701_);
v___x_2704_ = lean_box(0);
v_pos_2673_ = v_pos_2698_;
v_array_2674_ = v_array_2699_;
v_idx_2675_ = v_idx_2700_;
v_res_2676_ = v___x_2704_;
goto v___jp_2672_;
}
}
}
}
}
else
{
lean_object* v_pos_2734_; lean_object* v_err_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
lean_del_object(v___x_2618_);
lean_dec(v_res_2616_);
lean_dec_ref(v_config_2612_);
v_pos_2734_ = lean_ctor_get(v___x_2642_, 0);
v_err_2735_ = lean_ctor_get(v___x_2642_, 1);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___x_2642_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_err_2735_);
lean_inc(v_pos_2734_);
lean_dec(v___x_2642_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_pos_2734_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v_err_2735_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
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
lean_object* v_pos_2748_; lean_object* v_err_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2756_; 
lean_dec_ref(v_config_2612_);
v_pos_2748_ = lean_ctor_get(v___x_2614_, 0);
v_err_2749_ = lean_ctor_get(v___x_2614_, 1);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2751_ = v___x_2614_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_err_2749_);
lean_inc(v_pos_2748_);
lean_dec(v___x_2614_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2754_; 
if (v_isShared_2752_ == 0)
{
v___x_2754_ = v___x_2751_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_pos_2748_);
lean_ctor_set(v_reuseFailAlloc_2755_, 1, v_err_2749_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(lean_object* v_a_2760_){
_start:
{
lean_object* v_array_2761_; lean_object* v_idx_2762_; lean_object* v___x_2763_; uint8_t v___x_2764_; 
v_array_2761_ = lean_ctor_get(v_a_2760_, 0);
v_idx_2762_ = lean_ctor_get(v_a_2760_, 1);
v___x_2763_ = lean_byte_array_size(v_array_2761_);
v___x_2764_ = lean_nat_dec_lt(v_idx_2762_, v___x_2763_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2765_ = lean_box(0);
v___x_2766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2766_, 0, v_a_2760_);
lean_ctor_set(v___x_2766_, 1, v___x_2765_);
return v___x_2766_;
}
else
{
uint8_t v___x_2767_; uint8_t v_got_2768_; uint8_t v___x_2769_; 
v___x_2767_ = 42;
v_got_2768_ = lean_byte_array_fget(v_array_2761_, v_idx_2762_);
v___x_2769_ = lean_uint8_dec_eq(v_got_2768_, v___x_2767_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2770_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1));
v___x_2771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2771_, 0, v_a_2760_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
return v___x_2771_;
}
else
{
lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2782_; 
lean_inc(v_idx_2762_);
lean_inc_ref(v_array_2761_);
v_isSharedCheck_2782_ = !lean_is_exclusive(v_a_2760_);
if (v_isSharedCheck_2782_ == 0)
{
lean_object* v_unused_2783_; lean_object* v_unused_2784_; 
v_unused_2783_ = lean_ctor_get(v_a_2760_, 1);
lean_dec(v_unused_2783_);
v_unused_2784_ = lean_ctor_get(v_a_2760_, 0);
lean_dec(v_unused_2784_);
v___x_2773_ = v_a_2760_;
v_isShared_2774_ = v_isSharedCheck_2782_;
goto v_resetjp_2772_;
}
else
{
lean_dec(v_a_2760_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2782_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2778_; 
v___x_2775_ = lean_unsigned_to_nat(1u);
v___x_2776_ = lean_nat_add(v_idx_2762_, v___x_2775_);
lean_dec(v_idx_2762_);
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 1, v___x_2776_);
v___x_2778_ = v___x_2773_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_array_2761_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v___x_2776_);
v___x_2778_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2779_ = lean_box(3);
v___x_2780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2778_);
lean_ctor_set(v___x_2780_, 1, v___x_2779_);
return v___x_2780_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(lean_object* v_config_2788_, lean_object* v_a_2789_){
_start:
{
lean_object* v_array_2793_; lean_object* v_idx_2794_; lean_object* v___x_2795_; uint8_t v___x_2796_; 
v_array_2793_ = lean_ctor_get(v_a_2789_, 0);
v_idx_2794_ = lean_ctor_get(v_a_2789_, 1);
v___x_2795_ = lean_byte_array_size(v_array_2793_);
v___x_2796_ = lean_nat_dec_lt(v_idx_2794_, v___x_2795_);
if (v___x_2796_ == 0)
{
lean_dec_ref(v_config_2788_);
goto v___jp_2790_;
}
else
{
uint8_t v___x_2797_; uint8_t v___x_2798_; uint8_t v___x_2799_; 
v___x_2797_ = lean_byte_array_fget(v_array_2793_, v_idx_2794_);
v___x_2798_ = 47;
v___x_2799_ = lean_uint8_dec_eq(v___x_2797_, v___x_2798_);
if (v___x_2799_ == 0)
{
lean_dec_ref(v_config_2788_);
goto v___jp_2790_;
}
else
{
lean_object* v___x_2800_; 
lean_inc_ref(v_a_2789_);
lean_inc_ref(v_config_2788_);
v___x_2800_ = l_Std_Http_URI_Parser_parsePath(v_config_2788_, v___x_2799_, v___x_2799_, v_a_2789_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_pos_2801_; lean_object* v_res_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2847_; 
v_pos_2801_ = lean_ctor_get(v___x_2800_, 0);
v_res_2802_ = lean_ctor_get(v___x_2800_, 1);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2804_ = v___x_2800_;
v_isShared_2805_ = v_isSharedCheck_2847_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_res_2802_);
lean_inc(v_pos_2801_);
lean_dec(v___x_2800_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2847_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v_pos_2807_; lean_object* v_res_2808_; lean_object* v_array_2813_; lean_object* v_idx_2814_; lean_object* v_pos_2816_; lean_object* v_idx_2817_; lean_object* v_err_2818_; lean_object* v___x_2822_; uint8_t v___x_2823_; 
v_array_2813_ = lean_ctor_get(v_pos_2801_, 0);
v_idx_2814_ = lean_ctor_get(v_pos_2801_, 1);
lean_inc(v_idx_2814_);
v___x_2822_ = lean_byte_array_size(v_array_2813_);
v___x_2823_ = lean_nat_dec_lt(v_idx_2814_, v___x_2822_);
if (v___x_2823_ == 0)
{
lean_object* v___x_2824_; 
lean_dec_ref(v_config_2788_);
v___x_2824_ = lean_box(0);
lean_inc(v_idx_2814_);
v_pos_2816_ = v_pos_2801_;
v_idx_2817_ = v_idx_2814_;
v_err_2818_ = v___x_2824_;
goto v___jp_2815_;
}
else
{
uint8_t v___x_2825_; uint8_t v_got_2826_; uint8_t v___x_2827_; 
v___x_2825_ = 63;
v_got_2826_ = lean_byte_array_fget(v_array_2813_, v_idx_2814_);
v___x_2827_ = lean_uint8_dec_eq(v_got_2826_, v___x_2825_);
if (v___x_2827_ == 0)
{
lean_object* v___x_2828_; 
lean_dec_ref(v_config_2788_);
v___x_2828_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_2814_);
v_pos_2816_ = v_pos_2801_;
v_idx_2817_ = v_idx_2814_;
v_err_2818_ = v___x_2828_;
goto v___jp_2815_;
}
else
{
lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2844_; 
lean_inc_ref(v_array_2813_);
v_isSharedCheck_2844_ = !lean_is_exclusive(v_pos_2801_);
if (v_isSharedCheck_2844_ == 0)
{
lean_object* v_unused_2845_; lean_object* v_unused_2846_; 
v_unused_2845_ = lean_ctor_get(v_pos_2801_, 1);
lean_dec(v_unused_2845_);
v_unused_2846_ = lean_ctor_get(v_pos_2801_, 0);
lean_dec(v_unused_2846_);
v___x_2830_ = v_pos_2801_;
v_isShared_2831_ = v_isSharedCheck_2844_;
goto v_resetjp_2829_;
}
else
{
lean_dec(v_pos_2801_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2844_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2835_; 
v___x_2832_ = lean_unsigned_to_nat(1u);
v___x_2833_ = lean_nat_add(v_idx_2814_, v___x_2832_);
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 1, v___x_2833_);
v___x_2835_ = v___x_2830_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_array_2813_);
lean_ctor_set(v_reuseFailAlloc_2843_, 1, v___x_2833_);
v___x_2835_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
lean_object* v___x_2836_; 
v___x_2836_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2788_, v___x_2835_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_pos_2837_; lean_object* v_res_2838_; lean_object* v___x_2839_; 
lean_dec(v_idx_2814_);
lean_dec_ref(v_a_2789_);
v_pos_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_pos_2837_);
v_res_2838_ = lean_ctor_get(v___x_2836_, 1);
lean_inc(v_res_2838_);
lean_dec_ref_known(v___x_2836_, 2);
v___x_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2839_, 0, v_res_2838_);
v_pos_2807_ = v_pos_2837_;
v_res_2808_ = v___x_2839_;
goto v___jp_2806_;
}
else
{
lean_object* v_pos_2840_; lean_object* v_err_2841_; lean_object* v_idx_2842_; 
v_pos_2840_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_pos_2840_);
v_err_2841_ = lean_ctor_get(v___x_2836_, 1);
lean_inc(v_err_2841_);
lean_dec_ref_known(v___x_2836_, 2);
v_idx_2842_ = lean_ctor_get(v_pos_2840_, 1);
lean_inc(v_idx_2842_);
v_pos_2816_ = v_pos_2840_;
v_idx_2817_ = v_idx_2842_;
v_err_2818_ = v_err_2841_;
goto v___jp_2815_;
}
}
}
}
}
v___jp_2806_:
{
lean_object* v___x_2809_; lean_object* v___x_2811_; 
v___x_2809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2809_, 0, v_res_2802_);
lean_ctor_set(v___x_2809_, 1, v_res_2808_);
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 1, v___x_2809_);
lean_ctor_set(v___x_2804_, 0, v_pos_2807_);
v___x_2811_ = v___x_2804_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_pos_2807_);
lean_ctor_set(v_reuseFailAlloc_2812_, 1, v___x_2809_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
v___jp_2815_:
{
uint8_t v___x_2819_; 
v___x_2819_ = lean_nat_dec_eq(v_idx_2814_, v_idx_2817_);
lean_dec(v_idx_2817_);
lean_dec(v_idx_2814_);
if (v___x_2819_ == 0)
{
lean_object* v___x_2820_; 
lean_dec_ref(v_pos_2816_);
lean_del_object(v___x_2804_);
lean_dec(v_res_2802_);
v___x_2820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2820_, 0, v_a_2789_);
lean_ctor_set(v___x_2820_, 1, v_err_2818_);
return v___x_2820_;
}
else
{
lean_object* v___x_2821_; 
lean_dec(v_err_2818_);
lean_dec_ref(v_a_2789_);
v___x_2821_ = lean_box(0);
v_pos_2807_ = v_pos_2816_;
v_res_2808_ = v___x_2821_;
goto v___jp_2806_;
}
}
}
}
else
{
lean_object* v_err_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_dec_ref(v_config_2788_);
v_err_2848_ = lean_ctor_get(v___x_2800_, 1);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2855_ == 0)
{
lean_object* v_unused_2856_; 
v_unused_2856_ = lean_ctor_get(v___x_2800_, 0);
lean_dec(v_unused_2856_);
v___x_2850_ = v___x_2800_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_err_2848_);
lean_dec(v___x_2800_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 0, v_a_2789_);
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2789_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v_err_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
}
v___jp_2790_:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2791_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1));
v___x_2792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2792_, 0, v_a_2789_);
lean_ctor_set(v___x_2792_, 1, v___x_2791_);
return v___x_2792_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(lean_object* v_config_2857_, lean_object* v_scheme_2858_, lean_object* v_a_2859_){
_start:
{
lean_object* v_array_2860_; lean_object* v_idx_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; 
v_array_2860_ = lean_ctor_get(v_a_2859_, 0);
v_idx_2861_ = lean_ctor_get(v_a_2859_, 1);
v___x_2862_ = lean_byte_array_size(v_array_2860_);
v___x_2863_ = lean_nat_dec_lt(v_idx_2861_, v___x_2862_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
lean_dec_ref(v_scheme_2858_);
lean_dec_ref(v_config_2857_);
v___x_2864_ = lean_box(0);
v___x_2865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2865_, 0, v_a_2859_);
lean_ctor_set(v___x_2865_, 1, v___x_2864_);
return v___x_2865_;
}
else
{
uint8_t v___x_2866_; uint8_t v_got_2867_; uint8_t v___x_2868_; 
v___x_2866_ = 58;
v_got_2867_ = lean_byte_array_fget(v_array_2860_, v_idx_2861_);
v___x_2868_ = lean_uint8_dec_eq(v_got_2867_, v___x_2866_);
if (v___x_2868_ == 0)
{
lean_object* v___x_2869_; lean_object* v___x_2870_; 
lean_dec_ref(v_scheme_2858_);
lean_dec_ref(v_config_2857_);
v___x_2869_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
v___x_2870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2870_, 0, v_a_2859_);
lean_ctor_set(v___x_2870_, 1, v___x_2869_);
return v___x_2870_;
}
else
{
lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2945_; 
lean_inc(v_idx_2861_);
lean_inc_ref(v_array_2860_);
v_isSharedCheck_2945_ = !lean_is_exclusive(v_a_2859_);
if (v_isSharedCheck_2945_ == 0)
{
lean_object* v_unused_2946_; lean_object* v_unused_2947_; 
v_unused_2946_ = lean_ctor_get(v_a_2859_, 1);
lean_dec(v_unused_2946_);
v_unused_2947_ = lean_ctor_get(v_a_2859_, 0);
lean_dec(v_unused_2947_);
v___x_2872_ = v_a_2859_;
v_isShared_2873_ = v_isSharedCheck_2945_;
goto v_resetjp_2871_;
}
else
{
lean_dec(v_a_2859_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2945_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2877_; 
v___x_2874_ = lean_unsigned_to_nat(1u);
v___x_2875_ = lean_nat_add(v_idx_2861_, v___x_2874_);
lean_dec(v_idx_2861_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 1, v___x_2875_);
v___x_2877_ = v___x_2872_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_array_2860_);
lean_ctor_set(v_reuseFailAlloc_2944_, 1, v___x_2875_);
v___x_2877_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
lean_object* v___x_2878_; 
lean_inc_ref(v_config_2857_);
v___x_2878_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2857_, v___x_2877_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_res_2879_; lean_object* v_pos_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2934_; 
v_res_2879_ = lean_ctor_get(v___x_2878_, 1);
v_pos_2880_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2882_ = v___x_2878_;
v_isShared_2883_ = v_isSharedCheck_2934_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_res_2879_);
lean_inc(v_pos_2880_);
lean_dec(v___x_2878_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2934_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v_fst_2884_; lean_object* v_snd_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2933_; 
v_fst_2884_ = lean_ctor_get(v_res_2879_, 0);
v_snd_2885_ = lean_ctor_get(v_res_2879_, 1);
v_isSharedCheck_2933_ = !lean_is_exclusive(v_res_2879_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2887_ = v_res_2879_;
v_isShared_2888_ = v_isSharedCheck_2933_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_snd_2885_);
lean_inc(v_fst_2884_);
lean_dec(v_res_2879_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2933_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v_pos_2890_; lean_object* v_res_2891_; lean_object* v_array_2898_; lean_object* v_idx_2899_; lean_object* v_pos_2901_; lean_object* v_idx_2902_; lean_object* v_err_2903_; lean_object* v___x_2909_; uint8_t v___x_2910_; 
v_array_2898_ = lean_ctor_get(v_pos_2880_, 0);
v_idx_2899_ = lean_ctor_get(v_pos_2880_, 1);
lean_inc(v_idx_2899_);
v___x_2909_ = lean_byte_array_size(v_array_2898_);
v___x_2910_ = lean_nat_dec_lt(v_idx_2899_, v___x_2909_);
if (v___x_2910_ == 0)
{
lean_object* v___x_2911_; 
lean_dec_ref(v_config_2857_);
v___x_2911_ = lean_box(0);
lean_inc(v_idx_2899_);
v_pos_2901_ = v_pos_2880_;
v_idx_2902_ = v_idx_2899_;
v_err_2903_ = v___x_2911_;
goto v___jp_2900_;
}
else
{
uint8_t v___x_2912_; uint8_t v_got_2913_; uint8_t v___x_2914_; 
v___x_2912_ = 63;
v_got_2913_ = lean_byte_array_fget(v_array_2898_, v_idx_2899_);
v___x_2914_ = lean_uint8_dec_eq(v_got_2913_, v___x_2912_);
if (v___x_2914_ == 0)
{
lean_object* v___x_2915_; 
lean_dec_ref(v_config_2857_);
v___x_2915_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_2899_);
v_pos_2901_ = v_pos_2880_;
v_idx_2902_ = v_idx_2899_;
v_err_2903_ = v___x_2915_;
goto v___jp_2900_;
}
else
{
lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2930_; 
lean_inc_ref(v_array_2898_);
v_isSharedCheck_2930_ = !lean_is_exclusive(v_pos_2880_);
if (v_isSharedCheck_2930_ == 0)
{
lean_object* v_unused_2931_; lean_object* v_unused_2932_; 
v_unused_2931_ = lean_ctor_get(v_pos_2880_, 1);
lean_dec(v_unused_2931_);
v_unused_2932_ = lean_ctor_get(v_pos_2880_, 0);
lean_dec(v_unused_2932_);
v___x_2917_ = v_pos_2880_;
v_isShared_2918_ = v_isSharedCheck_2930_;
goto v_resetjp_2916_;
}
else
{
lean_dec(v_pos_2880_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2930_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2919_; lean_object* v___x_2921_; 
v___x_2919_ = lean_nat_add(v_idx_2899_, v___x_2874_);
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 1, v___x_2919_);
v___x_2921_ = v___x_2917_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_array_2898_);
lean_ctor_set(v_reuseFailAlloc_2929_, 1, v___x_2919_);
v___x_2921_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
lean_object* v___x_2922_; 
v___x_2922_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2857_, v___x_2921_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_pos_2923_; lean_object* v_res_2924_; lean_object* v___x_2925_; 
lean_dec(v_idx_2899_);
lean_del_object(v___x_2887_);
v_pos_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_pos_2923_);
v_res_2924_ = lean_ctor_get(v___x_2922_, 1);
lean_inc(v_res_2924_);
lean_dec_ref_known(v___x_2922_, 2);
v___x_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2925_, 0, v_res_2924_);
v_pos_2890_ = v_pos_2923_;
v_res_2891_ = v___x_2925_;
goto v___jp_2889_;
}
else
{
lean_object* v_pos_2926_; lean_object* v_err_2927_; lean_object* v_idx_2928_; 
v_pos_2926_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_pos_2926_);
v_err_2927_ = lean_ctor_get(v___x_2922_, 1);
lean_inc(v_err_2927_);
lean_dec_ref_known(v___x_2922_, 2);
v_idx_2928_ = lean_ctor_get(v_pos_2926_, 1);
lean_inc(v_idx_2928_);
v_pos_2901_ = v_pos_2926_;
v_idx_2902_ = v_idx_2928_;
v_err_2903_ = v_err_2927_;
goto v___jp_2900_;
}
}
}
}
}
v___jp_2889_:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2896_; 
v___x_2892_ = lean_box(0);
v___x_2893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2893_, 0, v_scheme_2858_);
lean_ctor_set(v___x_2893_, 1, v_fst_2884_);
lean_ctor_set(v___x_2893_, 2, v_snd_2885_);
lean_ctor_set(v___x_2893_, 3, v_res_2891_);
lean_ctor_set(v___x_2893_, 4, v___x_2892_);
v___x_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2893_);
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 1, v___x_2894_);
lean_ctor_set(v___x_2882_, 0, v_pos_2890_);
v___x_2896_ = v___x_2882_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_pos_2890_);
lean_ctor_set(v_reuseFailAlloc_2897_, 1, v___x_2894_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
v___jp_2900_:
{
uint8_t v___x_2904_; 
v___x_2904_ = lean_nat_dec_eq(v_idx_2899_, v_idx_2902_);
lean_dec(v_idx_2902_);
lean_dec(v_idx_2899_);
if (v___x_2904_ == 0)
{
lean_object* v___x_2906_; 
lean_dec(v_snd_2885_);
lean_dec(v_fst_2884_);
lean_del_object(v___x_2882_);
lean_dec_ref(v_scheme_2858_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set_tag(v___x_2887_, 1);
lean_ctor_set(v___x_2887_, 1, v_err_2903_);
lean_ctor_set(v___x_2887_, 0, v_pos_2901_);
v___x_2906_ = v___x_2887_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_pos_2901_);
lean_ctor_set(v_reuseFailAlloc_2907_, 1, v_err_2903_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
else
{
lean_object* v___x_2908_; 
lean_dec(v_err_2903_);
lean_del_object(v___x_2887_);
v___x_2908_ = lean_box(0);
v_pos_2890_ = v_pos_2901_;
v_res_2891_ = v___x_2908_;
goto v___jp_2889_;
}
}
}
}
}
else
{
lean_object* v_pos_2935_; lean_object* v_err_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
lean_dec_ref(v_scheme_2858_);
lean_dec_ref(v_config_2857_);
v_pos_2935_ = lean_ctor_get(v___x_2878_, 0);
v_err_2936_ = lean_ctor_get(v___x_2878_, 1);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2938_ = v___x_2878_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_err_2936_);
lean_inc(v_pos_2935_);
lean_dec(v___x_2878_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2941_; 
if (v_isShared_2939_ == 0)
{
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_pos_2935_);
lean_ctor_set(v_reuseFailAlloc_2942_, 1, v_err_2936_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(lean_object* v_config_2956_, lean_object* v_a_2957_){
_start:
{
lean_object* v___x_2961_; 
lean_inc_ref(v_a_2957_);
v___x_2961_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_2956_, v_a_2957_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_pos_2962_; lean_object* v_res_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_3059_; 
v_pos_2962_ = lean_ctor_get(v___x_2961_, 0);
v_res_2963_ = lean_ctor_get(v___x_2961_, 1);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_2965_ = v___x_2961_;
v_isShared_2966_ = v_isSharedCheck_3059_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_res_2963_);
lean_inc(v_pos_2962_);
lean_dec(v___x_2961_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_3059_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v_pos_2970_; lean_object* v_res_2971_; lean_object* v_idx_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v_pos_2982_; lean_object* v_idx_2983_; lean_object* v_err_2984_; lean_object* v___x_3053_; uint8_t v___x_3054_; 
v___x_3053_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2));
v___x_3054_ = lean_string_dec_eq(v_res_2963_, v___x_3053_);
if (v___x_3054_ == 0)
{
lean_object* v___x_3055_; uint8_t v___x_3056_; 
v___x_3055_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3));
v___x_3056_ = lean_string_dec_eq(v_res_2963_, v___x_3055_);
if (v___x_3056_ == 0)
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
lean_del_object(v___x_2965_);
lean_dec(v_res_2963_);
lean_dec(v_pos_2962_);
lean_dec_ref(v_config_2956_);
v___x_3057_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5));
v___x_3058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3058_, 0, v_a_2957_);
lean_ctor_set(v___x_3058_, 1, v___x_3057_);
return v___x_3058_;
}
else
{
goto v___jp_2988_;
}
}
else
{
goto v___jp_2988_;
}
v___jp_2967_:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2976_; 
v___x_2972_ = lean_box(0);
v___x_2973_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2973_, 0, v_res_2963_);
lean_ctor_set(v___x_2973_, 1, v___y_2969_);
lean_ctor_set(v___x_2973_, 2, v___y_2968_);
lean_ctor_set(v___x_2973_, 3, v_res_2971_);
lean_ctor_set(v___x_2973_, 4, v___x_2972_);
v___x_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2973_);
if (v_isShared_2966_ == 0)
{
lean_ctor_set(v___x_2965_, 1, v___x_2974_);
lean_ctor_set(v___x_2965_, 0, v_pos_2970_);
v___x_2976_ = v___x_2965_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_pos_2970_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v___x_2974_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
v___jp_2978_:
{
uint8_t v___x_2985_; 
v___x_2985_ = lean_nat_dec_eq(v_idx_2979_, v_idx_2983_);
lean_dec(v_idx_2983_);
lean_dec(v_idx_2979_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; 
lean_dec_ref(v_pos_2982_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
lean_del_object(v___x_2965_);
lean_dec(v_res_2963_);
v___x_2986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2986_, 0, v_a_2957_);
lean_ctor_set(v___x_2986_, 1, v_err_2984_);
return v___x_2986_;
}
else
{
lean_object* v___x_2987_; 
lean_dec(v_err_2984_);
lean_dec_ref(v_a_2957_);
v___x_2987_ = lean_box(0);
v___y_2968_ = v___y_2980_;
v___y_2969_ = v___y_2981_;
v_pos_2970_ = v_pos_2982_;
v_res_2971_ = v___x_2987_;
goto v___jp_2967_;
}
}
v___jp_2988_:
{
lean_object* v_array_2989_; lean_object* v_idx_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3052_; 
v_array_2989_ = lean_ctor_get(v_pos_2962_, 0);
v_idx_2990_ = lean_ctor_get(v_pos_2962_, 1);
v_isSharedCheck_3052_ = !lean_is_exclusive(v_pos_2962_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_2992_ = v_pos_2962_;
v_isShared_2993_ = v_isSharedCheck_3052_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_idx_2990_);
lean_inc(v_array_2989_);
lean_dec(v_pos_2962_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3052_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2994_; uint8_t v___x_2995_; 
v___x_2994_ = lean_byte_array_size(v_array_2989_);
v___x_2995_ = lean_nat_dec_lt(v_idx_2990_, v___x_2994_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2996_; lean_object* v___x_2997_; 
lean_del_object(v___x_2992_);
lean_dec(v_idx_2990_);
lean_dec_ref(v_array_2989_);
lean_del_object(v___x_2965_);
lean_dec(v_res_2963_);
lean_dec_ref(v_config_2956_);
v___x_2996_ = lean_box(0);
v___x_2997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2997_, 0, v_a_2957_);
lean_ctor_set(v___x_2997_, 1, v___x_2996_);
return v___x_2997_;
}
else
{
uint8_t v___x_2998_; uint8_t v_got_2999_; uint8_t v___x_3000_; 
v___x_2998_ = 58;
v_got_2999_ = lean_byte_array_fget(v_array_2989_, v_idx_2990_);
v___x_3000_ = lean_uint8_dec_eq(v_got_2999_, v___x_2998_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
lean_del_object(v___x_2992_);
lean_dec(v_idx_2990_);
lean_dec_ref(v_array_2989_);
lean_del_object(v___x_2965_);
lean_dec(v_res_2963_);
lean_dec_ref(v_config_2956_);
v___x_3001_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
v___x_3002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3002_, 0, v_a_2957_);
lean_ctor_set(v___x_3002_, 1, v___x_3001_);
return v___x_3002_;
}
else
{
lean_object* v___x_3003_; lean_object* v___x_3004_; uint8_t v___x_3005_; 
v___x_3003_ = lean_unsigned_to_nat(1u);
v___x_3004_ = lean_nat_add(v_idx_2990_, v___x_3003_);
lean_dec(v_idx_2990_);
v___x_3005_ = lean_nat_dec_lt(v___x_3004_, v___x_2994_);
if (v___x_3005_ == 0)
{
lean_dec(v___x_3004_);
lean_del_object(v___x_2992_);
lean_dec_ref(v_array_2989_);
lean_del_object(v___x_2965_);
lean_dec(v_res_2963_);
lean_dec_ref(v_config_2956_);
goto v___jp_2958_;
}
else
{
uint8_t v___x_3006_; uint8_t v___x_3007_; uint8_t v___x_3008_; 
v___x_3006_ = lean_byte_array_fget(v_array_2989_, v___x_3004_);
v___x_3007_ = 47;
v___x_3008_ = lean_uint8_dec_eq(v___x_3006_, v___x_3007_);
if (v___x_3008_ == 0)
{
lean_dec(v___x_3004_);
lean_del_object(v___x_2992_);
lean_dec_ref(v_array_2989_);
lean_del_object(v___x_2965_);
lean_dec(v_res_2963_);
lean_dec_ref(v_config_2956_);
goto v___jp_2958_;
}
else
{
lean_object* v___x_3010_; 
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 1, v___x_3004_);
v___x_3010_ = v___x_2992_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_array_2989_);
lean_ctor_set(v_reuseFailAlloc_3051_, 1, v___x_3004_);
v___x_3010_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
lean_object* v___x_3011_; 
lean_inc_ref(v_config_2956_);
v___x_3011_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2956_, v___x_3010_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_res_3012_; lean_object* v_pos_3013_; lean_object* v_fst_3014_; lean_object* v_snd_3015_; lean_object* v_array_3016_; lean_object* v_idx_3017_; lean_object* v___x_3018_; uint8_t v___x_3019_; 
v_res_3012_ = lean_ctor_get(v___x_3011_, 1);
lean_inc(v_res_3012_);
v_pos_3013_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_pos_3013_);
lean_dec_ref_known(v___x_3011_, 2);
v_fst_3014_ = lean_ctor_get(v_res_3012_, 0);
lean_inc(v_fst_3014_);
v_snd_3015_ = lean_ctor_get(v_res_3012_, 1);
lean_inc(v_snd_3015_);
lean_dec(v_res_3012_);
v_array_3016_ = lean_ctor_get(v_pos_3013_, 0);
v_idx_3017_ = lean_ctor_get(v_pos_3013_, 1);
lean_inc(v_idx_3017_);
v___x_3018_ = lean_byte_array_size(v_array_3016_);
v___x_3019_ = lean_nat_dec_lt(v_idx_3017_, v___x_3018_);
if (v___x_3019_ == 0)
{
lean_object* v___x_3020_; 
lean_dec_ref(v_config_2956_);
v___x_3020_ = lean_box(0);
lean_inc(v_idx_3017_);
v_idx_2979_ = v_idx_3017_;
v___y_2980_ = v_snd_3015_;
v___y_2981_ = v_fst_3014_;
v_pos_2982_ = v_pos_3013_;
v_idx_2983_ = v_idx_3017_;
v_err_2984_ = v___x_3020_;
goto v___jp_2978_;
}
else
{
uint8_t v___x_3021_; uint8_t v_got_3022_; uint8_t v___x_3023_; 
v___x_3021_ = 63;
v_got_3022_ = lean_byte_array_fget(v_array_3016_, v_idx_3017_);
v___x_3023_ = lean_uint8_dec_eq(v_got_3022_, v___x_3021_);
if (v___x_3023_ == 0)
{
lean_object* v___x_3024_; 
lean_dec_ref(v_config_2956_);
v___x_3024_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_3017_);
v_idx_2979_ = v_idx_3017_;
v___y_2980_ = v_snd_3015_;
v___y_2981_ = v_fst_3014_;
v_pos_2982_ = v_pos_3013_;
v_idx_2983_ = v_idx_3017_;
v_err_2984_ = v___x_3024_;
goto v___jp_2978_;
}
else
{
lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3039_; 
lean_inc_ref(v_array_3016_);
v_isSharedCheck_3039_ = !lean_is_exclusive(v_pos_3013_);
if (v_isSharedCheck_3039_ == 0)
{
lean_object* v_unused_3040_; lean_object* v_unused_3041_; 
v_unused_3040_ = lean_ctor_get(v_pos_3013_, 1);
lean_dec(v_unused_3040_);
v_unused_3041_ = lean_ctor_get(v_pos_3013_, 0);
lean_dec(v_unused_3041_);
v___x_3026_ = v_pos_3013_;
v_isShared_3027_ = v_isSharedCheck_3039_;
goto v_resetjp_3025_;
}
else
{
lean_dec(v_pos_3013_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3039_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3028_; lean_object* v___x_3030_; 
v___x_3028_ = lean_nat_add(v_idx_3017_, v___x_3003_);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 1, v___x_3028_);
v___x_3030_ = v___x_3026_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_array_3016_);
lean_ctor_set(v_reuseFailAlloc_3038_, 1, v___x_3028_);
v___x_3030_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
lean_object* v___x_3031_; 
v___x_3031_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2956_, v___x_3030_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_pos_3032_; lean_object* v_res_3033_; lean_object* v___x_3034_; 
lean_dec(v_idx_3017_);
lean_dec_ref(v_a_2957_);
v_pos_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc(v_pos_3032_);
v_res_3033_ = lean_ctor_get(v___x_3031_, 1);
lean_inc(v_res_3033_);
lean_dec_ref_known(v___x_3031_, 2);
v___x_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3034_, 0, v_res_3033_);
v___y_2968_ = v_snd_3015_;
v___y_2969_ = v_fst_3014_;
v_pos_2970_ = v_pos_3032_;
v_res_2971_ = v___x_3034_;
goto v___jp_2967_;
}
else
{
lean_object* v_pos_3035_; lean_object* v_err_3036_; lean_object* v_idx_3037_; 
v_pos_3035_ = lean_ctor_get(v___x_3031_, 0);
lean_inc(v_pos_3035_);
v_err_3036_ = lean_ctor_get(v___x_3031_, 1);
lean_inc(v_err_3036_);
lean_dec_ref_known(v___x_3031_, 2);
v_idx_3037_ = lean_ctor_get(v_pos_3035_, 1);
lean_inc(v_idx_3037_);
v_idx_2979_ = v_idx_3017_;
v___y_2980_ = v_snd_3015_;
v___y_2981_ = v_fst_3014_;
v_pos_2982_ = v_pos_3035_;
v_idx_2983_ = v_idx_3037_;
v_err_2984_ = v_err_3036_;
goto v___jp_2978_;
}
}
}
}
}
}
else
{
lean_object* v_err_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
lean_del_object(v___x_2965_);
lean_dec(v_res_2963_);
lean_dec_ref(v_config_2956_);
v_err_3042_ = lean_ctor_get(v___x_3011_, 1);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3049_ == 0)
{
lean_object* v_unused_3050_; 
v_unused_3050_ = lean_ctor_get(v___x_3011_, 0);
lean_dec(v_unused_3050_);
v___x_3044_ = v___x_3011_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_err_3042_);
lean_dec(v___x_3011_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 0, v_a_2957_);
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_2957_);
lean_ctor_set(v_reuseFailAlloc_3048_, 1, v_err_3042_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
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
lean_object* v_err_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
lean_dec_ref(v_config_2956_);
v_err_3060_ = lean_ctor_get(v___x_2961_, 1);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_3067_ == 0)
{
lean_object* v_unused_3068_; 
v_unused_3068_ = lean_ctor_get(v___x_2961_, 0);
lean_dec(v_unused_3068_);
v___x_3062_ = v___x_2961_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_err_3060_);
lean_dec(v___x_2961_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 0, v_a_2957_);
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_2957_);
lean_ctor_set(v_reuseFailAlloc_3066_, 1, v_err_3060_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
v___jp_2958_:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2959_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1));
v___x_2960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2960_, 0, v_a_2957_);
lean_ctor_set(v___x_2960_, 1, v___x_2959_);
return v___x_2960_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(lean_object* v_config_3069_, lean_object* v_a_3070_){
_start:
{
lean_object* v___x_3071_; 
lean_inc_ref(v_a_3070_);
v___x_3071_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3069_, v_a_3070_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v_pos_3072_; lean_object* v_res_3073_; lean_object* v___x_3074_; 
v_pos_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc(v_pos_3072_);
v_res_3073_ = lean_ctor_get(v___x_3071_, 1);
lean_inc(v_res_3073_);
lean_dec_ref_known(v___x_3071_, 2);
v___x_3074_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(v_config_3069_, v_res_3073_, v_pos_3072_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_dec_ref(v_a_3070_);
return v___x_3074_;
}
else
{
lean_object* v_err_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
v_err_3075_ = lean_ctor_get(v___x_3074_, 1);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3082_ == 0)
{
lean_object* v_unused_3083_; 
v_unused_3083_ = lean_ctor_get(v___x_3074_, 0);
lean_dec(v_unused_3083_);
v___x_3077_ = v___x_3074_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_err_3075_);
lean_dec(v___x_3074_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 0, v_a_3070_);
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3070_);
lean_ctor_set(v_reuseFailAlloc_3081_, 1, v_err_3075_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
else
{
lean_object* v_err_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec_ref(v_config_3069_);
v_err_3084_ = lean_ctor_get(v___x_3071_, 1);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3091_ == 0)
{
lean_object* v_unused_3092_; 
v_unused_3092_ = lean_ctor_get(v___x_3071_, 0);
lean_dec(v_unused_3092_);
v___x_3086_ = v___x_3071_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_err_3084_);
lean_dec(v___x_3071_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 0, v_a_3070_);
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3070_);
lean_ctor_set(v_reuseFailAlloc_3090_, 1, v_err_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(lean_object* v_config_3093_, lean_object* v_a_3094_){
_start:
{
lean_object* v___x_3095_; 
lean_inc_ref(v_a_3094_);
v___x_3095_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_3093_, v_a_3094_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v_pos_3096_; lean_object* v_res_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3149_; 
v_pos_3096_ = lean_ctor_get(v___x_3095_, 0);
v_res_3097_ = lean_ctor_get(v___x_3095_, 1);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3099_ = v___x_3095_;
v_isShared_3100_ = v_isSharedCheck_3149_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_res_3097_);
lean_inc(v_pos_3096_);
lean_dec(v___x_3095_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3149_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v_array_3101_; lean_object* v_idx_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3148_; 
v_array_3101_ = lean_ctor_get(v_pos_3096_, 0);
v_idx_3102_ = lean_ctor_get(v_pos_3096_, 1);
v_isSharedCheck_3148_ = !lean_is_exclusive(v_pos_3096_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3104_ = v_pos_3096_;
v_isShared_3105_ = v_isSharedCheck_3148_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_idx_3102_);
lean_inc(v_array_3101_);
lean_dec(v_pos_3096_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3148_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3106_; uint8_t v___x_3107_; 
v___x_3106_ = lean_byte_array_size(v_array_3101_);
v___x_3107_ = lean_nat_dec_lt(v_idx_3102_, v___x_3106_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3108_; lean_object* v___x_3110_; 
lean_del_object(v___x_3104_);
lean_dec(v_idx_3102_);
lean_dec_ref(v_array_3101_);
lean_dec(v_res_3097_);
v___x_3108_ = lean_box(0);
if (v_isShared_3100_ == 0)
{
lean_ctor_set_tag(v___x_3099_, 1);
lean_ctor_set(v___x_3099_, 1, v___x_3108_);
lean_ctor_set(v___x_3099_, 0, v_a_3094_);
v___x_3110_ = v___x_3099_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3094_);
lean_ctor_set(v_reuseFailAlloc_3111_, 1, v___x_3108_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
else
{
uint8_t v___x_3112_; uint8_t v_got_3113_; uint8_t v___x_3114_; 
v___x_3112_ = 58;
v_got_3113_ = lean_byte_array_fget(v_array_3101_, v_idx_3102_);
v___x_3114_ = lean_uint8_dec_eq(v_got_3113_, v___x_3112_);
if (v___x_3114_ == 0)
{
lean_object* v___x_3115_; lean_object* v___x_3117_; 
lean_del_object(v___x_3104_);
lean_dec(v_idx_3102_);
lean_dec_ref(v_array_3101_);
lean_dec(v_res_3097_);
v___x_3115_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_3100_ == 0)
{
lean_ctor_set_tag(v___x_3099_, 1);
lean_ctor_set(v___x_3099_, 1, v___x_3115_);
lean_ctor_set(v___x_3099_, 0, v_a_3094_);
v___x_3117_ = v___x_3099_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3094_);
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
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3122_; 
lean_del_object(v___x_3099_);
v___x_3119_ = lean_unsigned_to_nat(1u);
v___x_3120_ = lean_nat_add(v_idx_3102_, v___x_3119_);
lean_dec(v_idx_3102_);
if (v_isShared_3105_ == 0)
{
lean_ctor_set(v___x_3104_, 1, v___x_3120_);
v___x_3122_ = v___x_3104_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_array_3101_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v___x_3120_);
v___x_3122_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
lean_object* v___x_3123_; 
v___x_3123_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_3122_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_pos_3124_; lean_object* v_res_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3137_; 
lean_dec_ref(v_a_3094_);
v_pos_3124_ = lean_ctor_get(v___x_3123_, 0);
v_res_3125_ = lean_ctor_get(v___x_3123_, 1);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3127_ = v___x_3123_;
v_isShared_3128_ = v_isSharedCheck_3137_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_res_3125_);
lean_inc(v_pos_3124_);
lean_dec(v___x_3123_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3137_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; uint16_t v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3135_; 
v___x_3129_ = lean_box(0);
v___x_3130_ = lean_alloc_ctor(2, 0, 2);
v___x_3131_ = lean_unbox(v_res_3125_);
lean_dec(v_res_3125_);
lean_ctor_set_uint16(v___x_3130_, 0, v___x_3131_);
v___x_3132_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3129_);
lean_ctor_set(v___x_3132_, 1, v_res_3097_);
lean_ctor_set(v___x_3132_, 2, v___x_3130_);
v___x_3133_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3132_);
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 1, v___x_3133_);
v___x_3135_ = v___x_3127_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_pos_3124_);
lean_ctor_set(v_reuseFailAlloc_3136_, 1, v___x_3133_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
else
{
lean_object* v_err_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
lean_dec(v_res_3097_);
v_err_3138_ = lean_ctor_get(v___x_3123_, 1);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3145_ == 0)
{
lean_object* v_unused_3146_; 
v_unused_3146_ = lean_ctor_get(v___x_3123_, 0);
lean_dec(v_unused_3146_);
v___x_3140_ = v___x_3123_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_err_3138_);
lean_dec(v___x_3123_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 0, v_a_3094_);
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_3094_);
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
}
}
}
}
else
{
lean_object* v_err_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
v_err_3150_ = lean_ctor_get(v___x_3095_, 1);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3157_ == 0)
{
lean_object* v_unused_3158_; 
v_unused_3158_ = lean_ctor_get(v___x_3095_, 0);
lean_dec(v_unused_3158_);
v___x_3152_ = v___x_3095_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_err_3150_);
lean_dec(v___x_3095_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
lean_ctor_set(v___x_3152_, 0, v_a_3094_);
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3094_);
lean_ctor_set(v_reuseFailAlloc_3156_, 1, v_err_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority___boxed(lean_object* v_config_3159_, lean_object* v_a_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3159_, v_a_3160_);
lean_dec_ref(v_config_3159_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object* v_config_3162_, lean_object* v_a_3163_){
_start:
{
lean_object* v___x_3164_; 
lean_inc_ref(v_a_3163_);
v___x_3164_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(v_a_3163_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_dec_ref(v_a_3163_);
lean_dec_ref(v_config_3162_);
return v___x_3164_;
}
else
{
lean_object* v_pos_3165_; lean_object* v_idx_3166_; lean_object* v_idx_3167_; uint8_t v___x_3168_; 
v_pos_3165_ = lean_ctor_get(v___x_3164_, 0);
v_idx_3166_ = lean_ctor_get(v_a_3163_, 1);
lean_inc(v_idx_3166_);
lean_dec_ref(v_a_3163_);
v_idx_3167_ = lean_ctor_get(v_pos_3165_, 1);
v___x_3168_ = lean_nat_dec_eq(v_idx_3166_, v_idx_3167_);
lean_dec(v_idx_3166_);
if (v___x_3168_ == 0)
{
lean_dec_ref(v_config_3162_);
return v___x_3164_;
}
else
{
lean_object* v___x_3169_; 
lean_inc(v_idx_3167_);
lean_inc(v_pos_3165_);
lean_dec_ref_known(v___x_3164_, 2);
lean_inc_ref(v_config_3162_);
v___x_3169_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(v_config_3162_, v_pos_3165_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_dec(v_idx_3167_);
lean_dec_ref(v_config_3162_);
return v___x_3169_;
}
else
{
lean_object* v_pos_3170_; lean_object* v_idx_3171_; uint8_t v___x_3172_; 
v_pos_3170_ = lean_ctor_get(v___x_3169_, 0);
v_idx_3171_ = lean_ctor_get(v_pos_3170_, 1);
v___x_3172_ = lean_nat_dec_eq(v_idx_3167_, v_idx_3171_);
lean_dec(v_idx_3167_);
if (v___x_3172_ == 0)
{
lean_dec_ref(v_config_3162_);
return v___x_3169_;
}
else
{
lean_object* v___x_3173_; 
lean_inc(v_idx_3171_);
lean_inc(v_pos_3170_);
lean_dec_ref_known(v___x_3169_, 2);
lean_inc_ref(v_config_3162_);
v___x_3173_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(v_config_3162_, v_pos_3170_);
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_dec(v_idx_3171_);
lean_dec_ref(v_config_3162_);
return v___x_3173_;
}
else
{
lean_object* v_pos_3174_; lean_object* v_idx_3175_; uint8_t v___x_3176_; 
v_pos_3174_ = lean_ctor_get(v___x_3173_, 0);
v_idx_3175_ = lean_ctor_get(v_pos_3174_, 1);
v___x_3176_ = lean_nat_dec_eq(v_idx_3171_, v_idx_3175_);
lean_dec(v_idx_3171_);
if (v___x_3176_ == 0)
{
lean_dec_ref(v_config_3162_);
return v___x_3173_;
}
else
{
lean_object* v___x_3177_; 
lean_inc(v_idx_3175_);
lean_inc(v_pos_3174_);
lean_dec_ref_known(v___x_3173_, 2);
v___x_3177_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3162_, v_pos_3174_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_dec(v_idx_3175_);
lean_dec_ref(v_config_3162_);
return v___x_3177_;
}
else
{
lean_object* v_pos_3178_; lean_object* v_idx_3179_; uint8_t v___x_3180_; 
v_pos_3178_ = lean_ctor_get(v___x_3177_, 0);
v_idx_3179_ = lean_ctor_get(v_pos_3178_, 1);
v___x_3180_ = lean_nat_dec_eq(v_idx_3175_, v_idx_3179_);
lean_dec(v_idx_3175_);
if (v___x_3180_ == 0)
{
lean_dec_ref(v_config_3162_);
return v___x_3177_;
}
else
{
lean_object* v___x_3181_; 
lean_inc(v_pos_3178_);
lean_dec_ref_known(v___x_3177_, 2);
v___x_3181_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(v_config_3162_, v_pos_3178_);
return v___x_3181_;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(lean_object* v_config_3185_, lean_object* v_a_3186_){
_start:
{
lean_object* v___x_3187_; 
v___x_3187_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_3185_, v_a_3186_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_pos_3188_; lean_object* v_res_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3202_; 
v_pos_3188_ = lean_ctor_get(v___x_3187_, 0);
v_res_3189_ = lean_ctor_get(v___x_3187_, 1);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3191_ = v___x_3187_;
v_isShared_3192_ = v_isSharedCheck_3202_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_res_3189_);
lean_inc(v_pos_3188_);
lean_dec(v___x_3187_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3202_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3193_; 
v___x_3193_ = l_Std_Http_URI_EncodedFragment_decode(v_res_3189_);
lean_dec(v_res_3189_);
if (lean_obj_tag(v___x_3193_) == 1)
{
lean_object* v_val_3194_; lean_object* v___x_3196_; 
v_val_3194_ = lean_ctor_get(v___x_3193_, 0);
lean_inc(v_val_3194_);
lean_dec_ref_known(v___x_3193_, 1);
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 1, v_val_3194_);
v___x_3196_ = v___x_3191_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_pos_3188_);
lean_ctor_set(v_reuseFailAlloc_3197_, 1, v_val_3194_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
else
{
lean_object* v___x_3198_; lean_object* v___x_3200_; 
lean_dec(v___x_3193_);
v___x_3198_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___closed__1));
if (v_isShared_3192_ == 0)
{
lean_ctor_set_tag(v___x_3191_, 1);
lean_ctor_set(v___x_3191_, 1, v___x_3198_);
v___x_3200_ = v___x_3191_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_pos_3188_);
lean_ctor_set(v_reuseFailAlloc_3201_, 1, v___x_3198_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
}
else
{
lean_object* v_pos_3203_; lean_object* v_err_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3211_; 
v_pos_3203_ = lean_ctor_get(v___x_3187_, 0);
v_err_3204_ = lean_ctor_get(v___x_3187_, 1);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3206_ = v___x_3187_;
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_err_3204_);
lean_inc(v_pos_3203_);
lean_dec(v___x_3187_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3209_; 
if (v_isShared_3207_ == 0)
{
v___x_3209_ = v___x_3206_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_pos_3203_);
lean_ctor_set(v_reuseFailAlloc_3210_, 1, v_err_3204_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___boxed(lean_object* v_config_3212_, lean_object* v_a_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3212_, v_a_3213_);
lean_dec_ref(v_config_3212_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_uri(lean_object* v_config_3215_, lean_object* v_a_3216_){
_start:
{
lean_object* v___x_3217_; 
lean_inc_ref(v_a_3216_);
v___x_3217_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3215_, v_a_3216_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_pos_3218_; lean_object* v_res_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3348_; 
v_pos_3218_ = lean_ctor_get(v___x_3217_, 0);
v_res_3219_ = lean_ctor_get(v___x_3217_, 1);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3221_ = v___x_3217_;
v_isShared_3222_ = v_isSharedCheck_3348_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_res_3219_);
lean_inc(v_pos_3218_);
lean_dec(v___x_3217_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3348_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v_array_3223_; lean_object* v_idx_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3347_; 
v_array_3223_ = lean_ctor_get(v_pos_3218_, 0);
v_idx_3224_ = lean_ctor_get(v_pos_3218_, 1);
v_isSharedCheck_3347_ = !lean_is_exclusive(v_pos_3218_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3226_ = v_pos_3218_;
v_isShared_3227_ = v_isSharedCheck_3347_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_idx_3224_);
lean_inc(v_array_3223_);
lean_dec(v_pos_3218_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3347_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3228_; uint8_t v___x_3229_; 
v___x_3228_ = lean_byte_array_size(v_array_3223_);
v___x_3229_ = lean_nat_dec_lt(v_idx_3224_, v___x_3228_);
if (v___x_3229_ == 0)
{
lean_object* v___x_3230_; lean_object* v___x_3232_; 
lean_del_object(v___x_3226_);
lean_dec(v_idx_3224_);
lean_dec_ref(v_array_3223_);
lean_dec(v_res_3219_);
lean_dec_ref(v_config_3215_);
v___x_3230_ = lean_box(0);
if (v_isShared_3222_ == 0)
{
lean_ctor_set_tag(v___x_3221_, 1);
lean_ctor_set(v___x_3221_, 1, v___x_3230_);
lean_ctor_set(v___x_3221_, 0, v_a_3216_);
v___x_3232_ = v___x_3221_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3216_);
lean_ctor_set(v_reuseFailAlloc_3233_, 1, v___x_3230_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
else
{
uint8_t v___x_3234_; uint8_t v_got_3235_; uint8_t v___x_3236_; 
v___x_3234_ = 58;
v_got_3235_ = lean_byte_array_fget(v_array_3223_, v_idx_3224_);
v___x_3236_ = lean_uint8_dec_eq(v_got_3235_, v___x_3234_);
if (v___x_3236_ == 0)
{
lean_object* v___x_3237_; lean_object* v___x_3239_; 
lean_del_object(v___x_3226_);
lean_dec(v_idx_3224_);
lean_dec_ref(v_array_3223_);
lean_dec(v_res_3219_);
lean_dec_ref(v_config_3215_);
v___x_3237_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_3222_ == 0)
{
lean_ctor_set_tag(v___x_3221_, 1);
lean_ctor_set(v___x_3221_, 1, v___x_3237_);
lean_ctor_set(v___x_3221_, 0, v_a_3216_);
v___x_3239_ = v___x_3221_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3216_);
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
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3244_; 
v___x_3241_ = lean_unsigned_to_nat(1u);
v___x_3242_ = lean_nat_add(v_idx_3224_, v___x_3241_);
lean_dec(v_idx_3224_);
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 1, v___x_3242_);
v___x_3244_ = v___x_3226_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_array_3223_);
lean_ctor_set(v_reuseFailAlloc_3346_, 1, v___x_3242_);
v___x_3244_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
lean_object* v___x_3245_; 
lean_inc_ref(v_config_3215_);
v___x_3245_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_3215_, v___x_3244_);
if (lean_obj_tag(v___x_3245_) == 0)
{
lean_object* v_res_3246_; lean_object* v_pos_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3336_; 
v_res_3246_ = lean_ctor_get(v___x_3245_, 1);
v_pos_3247_ = lean_ctor_get(v___x_3245_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3249_ = v___x_3245_;
v_isShared_3250_ = v_isSharedCheck_3336_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_res_3246_);
lean_inc(v_pos_3247_);
lean_dec(v___x_3245_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3336_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v_fst_3251_; lean_object* v_snd_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3335_; 
v_fst_3251_ = lean_ctor_get(v_res_3246_, 0);
v_snd_3252_ = lean_ctor_get(v_res_3246_, 1);
v_isSharedCheck_3335_ = !lean_is_exclusive(v_res_3246_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3254_ = v_res_3246_;
v_isShared_3255_ = v_isSharedCheck_3335_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_snd_3252_);
lean_inc(v_fst_3251_);
lean_dec(v_res_3246_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3335_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___y_3257_; lean_object* v_pos_3258_; lean_object* v_res_3259_; lean_object* v___y_3266_; lean_object* v_idx_3267_; lean_object* v_pos_3268_; lean_object* v_err_3269_; lean_object* v_pos_3277_; lean_object* v_array_3278_; lean_object* v_idx_3279_; lean_object* v_res_3280_; lean_object* v_array_3298_; lean_object* v_idx_3299_; lean_object* v_pos_3301_; lean_object* v_array_3302_; lean_object* v_idx_3303_; lean_object* v_err_3304_; lean_object* v___x_3308_; uint8_t v___x_3309_; 
v_array_3298_ = lean_ctor_get(v_pos_3247_, 0);
lean_inc_ref(v_array_3298_);
v_idx_3299_ = lean_ctor_get(v_pos_3247_, 1);
lean_inc(v_idx_3299_);
v___x_3308_ = lean_byte_array_size(v_array_3298_);
v___x_3309_ = lean_nat_dec_lt(v_idx_3299_, v___x_3308_);
if (v___x_3309_ == 0)
{
lean_object* v___x_3310_; 
v___x_3310_ = lean_box(0);
lean_inc(v_idx_3299_);
v_pos_3301_ = v_pos_3247_;
v_array_3302_ = v_array_3298_;
v_idx_3303_ = v_idx_3299_;
v_err_3304_ = v___x_3310_;
goto v___jp_3300_;
}
else
{
uint8_t v___x_3311_; uint8_t v_got_3312_; uint8_t v___x_3313_; 
v___x_3311_ = 63;
v_got_3312_ = lean_byte_array_fget(v_array_3298_, v_idx_3299_);
v___x_3313_ = lean_uint8_dec_eq(v_got_3312_, v___x_3311_);
if (v___x_3313_ == 0)
{
lean_object* v___x_3314_; 
v___x_3314_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_3299_);
v_pos_3301_ = v_pos_3247_;
v_array_3302_ = v_array_3298_;
v_idx_3303_ = v_idx_3299_;
v_err_3304_ = v___x_3314_;
goto v___jp_3300_;
}
else
{
lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3332_; 
v_isSharedCheck_3332_ = !lean_is_exclusive(v_pos_3247_);
if (v_isSharedCheck_3332_ == 0)
{
lean_object* v_unused_3333_; lean_object* v_unused_3334_; 
v_unused_3333_ = lean_ctor_get(v_pos_3247_, 1);
lean_dec(v_unused_3333_);
v_unused_3334_ = lean_ctor_get(v_pos_3247_, 0);
lean_dec(v_unused_3334_);
v___x_3316_ = v_pos_3247_;
v_isShared_3317_ = v_isSharedCheck_3332_;
goto v_resetjp_3315_;
}
else
{
lean_dec(v_pos_3247_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3332_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v___x_3318_; lean_object* v___x_3320_; 
v___x_3318_ = lean_nat_add(v_idx_3299_, v___x_3241_);
if (v_isShared_3317_ == 0)
{
lean_ctor_set(v___x_3316_, 1, v___x_3318_);
v___x_3320_ = v___x_3316_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_array_3298_);
lean_ctor_set(v_reuseFailAlloc_3331_, 1, v___x_3318_);
v___x_3320_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
lean_object* v___x_3321_; 
lean_inc_ref(v_config_3215_);
v___x_3321_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3215_, v___x_3320_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_object* v_pos_3322_; lean_object* v_res_3323_; lean_object* v_array_3324_; lean_object* v_idx_3325_; lean_object* v___x_3326_; 
lean_dec(v_idx_3299_);
v_pos_3322_ = lean_ctor_get(v___x_3321_, 0);
lean_inc(v_pos_3322_);
v_res_3323_ = lean_ctor_get(v___x_3321_, 1);
lean_inc(v_res_3323_);
lean_dec_ref_known(v___x_3321_, 2);
v_array_3324_ = lean_ctor_get(v_pos_3322_, 0);
lean_inc_ref(v_array_3324_);
v_idx_3325_ = lean_ctor_get(v_pos_3322_, 1);
lean_inc(v_idx_3325_);
v___x_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3326_, 0, v_res_3323_);
v_pos_3277_ = v_pos_3322_;
v_array_3278_ = v_array_3324_;
v_idx_3279_ = v_idx_3325_;
v_res_3280_ = v___x_3326_;
goto v___jp_3276_;
}
else
{
lean_object* v_pos_3327_; lean_object* v_err_3328_; lean_object* v_array_3329_; lean_object* v_idx_3330_; 
v_pos_3327_ = lean_ctor_get(v___x_3321_, 0);
lean_inc(v_pos_3327_);
v_err_3328_ = lean_ctor_get(v___x_3321_, 1);
lean_inc(v_err_3328_);
lean_dec_ref_known(v___x_3321_, 2);
v_array_3329_ = lean_ctor_get(v_pos_3327_, 0);
lean_inc_ref(v_array_3329_);
v_idx_3330_ = lean_ctor_get(v_pos_3327_, 1);
lean_inc(v_idx_3330_);
v_pos_3301_ = v_pos_3327_;
v_array_3302_ = v_array_3329_;
v_idx_3303_ = v_idx_3330_;
v_err_3304_ = v_err_3328_;
goto v___jp_3300_;
}
}
}
}
}
v___jp_3256_:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3263_; 
v___x_3260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3260_, 0, v_res_3219_);
lean_ctor_set(v___x_3260_, 1, v_fst_3251_);
lean_ctor_set(v___x_3260_, 2, v_snd_3252_);
lean_ctor_set(v___x_3260_, 3, v___y_3257_);
lean_ctor_set(v___x_3260_, 4, v_res_3259_);
v___x_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3260_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 1, v___x_3261_);
lean_ctor_set(v___x_3249_, 0, v_pos_3258_);
v___x_3263_ = v___x_3249_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_pos_3258_);
lean_ctor_set(v_reuseFailAlloc_3264_, 1, v___x_3261_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
v___jp_3265_:
{
lean_object* v_idx_3270_; uint8_t v___x_3271_; 
v_idx_3270_ = lean_ctor_get(v_pos_3268_, 1);
v___x_3271_ = lean_nat_dec_eq(v_idx_3267_, v_idx_3270_);
lean_dec(v_idx_3267_);
if (v___x_3271_ == 0)
{
lean_object* v___x_3273_; 
lean_dec_ref(v_pos_3268_);
lean_dec(v___y_3266_);
lean_dec(v_snd_3252_);
lean_dec(v_fst_3251_);
lean_del_object(v___x_3249_);
lean_dec(v_res_3219_);
if (v_isShared_3222_ == 0)
{
lean_ctor_set_tag(v___x_3221_, 1);
lean_ctor_set(v___x_3221_, 1, v_err_3269_);
lean_ctor_set(v___x_3221_, 0, v_a_3216_);
v___x_3273_ = v___x_3221_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_a_3216_);
lean_ctor_set(v_reuseFailAlloc_3274_, 1, v_err_3269_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
else
{
lean_object* v___x_3275_; 
lean_dec(v_err_3269_);
lean_del_object(v___x_3221_);
lean_dec_ref(v_a_3216_);
v___x_3275_ = lean_box(0);
v___y_3257_ = v___y_3266_;
v_pos_3258_ = v_pos_3268_;
v_res_3259_ = v___x_3275_;
goto v___jp_3256_;
}
}
v___jp_3276_:
{
lean_object* v___x_3281_; uint8_t v___x_3282_; 
v___x_3281_ = lean_byte_array_size(v_array_3278_);
v___x_3282_ = lean_nat_dec_lt(v_idx_3279_, v___x_3281_);
if (v___x_3282_ == 0)
{
lean_object* v___x_3283_; 
lean_dec_ref(v_array_3278_);
lean_del_object(v___x_3254_);
lean_dec_ref(v_config_3215_);
v___x_3283_ = lean_box(0);
v___y_3266_ = v_res_3280_;
v_idx_3267_ = v_idx_3279_;
v_pos_3268_ = v_pos_3277_;
v_err_3269_ = v___x_3283_;
goto v___jp_3265_;
}
else
{
uint8_t v___x_3284_; uint8_t v_got_3285_; uint8_t v___x_3286_; 
v___x_3284_ = 35;
v_got_3285_ = lean_byte_array_fget(v_array_3278_, v_idx_3279_);
v___x_3286_ = lean_uint8_dec_eq(v_got_3285_, v___x_3284_);
if (v___x_3286_ == 0)
{
lean_object* v___x_3287_; 
lean_dec_ref(v_array_3278_);
lean_del_object(v___x_3254_);
lean_dec_ref(v_config_3215_);
v___x_3287_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v___y_3266_ = v_res_3280_;
v_idx_3267_ = v_idx_3279_;
v_pos_3268_ = v_pos_3277_;
v_err_3269_ = v___x_3287_;
goto v___jp_3265_;
}
else
{
lean_object* v___x_3288_; lean_object* v___x_3290_; 
lean_dec_ref(v_pos_3277_);
v___x_3288_ = lean_nat_add(v_idx_3279_, v___x_3241_);
if (v_isShared_3255_ == 0)
{
lean_ctor_set(v___x_3254_, 1, v___x_3288_);
lean_ctor_set(v___x_3254_, 0, v_array_3278_);
v___x_3290_ = v___x_3254_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_array_3278_);
lean_ctor_set(v_reuseFailAlloc_3297_, 1, v___x_3288_);
v___x_3290_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
lean_object* v___x_3291_; 
v___x_3291_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3215_, v___x_3290_);
lean_dec_ref(v_config_3215_);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_object* v_pos_3292_; lean_object* v_res_3293_; lean_object* v___x_3294_; 
lean_dec(v_idx_3279_);
lean_del_object(v___x_3221_);
lean_dec_ref(v_a_3216_);
v_pos_3292_ = lean_ctor_get(v___x_3291_, 0);
lean_inc(v_pos_3292_);
v_res_3293_ = lean_ctor_get(v___x_3291_, 1);
lean_inc(v_res_3293_);
lean_dec_ref_known(v___x_3291_, 2);
v___x_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3294_, 0, v_res_3293_);
v___y_3257_ = v_res_3280_;
v_pos_3258_ = v_pos_3292_;
v_res_3259_ = v___x_3294_;
goto v___jp_3256_;
}
else
{
lean_object* v_pos_3295_; lean_object* v_err_3296_; 
v_pos_3295_ = lean_ctor_get(v___x_3291_, 0);
lean_inc(v_pos_3295_);
v_err_3296_ = lean_ctor_get(v___x_3291_, 1);
lean_inc(v_err_3296_);
lean_dec_ref_known(v___x_3291_, 2);
v___y_3266_ = v_res_3280_;
v_idx_3267_ = v_idx_3279_;
v_pos_3268_ = v_pos_3295_;
v_err_3269_ = v_err_3296_;
goto v___jp_3265_;
}
}
}
}
}
v___jp_3300_:
{
uint8_t v___x_3305_; 
v___x_3305_ = lean_nat_dec_eq(v_idx_3299_, v_idx_3303_);
lean_dec(v_idx_3299_);
if (v___x_3305_ == 0)
{
lean_object* v___x_3306_; 
lean_dec(v_idx_3303_);
lean_dec_ref(v_array_3302_);
lean_dec_ref(v_pos_3301_);
lean_del_object(v___x_3254_);
lean_dec(v_snd_3252_);
lean_dec(v_fst_3251_);
lean_del_object(v___x_3249_);
lean_del_object(v___x_3221_);
lean_dec(v_res_3219_);
lean_dec_ref(v_config_3215_);
v___x_3306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3306_, 0, v_a_3216_);
lean_ctor_set(v___x_3306_, 1, v_err_3304_);
return v___x_3306_;
}
else
{
lean_object* v___x_3307_; 
lean_dec(v_err_3304_);
v___x_3307_ = lean_box(0);
v_pos_3277_ = v_pos_3301_;
v_array_3278_ = v_array_3302_;
v_idx_3279_ = v_idx_3303_;
v_res_3280_ = v___x_3307_;
goto v___jp_3276_;
}
}
}
}
}
else
{
lean_object* v_err_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3344_; 
lean_del_object(v___x_3221_);
lean_dec(v_res_3219_);
lean_dec_ref(v_config_3215_);
v_err_3337_ = lean_ctor_get(v___x_3245_, 1);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3344_ == 0)
{
lean_object* v_unused_3345_; 
v_unused_3345_ = lean_ctor_get(v___x_3245_, 0);
lean_dec(v_unused_3345_);
v___x_3339_ = v___x_3245_;
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_err_3337_);
lean_dec(v___x_3245_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3342_; 
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 0, v_a_3216_);
v___x_3342_ = v___x_3339_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3216_);
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
}
}
}
}
else
{
lean_object* v_err_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
lean_dec_ref(v_config_3215_);
v_err_3349_ = lean_ctor_get(v___x_3217_, 1);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3356_ == 0)
{
lean_object* v_unused_3357_; 
v_unused_3357_ = lean_ctor_get(v___x_3217_, 0);
lean_dec(v_unused_3357_);
v___x_3351_ = v___x_3217_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_err_3349_);
lean_dec(v___x_3217_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3354_; 
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 0, v_a_3216_);
v___x_3354_ = v___x_3351_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3216_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v_err_3349_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withAuthority(lean_object* v_config_3358_, lean_object* v_a_3359_){
_start:
{
lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v_pos_3364_; lean_object* v_res_3365_; lean_object* v_idx_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v_pos_3374_; lean_object* v_err_3375_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v_pos_3391_; lean_object* v_array_3392_; lean_object* v_idx_3393_; lean_object* v_res_3394_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v_idx_3414_; lean_object* v_pos_3415_; lean_object* v_array_3416_; lean_object* v_idx_3417_; lean_object* v_err_3418_; lean_object* v_pos_3423_; lean_object* v_utf8_3479_; lean_object* v___x_3480_; 
v_utf8_3479_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1);
lean_inc_ref(v_a_3359_);
v___x_3480_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_3479_, v_a_3359_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_pos_3481_; 
v_pos_3481_ = lean_ctor_get(v___x_3480_, 0);
lean_inc(v_pos_3481_);
lean_dec_ref_known(v___x_3480_, 2);
v_pos_3423_ = v_pos_3481_;
goto v___jp_3422_;
}
else
{
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_pos_3482_; 
v_pos_3482_ = lean_ctor_get(v___x_3480_, 0);
lean_inc(v_pos_3482_);
lean_dec_ref_known(v___x_3480_, 2);
v_pos_3423_ = v_pos_3482_;
goto v___jp_3422_;
}
else
{
lean_object* v_err_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
lean_dec_ref(v_config_3358_);
v_err_3483_ = lean_ctor_get(v___x_3480_, 1);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3490_ == 0)
{
lean_object* v_unused_3491_; 
v_unused_3491_ = lean_ctor_get(v___x_3480_, 0);
lean_dec(v_unused_3491_);
v___x_3485_ = v___x_3480_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_err_3483_);
lean_dec(v___x_3480_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 0, v_a_3359_);
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3359_);
lean_ctor_set(v_reuseFailAlloc_3489_, 1, v_err_3483_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
v___jp_3360_:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3366_, 0, v___y_3361_);
v___x_3367_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3366_);
lean_ctor_set(v___x_3367_, 1, v___y_3363_);
lean_ctor_set(v___x_3367_, 2, v___y_3362_);
lean_ctor_set(v___x_3367_, 3, v_res_3365_);
v___x_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3368_, 0, v_pos_3364_);
lean_ctor_set(v___x_3368_, 1, v___x_3367_);
return v___x_3368_;
}
v___jp_3369_:
{
lean_object* v_idx_3376_; uint8_t v___x_3377_; 
v_idx_3376_ = lean_ctor_get(v_pos_3374_, 1);
v___x_3377_ = lean_nat_dec_eq(v_idx_3370_, v_idx_3376_);
lean_dec(v_idx_3370_);
if (v___x_3377_ == 0)
{
lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
v_isSharedCheck_3384_ = !lean_is_exclusive(v_pos_3374_);
if (v_isSharedCheck_3384_ == 0)
{
lean_object* v_unused_3385_; lean_object* v_unused_3386_; 
v_unused_3385_ = lean_ctor_get(v_pos_3374_, 1);
lean_dec(v_unused_3385_);
v_unused_3386_ = lean_ctor_get(v_pos_3374_, 0);
lean_dec(v_unused_3386_);
v___x_3379_ = v_pos_3374_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_dec(v_pos_3374_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
lean_ctor_set_tag(v___x_3379_, 1);
lean_ctor_set(v___x_3379_, 1, v_err_3375_);
lean_ctor_set(v___x_3379_, 0, v_a_3359_);
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3359_);
lean_ctor_set(v_reuseFailAlloc_3383_, 1, v_err_3375_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
else
{
lean_object* v___x_3387_; 
lean_dec(v_err_3375_);
lean_dec_ref(v_a_3359_);
v___x_3387_ = lean_box(0);
v___y_3361_ = v___y_3371_;
v___y_3362_ = v___y_3372_;
v___y_3363_ = v___y_3373_;
v_pos_3364_ = v_pos_3374_;
v_res_3365_ = v___x_3387_;
goto v___jp_3360_;
}
}
v___jp_3388_:
{
lean_object* v___x_3395_; uint8_t v___x_3396_; 
v___x_3395_ = lean_byte_array_size(v_array_3392_);
v___x_3396_ = lean_nat_dec_lt(v_idx_3393_, v___x_3395_);
if (v___x_3396_ == 0)
{
lean_object* v___x_3397_; 
lean_dec_ref(v_array_3392_);
lean_dec_ref(v_config_3358_);
v___x_3397_ = lean_box(0);
v_idx_3370_ = v_idx_3393_;
v___y_3371_ = v___y_3389_;
v___y_3372_ = v_res_3394_;
v___y_3373_ = v___y_3390_;
v_pos_3374_ = v_pos_3391_;
v_err_3375_ = v___x_3397_;
goto v___jp_3369_;
}
else
{
uint8_t v___x_3398_; uint8_t v_got_3399_; uint8_t v___x_3400_; 
v___x_3398_ = 35;
v_got_3399_ = lean_byte_array_fget(v_array_3392_, v_idx_3393_);
v___x_3400_ = lean_uint8_dec_eq(v_got_3399_, v___x_3398_);
if (v___x_3400_ == 0)
{
lean_object* v___x_3401_; 
lean_dec_ref(v_array_3392_);
lean_dec_ref(v_config_3358_);
v___x_3401_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v_idx_3370_ = v_idx_3393_;
v___y_3371_ = v___y_3389_;
v___y_3372_ = v_res_3394_;
v___y_3373_ = v___y_3390_;
v_pos_3374_ = v_pos_3391_;
v_err_3375_ = v___x_3401_;
goto v___jp_3369_;
}
else
{
lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
lean_dec_ref(v_pos_3391_);
v___x_3402_ = lean_unsigned_to_nat(1u);
v___x_3403_ = lean_nat_add(v_idx_3393_, v___x_3402_);
v___x_3404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3404_, 0, v_array_3392_);
lean_ctor_set(v___x_3404_, 1, v___x_3403_);
v___x_3405_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3358_, v___x_3404_);
lean_dec_ref(v_config_3358_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_pos_3406_; lean_object* v_res_3407_; lean_object* v___x_3408_; 
lean_dec(v_idx_3393_);
lean_dec_ref(v_a_3359_);
v_pos_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_pos_3406_);
v_res_3407_ = lean_ctor_get(v___x_3405_, 1);
lean_inc(v_res_3407_);
lean_dec_ref_known(v___x_3405_, 2);
v___x_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3408_, 0, v_res_3407_);
v___y_3361_ = v___y_3389_;
v___y_3362_ = v_res_3394_;
v___y_3363_ = v___y_3390_;
v_pos_3364_ = v_pos_3406_;
v_res_3365_ = v___x_3408_;
goto v___jp_3360_;
}
else
{
lean_object* v_pos_3409_; lean_object* v_err_3410_; 
v_pos_3409_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_pos_3409_);
v_err_3410_ = lean_ctor_get(v___x_3405_, 1);
lean_inc(v_err_3410_);
lean_dec_ref_known(v___x_3405_, 2);
v_idx_3370_ = v_idx_3393_;
v___y_3371_ = v___y_3389_;
v___y_3372_ = v_res_3394_;
v___y_3373_ = v___y_3390_;
v_pos_3374_ = v_pos_3409_;
v_err_3375_ = v_err_3410_;
goto v___jp_3369_;
}
}
}
}
v___jp_3411_:
{
uint8_t v___x_3419_; 
v___x_3419_ = lean_nat_dec_eq(v_idx_3414_, v_idx_3417_);
lean_dec(v_idx_3414_);
if (v___x_3419_ == 0)
{
lean_object* v___x_3420_; 
lean_dec(v_idx_3417_);
lean_dec_ref(v_array_3416_);
lean_dec_ref(v_pos_3415_);
lean_dec_ref(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec_ref(v_config_3358_);
v___x_3420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3420_, 0, v_a_3359_);
lean_ctor_set(v___x_3420_, 1, v_err_3418_);
return v___x_3420_;
}
else
{
lean_object* v___x_3421_; 
lean_dec(v_err_3418_);
v___x_3421_ = lean_box(0);
v___y_3389_ = v___y_3412_;
v___y_3390_ = v___y_3413_;
v_pos_3391_ = v_pos_3415_;
v_array_3392_ = v_array_3416_;
v_idx_3393_ = v_idx_3417_;
v_res_3394_ = v___x_3421_;
goto v___jp_3388_;
}
}
v___jp_3422_:
{
lean_object* v___x_3424_; 
v___x_3424_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_3358_, v_pos_3423_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v_pos_3425_; lean_object* v_res_3426_; uint8_t v___x_3427_; lean_object* v___x_3428_; 
v_pos_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_pos_3425_);
v_res_3426_ = lean_ctor_get(v___x_3424_, 1);
lean_inc(v_res_3426_);
lean_dec_ref_known(v___x_3424_, 2);
v___x_3427_ = 1;
lean_inc_ref(v_config_3358_);
v___x_3428_ = l_Std_Http_URI_Parser_parsePath(v_config_3358_, v___x_3427_, v___x_3427_, v_pos_3425_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_pos_3429_; lean_object* v_res_3430_; lean_object* v_array_3431_; lean_object* v_idx_3432_; lean_object* v___x_3433_; uint8_t v___x_3434_; 
v_pos_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_pos_3429_);
v_res_3430_ = lean_ctor_get(v___x_3428_, 1);
lean_inc(v_res_3430_);
lean_dec_ref_known(v___x_3428_, 2);
v_array_3431_ = lean_ctor_get(v_pos_3429_, 0);
lean_inc_ref(v_array_3431_);
v_idx_3432_ = lean_ctor_get(v_pos_3429_, 1);
lean_inc(v_idx_3432_);
v___x_3433_ = lean_byte_array_size(v_array_3431_);
v___x_3434_ = lean_nat_dec_lt(v_idx_3432_, v___x_3433_);
if (v___x_3434_ == 0)
{
lean_object* v___x_3435_; 
v___x_3435_ = lean_box(0);
lean_inc(v_idx_3432_);
v___y_3412_ = v_res_3426_;
v___y_3413_ = v_res_3430_;
v_idx_3414_ = v_idx_3432_;
v_pos_3415_ = v_pos_3429_;
v_array_3416_ = v_array_3431_;
v_idx_3417_ = v_idx_3432_;
v_err_3418_ = v___x_3435_;
goto v___jp_3411_;
}
else
{
uint8_t v___x_3436_; uint8_t v_got_3437_; uint8_t v___x_3438_; 
v___x_3436_ = 63;
v_got_3437_ = lean_byte_array_fget(v_array_3431_, v_idx_3432_);
v___x_3438_ = lean_uint8_dec_eq(v_got_3437_, v___x_3436_);
if (v___x_3438_ == 0)
{
lean_object* v___x_3439_; 
v___x_3439_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_3432_);
v___y_3412_ = v_res_3426_;
v___y_3413_ = v_res_3430_;
v_idx_3414_ = v_idx_3432_;
v_pos_3415_ = v_pos_3429_;
v_array_3416_ = v_array_3431_;
v_idx_3417_ = v_idx_3432_;
v_err_3418_ = v___x_3439_;
goto v___jp_3411_;
}
else
{
lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3458_; 
v_isSharedCheck_3458_ = !lean_is_exclusive(v_pos_3429_);
if (v_isSharedCheck_3458_ == 0)
{
lean_object* v_unused_3459_; lean_object* v_unused_3460_; 
v_unused_3459_ = lean_ctor_get(v_pos_3429_, 1);
lean_dec(v_unused_3459_);
v_unused_3460_ = lean_ctor_get(v_pos_3429_, 0);
lean_dec(v_unused_3460_);
v___x_3441_ = v_pos_3429_;
v_isShared_3442_ = v_isSharedCheck_3458_;
goto v_resetjp_3440_;
}
else
{
lean_dec(v_pos_3429_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3458_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3446_; 
v___x_3443_ = lean_unsigned_to_nat(1u);
v___x_3444_ = lean_nat_add(v_idx_3432_, v___x_3443_);
if (v_isShared_3442_ == 0)
{
lean_ctor_set(v___x_3441_, 1, v___x_3444_);
v___x_3446_ = v___x_3441_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_array_3431_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v___x_3444_);
v___x_3446_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
lean_object* v___x_3447_; 
lean_inc_ref(v_config_3358_);
v___x_3447_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3358_, v___x_3446_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v_pos_3448_; lean_object* v_res_3449_; lean_object* v_array_3450_; lean_object* v_idx_3451_; lean_object* v___x_3452_; 
lean_dec(v_idx_3432_);
v_pos_3448_ = lean_ctor_get(v___x_3447_, 0);
lean_inc(v_pos_3448_);
v_res_3449_ = lean_ctor_get(v___x_3447_, 1);
lean_inc(v_res_3449_);
lean_dec_ref_known(v___x_3447_, 2);
v_array_3450_ = lean_ctor_get(v_pos_3448_, 0);
lean_inc_ref(v_array_3450_);
v_idx_3451_ = lean_ctor_get(v_pos_3448_, 1);
lean_inc(v_idx_3451_);
v___x_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3452_, 0, v_res_3449_);
v___y_3389_ = v_res_3426_;
v___y_3390_ = v_res_3430_;
v_pos_3391_ = v_pos_3448_;
v_array_3392_ = v_array_3450_;
v_idx_3393_ = v_idx_3451_;
v_res_3394_ = v___x_3452_;
goto v___jp_3388_;
}
else
{
lean_object* v_pos_3453_; lean_object* v_err_3454_; lean_object* v_array_3455_; lean_object* v_idx_3456_; 
v_pos_3453_ = lean_ctor_get(v___x_3447_, 0);
lean_inc(v_pos_3453_);
v_err_3454_ = lean_ctor_get(v___x_3447_, 1);
lean_inc(v_err_3454_);
lean_dec_ref_known(v___x_3447_, 2);
v_array_3455_ = lean_ctor_get(v_pos_3453_, 0);
lean_inc_ref(v_array_3455_);
v_idx_3456_ = lean_ctor_get(v_pos_3453_, 1);
lean_inc(v_idx_3456_);
v___y_3412_ = v_res_3426_;
v___y_3413_ = v_res_3430_;
v_idx_3414_ = v_idx_3432_;
v_pos_3415_ = v_pos_3453_;
v_array_3416_ = v_array_3455_;
v_idx_3417_ = v_idx_3456_;
v_err_3418_ = v_err_3454_;
goto v___jp_3411_;
}
}
}
}
}
}
else
{
lean_object* v_err_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3468_; 
lean_dec(v_res_3426_);
lean_dec_ref(v_config_3358_);
v_err_3461_ = lean_ctor_get(v___x_3428_, 1);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3468_ == 0)
{
lean_object* v_unused_3469_; 
v_unused_3469_ = lean_ctor_get(v___x_3428_, 0);
lean_dec(v_unused_3469_);
v___x_3463_ = v___x_3428_;
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_err_3461_);
lean_dec(v___x_3428_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3466_; 
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 0, v_a_3359_);
v___x_3466_ = v___x_3463_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3359_);
lean_ctor_set(v_reuseFailAlloc_3467_, 1, v_err_3461_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
}
else
{
lean_object* v_err_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3477_; 
lean_dec_ref(v_config_3358_);
v_err_3470_ = lean_ctor_get(v___x_3424_, 1);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3477_ == 0)
{
lean_object* v_unused_3478_; 
v_unused_3478_ = lean_ctor_get(v___x_3424_, 0);
lean_dec(v_unused_3478_);
v___x_3472_ = v___x_3424_;
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_err_3470_);
lean_dec(v___x_3424_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3475_; 
if (v_isShared_3473_ == 0)
{
lean_ctor_set(v___x_3472_, 0, v_a_3359_);
v___x_3475_ = v___x_3472_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3359_);
lean_ctor_set(v_reuseFailAlloc_3476_, 1, v_err_3470_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath(lean_object* v_config_3492_, lean_object* v_a_3493_){
_start:
{
uint8_t v___x_3494_; uint8_t v___x_3495_; lean_object* v___x_3496_; 
v___x_3494_ = 0;
v___x_3495_ = 1;
lean_inc_ref(v_config_3492_);
v___x_3496_ = l_Std_Http_URI_Parser_parsePath(v_config_3492_, v___x_3494_, v___x_3495_, v_a_3493_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_pos_3497_; lean_object* v_res_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3579_; 
v_pos_3497_ = lean_ctor_get(v___x_3496_, 0);
v_res_3498_ = lean_ctor_get(v___x_3496_, 1);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3500_ = v___x_3496_;
v_isShared_3501_ = v_isSharedCheck_3579_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_res_3498_);
lean_inc(v_pos_3497_);
lean_dec(v___x_3496_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3579_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___y_3503_; lean_object* v_pos_3504_; lean_object* v_res_3505_; lean_object* v_idx_3512_; lean_object* v___y_3513_; lean_object* v_pos_3514_; lean_object* v_err_3515_; lean_object* v_pos_3521_; lean_object* v_array_3522_; lean_object* v_idx_3523_; lean_object* v_res_3524_; lean_object* v_array_3541_; lean_object* v_idx_3542_; lean_object* v_pos_3544_; lean_object* v_array_3545_; lean_object* v_idx_3546_; lean_object* v_err_3547_; lean_object* v___x_3551_; uint8_t v___x_3552_; 
v_array_3541_ = lean_ctor_get(v_pos_3497_, 0);
lean_inc_ref(v_array_3541_);
v_idx_3542_ = lean_ctor_get(v_pos_3497_, 1);
lean_inc(v_idx_3542_);
v___x_3551_ = lean_byte_array_size(v_array_3541_);
v___x_3552_ = lean_nat_dec_lt(v_idx_3542_, v___x_3551_);
if (v___x_3552_ == 0)
{
lean_object* v___x_3553_; 
v___x_3553_ = lean_box(0);
lean_inc(v_idx_3542_);
v_pos_3544_ = v_pos_3497_;
v_array_3545_ = v_array_3541_;
v_idx_3546_ = v_idx_3542_;
v_err_3547_ = v___x_3553_;
goto v___jp_3543_;
}
else
{
uint8_t v___x_3554_; uint8_t v_got_3555_; uint8_t v___x_3556_; 
v___x_3554_ = 63;
v_got_3555_ = lean_byte_array_fget(v_array_3541_, v_idx_3542_);
v___x_3556_ = lean_uint8_dec_eq(v_got_3555_, v___x_3554_);
if (v___x_3556_ == 0)
{
lean_object* v___x_3557_; 
v___x_3557_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_3542_);
v_pos_3544_ = v_pos_3497_;
v_array_3545_ = v_array_3541_;
v_idx_3546_ = v_idx_3542_;
v_err_3547_ = v___x_3557_;
goto v___jp_3543_;
}
else
{
lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3576_; 
v_isSharedCheck_3576_ = !lean_is_exclusive(v_pos_3497_);
if (v_isSharedCheck_3576_ == 0)
{
lean_object* v_unused_3577_; lean_object* v_unused_3578_; 
v_unused_3577_ = lean_ctor_get(v_pos_3497_, 1);
lean_dec(v_unused_3577_);
v_unused_3578_ = lean_ctor_get(v_pos_3497_, 0);
lean_dec(v_unused_3578_);
v___x_3559_ = v_pos_3497_;
v_isShared_3560_ = v_isSharedCheck_3576_;
goto v_resetjp_3558_;
}
else
{
lean_dec(v_pos_3497_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3576_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3564_; 
v___x_3561_ = lean_unsigned_to_nat(1u);
v___x_3562_ = lean_nat_add(v_idx_3542_, v___x_3561_);
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 1, v___x_3562_);
v___x_3564_ = v___x_3559_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_array_3541_);
lean_ctor_set(v_reuseFailAlloc_3575_, 1, v___x_3562_);
v___x_3564_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
lean_object* v___x_3565_; 
lean_inc_ref(v_config_3492_);
v___x_3565_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3492_, v___x_3564_);
if (lean_obj_tag(v___x_3565_) == 0)
{
lean_object* v_pos_3566_; lean_object* v_res_3567_; lean_object* v_array_3568_; lean_object* v_idx_3569_; lean_object* v___x_3570_; 
lean_dec(v_idx_3542_);
v_pos_3566_ = lean_ctor_get(v___x_3565_, 0);
lean_inc(v_pos_3566_);
v_res_3567_ = lean_ctor_get(v___x_3565_, 1);
lean_inc(v_res_3567_);
lean_dec_ref_known(v___x_3565_, 2);
v_array_3568_ = lean_ctor_get(v_pos_3566_, 0);
lean_inc_ref(v_array_3568_);
v_idx_3569_ = lean_ctor_get(v_pos_3566_, 1);
lean_inc(v_idx_3569_);
v___x_3570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3570_, 0, v_res_3567_);
v_pos_3521_ = v_pos_3566_;
v_array_3522_ = v_array_3568_;
v_idx_3523_ = v_idx_3569_;
v_res_3524_ = v___x_3570_;
goto v___jp_3520_;
}
else
{
lean_object* v_pos_3571_; lean_object* v_err_3572_; lean_object* v_array_3573_; lean_object* v_idx_3574_; 
v_pos_3571_ = lean_ctor_get(v___x_3565_, 0);
lean_inc(v_pos_3571_);
v_err_3572_ = lean_ctor_get(v___x_3565_, 1);
lean_inc(v_err_3572_);
lean_dec_ref_known(v___x_3565_, 2);
v_array_3573_ = lean_ctor_get(v_pos_3571_, 0);
lean_inc_ref(v_array_3573_);
v_idx_3574_ = lean_ctor_get(v_pos_3571_, 1);
lean_inc(v_idx_3574_);
v_pos_3544_ = v_pos_3571_;
v_array_3545_ = v_array_3573_;
v_idx_3546_ = v_idx_3574_;
v_err_3547_ = v_err_3572_;
goto v___jp_3543_;
}
}
}
}
}
v___jp_3502_:
{
lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3509_; 
v___x_3506_ = lean_box(0);
v___x_3507_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3506_);
lean_ctor_set(v___x_3507_, 1, v_res_3498_);
lean_ctor_set(v___x_3507_, 2, v___y_3503_);
lean_ctor_set(v___x_3507_, 3, v_res_3505_);
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 1, v___x_3507_);
lean_ctor_set(v___x_3500_, 0, v_pos_3504_);
v___x_3509_ = v___x_3500_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_pos_3504_);
lean_ctor_set(v_reuseFailAlloc_3510_, 1, v___x_3507_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
v___jp_3511_:
{
lean_object* v_idx_3516_; uint8_t v___x_3517_; 
v_idx_3516_ = lean_ctor_get(v_pos_3514_, 1);
v___x_3517_ = lean_nat_dec_eq(v_idx_3512_, v_idx_3516_);
lean_dec(v_idx_3512_);
if (v___x_3517_ == 0)
{
lean_object* v___x_3518_; 
lean_dec(v___y_3513_);
lean_del_object(v___x_3500_);
lean_dec(v_res_3498_);
v___x_3518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3518_, 0, v_pos_3514_);
lean_ctor_set(v___x_3518_, 1, v_err_3515_);
return v___x_3518_;
}
else
{
lean_object* v___x_3519_; 
lean_dec(v_err_3515_);
v___x_3519_ = lean_box(0);
v___y_3503_ = v___y_3513_;
v_pos_3504_ = v_pos_3514_;
v_res_3505_ = v___x_3519_;
goto v___jp_3502_;
}
}
v___jp_3520_:
{
lean_object* v___x_3525_; uint8_t v___x_3526_; 
v___x_3525_ = lean_byte_array_size(v_array_3522_);
v___x_3526_ = lean_nat_dec_lt(v_idx_3523_, v___x_3525_);
if (v___x_3526_ == 0)
{
lean_object* v___x_3527_; 
lean_dec_ref(v_array_3522_);
lean_dec_ref(v_config_3492_);
v___x_3527_ = lean_box(0);
v_idx_3512_ = v_idx_3523_;
v___y_3513_ = v_res_3524_;
v_pos_3514_ = v_pos_3521_;
v_err_3515_ = v___x_3527_;
goto v___jp_3511_;
}
else
{
uint8_t v___x_3528_; uint8_t v_got_3529_; uint8_t v___x_3530_; 
v___x_3528_ = 35;
v_got_3529_ = lean_byte_array_fget(v_array_3522_, v_idx_3523_);
v___x_3530_ = lean_uint8_dec_eq(v_got_3529_, v___x_3528_);
if (v___x_3530_ == 0)
{
lean_object* v___x_3531_; 
lean_dec_ref(v_array_3522_);
lean_dec_ref(v_config_3492_);
v___x_3531_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v_idx_3512_ = v_idx_3523_;
v___y_3513_ = v_res_3524_;
v_pos_3514_ = v_pos_3521_;
v_err_3515_ = v___x_3531_;
goto v___jp_3511_;
}
else
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
lean_dec_ref(v_pos_3521_);
v___x_3532_ = lean_unsigned_to_nat(1u);
v___x_3533_ = lean_nat_add(v_idx_3523_, v___x_3532_);
v___x_3534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3534_, 0, v_array_3522_);
lean_ctor_set(v___x_3534_, 1, v___x_3533_);
v___x_3535_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3492_, v___x_3534_);
lean_dec_ref(v_config_3492_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_pos_3536_; lean_object* v_res_3537_; lean_object* v___x_3538_; 
lean_dec(v_idx_3523_);
v_pos_3536_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_pos_3536_);
v_res_3537_ = lean_ctor_get(v___x_3535_, 1);
lean_inc(v_res_3537_);
lean_dec_ref_known(v___x_3535_, 2);
v___x_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3538_, 0, v_res_3537_);
v___y_3503_ = v_res_3524_;
v_pos_3504_ = v_pos_3536_;
v_res_3505_ = v___x_3538_;
goto v___jp_3502_;
}
else
{
lean_object* v_pos_3539_; lean_object* v_err_3540_; 
v_pos_3539_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_pos_3539_);
v_err_3540_ = lean_ctor_get(v___x_3535_, 1);
lean_inc(v_err_3540_);
lean_dec_ref_known(v___x_3535_, 2);
v_idx_3512_ = v_idx_3523_;
v___y_3513_ = v_res_3524_;
v_pos_3514_ = v_pos_3539_;
v_err_3515_ = v_err_3540_;
goto v___jp_3511_;
}
}
}
}
v___jp_3543_:
{
uint8_t v___x_3548_; 
v___x_3548_ = lean_nat_dec_eq(v_idx_3542_, v_idx_3546_);
lean_dec(v_idx_3542_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3549_; 
lean_dec(v_idx_3546_);
lean_dec_ref(v_array_3545_);
lean_del_object(v___x_3500_);
lean_dec(v_res_3498_);
lean_dec_ref(v_config_3492_);
v___x_3549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3549_, 0, v_pos_3544_);
lean_ctor_set(v___x_3549_, 1, v_err_3547_);
return v___x_3549_;
}
else
{
lean_object* v___x_3550_; 
lean_dec(v_err_3547_);
v___x_3550_ = lean_box(0);
v_pos_3521_ = v_pos_3544_;
v_array_3522_ = v_array_3545_;
v_idx_3523_ = v_idx_3546_;
v_res_3524_ = v___x_3550_;
goto v___jp_3520_;
}
}
}
}
else
{
lean_object* v_pos_3580_; lean_object* v_err_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3588_; 
lean_dec_ref(v_config_3492_);
v_pos_3580_ = lean_ctor_get(v___x_3496_, 0);
v_err_3581_ = lean_ctor_get(v___x_3496_, 1);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3583_ = v___x_3496_;
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_err_3581_);
lean_inc(v_pos_3580_);
lean_dec(v___x_3496_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3586_; 
if (v_isShared_3584_ == 0)
{
v___x_3586_ = v___x_3583_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_pos_3580_);
lean_ctor_set(v_reuseFailAlloc_3587_, 1, v_err_3581_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_relative(lean_object* v_config_3589_, lean_object* v_a_3590_){
_start:
{
lean_object* v___y_3592_; lean_object* v___x_3612_; 
lean_inc_ref(v_a_3590_);
lean_inc_ref(v_config_3589_);
v___x_3612_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withAuthority(v_config_3589_, v_a_3590_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_dec_ref(v_a_3590_);
lean_dec_ref(v_config_3589_);
v___y_3592_ = v___x_3612_;
goto v___jp_3591_;
}
else
{
lean_object* v_pos_3613_; lean_object* v_idx_3614_; lean_object* v_idx_3615_; uint8_t v___x_3616_; 
v_pos_3613_ = lean_ctor_get(v___x_3612_, 0);
v_idx_3614_ = lean_ctor_get(v_a_3590_, 1);
lean_inc(v_idx_3614_);
lean_dec_ref(v_a_3590_);
v_idx_3615_ = lean_ctor_get(v_pos_3613_, 1);
v___x_3616_ = lean_nat_dec_eq(v_idx_3614_, v_idx_3615_);
lean_dec(v_idx_3614_);
if (v___x_3616_ == 0)
{
lean_dec_ref(v_config_3589_);
v___y_3592_ = v___x_3612_;
goto v___jp_3591_;
}
else
{
lean_object* v___x_3617_; 
lean_inc(v_pos_3613_);
lean_dec_ref_known(v___x_3612_, 2);
v___x_3617_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath(v_config_3589_, v_pos_3613_);
v___y_3592_ = v___x_3617_;
goto v___jp_3591_;
}
}
v___jp_3591_:
{
if (lean_obj_tag(v___y_3592_) == 0)
{
lean_object* v_pos_3593_; lean_object* v_res_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3602_; 
v_pos_3593_ = lean_ctor_get(v___y_3592_, 0);
v_res_3594_ = lean_ctor_get(v___y_3592_, 1);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___y_3592_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3596_ = v___y_3592_;
v_isShared_3597_ = v_isSharedCheck_3602_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_res_3594_);
lean_inc(v_pos_3593_);
lean_dec(v___y_3592_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3602_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3598_; lean_object* v___x_3600_; 
v___x_3598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3598_, 0, v_res_3594_);
if (v_isShared_3597_ == 0)
{
lean_ctor_set(v___x_3596_, 1, v___x_3598_);
v___x_3600_ = v___x_3596_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_pos_3593_);
lean_ctor_set(v_reuseFailAlloc_3601_, 1, v___x_3598_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
else
{
lean_object* v_pos_3603_; lean_object* v_err_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3611_; 
v_pos_3603_ = lean_ctor_get(v___y_3592_, 0);
v_err_3604_ = lean_ctor_get(v___y_3592_, 1);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___y_3592_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3606_ = v___y_3592_;
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_err_3604_);
lean_inc(v_pos_3603_);
lean_dec(v___y_3592_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3609_; 
if (v_isShared_3607_ == 0)
{
v___x_3609_ = v___x_3606_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_pos_3603_);
lean_ctor_set(v_reuseFailAlloc_3610_, 1, v_err_3604_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURIReference(lean_object* v_config_3618_, lean_object* v_a_3619_){
_start:
{
lean_object* v___y_3621_; lean_object* v_pos_3622_; lean_object* v___x_3627_; 
lean_inc_ref(v_a_3619_);
lean_inc_ref(v_config_3618_);
v___x_3627_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_uri(v_config_3618_, v_a_3619_);
if (lean_obj_tag(v___x_3627_) == 0)
{
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_dec_ref(v_a_3619_);
lean_dec_ref(v_config_3618_);
return v___x_3627_;
}
else
{
lean_object* v_pos_3628_; 
v_pos_3628_ = lean_ctor_get(v___x_3627_, 0);
lean_inc(v_pos_3628_);
v___y_3621_ = v___x_3627_;
v_pos_3622_ = v_pos_3628_;
goto v___jp_3620_;
}
}
else
{
lean_object* v_err_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3636_; 
v_err_3629_ = lean_ctor_get(v___x_3627_, 1);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3636_ == 0)
{
lean_object* v_unused_3637_; 
v_unused_3637_ = lean_ctor_get(v___x_3627_, 0);
lean_dec(v_unused_3637_);
v___x_3631_ = v___x_3627_;
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_err_3629_);
lean_dec(v___x_3627_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3634_; 
lean_inc_ref(v_a_3619_);
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 0, v_a_3619_);
v___x_3634_ = v___x_3631_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_a_3619_);
lean_ctor_set(v_reuseFailAlloc_3635_, 1, v_err_3629_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
lean_inc_ref(v_a_3619_);
v___y_3621_ = v___x_3634_;
v_pos_3622_ = v_a_3619_;
goto v___jp_3620_;
}
}
}
v___jp_3620_:
{
lean_object* v_idx_3623_; lean_object* v_idx_3624_; uint8_t v___x_3625_; 
v_idx_3623_ = lean_ctor_get(v_a_3619_, 1);
lean_inc(v_idx_3623_);
lean_dec_ref(v_a_3619_);
v_idx_3624_ = lean_ctor_get(v_pos_3622_, 1);
v___x_3625_ = lean_nat_dec_eq(v_idx_3623_, v_idx_3624_);
lean_dec(v_idx_3623_);
if (v___x_3625_ == 0)
{
lean_dec_ref(v_pos_3622_);
lean_dec_ref(v_config_3618_);
return v___y_3621_;
}
else
{
lean_object* v___x_3626_; 
lean_dec_ref(v___y_3621_);
v___x_3626_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_relative(v_config_3618_, v_pos_3622_);
return v___x_3626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader(lean_object* v_config_3644_, lean_object* v_a_3645_){
_start:
{
lean_object* v___x_3646_; 
v___x_3646_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_3644_, v_a_3645_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_pos_3647_; lean_object* v_res_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3721_; 
v_pos_3647_ = lean_ctor_get(v___x_3646_, 0);
v_res_3648_ = lean_ctor_get(v___x_3646_, 1);
v_isSharedCheck_3721_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3650_ = v___x_3646_;
v_isShared_3651_ = v_isSharedCheck_3721_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_res_3648_);
lean_inc(v_pos_3647_);
lean_dec(v___x_3646_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3721_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v_port_3653_; lean_object* v___y_3654_; lean_object* v_pos_3668_; lean_object* v_pos_3671_; lean_object* v_array_3672_; lean_object* v_idx_3673_; lean_object* v_array_3679_; lean_object* v_idx_3680_; lean_object* v___x_3681_; uint8_t v___x_3682_; 
v_array_3679_ = lean_ctor_get(v_pos_3647_, 0);
v_idx_3680_ = lean_ctor_get(v_pos_3647_, 1);
v___x_3681_ = lean_byte_array_size(v_array_3679_);
v___x_3682_ = lean_nat_dec_lt(v_idx_3680_, v___x_3681_);
if (v___x_3682_ == 0)
{
v_pos_3668_ = v_pos_3647_;
goto v___jp_3667_;
}
else
{
uint8_t v___x_3683_; uint8_t v___x_3684_; uint8_t v___x_3685_; 
v___x_3683_ = lean_byte_array_fget(v_array_3679_, v_idx_3680_);
v___x_3684_ = 58;
v___x_3685_ = lean_uint8_dec_eq(v___x_3683_, v___x_3684_);
if (v___x_3685_ == 0)
{
v_pos_3668_ = v_pos_3647_;
goto v___jp_3667_;
}
else
{
if (v___x_3682_ == 0)
{
lean_object* v___x_3686_; lean_object* v___x_3687_; 
lean_del_object(v___x_3650_);
lean_dec(v_res_3648_);
v___x_3686_ = lean_box(0);
v___x_3687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3687_, 0, v_pos_3647_);
lean_ctor_set(v___x_3687_, 1, v___x_3686_);
return v___x_3687_;
}
else
{
if (v___x_3685_ == 0)
{
lean_object* v___x_3688_; lean_object* v___x_3689_; 
lean_del_object(v___x_3650_);
lean_dec(v_res_3648_);
v___x_3688_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
v___x_3689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3689_, 0, v_pos_3647_);
lean_ctor_set(v___x_3689_, 1, v___x_3688_);
return v___x_3689_;
}
else
{
lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3718_; 
lean_inc(v_idx_3680_);
lean_inc_ref(v_array_3679_);
v_isSharedCheck_3718_ = !lean_is_exclusive(v_pos_3647_);
if (v_isSharedCheck_3718_ == 0)
{
lean_object* v_unused_3719_; lean_object* v_unused_3720_; 
v_unused_3719_ = lean_ctor_get(v_pos_3647_, 1);
lean_dec(v_unused_3719_);
v_unused_3720_ = lean_ctor_get(v_pos_3647_, 0);
lean_dec(v_unused_3720_);
v___x_3691_ = v_pos_3647_;
v_isShared_3692_ = v_isSharedCheck_3718_;
goto v_resetjp_3690_;
}
else
{
lean_dec(v_pos_3647_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3718_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3696_; 
v___x_3693_ = lean_unsigned_to_nat(1u);
v___x_3694_ = lean_nat_add(v_idx_3680_, v___x_3693_);
lean_dec(v_idx_3680_);
lean_inc(v___x_3694_);
lean_inc_ref(v_array_3679_);
if (v_isShared_3692_ == 0)
{
lean_ctor_set(v___x_3691_, 1, v___x_3694_);
v___x_3696_ = v___x_3691_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_array_3679_);
lean_ctor_set(v_reuseFailAlloc_3717_, 1, v___x_3694_);
v___x_3696_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
uint8_t v___x_3697_; 
v___x_3697_ = lean_nat_dec_lt(v___x_3694_, v___x_3681_);
if (v___x_3697_ == 0)
{
v_pos_3671_ = v___x_3696_;
v_array_3672_ = v_array_3679_;
v_idx_3673_ = v___x_3694_;
goto v___jp_3670_;
}
else
{
uint8_t v___x_3698_; uint8_t v___x_3699_; uint8_t v___x_3700_; 
v___x_3698_ = lean_byte_array_fget(v_array_3679_, v___x_3694_);
v___x_3699_ = 48;
v___x_3700_ = lean_uint8_dec_le(v___x_3699_, v___x_3698_);
if (v___x_3700_ == 0)
{
v_pos_3671_ = v___x_3696_;
v_array_3672_ = v_array_3679_;
v_idx_3673_ = v___x_3694_;
goto v___jp_3670_;
}
else
{
uint8_t v___x_3701_; uint8_t v___x_3702_; 
v___x_3701_ = 57;
v___x_3702_ = lean_uint8_dec_le(v___x_3698_, v___x_3701_);
if (v___x_3702_ == 0)
{
v_pos_3671_ = v___x_3696_;
v_array_3672_ = v_array_3679_;
v_idx_3673_ = v___x_3694_;
goto v___jp_3670_;
}
else
{
lean_object* v___x_3703_; 
lean_dec(v___x_3694_);
lean_dec_ref(v_array_3679_);
v___x_3703_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_3696_);
if (lean_obj_tag(v___x_3703_) == 0)
{
lean_object* v_pos_3704_; lean_object* v_res_3705_; lean_object* v___x_3706_; uint16_t v___x_3707_; 
v_pos_3704_ = lean_ctor_get(v___x_3703_, 0);
lean_inc(v_pos_3704_);
v_res_3705_ = lean_ctor_get(v___x_3703_, 1);
lean_inc(v_res_3705_);
lean_dec_ref_known(v___x_3703_, 2);
v___x_3706_ = lean_alloc_ctor(2, 0, 2);
v___x_3707_ = lean_unbox(v_res_3705_);
lean_dec(v_res_3705_);
lean_ctor_set_uint16(v___x_3706_, 0, v___x_3707_);
v_port_3653_ = v___x_3706_;
v___y_3654_ = v_pos_3704_;
goto v___jp_3652_;
}
else
{
lean_object* v_pos_3708_; lean_object* v_err_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3716_; 
lean_del_object(v___x_3650_);
lean_dec(v_res_3648_);
v_pos_3708_ = lean_ctor_get(v___x_3703_, 0);
v_err_3709_ = lean_ctor_get(v___x_3703_, 1);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3703_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3711_ = v___x_3703_;
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_err_3709_);
lean_inc(v_pos_3708_);
lean_dec(v___x_3703_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_pos_3708_);
lean_ctor_set(v_reuseFailAlloc_3715_, 1, v_err_3709_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
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
v___jp_3652_:
{
lean_object* v_array_3655_; lean_object* v_idx_3656_; lean_object* v___x_3657_; uint8_t v___x_3658_; 
v_array_3655_ = lean_ctor_get(v___y_3654_, 0);
v_idx_3656_ = lean_ctor_get(v___y_3654_, 1);
v___x_3657_ = lean_byte_array_size(v_array_3655_);
v___x_3658_ = lean_nat_dec_lt(v_idx_3656_, v___x_3657_);
if (v___x_3658_ == 0)
{
lean_object* v___x_3659_; lean_object* v___x_3661_; 
v___x_3659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3659_, 0, v_res_3648_);
lean_ctor_set(v___x_3659_, 1, v_port_3653_);
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 1, v___x_3659_);
lean_ctor_set(v___x_3650_, 0, v___y_3654_);
v___x_3661_ = v___x_3650_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___y_3654_);
lean_ctor_set(v_reuseFailAlloc_3662_, 1, v___x_3659_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
else
{
lean_object* v___x_3663_; lean_object* v___x_3665_; 
lean_dec(v_port_3653_);
lean_dec(v_res_3648_);
v___x_3663_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__1));
if (v_isShared_3651_ == 0)
{
lean_ctor_set_tag(v___x_3650_, 1);
lean_ctor_set(v___x_3650_, 1, v___x_3663_);
lean_ctor_set(v___x_3650_, 0, v___y_3654_);
v___x_3665_ = v___x_3650_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v___y_3654_);
lean_ctor_set(v_reuseFailAlloc_3666_, 1, v___x_3663_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
v___jp_3667_:
{
lean_object* v___x_3669_; 
v___x_3669_ = lean_box(0);
v_port_3653_ = v___x_3669_;
v___y_3654_ = v_pos_3668_;
goto v___jp_3652_;
}
v___jp_3670_:
{
lean_object* v___x_3674_; uint8_t v___x_3675_; 
v___x_3674_ = lean_byte_array_size(v_array_3672_);
lean_dec_ref(v_array_3672_);
v___x_3675_ = lean_nat_dec_lt(v_idx_3673_, v___x_3674_);
lean_dec(v_idx_3673_);
if (v___x_3675_ == 0)
{
lean_object* v___x_3676_; 
v___x_3676_ = lean_box(1);
v_port_3653_ = v___x_3676_;
v___y_3654_ = v_pos_3671_;
goto v___jp_3652_;
}
else
{
lean_object* v___x_3677_; lean_object* v___x_3678_; 
lean_del_object(v___x_3650_);
lean_dec(v_res_3648_);
v___x_3677_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__3));
v___x_3678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3678_, 0, v_pos_3671_);
lean_ctor_set(v___x_3678_, 1, v___x_3677_);
return v___x_3678_;
}
}
}
}
else
{
lean_object* v_pos_3722_; lean_object* v_err_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
v_pos_3722_ = lean_ctor_get(v___x_3646_, 0);
v_err_3723_ = lean_ctor_get(v___x_3646_, 1);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3725_ = v___x_3646_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_err_3723_);
lean_inc(v_pos_3722_);
lean_dec(v___x_3646_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3728_; 
if (v_isShared_3726_ == 0)
{
v___x_3728_ = v___x_3725_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_pos_3722_);
lean_ctor_set(v_reuseFailAlloc_3729_, 1, v_err_3723_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader___boxed(lean_object* v_config_3731_, lean_object* v_a_3732_){
_start:
{
lean_object* v_res_3733_; 
v_res_3733_ = l_Std_Http_URI_Parser_parseHostHeader(v_config_3731_, v_a_3732_);
lean_dec_ref(v_config_3731_);
return v_res_3733_;
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
