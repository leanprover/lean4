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
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "not an IPv4 address"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__4 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__4_value;
static const lean_closure_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__5 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__5_value;
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
lean_object* v___y_205_; uint32_t v___y_209_; lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v_maxSchemeLength_217_; lean_object* v___x_218_; lean_object* v___y_220_; lean_object* v___y_221_; uint8_t v___x_237_; lean_object* v___y_239_; lean_object* v___y_240_; uint8_t v___y_241_; lean_object* v_lower_242_; lean_object* v_upper_243_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_259_; uint8_t v___y_260_; lean_object* v___y_261_; 
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
v___y_256_ = v___x_282_;
v___y_257_ = v_fst_278_;
v___y_258_ = v_array_279_;
v___y_259_ = v___x_281_;
v___y_260_ = v_res_272_;
v___y_261_ = v_idx_280_;
goto v___jp_255_;
}
else
{
lean_dec(v_idx_280_);
v___y_256_ = v___x_282_;
v___y_257_ = v_fst_278_;
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
v___x_213_ = lean_uint32_dec_le(v___x_212_, v___y_209_);
if (v___x_213_ == 0)
{
lean_dec_ref(v___y_210_);
v___y_205_ = v___y_211_;
goto v___jp_204_;
}
else
{
uint32_t v___x_214_; uint8_t v___x_215_; 
v___x_214_ = 122;
v___x_215_ = lean_uint32_dec_le(v___y_209_, v___x_214_);
if (v___x_215_ == 0)
{
lean_dec_ref(v___y_210_);
v___y_205_ = v___y_211_;
goto v___jp_204_;
}
else
{
lean_object* v___x_216_; 
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v___y_211_);
lean_ctor_set(v___x_216_, 1, v___y_210_);
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
v___y_209_ = v___x_231_;
v___y_210_ = v___x_222_;
v___y_211_ = v___y_220_;
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
v___y_209_ = v___x_235_;
v___y_210_ = v___x_222_;
v___y_211_ = v___y_220_;
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
v___x_262_ = lean_nat_dec_le(v___y_259_, v___y_256_);
if (v___x_262_ == 0)
{
lean_dec(v___y_259_);
v___y_239_ = v___y_257_;
v___y_240_ = v___y_258_;
v___y_241_ = v___y_260_;
v_lower_242_ = v___y_261_;
v_upper_243_ = v___y_256_;
goto v___jp_238_;
}
else
{
lean_dec(v___y_256_);
v___y_239_ = v___y_257_;
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
v___y_499_ = v___y_506_;
v_userPassEncoded_500_ = v___x_512_;
v___y_501_ = v___y_507_;
goto v___jp_498_;
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; 
lean_dec(v___x_512_);
lean_dec_ref(v___y_506_);
v___x_513_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1));
v___x_514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_514_, 0, v___y_507_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
return v___x_514_;
}
}
v___jp_515_:
{
uint8_t v___x_522_; 
v___x_522_ = lean_nat_dec_le(v___y_516_, v___y_517_);
if (v___x_522_ == 0)
{
lean_dec(v___y_516_);
v___y_505_ = v___y_518_;
v___y_506_ = v___y_519_;
v___y_507_ = v___y_520_;
v_lower_508_ = v___y_521_;
v_upper_509_ = v___y_517_;
goto v___jp_504_;
}
else
{
lean_dec(v___y_517_);
v___y_505_ = v___y_518_;
v___y_506_ = v___y_519_;
v___y_507_ = v___y_520_;
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
v___y_517_ = v___x_548_;
v___y_518_ = v_array_546_;
v___y_519_ = v_val_545_;
v___y_520_ = v_fst_566_;
v___y_521_ = v___x_560_;
goto v___jp_515_;
}
else
{
lean_dec(v___x_560_);
v___y_516_ = v___x_567_;
v___y_517_ = v___x_548_;
v___y_518_ = v_array_546_;
v___y_519_ = v_val_545_;
v___y_520_ = v_fst_566_;
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
uint8_t v___x_14494__boxed_820_; uint8_t v_x_boxed_821_; uint8_t v_res_822_; lean_object* v_r_823_; 
v___x_14494__boxed_820_ = lean_unbox(v___x_818_);
v_x_boxed_821_ = lean_unbox(v_x_819_);
v_res_822_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(v___x_14494__boxed_820_, v_x_boxed_821_);
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
uint8_t v___x_14573__boxed_900_; uint8_t v_b_boxed_901_; uint8_t v_res_902_; lean_object* v_r_903_; 
v___x_14573__boxed_900_ = lean_unbox(v___x_894_);
v_b_boxed_901_ = lean_unbox(v_b_899_);
v_res_902_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_14573__boxed_900_, v___x_895_, v___x_896_, v___x_897_, v_a_898_, v_b_boxed_901_);
lean_dec_ref(v___x_896_);
lean_dec_ref(v___x_895_);
v_r_903_ = lean_box(v_res_902_);
return v_r_903_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(lean_object* v_config_914_, lean_object* v_a_915_){
_start:
{
lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v_lower_927_; lean_object* v_upper_928_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v_err_982_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_991_; lean_object* v_pos_992_; uint8_t v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; uint8_t v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; uint8_t v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1026_; lean_object* v_pos_1027_; lean_object* v___y_1042_; lean_object* v_pos_1043_; lean_object* v_res_1044_; lean_object* v_array_1045_; lean_object* v_idx_1046_; lean_object* v_pos_1048_; lean_object* v_res_1049_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v_array_1045_ = lean_ctor_get(v_a_915_, 0);
v_idx_1046_ = lean_ctor_get(v_a_915_, 1);
v___x_1058_ = lean_byte_array_size(v_array_1045_);
v___x_1059_ = lean_nat_dec_lt(v_idx_1046_, v___x_1058_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; 
lean_inc(v_idx_1046_);
lean_inc_ref(v_array_1045_);
v___x_1060_ = lean_box(0);
v_pos_1048_ = v_a_915_;
v_res_1049_ = v___x_1060_;
goto v___jp_1047_;
}
else
{
uint8_t v___x_1061_; uint8_t v___x_1062_; uint8_t v___x_1063_; 
v___x_1061_ = lean_byte_array_fget(v_array_1045_, v_idx_1046_);
v___x_1062_ = 91;
v___x_1063_ = lean_uint8_dec_eq(v___x_1061_, v___x_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; 
lean_inc(v_idx_1046_);
lean_inc_ref(v_array_1045_);
v___x_1064_ = lean_box(0);
v_pos_1048_ = v_a_915_;
v_res_1049_ = v___x_1064_;
goto v___jp_1047_;
}
else
{
lean_object* v___x_1065_; 
v___x_1065_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(v_a_915_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_pos_1066_; lean_object* v_res_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1075_; 
v_pos_1066_ = lean_ctor_get(v___x_1065_, 0);
v_res_1067_ = lean_ctor_get(v___x_1065_, 1);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1069_ = v___x_1065_;
v_isShared_1070_ = v_isSharedCheck_1075_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_res_1067_);
lean_inc(v_pos_1066_);
lean_dec(v___x_1065_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1075_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1071_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1071_, 0, v_res_1067_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 1, v___x_1071_);
v___x_1073_ = v___x_1069_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_pos_1066_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
else
{
lean_object* v_pos_1076_; lean_object* v_err_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
v_pos_1076_ = lean_ctor_get(v___x_1065_, 0);
v_err_1077_ = lean_ctor_get(v___x_1065_, 1);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1065_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_err_1077_);
lean_inc(v_pos_1076_);
lean_dec(v___x_1065_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_pos_1076_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_err_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
}
v___jp_916_:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_919_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0));
v___x_920_ = lean_string_append(v___x_919_, v___y_918_);
lean_dec_ref(v___y_918_);
v___x_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
v___x_922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_922_, 0, v___y_917_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
return v___x_922_;
}
v___jp_923_:
{
lean_object* v___x_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_929_ = l_ByteArray_toByteSlice(v___y_925_, v_lower_927_, v_upper_928_);
v___x_930_ = l_ByteSlice_toByteArray(v___x_929_);
v___x_931_ = lean_string_validate_utf8(v___x_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec_ref(v___x_930_);
lean_dec(v___y_926_);
v___x_932_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2));
v___x_933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_933_, 0, v___y_924_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
return v___x_933_;
}
else
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v___x_934_ = lean_string_from_utf8_unchecked(v___x_930_);
lean_inc_n(v___y_926_, 2);
lean_inc_ref(v___x_934_);
v___x_935_ = l_String_mapAux___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(v___x_934_, v___y_926_);
v___x_936_ = lean_string_utf8_byte_size(v___x_935_);
lean_inc_ref(v___x_935_);
v___x_937_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___y_926_);
lean_ctor_set(v___x_937_, 2, v___x_936_);
v___x_938_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0);
v___x_939_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_935_, v___x_936_, v___x_938_, v___x_931_);
if (v___x_939_ == 0)
{
uint8_t v___x_940_; 
v___x_940_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_939_, v___x_935_, v___x_937_, v___x_936_, v___x_938_, v___x_931_);
lean_dec_ref_known(v___x_937_, 3);
if (v___x_940_ == 0)
{
lean_dec_ref(v___x_935_);
lean_dec(v___y_926_);
v___y_917_ = v___y_924_;
v___y_918_ = v___x_934_;
goto v___jp_916_;
}
else
{
lean_object* v___x_941_; lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_941_ = lean_string_length(v___x_935_);
v___x_942_ = lean_unsigned_to_nat(255u);
v___x_943_ = lean_nat_dec_le(v___x_941_, v___x_942_);
if (v___x_943_ == 0)
{
lean_dec_ref(v___x_935_);
lean_dec(v___y_926_);
v___y_917_ = v___y_924_;
v___y_918_ = v___x_934_;
goto v___jp_916_;
}
else
{
uint8_t v___x_944_; 
v___x_944_ = lean_nat_dec_eq(v___x_936_, v___y_926_);
lean_dec(v___y_926_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; lean_object* v___x_946_; 
lean_dec_ref(v___x_934_);
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_935_);
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v___y_924_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
return v___x_946_;
}
else
{
lean_dec_ref(v___x_935_);
v___y_917_ = v___y_924_;
v___y_918_ = v___x_934_;
goto v___jp_916_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_937_, 3);
lean_dec_ref(v___x_935_);
lean_dec(v___y_926_);
v___y_917_ = v___y_924_;
v___y_918_ = v___x_934_;
goto v___jp_916_;
}
}
}
v___jp_947_:
{
uint8_t v___x_954_; 
v___x_954_ = lean_nat_dec_le(v___y_952_, v___y_948_);
if (v___x_954_ == 0)
{
lean_dec(v___y_952_);
v___y_924_ = v___y_949_;
v___y_925_ = v___y_950_;
v___y_926_ = v___y_951_;
v_lower_927_ = v___y_953_;
v_upper_928_ = v___y_948_;
goto v___jp_923_;
}
else
{
lean_dec(v___y_948_);
v___y_924_ = v___y_949_;
v___y_925_ = v___y_950_;
v___y_926_ = v___y_951_;
v_lower_927_ = v___y_953_;
v_upper_928_ = v___y_952_;
goto v___jp_923_;
}
}
v___jp_955_:
{
lean_object* v_maxHostLength_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v_snd_961_; lean_object* v_fst_962_; lean_object* v_fst_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_977_; 
v_maxHostLength_958_ = lean_ctor_get(v_config_914_, 1);
v___x_959_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___y_957_);
lean_inc_ref(v___y_956_);
v___x_960_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___y_956_, v_maxHostLength_958_, v___x_959_, v___y_957_);
v_snd_961_ = lean_ctor_get(v___x_960_, 1);
lean_inc(v_snd_961_);
v_fst_962_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_fst_962_);
lean_dec_ref(v___x_960_);
v_fst_963_ = lean_ctor_get(v_snd_961_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v_snd_961_);
if (v_isSharedCheck_977_ == 0)
{
lean_object* v_unused_978_; 
v_unused_978_ = lean_ctor_get(v_snd_961_, 1);
lean_dec(v_unused_978_);
v___x_965_ = v_snd_961_;
v_isShared_966_ = v_isSharedCheck_977_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_fst_963_);
lean_dec(v_snd_961_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_977_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
uint8_t v___x_967_; 
v___x_967_ = lean_nat_dec_eq(v_fst_962_, v___x_959_);
if (v___x_967_ == 0)
{
lean_object* v_array_968_; lean_object* v_idx_969_; lean_object* v___x_970_; lean_object* v___x_971_; uint8_t v___x_972_; 
lean_del_object(v___x_965_);
v_array_968_ = lean_ctor_get(v___y_957_, 0);
lean_inc_ref(v_array_968_);
v_idx_969_ = lean_ctor_get(v___y_957_, 1);
lean_inc(v_idx_969_);
lean_dec_ref(v___y_957_);
v___x_970_ = lean_nat_add(v_idx_969_, v_fst_962_);
lean_dec(v_fst_962_);
v___x_971_ = lean_byte_array_size(v_array_968_);
v___x_972_ = lean_nat_dec_le(v_idx_969_, v___x_959_);
if (v___x_972_ == 0)
{
v___y_948_ = v___x_971_;
v___y_949_ = v_fst_963_;
v___y_950_ = v_array_968_;
v___y_951_ = v___x_959_;
v___y_952_ = v___x_970_;
v___y_953_ = v_idx_969_;
goto v___jp_947_;
}
else
{
lean_dec(v_idx_969_);
v___y_948_ = v___x_971_;
v___y_949_ = v_fst_963_;
v___y_950_ = v_array_968_;
v___y_951_ = v___x_959_;
v___y_952_ = v___x_970_;
v___y_953_ = v___x_959_;
goto v___jp_947_;
}
}
else
{
lean_object* v___x_973_; lean_object* v___x_975_; 
lean_dec(v_fst_963_);
lean_dec(v_fst_962_);
v___x_973_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7));
if (v_isShared_966_ == 0)
{
lean_ctor_set_tag(v___x_965_, 1);
lean_ctor_set(v___x_965_, 1, v___x_973_);
lean_ctor_set(v___x_965_, 0, v___y_957_);
v___x_975_ = v___x_965_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___y_957_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
v___jp_979_:
{
lean_object* v_idx_983_; uint8_t v___x_984_; 
v_idx_983_ = lean_ctor_get(v___y_981_, 1);
v___x_984_ = lean_nat_dec_eq(v_idx_983_, v_idx_983_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; 
v___x_985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_985_, 0, v___y_981_);
lean_ctor_set(v___x_985_, 1, v_err_982_);
return v___x_985_;
}
else
{
lean_dec(v_err_982_);
v___y_956_ = v___y_980_;
v___y_957_ = v___y_981_;
goto v___jp_955_;
}
}
v___jp_986_:
{
lean_object* v___x_989_; 
v___x_989_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__4));
v___y_980_ = v___y_987_;
v___y_981_ = v___y_988_;
v_err_982_ = v___x_989_;
goto v___jp_979_;
}
v___jp_990_:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_993_, 0, v___y_991_);
v___x_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_994_, 0, v_pos_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
return v___x_994_;
}
v___jp_995_:
{
uint8_t v___x_1001_; uint8_t v___x_1002_; 
v___x_1001_ = 45;
v___x_1002_ = lean_uint8_dec_eq(v___y_996_, v___x_1001_);
if (v___x_1002_ == 0)
{
uint8_t v___x_1003_; uint8_t v___x_1004_; 
v___x_1003_ = 46;
v___x_1004_ = lean_uint8_dec_eq(v___y_996_, v___x_1003_);
if (v___x_1004_ == 0)
{
lean_dec_ref(v___y_999_);
v___y_991_ = v___y_1000_;
v_pos_992_ = v___y_998_;
goto v___jp_990_;
}
else
{
lean_dec_ref(v___y_1000_);
lean_dec_ref(v___y_998_);
v___y_987_ = v___y_997_;
v___y_988_ = v___y_999_;
goto v___jp_986_;
}
}
else
{
lean_dec_ref(v___y_1000_);
lean_dec_ref(v___y_998_);
v___y_987_ = v___y_997_;
v___y_988_ = v___y_999_;
goto v___jp_986_;
}
}
v___jp_1005_:
{
uint8_t v___x_1011_; uint8_t v___x_1012_; 
v___x_1011_ = 65;
v___x_1012_ = lean_uint8_dec_le(v___x_1011_, v___y_1006_);
if (v___x_1012_ == 0)
{
v___y_996_ = v___y_1006_;
v___y_997_ = v___y_1008_;
v___y_998_ = v___y_1007_;
v___y_999_ = v___y_1009_;
v___y_1000_ = v___y_1010_;
goto v___jp_995_;
}
else
{
uint8_t v___x_1013_; uint8_t v___x_1014_; 
v___x_1013_ = 90;
v___x_1014_ = lean_uint8_dec_le(v___y_1006_, v___x_1013_);
if (v___x_1014_ == 0)
{
v___y_996_ = v___y_1006_;
v___y_997_ = v___y_1008_;
v___y_998_ = v___y_1007_;
v___y_999_ = v___y_1009_;
v___y_1000_ = v___y_1010_;
goto v___jp_995_;
}
else
{
lean_dec_ref(v___y_1010_);
lean_dec_ref(v___y_1007_);
v___y_987_ = v___y_1008_;
v___y_988_ = v___y_1009_;
goto v___jp_986_;
}
}
}
v___jp_1015_:
{
uint8_t v___x_1021_; uint8_t v___x_1022_; 
v___x_1021_ = 97;
v___x_1022_ = lean_uint8_dec_le(v___x_1021_, v___y_1016_);
if (v___x_1022_ == 0)
{
v___y_1006_ = v___y_1016_;
v___y_1007_ = v___y_1018_;
v___y_1008_ = v___y_1017_;
v___y_1009_ = v___y_1019_;
v___y_1010_ = v___y_1020_;
goto v___jp_1005_;
}
else
{
uint8_t v___x_1023_; uint8_t v___x_1024_; 
v___x_1023_ = 122;
v___x_1024_ = lean_uint8_dec_le(v___y_1016_, v___x_1023_);
if (v___x_1024_ == 0)
{
v___y_1006_ = v___y_1016_;
v___y_1007_ = v___y_1018_;
v___y_1008_ = v___y_1017_;
v___y_1009_ = v___y_1019_;
v___y_1010_ = v___y_1020_;
goto v___jp_1005_;
}
else
{
lean_dec_ref(v___y_1020_);
lean_dec_ref(v___y_1018_);
v___y_987_ = v___y_1017_;
v___y_988_ = v___y_1019_;
goto v___jp_986_;
}
}
}
v___jp_1025_:
{
lean_object* v___x_1028_; 
lean_inc_ref(v_pos_1027_);
v___x_1028_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(v_pos_1027_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_pos_1029_; lean_object* v_res_1030_; lean_object* v_array_1031_; lean_object* v_idx_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v_pos_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_pos_1029_);
v_res_1030_ = lean_ctor_get(v___x_1028_, 1);
lean_inc(v_res_1030_);
lean_dec_ref_known(v___x_1028_, 2);
v_array_1031_ = lean_ctor_get(v_pos_1029_, 0);
v_idx_1032_ = lean_ctor_get(v_pos_1029_, 1);
v___x_1033_ = lean_byte_array_size(v_array_1031_);
v___x_1034_ = lean_nat_dec_lt(v_idx_1032_, v___x_1033_);
if (v___x_1034_ == 0)
{
lean_dec_ref(v_pos_1027_);
v___y_991_ = v_res_1030_;
v_pos_992_ = v_pos_1029_;
goto v___jp_990_;
}
else
{
uint8_t v___x_1035_; uint8_t v___x_1036_; uint8_t v___x_1037_; 
v___x_1035_ = lean_byte_array_fget(v_array_1031_, v_idx_1032_);
v___x_1036_ = 48;
v___x_1037_ = lean_uint8_dec_le(v___x_1036_, v___x_1035_);
if (v___x_1037_ == 0)
{
v___y_1016_ = v___x_1035_;
v___y_1017_ = v___y_1026_;
v___y_1018_ = v_pos_1029_;
v___y_1019_ = v_pos_1027_;
v___y_1020_ = v_res_1030_;
goto v___jp_1015_;
}
else
{
uint8_t v___x_1038_; uint8_t v___x_1039_; 
v___x_1038_ = 57;
v___x_1039_ = lean_uint8_dec_le(v___x_1035_, v___x_1038_);
if (v___x_1039_ == 0)
{
v___y_1016_ = v___x_1035_;
v___y_1017_ = v___y_1026_;
v___y_1018_ = v_pos_1029_;
v___y_1019_ = v_pos_1027_;
v___y_1020_ = v_res_1030_;
goto v___jp_1015_;
}
else
{
lean_dec(v_res_1030_);
lean_dec(v_pos_1029_);
v___y_987_ = v___y_1026_;
v___y_988_ = v_pos_1027_;
goto v___jp_986_;
}
}
}
}
else
{
lean_object* v_err_1040_; 
v_err_1040_ = lean_ctor_get(v___x_1028_, 1);
lean_inc(v_err_1040_);
lean_dec_ref_known(v___x_1028_, 2);
v___y_980_ = v___y_1026_;
v___y_981_ = v_pos_1027_;
v_err_982_ = v_err_1040_;
goto v___jp_979_;
}
}
v___jp_1041_:
{
v___y_956_ = v___y_1042_;
v___y_957_ = v_pos_1043_;
goto v___jp_955_;
}
v___jp_1047_:
{
lean_object* v___f_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___f_1050_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__5));
v___x_1051_ = lean_byte_array_size(v_array_1045_);
v___x_1052_ = lean_nat_dec_lt(v_idx_1046_, v___x_1051_);
if (v___x_1052_ == 0)
{
lean_dec(v_idx_1046_);
lean_dec_ref(v_array_1045_);
v___y_1042_ = v___f_1050_;
v_pos_1043_ = v_pos_1048_;
v_res_1044_ = v_res_1049_;
goto v___jp_1041_;
}
else
{
uint8_t v___x_1053_; uint8_t v___x_1054_; uint8_t v___x_1055_; 
v___x_1053_ = lean_byte_array_fget(v_array_1045_, v_idx_1046_);
lean_dec(v_idx_1046_);
lean_dec_ref(v_array_1045_);
v___x_1054_ = 48;
v___x_1055_ = lean_uint8_dec_le(v___x_1054_, v___x_1053_);
if (v___x_1055_ == 0)
{
v___y_1042_ = v___f_1050_;
v_pos_1043_ = v_pos_1048_;
v_res_1044_ = v_res_1049_;
goto v___jp_1041_;
}
else
{
uint8_t v___x_1056_; uint8_t v___x_1057_; 
v___x_1056_ = 57;
v___x_1057_ = lean_uint8_dec_le(v___x_1053_, v___x_1056_);
if (v___x_1057_ == 0)
{
v___y_1042_ = v___f_1050_;
v_pos_1043_ = v_pos_1048_;
v_res_1044_ = v_res_1049_;
goto v___jp_1041_;
}
else
{
v___y_1026_ = v___f_1050_;
v_pos_1027_ = v_pos_1048_;
goto v___jp_1025_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___boxed(lean_object* v_config_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_1085_, v_a_1086_);
lean_dec_ref(v_config_1085_);
return v_res_1087_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(lean_object* v___x_1088_, lean_object* v___x_1089_, lean_object* v___x_1090_, lean_object* v_inst_1091_, lean_object* v_R_1092_, lean_object* v_a_1093_, uint8_t v_b_1094_, lean_object* v_c_1095_){
_start:
{
uint8_t v___x_1096_; 
v___x_1096_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_1088_, v___x_1090_, v_a_1093_, v_b_1094_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___boxed(lean_object* v___x_1097_, lean_object* v___x_1098_, lean_object* v___x_1099_, lean_object* v_inst_1100_, lean_object* v_R_1101_, lean_object* v_a_1102_, lean_object* v_b_1103_, lean_object* v_c_1104_){
_start:
{
uint8_t v_b_boxed_1105_; uint8_t v_res_1106_; lean_object* v_r_1107_; 
v_b_boxed_1105_ = lean_unbox(v_b_1103_);
v_res_1106_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(v___x_1097_, v___x_1098_, v___x_1099_, v_inst_1100_, v_R_1101_, v_a_1102_, v_b_boxed_1105_, v_c_1104_);
lean_dec(v___x_1099_);
lean_dec_ref(v___x_1098_);
lean_dec_ref(v___x_1097_);
v_r_1107_ = lean_box(v_res_1106_);
return v_r_1107_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(uint8_t v___x_1108_, lean_object* v___x_1109_, lean_object* v___x_1110_, lean_object* v___x_1111_, lean_object* v_inst_1112_, lean_object* v_R_1113_, lean_object* v_a_1114_, uint8_t v_b_1115_, lean_object* v_c_1116_){
_start:
{
uint8_t v___x_1117_; 
v___x_1117_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_1108_, v___x_1109_, v___x_1110_, v___x_1111_, v_a_1114_, v_b_1115_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___boxed(lean_object* v___x_1118_, lean_object* v___x_1119_, lean_object* v___x_1120_, lean_object* v___x_1121_, lean_object* v_inst_1122_, lean_object* v_R_1123_, lean_object* v_a_1124_, lean_object* v_b_1125_, lean_object* v_c_1126_){
_start:
{
uint8_t v___x_15026__boxed_1127_; uint8_t v_b_boxed_1128_; uint8_t v_res_1129_; lean_object* v_r_1130_; 
v___x_15026__boxed_1127_ = lean_unbox(v___x_1118_);
v_b_boxed_1128_ = lean_unbox(v_b_1125_);
v_res_1129_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(v___x_15026__boxed_1127_, v___x_1119_, v___x_1120_, v___x_1121_, v_inst_1122_, v_R_1123_, v_a_1124_, v_b_boxed_1128_, v_c_1126_);
lean_dec_ref(v___x_1120_);
lean_dec_ref(v___x_1119_);
v_r_1130_ = lean_box(v_res_1129_);
return v_r_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(lean_object* v_config_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v_port_1145_; lean_object* v___y_1146_; lean_object* v___y_1150_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1159_; lean_object* v___y_1160_; uint8_t v_val_1161_; lean_object* v___y_1162_; lean_object* v___y_1170_; lean_object* v___y_1171_; uint8_t v___y_1172_; lean_object* v_pos_1173_; lean_object* v_array_1174_; lean_object* v_idx_1175_; lean_object* v_res_1176_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; uint8_t v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v_pos_1191_; lean_object* v_pos_1194_; lean_object* v_res_1195_; lean_object* v_err_1260_; lean_object* v___x_1265_; 
lean_inc_ref(v_a_1141_);
v___x_1265_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(v_config_1140_, v_a_1141_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_pos_1266_; lean_object* v_res_1267_; lean_object* v_array_1268_; lean_object* v_idx_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1286_; 
v_pos_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_pos_1266_);
v_res_1267_ = lean_ctor_get(v___x_1265_, 1);
lean_inc(v_res_1267_);
lean_dec_ref_known(v___x_1265_, 2);
v_array_1268_ = lean_ctor_get(v_pos_1266_, 0);
v_idx_1269_ = lean_ctor_get(v_pos_1266_, 1);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_pos_1266_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1271_ = v_pos_1266_;
v_isShared_1272_ = v_isSharedCheck_1286_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_idx_1269_);
lean_inc(v_array_1268_);
lean_dec(v_pos_1266_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1286_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1273_ = lean_byte_array_size(v_array_1268_);
v___x_1274_ = lean_nat_dec_lt(v_idx_1269_, v___x_1273_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; 
lean_del_object(v___x_1271_);
lean_dec(v_idx_1269_);
lean_dec_ref(v_array_1268_);
lean_dec(v_res_1267_);
v___x_1275_ = lean_box(0);
v_err_1260_ = v___x_1275_;
goto v___jp_1259_;
}
else
{
uint8_t v___x_1276_; uint8_t v_got_1277_; uint8_t v___x_1278_; 
v___x_1276_ = 64;
v_got_1277_ = lean_byte_array_fget(v_array_1268_, v_idx_1269_);
v___x_1278_ = lean_uint8_dec_eq(v_got_1277_, v___x_1276_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; 
lean_del_object(v___x_1271_);
lean_dec(v_idx_1269_);
lean_dec_ref(v_array_1268_);
lean_dec(v_res_1267_);
v___x_1279_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5));
v_err_1260_ = v___x_1279_;
goto v___jp_1259_;
}
else
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1283_; 
lean_dec_ref(v_a_1141_);
v___x_1280_ = lean_unsigned_to_nat(1u);
v___x_1281_ = lean_nat_add(v_idx_1269_, v___x_1280_);
lean_dec(v_idx_1269_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 1, v___x_1281_);
v___x_1283_ = v___x_1271_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_array_1268_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1284_; 
v___x_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1284_, 0, v_res_1267_);
v_pos_1194_ = v___x_1283_;
v_res_1195_ = v___x_1284_;
goto v___jp_1193_;
}
}
}
}
}
else
{
lean_object* v_err_1287_; 
v_err_1287_ = lean_ctor_get(v___x_1265_, 1);
lean_inc(v_err_1287_);
lean_dec_ref_known(v___x_1265_, 2);
v_err_1260_ = v_err_1287_;
goto v___jp_1259_;
}
v___jp_1142_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1147_, 0, v___y_1143_);
lean_ctor_set(v___x_1147_, 1, v___y_1144_);
lean_ctor_set(v___x_1147_, 2, v_port_1145_);
v___x_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___y_1146_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
return v___x_1148_;
}
v___jp_1149_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__1));
v___x_1152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___y_1150_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
return v___x_1152_;
}
v___jp_1153_:
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_box(1);
v___y_1143_ = v___y_1154_;
v___y_1144_ = v___y_1155_;
v_port_1145_ = v___x_1157_;
v___y_1146_ = v___y_1156_;
goto v___jp_1142_;
}
v___jp_1158_:
{
uint8_t v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = 47;
v___x_1164_ = lean_uint8_dec_eq(v_val_1161_, v___x_1163_);
if (v___x_1164_ == 0)
{
uint8_t v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = 63;
v___x_1166_ = lean_uint8_dec_eq(v_val_1161_, v___x_1165_);
if (v___x_1166_ == 0)
{
uint8_t v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = 35;
v___x_1168_ = lean_uint8_dec_eq(v_val_1161_, v___x_1167_);
if (v___x_1168_ == 0)
{
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
v___y_1150_ = v___y_1162_;
goto v___jp_1149_;
}
else
{
v___y_1154_ = v___y_1159_;
v___y_1155_ = v___y_1160_;
v___y_1156_ = v___y_1162_;
goto v___jp_1153_;
}
}
else
{
v___y_1154_ = v___y_1159_;
v___y_1155_ = v___y_1160_;
v___y_1156_ = v___y_1162_;
goto v___jp_1153_;
}
}
else
{
v___y_1154_ = v___y_1159_;
v___y_1155_ = v___y_1160_;
v___y_1156_ = v___y_1162_;
goto v___jp_1153_;
}
}
v___jp_1169_:
{
lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = lean_byte_array_size(v_array_1174_);
v___x_1178_ = lean_nat_dec_lt(v_idx_1175_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_dec(v_idx_1175_);
lean_dec_ref(v_array_1174_);
if (v___y_1172_ == 0)
{
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
v___y_1150_ = v_pos_1173_;
goto v___jp_1149_;
}
else
{
v___y_1154_ = v___y_1170_;
v___y_1155_ = v___y_1171_;
v___y_1156_ = v_pos_1173_;
goto v___jp_1153_;
}
}
else
{
uint8_t v___x_1179_; 
v___x_1179_ = lean_byte_array_fget(v_array_1174_, v_idx_1175_);
lean_dec(v_idx_1175_);
lean_dec_ref(v_array_1174_);
v___y_1159_ = v___y_1170_;
v___y_1160_ = v___y_1171_;
v_val_1161_ = v___x_1179_;
v___y_1162_ = v_pos_1173_;
goto v___jp_1158_;
}
}
v___jp_1180_:
{
lean_object* v___x_1187_; 
v___x_1187_ = lean_box(0);
v___y_1170_ = v___y_1181_;
v___y_1171_ = v___y_1183_;
v___y_1172_ = v___y_1185_;
v_pos_1173_ = v___y_1184_;
v_array_1174_ = v___y_1182_;
v_idx_1175_ = v___y_1186_;
v_res_1176_ = v___x_1187_;
goto v___jp_1169_;
}
v___jp_1188_:
{
lean_object* v___x_1192_; 
v___x_1192_ = lean_box(0);
v___y_1143_ = v___y_1189_;
v___y_1144_ = v___y_1190_;
v_port_1145_ = v___x_1192_;
v___y_1146_ = v_pos_1191_;
goto v___jp_1142_;
}
v___jp_1193_:
{
lean_object* v___x_1196_; 
v___x_1196_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_1140_, v_pos_1194_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_pos_1197_; lean_object* v_res_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1249_; 
v_pos_1197_ = lean_ctor_get(v___x_1196_, 0);
v_res_1198_ = lean_ctor_get(v___x_1196_, 1);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1200_ = v___x_1196_;
v_isShared_1201_ = v_isSharedCheck_1249_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_res_1198_);
lean_inc(v_pos_1197_);
lean_dec(v___x_1196_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1249_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v_array_1202_; lean_object* v_idx_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; 
v_array_1202_ = lean_ctor_get(v_pos_1197_, 0);
v_idx_1203_ = lean_ctor_get(v_pos_1197_, 1);
v___x_1204_ = lean_byte_array_size(v_array_1202_);
v___x_1205_ = lean_nat_dec_lt(v_idx_1203_, v___x_1204_);
if (v___x_1205_ == 0)
{
lean_del_object(v___x_1200_);
v___y_1189_ = v_res_1195_;
v___y_1190_ = v_res_1198_;
v_pos_1191_ = v_pos_1197_;
goto v___jp_1188_;
}
else
{
uint8_t v___x_1206_; uint8_t v___x_1207_; uint8_t v___x_1208_; 
v___x_1206_ = lean_byte_array_fget(v_array_1202_, v_idx_1203_);
v___x_1207_ = 58;
v___x_1208_ = lean_uint8_dec_eq(v___x_1206_, v___x_1207_);
if (v___x_1208_ == 0)
{
lean_del_object(v___x_1200_);
v___y_1189_ = v_res_1195_;
v___y_1190_ = v_res_1198_;
v_pos_1191_ = v_pos_1197_;
goto v___jp_1188_;
}
else
{
if (v___x_1205_ == 0)
{
lean_object* v___x_1209_; lean_object* v___x_1211_; 
lean_dec(v_res_1198_);
lean_dec(v_res_1195_);
v___x_1209_ = lean_box(0);
if (v_isShared_1201_ == 0)
{
lean_ctor_set_tag(v___x_1200_, 1);
lean_ctor_set(v___x_1200_, 1, v___x_1209_);
v___x_1211_ = v___x_1200_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_pos_1197_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v___x_1209_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
else
{
if (v___x_1208_ == 0)
{
lean_object* v___x_1213_; lean_object* v___x_1215_; 
lean_dec(v_res_1198_);
lean_dec(v_res_1195_);
v___x_1213_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_1201_ == 0)
{
lean_ctor_set_tag(v___x_1200_, 1);
lean_ctor_set(v___x_1200_, 1, v___x_1213_);
v___x_1215_ = v___x_1200_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_pos_1197_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v___x_1213_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
else
{
lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1246_; 
lean_inc(v_idx_1203_);
lean_inc_ref(v_array_1202_);
lean_del_object(v___x_1200_);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_pos_1197_);
if (v_isSharedCheck_1246_ == 0)
{
lean_object* v_unused_1247_; lean_object* v_unused_1248_; 
v_unused_1247_ = lean_ctor_get(v_pos_1197_, 1);
lean_dec(v_unused_1247_);
v_unused_1248_ = lean_ctor_get(v_pos_1197_, 0);
lean_dec(v_unused_1248_);
v___x_1218_ = v_pos_1197_;
v_isShared_1219_ = v_isSharedCheck_1246_;
goto v_resetjp_1217_;
}
else
{
lean_dec(v_pos_1197_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1246_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1223_; 
v___x_1220_ = lean_unsigned_to_nat(1u);
v___x_1221_ = lean_nat_add(v_idx_1203_, v___x_1220_);
lean_dec(v_idx_1203_);
lean_inc(v___x_1221_);
lean_inc_ref(v_array_1202_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 1, v___x_1221_);
v___x_1223_ = v___x_1218_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_array_1202_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
uint8_t v___x_1224_; 
v___x_1224_ = lean_nat_dec_lt(v___x_1221_, v___x_1204_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; 
v___x_1225_ = lean_box(0);
v___y_1170_ = v_res_1195_;
v___y_1171_ = v_res_1198_;
v___y_1172_ = v___x_1208_;
v_pos_1173_ = v___x_1223_;
v_array_1174_ = v_array_1202_;
v_idx_1175_ = v___x_1221_;
v_res_1176_ = v___x_1225_;
goto v___jp_1169_;
}
else
{
uint8_t v___x_1226_; uint8_t v___x_1227_; uint8_t v___x_1228_; 
v___x_1226_ = lean_byte_array_fget(v_array_1202_, v___x_1221_);
v___x_1227_ = 48;
v___x_1228_ = lean_uint8_dec_le(v___x_1227_, v___x_1226_);
if (v___x_1228_ == 0)
{
v___y_1181_ = v_res_1195_;
v___y_1182_ = v_array_1202_;
v___y_1183_ = v_res_1198_;
v___y_1184_ = v___x_1223_;
v___y_1185_ = v___x_1208_;
v___y_1186_ = v___x_1221_;
goto v___jp_1180_;
}
else
{
uint8_t v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = 57;
v___x_1230_ = lean_uint8_dec_le(v___x_1226_, v___x_1229_);
if (v___x_1230_ == 0)
{
v___y_1181_ = v_res_1195_;
v___y_1182_ = v_array_1202_;
v___y_1183_ = v_res_1198_;
v___y_1184_ = v___x_1223_;
v___y_1185_ = v___x_1208_;
v___y_1186_ = v___x_1221_;
goto v___jp_1180_;
}
else
{
lean_object* v___x_1231_; 
lean_dec(v___x_1221_);
lean_dec_ref(v_array_1202_);
v___x_1231_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_1223_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_pos_1232_; lean_object* v_res_1233_; lean_object* v___x_1234_; uint16_t v___x_1235_; 
v_pos_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_pos_1232_);
v_res_1233_ = lean_ctor_get(v___x_1231_, 1);
lean_inc(v_res_1233_);
lean_dec_ref_known(v___x_1231_, 2);
v___x_1234_ = lean_alloc_ctor(2, 0, 2);
v___x_1235_ = lean_unbox(v_res_1233_);
lean_dec(v_res_1233_);
lean_ctor_set_uint16(v___x_1234_, 0, v___x_1235_);
v___y_1143_ = v_res_1195_;
v___y_1144_ = v_res_1198_;
v_port_1145_ = v___x_1234_;
v___y_1146_ = v_pos_1232_;
goto v___jp_1142_;
}
else
{
lean_object* v_pos_1236_; lean_object* v_err_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
lean_dec(v_res_1198_);
lean_dec(v_res_1195_);
v_pos_1236_ = lean_ctor_get(v___x_1231_, 0);
v_err_1237_ = lean_ctor_get(v___x_1231_, 1);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1231_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_err_1237_);
lean_inc(v_pos_1236_);
lean_dec(v___x_1231_);
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
lean_object* v_pos_1250_; lean_object* v_err_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
lean_dec(v_res_1195_);
v_pos_1250_ = lean_ctor_get(v___x_1196_, 0);
v_err_1251_ = lean_ctor_get(v___x_1196_, 1);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1196_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_err_1251_);
lean_inc(v_pos_1250_);
lean_dec(v___x_1196_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_pos_1250_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_err_1251_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
v___jp_1259_:
{
lean_object* v_idx_1261_; uint8_t v___x_1262_; 
v_idx_1261_ = lean_ctor_get(v_a_1141_, 1);
v___x_1262_ = lean_nat_dec_eq(v_idx_1261_, v_idx_1261_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; 
v___x_1263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1263_, 0, v_a_1141_);
lean_ctor_set(v___x_1263_, 1, v_err_1260_);
return v___x_1263_;
}
else
{
lean_object* v___x_1264_; 
lean_dec(v_err_1260_);
v___x_1264_ = lean_box(0);
v_pos_1194_ = v_a_1141_;
v_res_1195_ = v___x_1264_;
goto v___jp_1193_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___boxed(lean_object* v_config_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_1288_, v_a_1289_);
lean_dec_ref(v_config_1288_);
return v_res_1290_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(uint8_t v_c_1291_){
_start:
{
uint8_t v___x_1339_; uint8_t v___x_1340_; 
v___x_1339_ = 48;
v___x_1340_ = lean_uint8_dec_le(v___x_1339_, v_c_1291_);
if (v___x_1340_ == 0)
{
goto v___jp_1334_;
}
else
{
uint8_t v___x_1341_; uint8_t v___x_1342_; 
v___x_1341_ = 57;
v___x_1342_ = lean_uint8_dec_le(v_c_1291_, v___x_1341_);
if (v___x_1342_ == 0)
{
goto v___jp_1334_;
}
else
{
return v___x_1342_;
}
}
v___jp_1292_:
{
uint8_t v___x_1293_; uint8_t v___x_1294_; 
v___x_1293_ = 45;
v___x_1294_ = lean_uint8_dec_eq(v_c_1291_, v___x_1293_);
if (v___x_1294_ == 0)
{
uint8_t v___x_1295_; uint8_t v___x_1296_; 
v___x_1295_ = 46;
v___x_1296_ = lean_uint8_dec_eq(v_c_1291_, v___x_1295_);
if (v___x_1296_ == 0)
{
uint8_t v___x_1297_; uint8_t v___x_1298_; 
v___x_1297_ = 95;
v___x_1298_ = lean_uint8_dec_eq(v_c_1291_, v___x_1297_);
if (v___x_1298_ == 0)
{
uint8_t v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = 126;
v___x_1300_ = lean_uint8_dec_eq(v_c_1291_, v___x_1299_);
if (v___x_1300_ == 0)
{
uint8_t v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = 33;
v___x_1302_ = lean_uint8_dec_eq(v_c_1291_, v___x_1301_);
if (v___x_1302_ == 0)
{
uint8_t v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = 36;
v___x_1304_ = lean_uint8_dec_eq(v_c_1291_, v___x_1303_);
if (v___x_1304_ == 0)
{
uint8_t v___x_1305_; uint8_t v___x_1306_; 
v___x_1305_ = 38;
v___x_1306_ = lean_uint8_dec_eq(v_c_1291_, v___x_1305_);
if (v___x_1306_ == 0)
{
uint8_t v___x_1307_; uint8_t v___x_1308_; 
v___x_1307_ = 39;
v___x_1308_ = lean_uint8_dec_eq(v_c_1291_, v___x_1307_);
if (v___x_1308_ == 0)
{
uint8_t v___x_1309_; uint8_t v___x_1310_; 
v___x_1309_ = 40;
v___x_1310_ = lean_uint8_dec_eq(v_c_1291_, v___x_1309_);
if (v___x_1310_ == 0)
{
uint8_t v___x_1311_; uint8_t v___x_1312_; 
v___x_1311_ = 41;
v___x_1312_ = lean_uint8_dec_eq(v_c_1291_, v___x_1311_);
if (v___x_1312_ == 0)
{
uint8_t v___x_1313_; uint8_t v___x_1314_; 
v___x_1313_ = 42;
v___x_1314_ = lean_uint8_dec_eq(v_c_1291_, v___x_1313_);
if (v___x_1314_ == 0)
{
uint8_t v___x_1315_; uint8_t v___x_1316_; 
v___x_1315_ = 43;
v___x_1316_ = lean_uint8_dec_eq(v_c_1291_, v___x_1315_);
if (v___x_1316_ == 0)
{
uint8_t v___x_1317_; uint8_t v___x_1318_; 
v___x_1317_ = 44;
v___x_1318_ = lean_uint8_dec_eq(v_c_1291_, v___x_1317_);
if (v___x_1318_ == 0)
{
uint8_t v___x_1319_; uint8_t v___x_1320_; 
v___x_1319_ = 59;
v___x_1320_ = lean_uint8_dec_eq(v_c_1291_, v___x_1319_);
if (v___x_1320_ == 0)
{
uint8_t v___x_1321_; uint8_t v___x_1322_; 
v___x_1321_ = 61;
v___x_1322_ = lean_uint8_dec_eq(v_c_1291_, v___x_1321_);
if (v___x_1322_ == 0)
{
uint8_t v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = 58;
v___x_1324_ = lean_uint8_dec_eq(v_c_1291_, v___x_1323_);
if (v___x_1324_ == 0)
{
uint8_t v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = 64;
v___x_1326_ = lean_uint8_dec_eq(v_c_1291_, v___x_1325_);
if (v___x_1326_ == 0)
{
uint8_t v___x_1327_; uint8_t v___x_1328_; 
v___x_1327_ = 37;
v___x_1328_ = lean_uint8_dec_eq(v_c_1291_, v___x_1327_);
return v___x_1328_;
}
else
{
return v___x_1326_;
}
}
else
{
return v___x_1324_;
}
}
else
{
return v___x_1322_;
}
}
else
{
return v___x_1320_;
}
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
v___jp_1329_:
{
uint8_t v___x_1330_; uint8_t v___x_1331_; 
v___x_1330_ = 65;
v___x_1331_ = lean_uint8_dec_le(v___x_1330_, v_c_1291_);
if (v___x_1331_ == 0)
{
goto v___jp_1292_;
}
else
{
uint8_t v___x_1332_; uint8_t v___x_1333_; 
v___x_1332_ = 90;
v___x_1333_ = lean_uint8_dec_le(v_c_1291_, v___x_1332_);
if (v___x_1333_ == 0)
{
goto v___jp_1292_;
}
else
{
return v___x_1333_;
}
}
}
v___jp_1334_:
{
uint8_t v___x_1335_; uint8_t v___x_1336_; 
v___x_1335_ = 97;
v___x_1336_ = lean_uint8_dec_le(v___x_1335_, v_c_1291_);
if (v___x_1336_ == 0)
{
goto v___jp_1329_;
}
else
{
uint8_t v___x_1337_; uint8_t v___x_1338_; 
v___x_1337_ = 122;
v___x_1338_ = lean_uint8_dec_le(v_c_1291_, v___x_1337_);
if (v___x_1338_ == 0)
{
goto v___jp_1329_;
}
else
{
return v___x_1338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0___boxed(lean_object* v_c_1343_){
_start:
{
uint8_t v_c_boxed_1344_; uint8_t v_res_1345_; lean_object* v_r_1346_; 
v_c_boxed_1344_ = lean_unbox(v_c_1343_);
v_res_1345_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(v_c_boxed_1344_);
v_r_1346_ = lean_box(v_res_1345_);
return v_r_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(lean_object* v_config_1348_, lean_object* v_a_1349_){
_start:
{
lean_object* v_maxSegmentLength_1350_; lean_object* v___f_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v_snd_1354_; lean_object* v_fst_1355_; lean_object* v_fst_1356_; lean_object* v_array_1357_; lean_object* v_idx_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1375_; 
v_maxSegmentLength_1350_ = lean_ctor_get(v_config_1348_, 3);
v___f_1351_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___closed__0));
v___x_1352_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1349_);
v___x_1353_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1351_, v_maxSegmentLength_1350_, v___x_1352_, v_a_1349_);
v_snd_1354_ = lean_ctor_get(v___x_1353_, 1);
lean_inc(v_snd_1354_);
v_fst_1355_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_fst_1355_);
lean_dec_ref(v___x_1353_);
v_fst_1356_ = lean_ctor_get(v_snd_1354_, 0);
lean_inc(v_fst_1356_);
lean_dec(v_snd_1354_);
v_array_1357_ = lean_ctor_get(v_a_1349_, 0);
v_idx_1358_ = lean_ctor_get(v_a_1349_, 1);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_a_1349_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1360_ = v_a_1349_;
v_isShared_1361_ = v_isSharedCheck_1375_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_idx_1358_);
lean_inc(v_array_1357_);
lean_dec(v_a_1349_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1375_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v_lower_1363_; lean_object* v_upper_1364_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___y_1372_; uint8_t v___x_1374_; 
v___x_1369_ = lean_nat_add(v_idx_1358_, v_fst_1355_);
lean_dec(v_fst_1355_);
v___x_1370_ = lean_byte_array_size(v_array_1357_);
v___x_1374_ = lean_nat_dec_le(v_idx_1358_, v___x_1352_);
if (v___x_1374_ == 0)
{
v___y_1372_ = v_idx_1358_;
goto v___jp_1371_;
}
else
{
lean_dec(v_idx_1358_);
v___y_1372_ = v___x_1352_;
goto v___jp_1371_;
}
v___jp_1362_:
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
v___x_1365_ = l_ByteArray_toByteSlice(v_array_1357_, v_lower_1363_, v_upper_1364_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 1, v___x_1365_);
lean_ctor_set(v___x_1360_, 0, v_fst_1356_);
v___x_1367_ = v___x_1360_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_fst_1356_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
v___jp_1371_:
{
uint8_t v___x_1373_; 
v___x_1373_ = lean_nat_dec_le(v___x_1369_, v___x_1370_);
if (v___x_1373_ == 0)
{
lean_dec(v___x_1369_);
v_lower_1363_ = v___y_1372_;
v_upper_1364_ = v___x_1370_;
goto v___jp_1362_;
}
else
{
v_lower_1363_ = v___y_1372_;
v_upper_1364_ = v___x_1369_;
goto v___jp_1362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___boxed(lean_object* v_config_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1376_, v_a_1377_);
lean_dec_ref(v_config_1376_);
return v_res_1378_;
}
}
LEAN_EXPORT uint8_t l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(uint8_t v_c_1379_){
_start:
{
uint8_t v___x_1380_; uint8_t v___x_1381_; 
v___x_1380_ = 63;
v___x_1381_ = lean_uint8_dec_eq(v_c_1379_, v___x_1380_);
if (v___x_1381_ == 0)
{
uint8_t v___x_1382_; uint8_t v___x_1383_; 
v___x_1382_ = 35;
v___x_1383_ = lean_uint8_dec_eq(v_c_1379_, v___x_1382_);
return v___x_1383_;
}
else
{
return v___x_1381_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0___boxed(lean_object* v_c_1384_){
_start:
{
uint8_t v_c_boxed_1385_; uint8_t v_res_1386_; lean_object* v_r_1387_; 
v_c_boxed_1385_ = lean_unbox(v_c_1384_);
v_res_1386_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v_c_boxed_1385_);
v_r_1387_ = lean_box(v_res_1386_);
return v_r_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(lean_object* v_config_1395_, lean_object* v_a_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v_array_1422_; lean_object* v_idx_1423_; lean_object* v_fst_1424_; lean_object* v_snd_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1590_; 
v_array_1422_ = lean_ctor_get(v___y_1397_, 0);
v_idx_1423_ = lean_ctor_get(v___y_1397_, 1);
v_fst_1424_ = lean_ctor_get(v_a_1396_, 0);
v_snd_1425_ = lean_ctor_get(v_a_1396_, 1);
v_isSharedCheck_1590_ = !lean_is_exclusive(v_a_1396_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1427_ = v_a_1396_;
v_isShared_1428_ = v_isSharedCheck_1590_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_snd_1425_);
lean_inc(v_fst_1424_);
lean_dec(v_a_1396_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1590_;
goto v_resetjp_1426_;
}
v___jp_1398_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1402_, 0, v___y_1399_);
lean_ctor_set(v___x_1402_, 1, v___y_1400_);
v___x_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___y_1401_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
return v___x_1403_;
}
v___jp_1404_:
{
lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1409_ = lean_array_get_size(v___y_1405_);
v___x_1410_ = lean_nat_dec_le(v___y_1407_, v___x_1409_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
lean_dec(v___y_1407_);
v___x_1411_ = l_ByteArray_empty;
v___x_1412_ = lean_array_push(v___y_1405_, v___x_1411_);
v___x_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1412_);
lean_ctor_set(v___x_1413_, 1, v___y_1408_);
v_a_1396_ = v___x_1413_;
v___y_1397_ = v___y_1406_;
goto _start;
}
else
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1405_);
lean_dec_ref(v_config_1395_);
v___x_1415_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1416_ = l_Nat_reprFast(v___y_1407_);
v___x_1417_ = lean_string_append(v___x_1415_, v___x_1416_);
lean_dec_ref(v___x_1416_);
v___x_1418_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1419_ = lean_string_append(v___x_1417_, v___x_1418_);
v___x_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
v___x_1421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1421_, 0, v___y_1406_);
lean_ctor_set(v___x_1421_, 1, v___x_1420_);
return v___x_1421_;
}
}
v_resetjp_1426_:
{
lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1429_ = lean_byte_array_size(v_array_1422_);
v___x_1430_ = lean_nat_dec_lt(v_idx_1423_, v___x_1429_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1432_; 
lean_dec_ref(v_config_1395_);
if (v_isShared_1428_ == 0)
{
v___x_1432_ = v___x_1427_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_fst_1424_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_snd_1425_);
v___x_1432_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___y_1397_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
return v___x_1433_;
}
}
else
{
uint8_t v___x_1531_; uint8_t v___x_1581_; 
v___x_1531_ = lean_byte_array_fget(v_array_1422_, v_idx_1423_);
v___x_1581_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1531_);
if (v___x_1581_ == 0)
{
uint8_t v___x_1582_; uint8_t v___x_1583_; 
v___x_1582_ = 47;
v___x_1583_ = lean_uint8_dec_eq(v___x_1531_, v___x_1582_);
if (v___x_1583_ == 0)
{
uint8_t v___x_1584_; uint8_t v___x_1585_; 
v___x_1584_ = 48;
v___x_1585_ = lean_uint8_dec_le(v___x_1584_, v___x_1531_);
if (v___x_1585_ == 0)
{
goto v___jp_1576_;
}
else
{
uint8_t v___x_1586_; uint8_t v___x_1587_; 
v___x_1586_ = 57;
v___x_1587_ = lean_uint8_dec_le(v___x_1531_, v___x_1586_);
if (v___x_1587_ == 0)
{
goto v___jp_1576_;
}
else
{
goto v___jp_1435_;
}
}
}
else
{
goto v___jp_1435_;
}
}
else
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
lean_del_object(v___x_1427_);
lean_dec_ref(v_config_1395_);
v___x_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1588_, 0, v_fst_1424_);
lean_ctor_set(v___x_1588_, 1, v_snd_1425_);
v___x_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___y_1397_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
return v___x_1589_;
}
v___jp_1435_:
{
lean_object* v_maxPathSegments_1436_; lean_object* v_maxTotalPathLength_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; 
v_maxPathSegments_1436_ = lean_ctor_get(v_config_1395_, 6);
v_maxTotalPathLength_1437_ = lean_ctor_get(v_config_1395_, 7);
v___x_1438_ = lean_array_get_size(v_fst_1424_);
v___x_1439_ = lean_nat_dec_le(v_maxPathSegments_1436_, v___x_1438_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; 
v___x_1440_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1395_, v___y_1397_);
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
v___x_1453_ = lean_nat_add(v_snd_1425_, v___x_1452_);
lean_dec(v___x_1452_);
lean_dec(v_snd_1425_);
v___x_1454_ = lean_nat_dec_lt(v_maxTotalPathLength_1437_, v___x_1453_);
if (v___x_1454_ == 0)
{
lean_object* v_array_1455_; lean_object* v_idx_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; uint8_t v___x_1459_; 
v_array_1455_ = lean_ctor_get(v_pos_1441_, 0);
v_idx_1456_ = lean_ctor_get(v_pos_1441_, 1);
v___x_1457_ = lean_array_push(v_fst_1424_, v_val_1448_);
v___x_1458_ = lean_byte_array_size(v_array_1455_);
v___x_1459_ = lean_nat_dec_lt(v_idx_1456_, v___x_1458_);
if (v___x_1459_ == 0)
{
lean_del_object(v___x_1450_);
lean_del_object(v___x_1444_);
lean_del_object(v___x_1427_);
lean_dec_ref(v_config_1395_);
v___y_1399_ = v___x_1457_;
v___y_1400_ = v___x_1453_;
v___y_1401_ = v_pos_1441_;
goto v___jp_1398_;
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
lean_del_object(v___x_1427_);
lean_dec_ref(v_config_1395_);
v___y_1399_ = v___x_1457_;
v___y_1400_ = v___x_1453_;
v___y_1401_ = v_pos_1441_;
goto v___jp_1398_;
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
lean_del_object(v___x_1427_);
lean_dec_ref(v_config_1395_);
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
lean_del_object(v___x_1427_);
lean_inc(v_maxPathSegments_1436_);
v___y_1405_ = v___x_1457_;
v___y_1406_ = v___x_1475_;
v___y_1407_ = v_maxPathSegments_1436_;
v___y_1408_ = v___x_1464_;
goto v___jp_1404_;
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
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 1, v___x_1464_);
lean_ctor_set(v___x_1427_, 0, v___x_1457_);
v___x_1480_ = v___x_1427_;
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
v_a_1396_ = v___x_1480_;
v___y_1397_ = v___x_1475_;
goto _start;
}
}
else
{
lean_del_object(v___x_1427_);
lean_inc(v_maxPathSegments_1436_);
v___y_1405_ = v___x_1457_;
v___y_1406_ = v___x_1475_;
v___y_1407_ = v_maxPathSegments_1436_;
v___y_1408_ = v___x_1464_;
goto v___jp_1404_;
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
lean_del_object(v___x_1427_);
lean_dec_ref(v_config_1395_);
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
lean_del_object(v___x_1427_);
lean_dec(v_fst_1424_);
lean_dec_ref(v_config_1395_);
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
lean_del_object(v___x_1427_);
lean_dec(v_snd_1425_);
lean_dec(v_fst_1424_);
lean_dec_ref(v_config_1395_);
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
lean_del_object(v___x_1427_);
lean_dec(v_snd_1425_);
lean_dec(v_fst_1424_);
lean_dec_ref(v_config_1395_);
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
lean_del_object(v___x_1427_);
lean_dec(v_snd_1425_);
lean_dec(v_fst_1424_);
lean_dec_ref(v_config_1395_);
v___x_1524_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1525_ = l_Nat_reprFast(v_maxPathSegments_1436_);
v___x_1526_ = lean_string_append(v___x_1524_, v___x_1525_);
lean_dec_ref(v___x_1525_);
v___x_1527_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1528_ = lean_string_append(v___x_1526_, v___x_1527_);
v___x_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
v___x_1530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___y_1397_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
return v___x_1530_;
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
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
lean_del_object(v___x_1427_);
lean_dec_ref(v_config_1395_);
v___x_1569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1569_, 0, v_fst_1424_);
lean_ctor_set(v___x_1569_, 1, v_snd_1425_);
v___x_1570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___y_1397_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
return v___x_1570_;
}
else
{
goto v___jp_1435_;
}
}
else
{
goto v___jp_1435_;
}
}
else
{
goto v___jp_1435_;
}
}
else
{
goto v___jp_1435_;
}
}
else
{
goto v___jp_1435_;
}
}
else
{
goto v___jp_1435_;
}
}
else
{
goto v___jp_1435_;
}
}
else
{
goto v___jp_1435_;
}
}
else
{
goto v___jp_1435_;
}
}
else
{
goto v___jp_1435_;
}
}
else
{
goto v___jp_1435_;
}
}
else
{
goto v___jp_1435_;
}
}
else
{
goto v___jp_1435_;
}
}
else
{
goto v___jp_1435_;
}
}
else
{
goto v___jp_1435_;
}
}
else
{
goto v___jp_1435_;
}
}
else
{
goto v___jp_1435_;
}
}
else
{
goto v___jp_1435_;
}
}
v___jp_1571_:
{
uint8_t v___x_1572_; uint8_t v___x_1573_; 
v___x_1572_ = 65;
v___x_1573_ = lean_uint8_dec_le(v___x_1572_, v___x_1531_);
if (v___x_1573_ == 0)
{
goto v___jp_1532_;
}
else
{
uint8_t v___x_1574_; uint8_t v___x_1575_; 
v___x_1574_ = 90;
v___x_1575_ = lean_uint8_dec_le(v___x_1531_, v___x_1574_);
if (v___x_1575_ == 0)
{
goto v___jp_1532_;
}
else
{
goto v___jp_1435_;
}
}
}
v___jp_1576_:
{
uint8_t v___x_1577_; uint8_t v___x_1578_; 
v___x_1577_ = 97;
v___x_1578_ = lean_uint8_dec_le(v___x_1577_, v___x_1531_);
if (v___x_1578_ == 0)
{
goto v___jp_1571_;
}
else
{
uint8_t v___x_1579_; uint8_t v___x_1580_; 
v___x_1579_ = 122;
v___x_1580_ = lean_uint8_dec_le(v___x_1531_, v___x_1579_);
if (v___x_1580_ == 0)
{
goto v___jp_1571_;
}
else
{
goto v___jp_1435_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(lean_object* v_config_1591_, lean_object* v_a_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v_array_1618_; lean_object* v_idx_1619_; lean_object* v_fst_1620_; lean_object* v_snd_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1786_; 
v_array_1618_ = lean_ctor_get(v___y_1593_, 0);
v_idx_1619_ = lean_ctor_get(v___y_1593_, 1);
v_fst_1620_ = lean_ctor_get(v_a_1592_, 0);
v_snd_1621_ = lean_ctor_get(v_a_1592_, 1);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_a_1592_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1623_ = v_a_1592_;
v_isShared_1624_ = v_isSharedCheck_1786_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_snd_1621_);
lean_inc(v_fst_1620_);
lean_dec(v_a_1592_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1786_;
goto v_resetjp_1622_;
}
v___jp_1594_:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___y_1595_);
lean_ctor_set(v___x_1598_, 1, v___y_1596_);
v___x_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___y_1597_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
return v___x_1599_;
}
v___jp_1600_:
{
lean_object* v___x_1605_; uint8_t v___x_1606_; 
v___x_1605_ = lean_array_get_size(v___y_1602_);
v___x_1606_ = lean_nat_dec_le(v___y_1604_, v___x_1605_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
lean_dec(v___y_1604_);
v___x_1607_ = l_ByteArray_empty;
v___x_1608_ = lean_array_push(v___y_1602_, v___x_1607_);
v___x_1609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
lean_ctor_set(v___x_1609_, 1, v___y_1601_);
v___x_1610_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_1591_, v___x_1609_, v___y_1603_);
return v___x_1610_;
}
else
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v_config_1591_);
v___x_1611_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1612_ = l_Nat_reprFast(v___y_1604_);
v___x_1613_ = lean_string_append(v___x_1611_, v___x_1612_);
lean_dec_ref(v___x_1612_);
v___x_1614_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1615_ = lean_string_append(v___x_1613_, v___x_1614_);
v___x_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
v___x_1617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___y_1603_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
return v___x_1617_;
}
}
v_resetjp_1622_:
{
lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1625_ = lean_byte_array_size(v_array_1618_);
v___x_1626_ = lean_nat_dec_lt(v_idx_1619_, v___x_1625_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1628_; 
lean_dec_ref(v_config_1591_);
if (v_isShared_1624_ == 0)
{
v___x_1628_ = v___x_1623_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_fst_1620_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_snd_1621_);
v___x_1628_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
lean_object* v___x_1629_; 
v___x_1629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___y_1593_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
return v___x_1629_;
}
}
else
{
uint8_t v___x_1727_; uint8_t v___x_1777_; 
v___x_1727_ = lean_byte_array_fget(v_array_1618_, v_idx_1619_);
v___x_1777_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1727_);
if (v___x_1777_ == 0)
{
uint8_t v___x_1778_; uint8_t v___x_1779_; 
v___x_1778_ = 47;
v___x_1779_ = lean_uint8_dec_eq(v___x_1727_, v___x_1778_);
if (v___x_1779_ == 0)
{
uint8_t v___x_1780_; uint8_t v___x_1781_; 
v___x_1780_ = 48;
v___x_1781_ = lean_uint8_dec_le(v___x_1780_, v___x_1727_);
if (v___x_1781_ == 0)
{
goto v___jp_1772_;
}
else
{
uint8_t v___x_1782_; uint8_t v___x_1783_; 
v___x_1782_ = 57;
v___x_1783_ = lean_uint8_dec_le(v___x_1727_, v___x_1782_);
if (v___x_1783_ == 0)
{
goto v___jp_1772_;
}
else
{
goto v___jp_1631_;
}
}
}
else
{
goto v___jp_1631_;
}
}
else
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
lean_del_object(v___x_1623_);
lean_dec_ref(v_config_1591_);
v___x_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1784_, 0, v_fst_1620_);
lean_ctor_set(v___x_1784_, 1, v_snd_1621_);
v___x_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___y_1593_);
lean_ctor_set(v___x_1785_, 1, v___x_1784_);
return v___x_1785_;
}
v___jp_1631_:
{
lean_object* v_maxPathSegments_1632_; lean_object* v_maxTotalPathLength_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v_maxPathSegments_1632_ = lean_ctor_get(v_config_1591_, 6);
v_maxTotalPathLength_1633_ = lean_ctor_get(v_config_1591_, 7);
v___x_1634_ = lean_array_get_size(v_fst_1620_);
v___x_1635_ = lean_nat_dec_le(v_maxPathSegments_1632_, v___x_1634_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; 
v___x_1636_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1591_, v___y_1593_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_pos_1637_; lean_object* v_res_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1710_; 
v_pos_1637_ = lean_ctor_get(v___x_1636_, 0);
v_res_1638_ = lean_ctor_get(v___x_1636_, 1);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1640_ = v___x_1636_;
v_isShared_1641_ = v_isSharedCheck_1710_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_res_1638_);
lean_inc(v_pos_1637_);
lean_dec(v___x_1636_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1710_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
lean_inc(v_res_1638_);
v___x_1642_ = l_ByteSlice_toByteArray(v_res_1638_);
v___x_1643_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_1642_);
if (lean_obj_tag(v___x_1643_) == 1)
{
lean_object* v_val_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1705_; 
v_val_1644_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1646_ = v___x_1643_;
v_isShared_1647_ = v_isSharedCheck_1705_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_val_1644_);
lean_dec(v___x_1643_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1705_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; uint8_t v___x_1650_; 
v___x_1648_ = l_ByteSlice_size(v_res_1638_);
lean_dec(v_res_1638_);
v___x_1649_ = lean_nat_add(v_snd_1621_, v___x_1648_);
lean_dec(v___x_1648_);
lean_dec(v_snd_1621_);
v___x_1650_ = lean_nat_dec_lt(v_maxTotalPathLength_1633_, v___x_1649_);
if (v___x_1650_ == 0)
{
lean_object* v_array_1651_; lean_object* v_idx_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; uint8_t v___x_1655_; 
v_array_1651_ = lean_ctor_get(v_pos_1637_, 0);
v_idx_1652_ = lean_ctor_get(v_pos_1637_, 1);
v___x_1653_ = lean_array_push(v_fst_1620_, v_val_1644_);
v___x_1654_ = lean_byte_array_size(v_array_1651_);
v___x_1655_ = lean_nat_dec_lt(v_idx_1652_, v___x_1654_);
if (v___x_1655_ == 0)
{
lean_del_object(v___x_1646_);
lean_del_object(v___x_1640_);
lean_del_object(v___x_1623_);
lean_dec_ref(v_config_1591_);
v___y_1595_ = v___x_1653_;
v___y_1596_ = v___x_1649_;
v___y_1597_ = v_pos_1637_;
goto v___jp_1594_;
}
else
{
uint8_t v___x_1656_; uint8_t v___x_1657_; uint8_t v___x_1658_; 
v___x_1656_ = lean_byte_array_fget(v_array_1651_, v_idx_1652_);
v___x_1657_ = 47;
v___x_1658_ = lean_uint8_dec_eq(v___x_1656_, v___x_1657_);
if (v___x_1658_ == 0)
{
lean_del_object(v___x_1646_);
lean_del_object(v___x_1640_);
lean_del_object(v___x_1623_);
lean_dec_ref(v_config_1591_);
v___y_1595_ = v___x_1653_;
v___y_1596_ = v___x_1649_;
v___y_1597_ = v_pos_1637_;
goto v___jp_1594_;
}
else
{
lean_object* v___x_1659_; lean_object* v___x_1660_; uint8_t v___x_1661_; 
v___x_1659_ = lean_unsigned_to_nat(1u);
v___x_1660_ = lean_nat_add(v___x_1649_, v___x_1659_);
lean_dec(v___x_1649_);
v___x_1661_ = lean_nat_dec_lt(v_maxTotalPathLength_1633_, v___x_1660_);
if (v___x_1661_ == 0)
{
lean_del_object(v___x_1646_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1662_; lean_object* v___x_1664_; 
lean_dec(v___x_1660_);
lean_dec_ref(v___x_1653_);
lean_del_object(v___x_1623_);
lean_dec_ref(v_config_1591_);
v___x_1662_ = lean_box(0);
if (v_isShared_1641_ == 0)
{
lean_ctor_set_tag(v___x_1640_, 1);
lean_ctor_set(v___x_1640_, 1, v___x_1662_);
v___x_1664_ = v___x_1640_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_pos_1637_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v___x_1662_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
else
{
lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1680_; 
lean_inc(v_idx_1652_);
lean_inc_ref(v_array_1651_);
lean_del_object(v___x_1640_);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_pos_1637_);
if (v_isSharedCheck_1680_ == 0)
{
lean_object* v_unused_1681_; lean_object* v_unused_1682_; 
v_unused_1681_ = lean_ctor_get(v_pos_1637_, 1);
lean_dec(v_unused_1681_);
v_unused_1682_ = lean_ctor_get(v_pos_1637_, 0);
lean_dec(v_unused_1682_);
v___x_1667_ = v_pos_1637_;
v_isShared_1668_ = v_isSharedCheck_1680_;
goto v_resetjp_1666_;
}
else
{
lean_dec(v_pos_1637_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1680_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1669_ = lean_nat_add(v_idx_1652_, v___x_1659_);
lean_dec(v_idx_1652_);
lean_inc(v___x_1669_);
lean_inc_ref(v_array_1651_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 1, v___x_1669_);
v___x_1671_ = v___x_1667_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_array_1651_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
uint8_t v___x_1672_; 
v___x_1672_ = lean_nat_dec_lt(v___x_1669_, v___x_1654_);
if (v___x_1672_ == 0)
{
lean_dec(v___x_1669_);
lean_dec_ref(v_array_1651_);
lean_del_object(v___x_1623_);
lean_inc(v_maxPathSegments_1632_);
v___y_1601_ = v___x_1660_;
v___y_1602_ = v___x_1653_;
v___y_1603_ = v___x_1671_;
v___y_1604_ = v_maxPathSegments_1632_;
goto v___jp_1600_;
}
else
{
uint8_t v___x_1673_; uint8_t v___x_1674_; 
v___x_1673_ = lean_byte_array_fget(v_array_1651_, v___x_1669_);
lean_dec(v___x_1669_);
lean_dec_ref(v_array_1651_);
v___x_1674_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1673_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1676_; 
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 1, v___x_1660_);
lean_ctor_set(v___x_1623_, 0, v___x_1653_);
v___x_1676_ = v___x_1623_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1653_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v___x_1660_);
v___x_1676_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
lean_object* v___x_1677_; 
v___x_1677_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_1591_, v___x_1676_, v___x_1671_);
return v___x_1677_;
}
}
else
{
lean_del_object(v___x_1623_);
lean_inc(v_maxPathSegments_1632_);
v___y_1601_ = v___x_1660_;
v___y_1602_ = v___x_1653_;
v___y_1603_ = v___x_1671_;
v___y_1604_ = v_maxPathSegments_1632_;
goto v___jp_1600_;
}
}
}
}
}
}
else
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1689_; 
lean_inc(v_maxTotalPathLength_1633_);
lean_dec(v___x_1660_);
lean_dec_ref(v___x_1653_);
lean_del_object(v___x_1623_);
lean_dec_ref(v_config_1591_);
v___x_1683_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1684_ = l_Nat_reprFast(v_maxTotalPathLength_1633_);
v___x_1685_ = lean_string_append(v___x_1683_, v___x_1684_);
lean_dec_ref(v___x_1684_);
v___x_1686_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1687_ = lean_string_append(v___x_1685_, v___x_1686_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v___x_1687_);
v___x_1689_ = v___x_1646_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
lean_object* v___x_1691_; 
if (v_isShared_1641_ == 0)
{
lean_ctor_set_tag(v___x_1640_, 1);
lean_ctor_set(v___x_1640_, 1, v___x_1689_);
v___x_1691_ = v___x_1640_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_pos_1637_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
}
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1700_; 
lean_inc(v_maxTotalPathLength_1633_);
lean_dec(v___x_1649_);
lean_dec(v_val_1644_);
lean_del_object(v___x_1623_);
lean_dec(v_fst_1620_);
lean_dec_ref(v_config_1591_);
v___x_1694_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1695_ = l_Nat_reprFast(v_maxTotalPathLength_1633_);
v___x_1696_ = lean_string_append(v___x_1694_, v___x_1695_);
lean_dec_ref(v___x_1695_);
v___x_1697_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1698_ = lean_string_append(v___x_1696_, v___x_1697_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v___x_1698_);
v___x_1700_ = v___x_1646_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
lean_object* v___x_1702_; 
if (v_isShared_1641_ == 0)
{
lean_ctor_set_tag(v___x_1640_, 1);
lean_ctor_set(v___x_1640_, 1, v___x_1700_);
v___x_1702_ = v___x_1640_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_pos_1637_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v___x_1700_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
}
else
{
lean_object* v___x_1706_; lean_object* v___x_1708_; 
lean_dec(v___x_1643_);
lean_dec(v_res_1638_);
lean_del_object(v___x_1623_);
lean_dec(v_snd_1621_);
lean_dec(v_fst_1620_);
lean_dec_ref(v_config_1591_);
v___x_1706_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5));
if (v_isShared_1641_ == 0)
{
lean_ctor_set_tag(v___x_1640_, 1);
lean_ctor_set(v___x_1640_, 1, v___x_1706_);
v___x_1708_ = v___x_1640_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_pos_1637_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
else
{
lean_object* v_pos_1711_; lean_object* v_err_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
lean_del_object(v___x_1623_);
lean_dec(v_snd_1621_);
lean_dec(v_fst_1620_);
lean_dec_ref(v_config_1591_);
v_pos_1711_ = lean_ctor_get(v___x_1636_, 0);
v_err_1712_ = lean_ctor_get(v___x_1636_, 1);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1636_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_err_1712_);
lean_inc(v_pos_1711_);
lean_dec(v___x_1636_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_pos_1711_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_err_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
else
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
lean_inc(v_maxPathSegments_1632_);
lean_del_object(v___x_1623_);
lean_dec(v_snd_1621_);
lean_dec(v_fst_1620_);
lean_dec_ref(v_config_1591_);
v___x_1720_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1721_ = l_Nat_reprFast(v_maxPathSegments_1632_);
v___x_1722_ = lean_string_append(v___x_1720_, v___x_1721_);
lean_dec_ref(v___x_1721_);
v___x_1723_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1724_ = lean_string_append(v___x_1722_, v___x_1723_);
v___x_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1724_);
v___x_1726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___y_1593_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
return v___x_1726_;
}
}
v___jp_1728_:
{
uint8_t v___x_1729_; uint8_t v___x_1730_; 
v___x_1729_ = 45;
v___x_1730_ = lean_uint8_dec_eq(v___x_1727_, v___x_1729_);
if (v___x_1730_ == 0)
{
uint8_t v___x_1731_; uint8_t v___x_1732_; 
v___x_1731_ = 46;
v___x_1732_ = lean_uint8_dec_eq(v___x_1727_, v___x_1731_);
if (v___x_1732_ == 0)
{
uint8_t v___x_1733_; uint8_t v___x_1734_; 
v___x_1733_ = 95;
v___x_1734_ = lean_uint8_dec_eq(v___x_1727_, v___x_1733_);
if (v___x_1734_ == 0)
{
uint8_t v___x_1735_; uint8_t v___x_1736_; 
v___x_1735_ = 126;
v___x_1736_ = lean_uint8_dec_eq(v___x_1727_, v___x_1735_);
if (v___x_1736_ == 0)
{
uint8_t v___x_1737_; uint8_t v___x_1738_; 
v___x_1737_ = 33;
v___x_1738_ = lean_uint8_dec_eq(v___x_1727_, v___x_1737_);
if (v___x_1738_ == 0)
{
uint8_t v___x_1739_; uint8_t v___x_1740_; 
v___x_1739_ = 36;
v___x_1740_ = lean_uint8_dec_eq(v___x_1727_, v___x_1739_);
if (v___x_1740_ == 0)
{
uint8_t v___x_1741_; uint8_t v___x_1742_; 
v___x_1741_ = 38;
v___x_1742_ = lean_uint8_dec_eq(v___x_1727_, v___x_1741_);
if (v___x_1742_ == 0)
{
uint8_t v___x_1743_; uint8_t v___x_1744_; 
v___x_1743_ = 39;
v___x_1744_ = lean_uint8_dec_eq(v___x_1727_, v___x_1743_);
if (v___x_1744_ == 0)
{
uint8_t v___x_1745_; uint8_t v___x_1746_; 
v___x_1745_ = 40;
v___x_1746_ = lean_uint8_dec_eq(v___x_1727_, v___x_1745_);
if (v___x_1746_ == 0)
{
uint8_t v___x_1747_; uint8_t v___x_1748_; 
v___x_1747_ = 41;
v___x_1748_ = lean_uint8_dec_eq(v___x_1727_, v___x_1747_);
if (v___x_1748_ == 0)
{
uint8_t v___x_1749_; uint8_t v___x_1750_; 
v___x_1749_ = 42;
v___x_1750_ = lean_uint8_dec_eq(v___x_1727_, v___x_1749_);
if (v___x_1750_ == 0)
{
uint8_t v___x_1751_; uint8_t v___x_1752_; 
v___x_1751_ = 43;
v___x_1752_ = lean_uint8_dec_eq(v___x_1727_, v___x_1751_);
if (v___x_1752_ == 0)
{
uint8_t v___x_1753_; uint8_t v___x_1754_; 
v___x_1753_ = 44;
v___x_1754_ = lean_uint8_dec_eq(v___x_1727_, v___x_1753_);
if (v___x_1754_ == 0)
{
uint8_t v___x_1755_; uint8_t v___x_1756_; 
v___x_1755_ = 59;
v___x_1756_ = lean_uint8_dec_eq(v___x_1727_, v___x_1755_);
if (v___x_1756_ == 0)
{
uint8_t v___x_1757_; uint8_t v___x_1758_; 
v___x_1757_ = 61;
v___x_1758_ = lean_uint8_dec_eq(v___x_1727_, v___x_1757_);
if (v___x_1758_ == 0)
{
uint8_t v___x_1759_; uint8_t v___x_1760_; 
v___x_1759_ = 58;
v___x_1760_ = lean_uint8_dec_eq(v___x_1727_, v___x_1759_);
if (v___x_1760_ == 0)
{
uint8_t v___x_1761_; uint8_t v___x_1762_; 
v___x_1761_ = 64;
v___x_1762_ = lean_uint8_dec_eq(v___x_1727_, v___x_1761_);
if (v___x_1762_ == 0)
{
uint8_t v___x_1763_; uint8_t v___x_1764_; 
v___x_1763_ = 37;
v___x_1764_ = lean_uint8_dec_eq(v___x_1727_, v___x_1763_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
lean_del_object(v___x_1623_);
lean_dec_ref(v_config_1591_);
v___x_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1765_, 0, v_fst_1620_);
lean_ctor_set(v___x_1765_, 1, v_snd_1621_);
v___x_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1766_, 0, v___y_1593_);
lean_ctor_set(v___x_1766_, 1, v___x_1765_);
return v___x_1766_;
}
else
{
goto v___jp_1631_;
}
}
else
{
goto v___jp_1631_;
}
}
else
{
goto v___jp_1631_;
}
}
else
{
goto v___jp_1631_;
}
}
else
{
goto v___jp_1631_;
}
}
else
{
goto v___jp_1631_;
}
}
else
{
goto v___jp_1631_;
}
}
else
{
goto v___jp_1631_;
}
}
else
{
goto v___jp_1631_;
}
}
else
{
goto v___jp_1631_;
}
}
else
{
goto v___jp_1631_;
}
}
else
{
goto v___jp_1631_;
}
}
else
{
goto v___jp_1631_;
}
}
else
{
goto v___jp_1631_;
}
}
else
{
goto v___jp_1631_;
}
}
else
{
goto v___jp_1631_;
}
}
else
{
goto v___jp_1631_;
}
}
else
{
goto v___jp_1631_;
}
}
v___jp_1767_:
{
uint8_t v___x_1768_; uint8_t v___x_1769_; 
v___x_1768_ = 65;
v___x_1769_ = lean_uint8_dec_le(v___x_1768_, v___x_1727_);
if (v___x_1769_ == 0)
{
goto v___jp_1728_;
}
else
{
uint8_t v___x_1770_; uint8_t v___x_1771_; 
v___x_1770_ = 90;
v___x_1771_ = lean_uint8_dec_le(v___x_1727_, v___x_1770_);
if (v___x_1771_ == 0)
{
goto v___jp_1728_;
}
else
{
goto v___jp_1631_;
}
}
}
v___jp_1772_:
{
uint8_t v___x_1773_; uint8_t v___x_1774_; 
v___x_1773_ = 97;
v___x_1774_ = lean_uint8_dec_le(v___x_1773_, v___x_1727_);
if (v___x_1774_ == 0)
{
goto v___jp_1767_;
}
else
{
uint8_t v___x_1775_; uint8_t v___x_1776_; 
v___x_1775_ = 122;
v___x_1776_ = lean_uint8_dec_le(v___x_1727_, v___x_1775_);
if (v___x_1776_ == 0)
{
goto v___jp_1767_;
}
else
{
goto v___jp_1631_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath(lean_object* v_config_1798_, uint8_t v_forceAbsolute_1799_, uint8_t v_allowEmpty_1800_, lean_object* v_a_1801_){
_start:
{
lean_object* v___y_1803_; lean_object* v___y_1807_; lean_object* v_array_1810_; lean_object* v_idx_1811_; uint8_t v_isAbsolute_1812_; lean_object* v___x_1813_; lean_object* v_segments_1814_; uint8_t v_isAbsolute_1816_; lean_object* v_totalLength_1817_; lean_object* v___y_1818_; lean_object* v_pos_1842_; lean_object* v_array_1843_; lean_object* v_idx_1844_; lean_object* v___y_1853_; uint8_t v___y_1857_; lean_object* v_pos_1858_; uint8_t v_res_1859_; uint8_t v___y_1861_; lean_object* v_pos_1862_; uint8_t v_res_1863_; lean_object* v___y_1871_; uint8_t v___y_1872_; uint8_t v___y_1873_; uint8_t v___y_1882_; lean_object* v_pos_1883_; uint8_t v_res_1884_; lean_object* v_pos_1886_; lean_object* v_array_1887_; lean_object* v_idx_1888_; uint8_t v_res_1889_; lean_object* v___x_1893_; uint8_t v___x_1894_; 
v_array_1810_ = lean_ctor_get(v_a_1801_, 0);
lean_inc_ref(v_array_1810_);
v_idx_1811_ = lean_ctor_get(v_a_1801_, 1);
lean_inc(v_idx_1811_);
v_isAbsolute_1812_ = 0;
v___x_1813_ = lean_unsigned_to_nat(0u);
v_segments_1814_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__4));
v___x_1893_ = lean_byte_array_size(v_array_1810_);
v___x_1894_ = lean_nat_dec_lt(v_idx_1811_, v___x_1893_);
if (v___x_1894_ == 0)
{
v_pos_1886_ = v_a_1801_;
v_array_1887_ = v_array_1810_;
v_idx_1888_ = v_idx_1811_;
v_res_1889_ = v_isAbsolute_1812_;
goto v___jp_1885_;
}
else
{
uint8_t v___x_1895_; uint8_t v___x_1945_; uint8_t v___x_1946_; 
v___x_1895_ = lean_byte_array_fget(v_array_1810_, v_idx_1811_);
v___x_1945_ = 48;
v___x_1946_ = lean_uint8_dec_le(v___x_1945_, v___x_1895_);
if (v___x_1946_ == 0)
{
goto v___jp_1940_;
}
else
{
uint8_t v___x_1947_; uint8_t v___x_1948_; 
v___x_1947_ = 57;
v___x_1948_ = lean_uint8_dec_le(v___x_1895_, v___x_1947_);
if (v___x_1948_ == 0)
{
goto v___jp_1940_;
}
else
{
v_pos_1886_ = v_a_1801_;
v_array_1887_ = v_array_1810_;
v_idx_1888_ = v_idx_1811_;
v_res_1889_ = v___x_1948_;
goto v___jp_1885_;
}
}
v___jp_1896_:
{
uint8_t v___x_1897_; uint8_t v___x_1898_; 
v___x_1897_ = 45;
v___x_1898_ = lean_uint8_dec_eq(v___x_1895_, v___x_1897_);
if (v___x_1898_ == 0)
{
uint8_t v___x_1899_; uint8_t v___x_1900_; 
v___x_1899_ = 46;
v___x_1900_ = lean_uint8_dec_eq(v___x_1895_, v___x_1899_);
if (v___x_1900_ == 0)
{
uint8_t v___x_1901_; uint8_t v___x_1902_; 
v___x_1901_ = 95;
v___x_1902_ = lean_uint8_dec_eq(v___x_1895_, v___x_1901_);
if (v___x_1902_ == 0)
{
uint8_t v___x_1903_; uint8_t v___x_1904_; 
v___x_1903_ = 126;
v___x_1904_ = lean_uint8_dec_eq(v___x_1895_, v___x_1903_);
if (v___x_1904_ == 0)
{
uint8_t v___x_1905_; uint8_t v___x_1906_; 
v___x_1905_ = 33;
v___x_1906_ = lean_uint8_dec_eq(v___x_1895_, v___x_1905_);
if (v___x_1906_ == 0)
{
uint8_t v___x_1907_; uint8_t v___x_1908_; 
v___x_1907_ = 36;
v___x_1908_ = lean_uint8_dec_eq(v___x_1895_, v___x_1907_);
if (v___x_1908_ == 0)
{
uint8_t v___x_1909_; uint8_t v___x_1910_; 
v___x_1909_ = 38;
v___x_1910_ = lean_uint8_dec_eq(v___x_1895_, v___x_1909_);
if (v___x_1910_ == 0)
{
uint8_t v___x_1911_; uint8_t v___x_1912_; 
v___x_1911_ = 39;
v___x_1912_ = lean_uint8_dec_eq(v___x_1895_, v___x_1911_);
if (v___x_1912_ == 0)
{
uint8_t v___x_1913_; uint8_t v___x_1914_; 
v___x_1913_ = 40;
v___x_1914_ = lean_uint8_dec_eq(v___x_1895_, v___x_1913_);
if (v___x_1914_ == 0)
{
uint8_t v___x_1915_; uint8_t v___x_1916_; 
v___x_1915_ = 41;
v___x_1916_ = lean_uint8_dec_eq(v___x_1895_, v___x_1915_);
if (v___x_1916_ == 0)
{
uint8_t v___x_1917_; uint8_t v___x_1918_; 
v___x_1917_ = 42;
v___x_1918_ = lean_uint8_dec_eq(v___x_1895_, v___x_1917_);
if (v___x_1918_ == 0)
{
uint8_t v___x_1919_; uint8_t v___x_1920_; 
v___x_1919_ = 43;
v___x_1920_ = lean_uint8_dec_eq(v___x_1895_, v___x_1919_);
if (v___x_1920_ == 0)
{
uint8_t v___x_1921_; uint8_t v___x_1922_; 
v___x_1921_ = 44;
v___x_1922_ = lean_uint8_dec_eq(v___x_1895_, v___x_1921_);
if (v___x_1922_ == 0)
{
uint8_t v___x_1923_; uint8_t v___x_1924_; 
v___x_1923_ = 59;
v___x_1924_ = lean_uint8_dec_eq(v___x_1895_, v___x_1923_);
if (v___x_1924_ == 0)
{
uint8_t v___x_1925_; uint8_t v___x_1926_; 
v___x_1925_ = 61;
v___x_1926_ = lean_uint8_dec_eq(v___x_1895_, v___x_1925_);
if (v___x_1926_ == 0)
{
uint8_t v___x_1927_; uint8_t v___x_1928_; 
v___x_1927_ = 58;
v___x_1928_ = lean_uint8_dec_eq(v___x_1895_, v___x_1927_);
if (v___x_1928_ == 0)
{
uint8_t v___x_1929_; uint8_t v___x_1930_; 
v___x_1929_ = 64;
v___x_1930_ = lean_uint8_dec_eq(v___x_1895_, v___x_1929_);
if (v___x_1930_ == 0)
{
uint8_t v___x_1931_; uint8_t v___x_1932_; 
v___x_1931_ = 37;
v___x_1932_ = lean_uint8_dec_eq(v___x_1895_, v___x_1931_);
if (v___x_1932_ == 0)
{
uint8_t v___x_1933_; uint8_t v___x_1934_; 
v___x_1933_ = 47;
v___x_1934_ = lean_uint8_dec_eq(v___x_1895_, v___x_1933_);
if (v___x_1934_ == 0)
{
v_pos_1886_ = v_a_1801_;
v_array_1887_ = v_array_1810_;
v_idx_1888_ = v_idx_1811_;
v_res_1889_ = v_isAbsolute_1812_;
goto v___jp_1885_;
}
else
{
v_pos_1886_ = v_a_1801_;
v_array_1887_ = v_array_1810_;
v_idx_1888_ = v_idx_1811_;
v_res_1889_ = v___x_1934_;
goto v___jp_1885_;
}
}
else
{
v_pos_1886_ = v_a_1801_;
v_array_1887_ = v_array_1810_;
v_idx_1888_ = v_idx_1811_;
v_res_1889_ = v___x_1932_;
goto v___jp_1885_;
}
}
else
{
v_pos_1886_ = v_a_1801_;
v_array_1887_ = v_array_1810_;
v_idx_1888_ = v_idx_1811_;
v_res_1889_ = v___x_1930_;
goto v___jp_1885_;
}
}
else
{
v_pos_1886_ = v_a_1801_;
v_array_1887_ = v_array_1810_;
v_idx_1888_ = v_idx_1811_;
v_res_1889_ = v___x_1928_;
goto v___jp_1885_;
}
}
else
{
v_pos_1886_ = v_a_1801_;
v_array_1887_ = v_array_1810_;
v_idx_1888_ = v_idx_1811_;
v_res_1889_ = v___x_1926_;
goto v___jp_1885_;
}
}
else
{
v_pos_1886_ = v_a_1801_;
v_array_1887_ = v_array_1810_;
v_idx_1888_ = v_idx_1811_;
v_res_1889_ = v___x_1924_;
goto v___jp_1885_;
}
}
else
{
v_pos_1886_ = v_a_1801_;
v_array_1887_ = v_array_1810_;
v_idx_1888_ = v_idx_1811_;
v_res_1889_ = v___x_1922_;
goto v___jp_1885_;
}
}
else
{
v_pos_1886_ = v_a_1801_;
v_array_1887_ = v_array_1810_;
v_idx_1888_ = v_idx_1811_;
v_res_1889_ = v___x_1920_;
goto v___jp_1885_;
}
}
else
{
v_pos_1886_ = v_a_1801_;
v_array_1887_ = v_array_1810_;
v_idx_1888_ = v_idx_1811_;
v_res_1889_ = v___x_1918_;
goto v___jp_1885_;
}
}
else
{
v_pos_1886_ = v_a_1801_;
v_array_1887_ = v_array_1810_;
v_idx_1888_ = v_idx_1811_;
v_res_1889_ = v___x_1916_;
goto v___jp_1885_;
}
}
else
{
v_pos_1886_ = v_a_1801_;
v_array_1887_ = v_array_1810_;
v_idx_1888_ = v_idx_1811_;
v_res_1889_ = v___x_1914_;
goto v___jp_1885_;
}
}
else
{
v_pos_1886_ = v_a_1801_;
v_array_1887_ = v_array_1810_;
v_idx_1888_ = v_idx_1811_;
v_res_1889_ = v___x_1912_;
goto v___jp_1885_;
}
}
else
{
v_pos_1886_ = v_a_1801_;
v_array_1887_ = v_array_1810_;
v_idx_1888_ = v_idx_1811_;
v_res_1889_ = v___x_1910_;
goto v___jp_1885_;
}
}
else
{
v_pos_1886_ = v_a_1801_;
v_array_1887_ = v_array_1810_;
v_idx_1888_ = v_idx_1811_;
v_res_1889_ = v___x_1908_;
goto v___jp_1885_;
}
}
else
{
v_pos_1886_ = v_a_1801_;
v_array_1887_ = v_array_1810_;
v_idx_1888_ = v_idx_1811_;
v_res_1889_ = v___x_1906_;
goto v___jp_1885_;
}
}
else
{
v_pos_1886_ = v_a_1801_;
v_array_1887_ = v_array_1810_;
v_idx_1888_ = v_idx_1811_;
v_res_1889_ = v___x_1904_;
goto v___jp_1885_;
}
}
else
{
v_pos_1886_ = v_a_1801_;
v_array_1887_ = v_array_1810_;
v_idx_1888_ = v_idx_1811_;
v_res_1889_ = v___x_1902_;
goto v___jp_1885_;
}
}
else
{
v_pos_1886_ = v_a_1801_;
v_array_1887_ = v_array_1810_;
v_idx_1888_ = v_idx_1811_;
v_res_1889_ = v___x_1900_;
goto v___jp_1885_;
}
}
else
{
v_pos_1886_ = v_a_1801_;
v_array_1887_ = v_array_1810_;
v_idx_1888_ = v_idx_1811_;
v_res_1889_ = v___x_1898_;
goto v___jp_1885_;
}
}
v___jp_1935_:
{
uint8_t v___x_1936_; uint8_t v___x_1937_; 
v___x_1936_ = 65;
v___x_1937_ = lean_uint8_dec_le(v___x_1936_, v___x_1895_);
if (v___x_1937_ == 0)
{
goto v___jp_1896_;
}
else
{
uint8_t v___x_1938_; uint8_t v___x_1939_; 
v___x_1938_ = 90;
v___x_1939_ = lean_uint8_dec_le(v___x_1895_, v___x_1938_);
if (v___x_1939_ == 0)
{
goto v___jp_1896_;
}
else
{
v_pos_1886_ = v_a_1801_;
v_array_1887_ = v_array_1810_;
v_idx_1888_ = v_idx_1811_;
v_res_1889_ = v___x_1939_;
goto v___jp_1885_;
}
}
}
v___jp_1940_:
{
uint8_t v___x_1941_; uint8_t v___x_1942_; 
v___x_1941_ = 97;
v___x_1942_ = lean_uint8_dec_le(v___x_1941_, v___x_1895_);
if (v___x_1942_ == 0)
{
goto v___jp_1935_;
}
else
{
uint8_t v___x_1943_; uint8_t v___x_1944_; 
v___x_1943_ = 122;
v___x_1944_ = lean_uint8_dec_le(v___x_1895_, v___x_1943_);
if (v___x_1944_ == 0)
{
goto v___jp_1935_;
}
else
{
v_pos_1886_ = v_a_1801_;
v_array_1887_ = v_array_1810_;
v_idx_1888_ = v_idx_1811_;
v_res_1889_ = v___x_1944_;
goto v___jp_1885_;
}
}
}
}
v___jp_1802_:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__1));
v___x_1805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___y_1803_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
return v___x_1805_;
}
v___jp_1806_:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__3));
v___x_1809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___y_1807_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
return v___x_1809_;
}
v___jp_1815_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1819_, 0, v_segments_1814_);
lean_ctor_set(v___x_1819_, 1, v_totalLength_1817_);
v___x_1820_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(v_config_1798_, v___x_1819_, v___y_1818_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_res_1821_; lean_object* v_pos_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1831_; 
v_res_1821_ = lean_ctor_get(v___x_1820_, 1);
v_pos_1822_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1824_ = v___x_1820_;
v_isShared_1825_ = v_isSharedCheck_1831_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_res_1821_);
lean_inc(v_pos_1822_);
lean_dec(v___x_1820_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1831_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v_fst_1826_; lean_object* v___x_1827_; lean_object* v___x_1829_; 
v_fst_1826_ = lean_ctor_get(v_res_1821_, 0);
lean_inc(v_fst_1826_);
lean_dec(v_res_1821_);
v___x_1827_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1827_, 0, v_fst_1826_);
lean_ctor_set_uint8(v___x_1827_, sizeof(void*)*1, v_isAbsolute_1816_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 1, v___x_1827_);
v___x_1829_ = v___x_1824_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_pos_1822_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
else
{
lean_object* v_pos_1832_; lean_object* v_err_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
v_pos_1832_ = lean_ctor_get(v___x_1820_, 0);
v_err_1833_ = lean_ctor_get(v___x_1820_, 1);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1820_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_err_1833_);
lean_inc(v_pos_1832_);
lean_dec(v___x_1820_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_pos_1832_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_err_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
v___jp_1841_:
{
lean_object* v___x_1845_; uint8_t v___x_1846_; 
v___x_1845_ = lean_byte_array_size(v_array_1843_);
v___x_1846_ = lean_nat_dec_lt(v_idx_1844_, v___x_1845_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
lean_dec(v_idx_1844_);
lean_dec_ref(v_array_1843_);
lean_dec_ref(v_config_1798_);
v___x_1847_ = lean_box(0);
v___x_1848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1848_, 0, v_pos_1842_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
return v___x_1848_;
}
else
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
lean_dec_ref(v_pos_1842_);
v___x_1849_ = lean_unsigned_to_nat(1u);
v___x_1850_ = lean_nat_add(v_idx_1844_, v___x_1849_);
lean_dec(v_idx_1844_);
v___x_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1851_, 0, v_array_1843_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v_isAbsolute_1816_ = v___x_1846_;
v_totalLength_1817_ = v___x_1849_;
v___y_1818_ = v___x_1851_;
goto v___jp_1815_;
}
}
v___jp_1852_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__5));
v___x_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___y_1853_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
return v___x_1855_;
}
v___jp_1856_:
{
if (v_allowEmpty_1800_ == 0)
{
v___y_1803_ = v_pos_1858_;
goto v___jp_1802_;
}
else
{
if (v_res_1859_ == 0)
{
if (v___y_1857_ == 0)
{
v___y_1853_ = v_pos_1858_;
goto v___jp_1852_;
}
else
{
v___y_1803_ = v_pos_1858_;
goto v___jp_1802_;
}
}
else
{
v___y_1853_ = v_pos_1858_;
goto v___jp_1852_;
}
}
}
v___jp_1860_:
{
if (v_res_1863_ == 0)
{
if (v_forceAbsolute_1799_ == 0)
{
v_isAbsolute_1816_ = v_isAbsolute_1812_;
v_totalLength_1817_ = v___x_1813_;
v___y_1818_ = v_pos_1862_;
goto v___jp_1815_;
}
else
{
lean_object* v_array_1864_; lean_object* v_idx_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; 
lean_dec_ref(v_config_1798_);
v_array_1864_ = lean_ctor_get(v_pos_1862_, 0);
v_idx_1865_ = lean_ctor_get(v_pos_1862_, 1);
v___x_1866_ = lean_byte_array_size(v_array_1864_);
v___x_1867_ = lean_nat_dec_lt(v_idx_1865_, v___x_1866_);
if (v___x_1867_ == 0)
{
v___y_1857_ = v___y_1861_;
v_pos_1858_ = v_pos_1862_;
v_res_1859_ = v_forceAbsolute_1799_;
goto v___jp_1856_;
}
else
{
v___y_1857_ = v___y_1861_;
v_pos_1858_ = v_pos_1862_;
v_res_1859_ = v_res_1863_;
goto v___jp_1856_;
}
}
}
else
{
lean_object* v_array_1868_; lean_object* v_idx_1869_; 
v_array_1868_ = lean_ctor_get(v_pos_1862_, 0);
lean_inc_ref(v_array_1868_);
v_idx_1869_ = lean_ctor_get(v_pos_1862_, 1);
lean_inc(v_idx_1869_);
v_pos_1842_ = v_pos_1862_;
v_array_1843_ = v_array_1868_;
v_idx_1844_ = v_idx_1869_;
goto v___jp_1841_;
}
}
v___jp_1870_:
{
lean_object* v_array_1874_; lean_object* v_idx_1875_; lean_object* v___x_1876_; uint8_t v___x_1877_; 
v_array_1874_ = lean_ctor_get(v___y_1871_, 0);
v_idx_1875_ = lean_ctor_get(v___y_1871_, 1);
v___x_1876_ = lean_byte_array_size(v_array_1874_);
v___x_1877_ = lean_nat_dec_lt(v_idx_1875_, v___x_1876_);
if (v___x_1877_ == 0)
{
v___y_1861_ = v___y_1872_;
v_pos_1862_ = v___y_1871_;
v_res_1863_ = v___y_1873_;
goto v___jp_1860_;
}
else
{
uint8_t v___x_1878_; uint8_t v___x_1879_; uint8_t v___x_1880_; 
v___x_1878_ = lean_byte_array_fget(v_array_1874_, v_idx_1875_);
v___x_1879_ = 47;
v___x_1880_ = lean_uint8_dec_eq(v___x_1878_, v___x_1879_);
if (v___x_1880_ == 0)
{
v___y_1861_ = v___y_1872_;
v_pos_1862_ = v___y_1871_;
v_res_1863_ = v___y_1873_;
goto v___jp_1860_;
}
else
{
lean_inc(v_idx_1875_);
lean_inc_ref(v_array_1874_);
v_pos_1842_ = v___y_1871_;
v_array_1843_ = v_array_1874_;
v_idx_1844_ = v_idx_1875_;
goto v___jp_1841_;
}
}
}
v___jp_1881_:
{
if (v_allowEmpty_1800_ == 0)
{
if (v_res_1884_ == 0)
{
if (v___y_1882_ == 0)
{
lean_dec_ref(v_config_1798_);
v___y_1807_ = v_pos_1883_;
goto v___jp_1806_;
}
else
{
v___y_1871_ = v_pos_1883_;
v___y_1872_ = v___y_1882_;
v___y_1873_ = v_res_1884_;
goto v___jp_1870_;
}
}
else
{
lean_dec_ref(v_config_1798_);
v___y_1807_ = v_pos_1883_;
goto v___jp_1806_;
}
}
else
{
v___y_1871_ = v_pos_1883_;
v___y_1872_ = v___y_1882_;
v___y_1873_ = v_isAbsolute_1812_;
goto v___jp_1870_;
}
}
v___jp_1885_:
{
lean_object* v___x_1890_; uint8_t v___x_1891_; 
v___x_1890_ = lean_byte_array_size(v_array_1887_);
lean_dec_ref(v_array_1887_);
v___x_1891_ = lean_nat_dec_lt(v_idx_1888_, v___x_1890_);
lean_dec(v_idx_1888_);
if (v___x_1891_ == 0)
{
uint8_t v___x_1892_; 
v___x_1892_ = 1;
v___y_1882_ = v_res_1889_;
v_pos_1883_ = v_pos_1886_;
v_res_1884_ = v___x_1892_;
goto v___jp_1881_;
}
else
{
v___y_1882_ = v_res_1889_;
v_pos_1883_ = v_pos_1886_;
v_res_1884_ = v_isAbsolute_1812_;
goto v___jp_1881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath___boxed(lean_object* v_config_1949_, lean_object* v_forceAbsolute_1950_, lean_object* v_allowEmpty_1951_, lean_object* v_a_1952_){
_start:
{
uint8_t v_forceAbsolute_boxed_1953_; uint8_t v_allowEmpty_boxed_1954_; lean_object* v_res_1955_; 
v_forceAbsolute_boxed_1953_ = lean_unbox(v_forceAbsolute_1950_);
v_allowEmpty_boxed_1954_ = lean_unbox(v_allowEmpty_1951_);
v_res_1955_ = l_Std_Http_URI_Parser_parsePath(v_config_1949_, v_forceAbsolute_boxed_1953_, v_allowEmpty_boxed_1954_, v_a_1952_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0(lean_object* v_config_1956_, lean_object* v_inst_1957_, lean_object* v_a_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(v_config_1956_, v_a_1958_, v___y_1959_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0(lean_object* v_config_1961_, lean_object* v_inst_1962_, lean_object* v_a_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_1961_, v_a_1963_, v___y_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg(){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0));
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg___boxed(lean_object* v___dummy_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg();
return v_res_1969_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1970_; 
v___x_1970_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg();
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(lean_object* v_s_1971_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___boxed(lean_object* v_s_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(v_s_1973_);
lean_dec_ref(v_s_1973_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg(){
_start:
{
lean_object* v___x_1976_; 
v___x_1976_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0));
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg___boxed(lean_object* v___dummy_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg();
return v_res_1978_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1979_; 
v___x_1979_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg();
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(lean_object* v_s_1980_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___boxed(lean_object* v_s_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(v_s_1982_);
lean_dec_ref(v_s_1982_);
return v_res_1983_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(uint8_t v_c_1984_){
_start:
{
uint8_t v___x_2036_; uint8_t v___x_2037_; 
v___x_2036_ = 48;
v___x_2037_ = lean_uint8_dec_le(v___x_2036_, v_c_1984_);
if (v___x_2037_ == 0)
{
goto v___jp_2031_;
}
else
{
uint8_t v___x_2038_; uint8_t v___x_2039_; 
v___x_2038_ = 57;
v___x_2039_ = lean_uint8_dec_le(v_c_1984_, v___x_2038_);
if (v___x_2039_ == 0)
{
goto v___jp_2031_;
}
else
{
return v___x_2039_;
}
}
v___jp_1985_:
{
uint8_t v___x_1986_; uint8_t v___x_1987_; 
v___x_1986_ = 45;
v___x_1987_ = lean_uint8_dec_eq(v_c_1984_, v___x_1986_);
if (v___x_1987_ == 0)
{
uint8_t v___x_1988_; uint8_t v___x_1989_; 
v___x_1988_ = 46;
v___x_1989_ = lean_uint8_dec_eq(v_c_1984_, v___x_1988_);
if (v___x_1989_ == 0)
{
uint8_t v___x_1990_; uint8_t v___x_1991_; 
v___x_1990_ = 95;
v___x_1991_ = lean_uint8_dec_eq(v_c_1984_, v___x_1990_);
if (v___x_1991_ == 0)
{
uint8_t v___x_1992_; uint8_t v___x_1993_; 
v___x_1992_ = 126;
v___x_1993_ = lean_uint8_dec_eq(v_c_1984_, v___x_1992_);
if (v___x_1993_ == 0)
{
uint8_t v___x_1994_; uint8_t v___x_1995_; 
v___x_1994_ = 33;
v___x_1995_ = lean_uint8_dec_eq(v_c_1984_, v___x_1994_);
if (v___x_1995_ == 0)
{
uint8_t v___x_1996_; uint8_t v___x_1997_; 
v___x_1996_ = 36;
v___x_1997_ = lean_uint8_dec_eq(v_c_1984_, v___x_1996_);
if (v___x_1997_ == 0)
{
uint8_t v___x_1998_; uint8_t v___x_1999_; 
v___x_1998_ = 38;
v___x_1999_ = lean_uint8_dec_eq(v_c_1984_, v___x_1998_);
if (v___x_1999_ == 0)
{
uint8_t v___x_2000_; uint8_t v___x_2001_; 
v___x_2000_ = 39;
v___x_2001_ = lean_uint8_dec_eq(v_c_1984_, v___x_2000_);
if (v___x_2001_ == 0)
{
uint8_t v___x_2002_; uint8_t v___x_2003_; 
v___x_2002_ = 40;
v___x_2003_ = lean_uint8_dec_eq(v_c_1984_, v___x_2002_);
if (v___x_2003_ == 0)
{
uint8_t v___x_2004_; uint8_t v___x_2005_; 
v___x_2004_ = 41;
v___x_2005_ = lean_uint8_dec_eq(v_c_1984_, v___x_2004_);
if (v___x_2005_ == 0)
{
uint8_t v___x_2006_; uint8_t v___x_2007_; 
v___x_2006_ = 42;
v___x_2007_ = lean_uint8_dec_eq(v_c_1984_, v___x_2006_);
if (v___x_2007_ == 0)
{
uint8_t v___x_2008_; uint8_t v___x_2009_; 
v___x_2008_ = 43;
v___x_2009_ = lean_uint8_dec_eq(v_c_1984_, v___x_2008_);
if (v___x_2009_ == 0)
{
uint8_t v___x_2010_; uint8_t v___x_2011_; 
v___x_2010_ = 44;
v___x_2011_ = lean_uint8_dec_eq(v_c_1984_, v___x_2010_);
if (v___x_2011_ == 0)
{
uint8_t v___x_2012_; uint8_t v___x_2013_; 
v___x_2012_ = 59;
v___x_2013_ = lean_uint8_dec_eq(v_c_1984_, v___x_2012_);
if (v___x_2013_ == 0)
{
uint8_t v___x_2014_; uint8_t v___x_2015_; 
v___x_2014_ = 61;
v___x_2015_ = lean_uint8_dec_eq(v_c_1984_, v___x_2014_);
if (v___x_2015_ == 0)
{
uint8_t v___x_2016_; uint8_t v___x_2017_; 
v___x_2016_ = 58;
v___x_2017_ = lean_uint8_dec_eq(v_c_1984_, v___x_2016_);
if (v___x_2017_ == 0)
{
uint8_t v___x_2018_; uint8_t v___x_2019_; 
v___x_2018_ = 64;
v___x_2019_ = lean_uint8_dec_eq(v_c_1984_, v___x_2018_);
if (v___x_2019_ == 0)
{
uint8_t v___x_2020_; uint8_t v___x_2021_; 
v___x_2020_ = 47;
v___x_2021_ = lean_uint8_dec_eq(v_c_1984_, v___x_2020_);
if (v___x_2021_ == 0)
{
uint8_t v___x_2022_; uint8_t v___x_2023_; 
v___x_2022_ = 63;
v___x_2023_ = lean_uint8_dec_eq(v_c_1984_, v___x_2022_);
if (v___x_2023_ == 0)
{
uint8_t v___x_2024_; uint8_t v___x_2025_; 
v___x_2024_ = 37;
v___x_2025_ = lean_uint8_dec_eq(v_c_1984_, v___x_2024_);
return v___x_2025_;
}
else
{
return v___x_2023_;
}
}
else
{
return v___x_2021_;
}
}
else
{
return v___x_2019_;
}
}
else
{
return v___x_2017_;
}
}
else
{
return v___x_2015_;
}
}
else
{
return v___x_2013_;
}
}
else
{
return v___x_2011_;
}
}
else
{
return v___x_2009_;
}
}
else
{
return v___x_2007_;
}
}
else
{
return v___x_2005_;
}
}
else
{
return v___x_2003_;
}
}
else
{
return v___x_2001_;
}
}
else
{
return v___x_1999_;
}
}
else
{
return v___x_1997_;
}
}
else
{
return v___x_1995_;
}
}
else
{
return v___x_1993_;
}
}
else
{
return v___x_1991_;
}
}
else
{
return v___x_1989_;
}
}
else
{
return v___x_1987_;
}
}
v___jp_2026_:
{
uint8_t v___x_2027_; uint8_t v___x_2028_; 
v___x_2027_ = 65;
v___x_2028_ = lean_uint8_dec_le(v___x_2027_, v_c_1984_);
if (v___x_2028_ == 0)
{
goto v___jp_1985_;
}
else
{
uint8_t v___x_2029_; uint8_t v___x_2030_; 
v___x_2029_ = 90;
v___x_2030_ = lean_uint8_dec_le(v_c_1984_, v___x_2029_);
if (v___x_2030_ == 0)
{
goto v___jp_1985_;
}
else
{
return v___x_2030_;
}
}
}
v___jp_2031_:
{
uint8_t v___x_2032_; uint8_t v___x_2033_; 
v___x_2032_ = 97;
v___x_2033_ = lean_uint8_dec_le(v___x_2032_, v_c_1984_);
if (v___x_2033_ == 0)
{
goto v___jp_2026_;
}
else
{
uint8_t v___x_2034_; uint8_t v___x_2035_; 
v___x_2034_ = 122;
v___x_2035_ = lean_uint8_dec_le(v_c_1984_, v___x_2034_);
if (v___x_2035_ == 0)
{
goto v___jp_2026_;
}
else
{
return v___x_2035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0___boxed(lean_object* v_c_2040_){
_start:
{
uint8_t v_c_boxed_2041_; uint8_t v_res_2042_; lean_object* v_r_2043_; 
v_c_boxed_2041_ = lean_unbox(v_c_2040_);
v_res_2042_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(v_c_boxed_2041_);
v_r_2043_ = lean_box(v_res_2042_);
return v_r_2043_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(lean_object* v___x_2044_, lean_object* v___x_2045_, lean_object* v_a_2046_, lean_object* v_b_2047_){
_start:
{
lean_object* v_it_2049_; 
if (lean_obj_tag(v_a_2046_) == 0)
{
lean_object* v_currPos_2053_; lean_object* v_searcher_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2080_; 
v_currPos_2053_ = lean_ctor_get(v_a_2046_, 0);
v_searcher_2054_ = lean_ctor_get(v_a_2046_, 1);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_a_2046_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2056_ = v_a_2046_;
v_isShared_2057_ = v_isSharedCheck_2080_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_searcher_2054_);
lean_inc(v_currPos_2053_);
lean_dec(v_a_2046_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2080_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v_str_2058_; lean_object* v_startInclusive_2059_; lean_object* v_endExclusive_2060_; lean_object* v___x_2061_; uint8_t v_decide_2062_; 
v_str_2058_ = lean_ctor_get(v___x_2044_, 0);
v_startInclusive_2059_ = lean_ctor_get(v___x_2044_, 1);
v_endExclusive_2060_ = lean_ctor_get(v___x_2044_, 2);
v___x_2061_ = lean_nat_sub(v_endExclusive_2060_, v_startInclusive_2059_);
v_decide_2062_ = lean_nat_dec_eq(v_searcher_2054_, v___x_2061_);
lean_dec(v___x_2061_);
if (v_decide_2062_ == 0)
{
uint32_t v___x_2063_; lean_object* v___x_2064_; uint32_t v___x_2065_; uint8_t v___x_2066_; 
v___x_2063_ = 38;
v___x_2064_ = lean_nat_add(v_startInclusive_2059_, v_searcher_2054_);
v___x_2065_ = lean_string_utf8_get_fast(v_str_2058_, v___x_2064_);
v___x_2066_ = lean_uint32_dec_eq(v___x_2065_, v___x_2063_);
if (v___x_2066_ == 0)
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2070_; 
lean_dec(v_searcher_2054_);
v___x_2067_ = lean_string_utf8_next_fast(v_str_2058_, v___x_2064_);
lean_dec(v___x_2064_);
v___x_2068_ = lean_nat_sub(v___x_2067_, v_startInclusive_2059_);
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 1, v___x_2068_);
v___x_2070_ = v___x_2056_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_currPos_2053_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v___x_2068_);
v___x_2070_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
v_a_2046_ = v___x_2070_;
goto _start;
}
}
else
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v_nextIt_2077_; 
lean_dec(v_currPos_2053_);
v___x_2073_ = lean_string_utf8_next_fast(v_str_2058_, v___x_2064_);
v___x_2074_ = lean_nat_sub(v___x_2073_, v___x_2064_);
lean_dec(v___x_2064_);
v___x_2075_ = lean_nat_add(v_searcher_2054_, v___x_2074_);
lean_dec(v___x_2074_);
lean_dec(v_searcher_2054_);
lean_inc(v___x_2075_);
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 1, v___x_2075_);
lean_ctor_set(v___x_2056_, 0, v___x_2075_);
v_nextIt_2077_ = v___x_2056_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v___x_2075_);
v_nextIt_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
v_it_2049_ = v_nextIt_2077_;
goto v___jp_2048_;
}
}
}
else
{
lean_object* v___x_2079_; 
lean_del_object(v___x_2056_);
lean_dec(v_searcher_2054_);
lean_dec(v_currPos_2053_);
v___x_2079_ = lean_box(1);
v_it_2049_ = v___x_2079_;
goto v___jp_2048_;
}
}
}
else
{
return v_b_2047_;
}
v___jp_2048_:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = lean_unsigned_to_nat(1u);
v___x_2051_ = lean_nat_add(v_b_2047_, v___x_2050_);
lean_dec(v_b_2047_);
v_a_2046_ = v_it_2049_;
v_b_2047_ = v___x_2051_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg___boxed(lean_object* v___x_2081_, lean_object* v___x_2082_, lean_object* v_a_2083_, lean_object* v_b_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2081_, v___x_2082_, v_a_2083_, v_b_2084_);
lean_dec(v___x_2082_);
lean_dec_ref(v___x_2081_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(lean_object* v___x_2086_, lean_object* v___x_2087_, lean_object* v___x_2088_, lean_object* v_a_2089_, lean_object* v_b_2090_){
_start:
{
lean_object* v_it_2092_; 
if (lean_obj_tag(v_a_2089_) == 0)
{
lean_object* v_currPos_2096_; lean_object* v_searcher_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2123_; 
v_currPos_2096_ = lean_ctor_get(v_a_2089_, 0);
v_searcher_2097_ = lean_ctor_get(v_a_2089_, 1);
v_isSharedCheck_2123_ = !lean_is_exclusive(v_a_2089_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2099_ = v_a_2089_;
v_isShared_2100_ = v_isSharedCheck_2123_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_searcher_2097_);
lean_inc(v_currPos_2096_);
lean_dec(v_a_2089_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2123_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v_str_2101_; lean_object* v_startInclusive_2102_; lean_object* v_endExclusive_2103_; lean_object* v___x_2104_; uint8_t v_decide_2105_; 
v_str_2101_ = lean_ctor_get(v___x_2087_, 0);
v_startInclusive_2102_ = lean_ctor_get(v___x_2087_, 1);
v_endExclusive_2103_ = lean_ctor_get(v___x_2087_, 2);
v___x_2104_ = lean_nat_sub(v_endExclusive_2103_, v_startInclusive_2102_);
v_decide_2105_ = lean_nat_dec_eq(v_searcher_2097_, v___x_2104_);
lean_dec(v___x_2104_);
if (v_decide_2105_ == 0)
{
lean_object* v___x_2106_; uint32_t v___x_2107_; uint32_t v___x_2108_; uint8_t v___x_2109_; 
v___x_2106_ = lean_nat_add(v_startInclusive_2102_, v_searcher_2097_);
v___x_2107_ = lean_string_utf8_get_fast(v_str_2101_, v___x_2106_);
v___x_2108_ = 38;
v___x_2109_ = lean_uint32_dec_eq(v___x_2107_, v___x_2108_);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2113_; 
lean_dec(v_searcher_2097_);
v___x_2110_ = lean_string_utf8_next_fast(v_str_2101_, v___x_2106_);
lean_dec(v___x_2106_);
v___x_2111_ = lean_nat_sub(v___x_2110_, v_startInclusive_2102_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 1, v___x_2111_);
v___x_2113_ = v___x_2099_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_currPos_2096_);
lean_ctor_set(v_reuseFailAlloc_2115_, 1, v___x_2111_);
v___x_2113_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2087_, v___x_2088_, v___x_2113_, v_b_2090_);
return v___x_2114_;
}
}
else
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v_nextIt_2120_; 
lean_dec(v_currPos_2096_);
v___x_2116_ = lean_string_utf8_next_fast(v_str_2101_, v___x_2106_);
v___x_2117_ = lean_nat_sub(v___x_2116_, v___x_2106_);
lean_dec(v___x_2106_);
v___x_2118_ = lean_nat_add(v_searcher_2097_, v___x_2117_);
lean_dec(v___x_2117_);
lean_dec(v_searcher_2097_);
lean_inc(v___x_2118_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 1, v___x_2118_);
lean_ctor_set(v___x_2099_, 0, v___x_2118_);
v_nextIt_2120_ = v___x_2099_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2118_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v___x_2118_);
v_nextIt_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
v_it_2092_ = v_nextIt_2120_;
goto v___jp_2091_;
}
}
}
else
{
lean_object* v___x_2122_; 
lean_del_object(v___x_2099_);
lean_dec(v_searcher_2097_);
lean_dec(v_currPos_2096_);
v___x_2122_ = lean_box(1);
v_it_2092_ = v___x_2122_;
goto v___jp_2091_;
}
}
}
else
{
return v_b_2090_;
}
v___jp_2091_:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2093_ = lean_unsigned_to_nat(1u);
v___x_2094_ = lean_nat_add(v_b_2090_, v___x_2093_);
lean_dec(v_b_2090_);
v___x_2095_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2087_, v___x_2088_, v_it_2092_, v___x_2094_);
return v___x_2095_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg___boxed(lean_object* v___x_2124_, lean_object* v___x_2125_, lean_object* v___x_2126_, lean_object* v_a_2127_, lean_object* v_b_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2124_, v___x_2125_, v___x_2126_, v_a_2127_, v_b_2128_);
lean_dec(v___x_2126_);
lean_dec_ref(v___x_2125_);
lean_dec_ref(v___x_2124_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(lean_object* v_out_2130_, lean_object* v_a_2131_, lean_object* v_b_2132_){
_start:
{
if (lean_obj_tag(v_a_2131_) == 0)
{
lean_object* v_currPos_2133_; lean_object* v_searcher_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2173_; 
v_currPos_2133_ = lean_ctor_get(v_a_2131_, 0);
v_searcher_2134_ = lean_ctor_get(v_a_2131_, 1);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_a_2131_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2136_ = v_a_2131_;
v_isShared_2137_ = v_isSharedCheck_2173_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_searcher_2134_);
lean_inc(v_currPos_2133_);
lean_dec(v_a_2131_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2173_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v_str_2138_; lean_object* v_startInclusive_2139_; lean_object* v_endExclusive_2140_; lean_object* v_it_2142_; lean_object* v_startInclusive_2143_; lean_object* v_endExclusive_2144_; lean_object* v___x_2151_; uint8_t v_decide_2152_; 
v_str_2138_ = lean_ctor_get(v_out_2130_, 0);
v_startInclusive_2139_ = lean_ctor_get(v_out_2130_, 1);
v_endExclusive_2140_ = lean_ctor_get(v_out_2130_, 2);
v___x_2151_ = lean_nat_sub(v_endExclusive_2140_, v_startInclusive_2139_);
v_decide_2152_ = lean_nat_dec_eq(v_searcher_2134_, v___x_2151_);
if (v_decide_2152_ == 0)
{
uint32_t v___x_2153_; lean_object* v___x_2154_; uint32_t v___x_2155_; uint8_t v___x_2156_; 
lean_dec(v___x_2151_);
v___x_2153_ = 61;
v___x_2154_ = lean_nat_add(v_startInclusive_2139_, v_searcher_2134_);
v___x_2155_ = lean_string_utf8_get_fast(v_str_2138_, v___x_2154_);
v___x_2156_ = lean_uint32_dec_eq(v___x_2155_, v___x_2153_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2160_; 
lean_dec(v_searcher_2134_);
v___x_2157_ = lean_string_utf8_next_fast(v_str_2138_, v___x_2154_);
lean_dec(v___x_2154_);
v___x_2158_ = lean_nat_sub(v___x_2157_, v_startInclusive_2139_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 1, v___x_2158_);
v___x_2160_ = v___x_2136_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_currPos_2133_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v___x_2158_);
v___x_2160_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
v_a_2131_ = v___x_2160_;
goto _start;
}
}
else
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v_slice_2166_; lean_object* v_nextIt_2168_; 
v___x_2163_ = lean_string_utf8_next_fast(v_str_2138_, v___x_2154_);
v___x_2164_ = lean_nat_sub(v___x_2163_, v___x_2154_);
lean_dec(v___x_2154_);
v___x_2165_ = lean_nat_add(v_searcher_2134_, v___x_2164_);
lean_dec(v___x_2164_);
v_slice_2166_ = l_String_Slice_subslice_x21(v_out_2130_, v_currPos_2133_, v_searcher_2134_);
lean_inc(v___x_2165_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 1, v___x_2165_);
lean_ctor_set(v___x_2136_, 0, v___x_2165_);
v_nextIt_2168_ = v___x_2136_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2165_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v___x_2165_);
v_nextIt_2168_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
lean_object* v_startInclusive_2169_; lean_object* v_endExclusive_2170_; 
v_startInclusive_2169_ = lean_ctor_get(v_slice_2166_, 0);
lean_inc(v_startInclusive_2169_);
v_endExclusive_2170_ = lean_ctor_get(v_slice_2166_, 1);
lean_inc(v_endExclusive_2170_);
lean_dec_ref(v_slice_2166_);
v_it_2142_ = v_nextIt_2168_;
v_startInclusive_2143_ = v_startInclusive_2169_;
v_endExclusive_2144_ = v_endExclusive_2170_;
goto v___jp_2141_;
}
}
}
else
{
lean_object* v___x_2172_; 
lean_del_object(v___x_2136_);
lean_dec(v_searcher_2134_);
v___x_2172_ = lean_box(1);
v_it_2142_ = v___x_2172_;
v_startInclusive_2143_ = v_currPos_2133_;
v_endExclusive_2144_ = v___x_2151_;
goto v___jp_2141_;
}
v___jp_2141_:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2145_ = lean_nat_add(v_startInclusive_2139_, v_startInclusive_2143_);
lean_dec(v_startInclusive_2143_);
v___x_2146_ = lean_nat_add(v_startInclusive_2139_, v_endExclusive_2144_);
lean_dec(v_endExclusive_2144_);
lean_inc_ref(v_str_2138_);
v___x_2147_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2147_, 0, v_str_2138_);
lean_ctor_set(v___x_2147_, 1, v___x_2145_);
lean_ctor_set(v___x_2147_, 2, v___x_2146_);
v___x_2148_ = l_String_Slice_toString(v___x_2147_);
lean_dec_ref_known(v___x_2147_, 3);
v___x_2149_ = lean_array_push(v_b_2132_, v___x_2148_);
v_a_2131_ = v_it_2142_;
v_b_2132_ = v___x_2149_;
goto _start;
}
}
}
else
{
return v_b_2132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg___boxed(lean_object* v_out_2174_, lean_object* v_a_2175_, lean_object* v_b_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_2174_, v_a_2175_, v_b_2176_);
lean_dec_ref(v_out_2174_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(lean_object* v___x_2181_, lean_object* v___x_2182_, lean_object* v___x_2183_, lean_object* v_a_2184_, lean_object* v_b_2185_){
_start:
{
lean_object* v_it_2187_; lean_object* v_startInclusive_2188_; lean_object* v_endExclusive_2189_; 
if (lean_obj_tag(v_a_2184_) == 0)
{
lean_object* v_currPos_2214_; lean_object* v_searcher_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2244_; 
v_currPos_2214_ = lean_ctor_get(v_a_2184_, 0);
v_searcher_2215_ = lean_ctor_get(v_a_2184_, 1);
v_isSharedCheck_2244_ = !lean_is_exclusive(v_a_2184_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2217_ = v_a_2184_;
v_isShared_2218_ = v_isSharedCheck_2244_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_searcher_2215_);
lean_inc(v_currPos_2214_);
lean_dec(v_a_2184_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2244_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v_str_2219_; lean_object* v_startInclusive_2220_; lean_object* v_endExclusive_2221_; lean_object* v___x_2222_; uint8_t v_decide_2223_; 
v_str_2219_ = lean_ctor_get(v___x_2182_, 0);
v_startInclusive_2220_ = lean_ctor_get(v___x_2182_, 1);
v_endExclusive_2221_ = lean_ctor_get(v___x_2182_, 2);
v___x_2222_ = lean_nat_sub(v_endExclusive_2221_, v_startInclusive_2220_);
v_decide_2223_ = lean_nat_dec_eq(v_searcher_2215_, v___x_2222_);
lean_dec(v___x_2222_);
if (v_decide_2223_ == 0)
{
uint32_t v___x_2224_; lean_object* v___x_2225_; uint32_t v___x_2226_; uint8_t v___x_2227_; 
v___x_2224_ = 38;
v___x_2225_ = lean_nat_add(v_startInclusive_2220_, v_searcher_2215_);
v___x_2226_ = lean_string_utf8_get_fast(v_str_2219_, v___x_2225_);
v___x_2227_ = lean_uint32_dec_eq(v___x_2226_, v___x_2224_);
if (v___x_2227_ == 0)
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2231_; 
lean_dec(v_searcher_2215_);
v___x_2228_ = lean_string_utf8_next_fast(v_str_2219_, v___x_2225_);
lean_dec(v___x_2225_);
v___x_2229_ = lean_nat_sub(v___x_2228_, v_startInclusive_2220_);
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 1, v___x_2229_);
v___x_2231_ = v___x_2217_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_currPos_2214_);
lean_ctor_set(v_reuseFailAlloc_2233_, 1, v___x_2229_);
v___x_2231_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
v_a_2184_ = v___x_2231_;
goto _start;
}
}
else
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v_slice_2237_; lean_object* v_nextIt_2239_; 
v___x_2234_ = lean_string_utf8_next_fast(v_str_2219_, v___x_2225_);
v___x_2235_ = lean_nat_sub(v___x_2234_, v___x_2225_);
lean_dec(v___x_2225_);
v___x_2236_ = lean_nat_add(v_searcher_2215_, v___x_2235_);
lean_dec(v___x_2235_);
v_slice_2237_ = l_String_Slice_subslice_x21(v___x_2182_, v_currPos_2214_, v_searcher_2215_);
lean_inc(v___x_2236_);
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 1, v___x_2236_);
lean_ctor_set(v___x_2217_, 0, v___x_2236_);
v_nextIt_2239_ = v___x_2217_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2236_);
lean_ctor_set(v_reuseFailAlloc_2242_, 1, v___x_2236_);
v_nextIt_2239_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
lean_object* v_startInclusive_2240_; lean_object* v_endExclusive_2241_; 
v_startInclusive_2240_ = lean_ctor_get(v_slice_2237_, 0);
lean_inc(v_startInclusive_2240_);
v_endExclusive_2241_ = lean_ctor_get(v_slice_2237_, 1);
lean_inc(v_endExclusive_2241_);
lean_dec_ref(v_slice_2237_);
v_it_2187_ = v_nextIt_2239_;
v_startInclusive_2188_ = v_startInclusive_2240_;
v_endExclusive_2189_ = v_endExclusive_2241_;
goto v___jp_2186_;
}
}
}
else
{
lean_object* v___x_2243_; 
lean_del_object(v___x_2217_);
lean_dec(v_searcher_2215_);
v___x_2243_ = lean_box(1);
lean_inc(v___x_2183_);
v_it_2187_ = v___x_2243_;
v_startInclusive_2188_ = v_currPos_2214_;
v_endExclusive_2189_ = v___x_2183_;
goto v___jp_2186_;
}
}
}
else
{
lean_object* v___x_2245_; 
lean_dec(v___x_2183_);
lean_dec_ref(v___x_2181_);
v___x_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2245_, 0, v_b_2185_);
return v___x_2245_;
}
v___jp_2186_:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
lean_inc_ref(v___x_2181_);
v___x_2190_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2181_);
lean_ctor_set(v___x_2190_, 1, v_startInclusive_2188_);
lean_ctor_set(v___x_2190_, 2, v_endExclusive_2189_);
v___x_2191_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
v___x_2192_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0));
v___x_2193_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_2190_, v___x_2191_, v___x_2192_);
lean_dec_ref_known(v___x_2190_, 3);
v___x_2194_ = lean_array_to_list(v___x_2193_);
if (lean_obj_tag(v___x_2194_) == 0)
{
v_a_2184_ = v_it_2187_;
goto _start;
}
else
{
lean_object* v_tail_2196_; 
v_tail_2196_ = lean_ctor_get(v___x_2194_, 1);
if (lean_obj_tag(v_tail_2196_) == 0)
{
lean_object* v_head_2197_; lean_object* v___x_2198_; 
v_head_2197_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_head_2197_);
lean_dec_ref_known(v___x_2194_, 2);
v___x_2198_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2197_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v___x_2199_; 
lean_dec(v_it_2187_);
lean_dec_ref(v_b_2185_);
lean_dec(v___x_2183_);
lean_dec_ref(v___x_2181_);
v___x_2199_ = lean_box(0);
return v___x_2199_;
}
else
{
lean_object* v_val_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v_val_2200_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_val_2200_);
lean_dec_ref_known(v___x_2198_, 1);
v___x_2201_ = lean_box(0);
v___x_2202_ = l_Std_Http_URI_Query_insertEncoded(v_b_2185_, v_val_2200_, v___x_2201_);
v_a_2184_ = v_it_2187_;
v_b_2185_ = v___x_2202_;
goto _start;
}
}
else
{
lean_object* v_head_2204_; lean_object* v___x_2205_; 
lean_inc(v_tail_2196_);
v_head_2204_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_head_2204_);
lean_dec_ref_known(v___x_2194_, 2);
v___x_2205_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2204_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v___x_2206_; 
lean_dec(v_tail_2196_);
lean_dec(v_it_2187_);
lean_dec_ref(v_b_2185_);
lean_dec(v___x_2183_);
lean_dec_ref(v___x_2181_);
v___x_2206_ = lean_box(0);
return v___x_2206_;
}
else
{
lean_object* v_val_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v_val_2207_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_val_2207_);
lean_dec_ref_known(v___x_2205_, 1);
v___x_2208_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1));
v___x_2209_ = l_String_intercalate(v___x_2208_, v_tail_2196_);
v___x_2210_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2209_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v___x_2211_; 
lean_dec(v_val_2207_);
lean_dec(v_it_2187_);
lean_dec_ref(v_b_2185_);
lean_dec(v___x_2183_);
lean_dec_ref(v___x_2181_);
v___x_2211_ = lean_box(0);
return v___x_2211_;
}
else
{
lean_object* v___x_2212_; 
v___x_2212_ = l_Std_Http_URI_Query_insertEncoded(v_b_2185_, v_val_2207_, v___x_2210_);
v_a_2184_ = v_it_2187_;
v_b_2185_ = v___x_2212_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___boxed(lean_object* v___x_2246_, lean_object* v___x_2247_, lean_object* v___x_2248_, lean_object* v_a_2249_, lean_object* v_b_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2246_, v___x_2247_, v___x_2248_, v_a_2249_, v_b_2250_);
lean_dec_ref(v___x_2247_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(lean_object* v___x_2252_, lean_object* v___x_2253_, lean_object* v___x_2254_, lean_object* v_a_2255_, lean_object* v_b_2256_){
_start:
{
lean_object* v_it_2258_; lean_object* v_startInclusive_2259_; lean_object* v_endExclusive_2260_; 
if (lean_obj_tag(v_a_2255_) == 0)
{
lean_object* v_currPos_2285_; lean_object* v_searcher_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2315_; 
v_currPos_2285_ = lean_ctor_get(v_a_2255_, 0);
v_searcher_2286_ = lean_ctor_get(v_a_2255_, 1);
v_isSharedCheck_2315_ = !lean_is_exclusive(v_a_2255_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2288_ = v_a_2255_;
v_isShared_2289_ = v_isSharedCheck_2315_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_searcher_2286_);
lean_inc(v_currPos_2285_);
lean_dec(v_a_2255_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2315_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v_str_2290_; lean_object* v_startInclusive_2291_; lean_object* v_endExclusive_2292_; lean_object* v___x_2293_; uint8_t v_decide_2294_; 
v_str_2290_ = lean_ctor_get(v___x_2253_, 0);
v_startInclusive_2291_ = lean_ctor_get(v___x_2253_, 1);
v_endExclusive_2292_ = lean_ctor_get(v___x_2253_, 2);
v___x_2293_ = lean_nat_sub(v_endExclusive_2292_, v_startInclusive_2291_);
v_decide_2294_ = lean_nat_dec_eq(v_searcher_2286_, v___x_2293_);
lean_dec(v___x_2293_);
if (v_decide_2294_ == 0)
{
lean_object* v___x_2295_; uint32_t v___x_2296_; uint32_t v___x_2297_; uint8_t v___x_2298_; 
v___x_2295_ = lean_nat_add(v_startInclusive_2291_, v_searcher_2286_);
v___x_2296_ = lean_string_utf8_get_fast(v_str_2290_, v___x_2295_);
v___x_2297_ = 38;
v___x_2298_ = lean_uint32_dec_eq(v___x_2296_, v___x_2297_);
if (v___x_2298_ == 0)
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2302_; 
lean_dec(v_searcher_2286_);
v___x_2299_ = lean_string_utf8_next_fast(v_str_2290_, v___x_2295_);
lean_dec(v___x_2295_);
v___x_2300_ = lean_nat_sub(v___x_2299_, v_startInclusive_2291_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 1, v___x_2300_);
v___x_2302_ = v___x_2288_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_currPos_2285_);
lean_ctor_set(v_reuseFailAlloc_2304_, 1, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2303_; 
v___x_2303_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2252_, v___x_2253_, v___x_2254_, v___x_2302_, v_b_2256_);
return v___x_2303_;
}
}
else
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v_slice_2308_; lean_object* v_nextIt_2310_; 
v___x_2305_ = lean_string_utf8_next_fast(v_str_2290_, v___x_2295_);
v___x_2306_ = lean_nat_sub(v___x_2305_, v___x_2295_);
lean_dec(v___x_2295_);
v___x_2307_ = lean_nat_add(v_searcher_2286_, v___x_2306_);
lean_dec(v___x_2306_);
v_slice_2308_ = l_String_Slice_subslice_x21(v___x_2253_, v_currPos_2285_, v_searcher_2286_);
lean_inc(v___x_2307_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 1, v___x_2307_);
lean_ctor_set(v___x_2288_, 0, v___x_2307_);
v_nextIt_2310_ = v___x_2288_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2307_);
lean_ctor_set(v_reuseFailAlloc_2313_, 1, v___x_2307_);
v_nextIt_2310_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
lean_object* v_startInclusive_2311_; lean_object* v_endExclusive_2312_; 
v_startInclusive_2311_ = lean_ctor_get(v_slice_2308_, 0);
lean_inc(v_startInclusive_2311_);
v_endExclusive_2312_ = lean_ctor_get(v_slice_2308_, 1);
lean_inc(v_endExclusive_2312_);
lean_dec_ref(v_slice_2308_);
v_it_2258_ = v_nextIt_2310_;
v_startInclusive_2259_ = v_startInclusive_2311_;
v_endExclusive_2260_ = v_endExclusive_2312_;
goto v___jp_2257_;
}
}
}
else
{
lean_object* v___x_2314_; 
lean_del_object(v___x_2288_);
lean_dec(v_searcher_2286_);
v___x_2314_ = lean_box(1);
lean_inc(v___x_2254_);
v_it_2258_ = v___x_2314_;
v_startInclusive_2259_ = v_currPos_2285_;
v_endExclusive_2260_ = v___x_2254_;
goto v___jp_2257_;
}
}
}
else
{
lean_object* v___x_2316_; 
lean_dec(v___x_2254_);
lean_dec_ref(v___x_2252_);
v___x_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2316_, 0, v_b_2256_);
return v___x_2316_;
}
v___jp_2257_:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
lean_inc_ref(v___x_2252_);
v___x_2261_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2252_);
lean_ctor_set(v___x_2261_, 1, v_startInclusive_2259_);
lean_ctor_set(v___x_2261_, 2, v_endExclusive_2260_);
v___x_2262_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
v___x_2263_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0));
v___x_2264_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_2261_, v___x_2262_, v___x_2263_);
lean_dec_ref_known(v___x_2261_, 3);
v___x_2265_ = lean_array_to_list(v___x_2264_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v___x_2266_; 
v___x_2266_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2252_, v___x_2253_, v___x_2254_, v_it_2258_, v_b_2256_);
return v___x_2266_;
}
else
{
lean_object* v_tail_2267_; 
v_tail_2267_ = lean_ctor_get(v___x_2265_, 1);
if (lean_obj_tag(v_tail_2267_) == 0)
{
lean_object* v_head_2268_; lean_object* v___x_2269_; 
v_head_2268_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_head_2268_);
lean_dec_ref_known(v___x_2265_, 2);
v___x_2269_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2268_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v___x_2270_; 
lean_dec(v_it_2258_);
lean_dec_ref(v_b_2256_);
lean_dec(v___x_2254_);
lean_dec_ref(v___x_2252_);
v___x_2270_ = lean_box(0);
return v___x_2270_;
}
else
{
lean_object* v_val_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v_val_2271_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_val_2271_);
lean_dec_ref_known(v___x_2269_, 1);
v___x_2272_ = lean_box(0);
v___x_2273_ = l_Std_Http_URI_Query_insertEncoded(v_b_2256_, v_val_2271_, v___x_2272_);
v___x_2274_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2252_, v___x_2253_, v___x_2254_, v_it_2258_, v___x_2273_);
return v___x_2274_;
}
}
else
{
lean_object* v_head_2275_; lean_object* v___x_2276_; 
lean_inc(v_tail_2267_);
v_head_2275_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_head_2275_);
lean_dec_ref_known(v___x_2265_, 2);
v___x_2276_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2275_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v___x_2277_; 
lean_dec(v_tail_2267_);
lean_dec(v_it_2258_);
lean_dec_ref(v_b_2256_);
lean_dec(v___x_2254_);
lean_dec_ref(v___x_2252_);
v___x_2277_ = lean_box(0);
return v___x_2277_;
}
else
{
lean_object* v_val_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v_val_2278_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_val_2278_);
lean_dec_ref_known(v___x_2276_, 1);
v___x_2279_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1));
v___x_2280_ = l_String_intercalate(v___x_2279_, v_tail_2267_);
v___x_2281_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2280_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v___x_2282_; 
lean_dec(v_val_2278_);
lean_dec(v_it_2258_);
lean_dec_ref(v_b_2256_);
lean_dec(v___x_2254_);
lean_dec_ref(v___x_2252_);
v___x_2282_ = lean_box(0);
return v___x_2282_;
}
else
{
lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2283_ = l_Std_Http_URI_Query_insertEncoded(v_b_2256_, v_val_2278_, v___x_2281_);
v___x_2284_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2252_, v___x_2253_, v___x_2254_, v_it_2258_, v___x_2283_);
return v___x_2284_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg___boxed(lean_object* v___x_2317_, lean_object* v___x_2318_, lean_object* v___x_2319_, lean_object* v_a_2320_, lean_object* v_b_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2317_, v___x_2318_, v___x_2319_, v_a_2320_, v_b_2321_);
lean_dec_ref(v___x_2318_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(lean_object* v_config_2328_, lean_object* v_a_2329_){
_start:
{
lean_object* v_maxQueryLength_2330_; lean_object* v_maxQueryParams_2331_; lean_object* v___f_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v_snd_2335_; lean_object* v_fst_2336_; lean_object* v_fst_2337_; lean_object* v_array_2338_; lean_object* v_idx_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2389_; 
v_maxQueryLength_2330_ = lean_ctor_get(v_config_2328_, 4);
lean_inc(v_maxQueryLength_2330_);
v_maxQueryParams_2331_ = lean_ctor_get(v_config_2328_, 8);
lean_inc(v_maxQueryParams_2331_);
lean_dec_ref(v_config_2328_);
v___f_2332_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2333_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2329_);
v___x_2334_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2332_, v_maxQueryLength_2330_, v___x_2333_, v_a_2329_);
lean_dec(v_maxQueryLength_2330_);
v_snd_2335_ = lean_ctor_get(v___x_2334_, 1);
lean_inc(v_snd_2335_);
v_fst_2336_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_fst_2336_);
lean_dec_ref(v___x_2334_);
v_fst_2337_ = lean_ctor_get(v_snd_2335_, 0);
lean_inc(v_fst_2337_);
lean_dec(v_snd_2335_);
v_array_2338_ = lean_ctor_get(v_a_2329_, 0);
v_idx_2339_ = lean_ctor_get(v_a_2329_, 1);
v_isSharedCheck_2389_ = !lean_is_exclusive(v_a_2329_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2341_ = v_a_2329_;
v_isShared_2342_ = v_isSharedCheck_2389_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_idx_2339_);
lean_inc(v_array_2338_);
lean_dec(v_a_2329_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2389_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v_lower_2344_; lean_object* v_upper_2345_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___y_2386_; uint8_t v___x_2388_; 
v___x_2383_ = lean_nat_add(v_idx_2339_, v_fst_2336_);
lean_dec(v_fst_2336_);
v___x_2384_ = lean_byte_array_size(v_array_2338_);
v___x_2388_ = lean_nat_dec_le(v_idx_2339_, v___x_2333_);
if (v___x_2388_ == 0)
{
v___y_2386_ = v_idx_2339_;
goto v___jp_2385_;
}
else
{
lean_dec(v_idx_2339_);
v___y_2386_ = v___x_2333_;
goto v___jp_2385_;
}
v___jp_2343_:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; uint8_t v___x_2348_; 
v___x_2346_ = l_ByteArray_toByteSlice(v_array_2338_, v_lower_2344_, v_upper_2345_);
v___x_2347_ = l_ByteSlice_toByteArray(v___x_2346_);
v___x_2348_ = lean_string_validate_utf8(v___x_2347_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2349_; lean_object* v___x_2351_; 
lean_dec_ref(v___x_2347_);
lean_dec(v_maxQueryParams_2331_);
v___x_2349_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2342_ == 0)
{
lean_ctor_set_tag(v___x_2341_, 1);
lean_ctor_set(v___x_2341_, 1, v___x_2349_);
lean_ctor_set(v___x_2341_, 0, v_fst_2337_);
v___x_2351_ = v___x_2341_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_fst_2337_);
lean_ctor_set(v_reuseFailAlloc_2352_, 1, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
else
{
lean_object* v___x_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; 
v___x_2353_ = lean_string_from_utf8_unchecked(v___x_2347_);
v___x_2354_ = lean_string_utf8_byte_size(v___x_2353_);
v___x_2355_ = lean_nat_dec_eq(v___x_2354_, v___x_2333_);
if (v___x_2355_ == 0)
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; uint8_t v___x_2359_; 
lean_inc_ref(v___x_2353_);
v___x_2356_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2353_);
lean_ctor_set(v___x_2356_, 1, v___x_2333_);
lean_ctor_set(v___x_2356_, 2, v___x_2354_);
v___x_2357_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0);
v___x_2358_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2353_, v___x_2356_, v___x_2354_, v___x_2357_, v___x_2333_);
v___x_2359_ = lean_nat_dec_lt(v_maxQueryParams_2331_, v___x_2358_);
lean_dec(v___x_2358_);
if (v___x_2359_ == 0)
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
lean_dec(v_maxQueryParams_2331_);
v___x_2360_ = l_Std_Http_URI_Query_empty;
v___x_2361_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2353_, v___x_2356_, v___x_2354_, v___x_2357_, v___x_2360_);
lean_dec_ref_known(v___x_2356_, 3);
if (lean_obj_tag(v___x_2361_) == 1)
{
lean_object* v_val_2362_; lean_object* v___x_2364_; 
v_val_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_val_2362_);
lean_dec_ref_known(v___x_2361_, 1);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 1, v_val_2362_);
lean_ctor_set(v___x_2341_, 0, v_fst_2337_);
v___x_2364_ = v___x_2341_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_fst_2337_);
lean_ctor_set(v_reuseFailAlloc_2365_, 1, v_val_2362_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
else
{
lean_object* v___x_2366_; lean_object* v___x_2368_; 
lean_dec(v___x_2361_);
v___x_2366_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2342_ == 0)
{
lean_ctor_set_tag(v___x_2341_, 1);
lean_ctor_set(v___x_2341_, 1, v___x_2366_);
lean_ctor_set(v___x_2341_, 0, v_fst_2337_);
v___x_2368_ = v___x_2341_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_fst_2337_);
lean_ctor_set(v_reuseFailAlloc_2369_, 1, v___x_2366_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
else
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2377_; 
lean_dec_ref_known(v___x_2356_, 3);
lean_dec_ref(v___x_2353_);
v___x_2370_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3));
v___x_2371_ = l_Nat_reprFast(v_maxQueryParams_2331_);
v___x_2372_ = lean_string_append(v___x_2370_, v___x_2371_);
lean_dec_ref(v___x_2371_);
v___x_2373_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_2374_ = lean_string_append(v___x_2372_, v___x_2373_);
v___x_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2374_);
if (v_isShared_2342_ == 0)
{
lean_ctor_set_tag(v___x_2341_, 1);
lean_ctor_set(v___x_2341_, 1, v___x_2375_);
lean_ctor_set(v___x_2341_, 0, v_fst_2337_);
v___x_2377_ = v___x_2341_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_fst_2337_);
lean_ctor_set(v_reuseFailAlloc_2378_, 1, v___x_2375_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
else
{
lean_object* v___x_2379_; lean_object* v___x_2381_; 
lean_dec_ref(v___x_2353_);
lean_dec(v_maxQueryParams_2331_);
v___x_2379_ = l_Std_Http_URI_Query_empty;
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 1, v___x_2379_);
lean_ctor_set(v___x_2341_, 0, v_fst_2337_);
v___x_2381_ = v___x_2341_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_fst_2337_);
lean_ctor_set(v_reuseFailAlloc_2382_, 1, v___x_2379_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
v___jp_2385_:
{
uint8_t v___x_2387_; 
v___x_2387_ = lean_nat_dec_le(v___x_2383_, v___x_2384_);
if (v___x_2387_ == 0)
{
lean_dec(v___x_2383_);
v_lower_2344_ = v___y_2386_;
v_upper_2345_ = v___x_2384_;
goto v___jp_2343_;
}
else
{
v_lower_2344_ = v___y_2386_;
v_upper_2345_ = v___x_2383_;
goto v___jp_2343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(lean_object* v___x_2390_, lean_object* v___x_2391_, lean_object* v___x_2392_, lean_object* v_inst_2393_, lean_object* v_R_2394_, lean_object* v_a_2395_, lean_object* v_b_2396_, lean_object* v_c_2397_){
_start:
{
lean_object* v___x_2398_; 
v___x_2398_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2390_, v___x_2391_, v___x_2392_, v_a_2395_, v_b_2396_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___boxed(lean_object* v___x_2399_, lean_object* v___x_2400_, lean_object* v___x_2401_, lean_object* v_inst_2402_, lean_object* v_R_2403_, lean_object* v_a_2404_, lean_object* v_b_2405_, lean_object* v_c_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(v___x_2399_, v___x_2400_, v___x_2401_, v_inst_2402_, v_R_2403_, v_a_2404_, v_b_2405_, v_c_2406_);
lean_dec(v___x_2401_);
lean_dec_ref(v___x_2400_);
lean_dec_ref(v___x_2399_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(lean_object* v_out_2408_, lean_object* v_inst_2409_, lean_object* v_R_2410_, lean_object* v_a_2411_, lean_object* v_b_2412_){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_2408_, v_a_2411_, v_b_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___boxed(lean_object* v_out_2414_, lean_object* v_inst_2415_, lean_object* v_R_2416_, lean_object* v_a_2417_, lean_object* v_b_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(v_out_2414_, v_inst_2415_, v_R_2416_, v_a_2417_, v_b_2418_);
lean_dec_ref(v_out_2414_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(lean_object* v___x_2420_, lean_object* v___x_2421_, lean_object* v___x_2422_, lean_object* v_inst_2423_, lean_object* v_R_2424_, lean_object* v_a_2425_, lean_object* v_b_2426_, lean_object* v_c_2427_){
_start:
{
lean_object* v___x_2428_; 
v___x_2428_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2420_, v___x_2421_, v___x_2422_, v_a_2425_, v_b_2426_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___boxed(lean_object* v___x_2429_, lean_object* v___x_2430_, lean_object* v___x_2431_, lean_object* v_inst_2432_, lean_object* v_R_2433_, lean_object* v_a_2434_, lean_object* v_b_2435_, lean_object* v_c_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(v___x_2429_, v___x_2430_, v___x_2431_, v_inst_2432_, v_R_2433_, v_a_2434_, v_b_2435_, v_c_2436_);
lean_dec_ref(v___x_2430_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(lean_object* v___x_2438_, lean_object* v___x_2439_, lean_object* v___x_2440_, lean_object* v_inst_2441_, lean_object* v_R_2442_, lean_object* v_a_2443_, lean_object* v_b_2444_, lean_object* v_c_2445_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2439_, v___x_2440_, v_a_2443_, v_b_2444_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___boxed(lean_object* v___x_2447_, lean_object* v___x_2448_, lean_object* v___x_2449_, lean_object* v_inst_2450_, lean_object* v_R_2451_, lean_object* v_a_2452_, lean_object* v_b_2453_, lean_object* v_c_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(v___x_2447_, v___x_2448_, v___x_2449_, v_inst_2450_, v_R_2451_, v_a_2452_, v_b_2453_, v_c_2454_);
lean_dec(v___x_2449_);
lean_dec_ref(v___x_2448_);
lean_dec_ref(v___x_2447_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(lean_object* v___x_2456_, lean_object* v___x_2457_, lean_object* v___x_2458_, lean_object* v_inst_2459_, lean_object* v_R_2460_, lean_object* v_a_2461_, lean_object* v_b_2462_, lean_object* v_c_2463_){
_start:
{
lean_object* v___x_2464_; 
v___x_2464_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2456_, v___x_2457_, v___x_2458_, v_a_2461_, v_b_2462_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___boxed(lean_object* v___x_2465_, lean_object* v___x_2466_, lean_object* v___x_2467_, lean_object* v_inst_2468_, lean_object* v_R_2469_, lean_object* v_a_2470_, lean_object* v_b_2471_, lean_object* v_c_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(v___x_2465_, v___x_2466_, v___x_2467_, v_inst_2468_, v_R_2469_, v_a_2470_, v_b_2471_, v_c_2472_);
lean_dec_ref(v___x_2466_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(lean_object* v_config_2477_, lean_object* v_a_2478_){
_start:
{
lean_object* v_maxFragmentLength_2479_; lean_object* v___f_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v_snd_2483_; lean_object* v_fst_2484_; lean_object* v_fst_2485_; lean_object* v_array_2486_; lean_object* v_idx_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2511_; 
v_maxFragmentLength_2479_ = lean_ctor_get(v_config_2477_, 5);
v___f_2480_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2481_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2478_);
v___x_2482_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2480_, v_maxFragmentLength_2479_, v___x_2481_, v_a_2478_);
v_snd_2483_ = lean_ctor_get(v___x_2482_, 1);
lean_inc(v_snd_2483_);
v_fst_2484_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_fst_2484_);
lean_dec_ref(v___x_2482_);
v_fst_2485_ = lean_ctor_get(v_snd_2483_, 0);
lean_inc(v_fst_2485_);
lean_dec(v_snd_2483_);
v_array_2486_ = lean_ctor_get(v_a_2478_, 0);
v_idx_2487_ = lean_ctor_get(v_a_2478_, 1);
v_isSharedCheck_2511_ = !lean_is_exclusive(v_a_2478_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2489_ = v_a_2478_;
v_isShared_2490_ = v_isSharedCheck_2511_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_idx_2487_);
lean_inc(v_array_2486_);
lean_dec(v_a_2478_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2511_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v_lower_2492_; lean_object* v_upper_2493_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___y_2508_; uint8_t v___x_2510_; 
v___x_2505_ = lean_nat_add(v_idx_2487_, v_fst_2484_);
lean_dec(v_fst_2484_);
v___x_2506_ = lean_byte_array_size(v_array_2486_);
v___x_2510_ = lean_nat_dec_le(v_idx_2487_, v___x_2481_);
if (v___x_2510_ == 0)
{
v___y_2508_ = v_idx_2487_;
goto v___jp_2507_;
}
else
{
lean_dec(v_idx_2487_);
v___y_2508_ = v___x_2481_;
goto v___jp_2507_;
}
v___jp_2491_:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2494_ = l_ByteArray_toByteSlice(v_array_2486_, v_lower_2492_, v_upper_2493_);
v___x_2495_ = l_ByteSlice_toByteArray(v___x_2494_);
v___x_2496_ = l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(v___x_2495_);
if (lean_obj_tag(v___x_2496_) == 1)
{
lean_object* v_val_2497_; lean_object* v___x_2499_; 
v_val_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_val_2497_);
lean_dec_ref_known(v___x_2496_, 1);
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 1, v_val_2497_);
lean_ctor_set(v___x_2489_, 0, v_fst_2485_);
v___x_2499_ = v___x_2489_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_fst_2485_);
lean_ctor_set(v_reuseFailAlloc_2500_, 1, v_val_2497_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
else
{
lean_object* v___x_2501_; lean_object* v___x_2503_; 
lean_dec(v___x_2496_);
v___x_2501_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1));
if (v_isShared_2490_ == 0)
{
lean_ctor_set_tag(v___x_2489_, 1);
lean_ctor_set(v___x_2489_, 1, v___x_2501_);
lean_ctor_set(v___x_2489_, 0, v_fst_2485_);
v___x_2503_ = v___x_2489_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_fst_2485_);
lean_ctor_set(v_reuseFailAlloc_2504_, 1, v___x_2501_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
v___jp_2507_:
{
uint8_t v___x_2509_; 
v___x_2509_ = lean_nat_dec_le(v___x_2505_, v___x_2506_);
if (v___x_2509_ == 0)
{
lean_dec(v___x_2505_);
v_lower_2492_ = v___y_2508_;
v_upper_2493_ = v___x_2506_;
goto v___jp_2491_;
}
else
{
v_lower_2492_ = v___y_2508_;
v_upper_2493_ = v___x_2505_;
goto v___jp_2491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___boxed(lean_object* v_config_2512_, lean_object* v_a_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2512_, v_a_2513_);
lean_dec_ref(v_config_2512_);
return v_res_2514_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1(void){
_start:
{
lean_object* v___x_2516_; lean_object* v_utf8_2517_; 
v___x_2516_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0));
v_utf8_2517_ = lean_string_to_utf8(v___x_2516_);
return v_utf8_2517_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(lean_object* v_config_2518_, lean_object* v_a_2519_){
_start:
{
lean_object* v_utf8_2520_; lean_object* v___x_2521_; 
v_utf8_2520_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1);
lean_inc_ref(v_a_2519_);
v___x_2521_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_2520_, v_a_2519_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_pos_2522_; uint8_t v___x_2523_; lean_object* v_pos_2525_; lean_object* v_res_2526_; lean_object* v___x_2547_; 
lean_dec_ref(v_a_2519_);
v_pos_2522_ = lean_ctor_get(v___x_2521_, 0);
lean_inc_n(v_pos_2522_, 2);
lean_dec_ref_known(v___x_2521_, 2);
v___x_2523_ = 1;
v___x_2547_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_2518_, v_pos_2522_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_pos_2548_; lean_object* v_res_2549_; lean_object* v___x_2550_; 
lean_dec(v_pos_2522_);
v_pos_2548_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_pos_2548_);
v_res_2549_ = lean_ctor_get(v___x_2547_, 1);
lean_inc(v_res_2549_);
lean_dec_ref_known(v___x_2547_, 2);
v___x_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2550_, 0, v_res_2549_);
v_pos_2525_ = v_pos_2548_;
v_res_2526_ = v___x_2550_;
goto v___jp_2524_;
}
else
{
lean_object* v_err_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2561_; 
v_err_2551_ = lean_ctor_get(v___x_2547_, 1);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2561_ == 0)
{
lean_object* v_unused_2562_; 
v_unused_2562_ = lean_ctor_get(v___x_2547_, 0);
lean_dec(v_unused_2562_);
v___x_2553_ = v___x_2547_;
v_isShared_2554_ = v_isSharedCheck_2561_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_err_2551_);
lean_dec(v___x_2547_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2561_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v_idx_2555_; uint8_t v___x_2556_; 
v_idx_2555_ = lean_ctor_get(v_pos_2522_, 1);
v___x_2556_ = lean_nat_dec_eq(v_idx_2555_, v_idx_2555_);
if (v___x_2556_ == 0)
{
lean_object* v___x_2558_; 
lean_dec_ref(v_config_2518_);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 0, v_pos_2522_);
v___x_2558_ = v___x_2553_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_pos_2522_);
lean_ctor_set(v_reuseFailAlloc_2559_, 1, v_err_2551_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
else
{
lean_object* v___x_2560_; 
lean_del_object(v___x_2553_);
lean_dec(v_err_2551_);
v___x_2560_ = lean_box(0);
v_pos_2525_ = v_pos_2522_;
v_res_2526_ = v___x_2560_;
goto v___jp_2524_;
}
}
}
v___jp_2524_:
{
lean_object* v___x_2527_; 
v___x_2527_ = l_Std_Http_URI_Parser_parsePath(v_config_2518_, v___x_2523_, v___x_2523_, v_pos_2525_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_pos_2528_; lean_object* v_res_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2537_; 
v_pos_2528_ = lean_ctor_get(v___x_2527_, 0);
v_res_2529_ = lean_ctor_get(v___x_2527_, 1);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2531_ = v___x_2527_;
v_isShared_2532_ = v_isSharedCheck_2537_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_res_2529_);
lean_inc(v_pos_2528_);
lean_dec(v___x_2527_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2537_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2533_; lean_object* v___x_2535_; 
v___x_2533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2533_, 0, v_res_2526_);
lean_ctor_set(v___x_2533_, 1, v_res_2529_);
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 1, v___x_2533_);
v___x_2535_ = v___x_2531_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_pos_2528_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v___x_2533_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
else
{
lean_object* v_pos_2538_; lean_object* v_err_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2546_; 
lean_dec(v_res_2526_);
v_pos_2538_ = lean_ctor_get(v___x_2527_, 0);
v_err_2539_ = lean_ctor_get(v___x_2527_, 1);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2541_ = v___x_2527_;
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_err_2539_);
lean_inc(v_pos_2538_);
lean_dec(v___x_2527_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2544_; 
if (v_isShared_2542_ == 0)
{
v___x_2544_ = v___x_2541_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_pos_2538_);
lean_ctor_set(v_reuseFailAlloc_2545_, 1, v_err_2539_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
}
}
else
{
lean_object* v_err_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2594_; 
v_err_2563_ = lean_ctor_get(v___x_2521_, 1);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2594_ == 0)
{
lean_object* v_unused_2595_; 
v_unused_2595_ = lean_ctor_get(v___x_2521_, 0);
lean_dec(v_unused_2595_);
v___x_2565_ = v___x_2521_;
v_isShared_2566_ = v_isSharedCheck_2594_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_err_2563_);
lean_dec(v___x_2521_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2594_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v_idx_2567_; uint8_t v___x_2568_; 
v_idx_2567_ = lean_ctor_get(v_a_2519_, 1);
v___x_2568_ = lean_nat_dec_eq(v_idx_2567_, v_idx_2567_);
if (v___x_2568_ == 0)
{
lean_object* v___x_2570_; 
lean_dec_ref(v_config_2518_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v_a_2519_);
v___x_2570_ = v___x_2565_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2519_);
lean_ctor_set(v_reuseFailAlloc_2571_, 1, v_err_2563_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
else
{
uint8_t v___x_2572_; lean_object* v___x_2573_; 
lean_del_object(v___x_2565_);
lean_dec(v_err_2563_);
v___x_2572_ = 0;
v___x_2573_ = l_Std_Http_URI_Parser_parsePath(v_config_2518_, v___x_2572_, v___x_2568_, v_a_2519_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_pos_2574_; lean_object* v_res_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2584_; 
v_pos_2574_ = lean_ctor_get(v___x_2573_, 0);
v_res_2575_ = lean_ctor_get(v___x_2573_, 1);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2577_ = v___x_2573_;
v_isShared_2578_ = v_isSharedCheck_2584_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_res_2575_);
lean_inc(v_pos_2574_);
lean_dec(v___x_2573_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2584_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2582_; 
v___x_2579_ = lean_box(0);
v___x_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2579_);
lean_ctor_set(v___x_2580_, 1, v_res_2575_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 1, v___x_2580_);
v___x_2582_ = v___x_2577_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_pos_2574_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v___x_2580_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
else
{
lean_object* v_pos_2585_; lean_object* v_err_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
v_pos_2585_ = lean_ctor_get(v___x_2573_, 0);
v_err_2586_ = lean_ctor_get(v___x_2573_, 1);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2573_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_err_2586_);
lean_inc(v_pos_2585_);
lean_dec(v___x_2573_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_pos_2585_);
lean_ctor_set(v_reuseFailAlloc_2592_, 1, v_err_2586_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURI(lean_object* v_config_2605_, lean_object* v_a_2606_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_2605_, v_a_2606_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_pos_2608_; lean_object* v_res_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2740_; 
v_pos_2608_ = lean_ctor_get(v___x_2607_, 0);
v_res_2609_ = lean_ctor_get(v___x_2607_, 1);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2611_ = v___x_2607_;
v_isShared_2612_ = v_isSharedCheck_2740_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_res_2609_);
lean_inc(v_pos_2608_);
lean_dec(v___x_2607_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2740_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v_array_2613_; lean_object* v_idx_2614_; lean_object* v___x_2615_; uint8_t v___x_2616_; 
v_array_2613_ = lean_ctor_get(v_pos_2608_, 0);
v_idx_2614_ = lean_ctor_get(v_pos_2608_, 1);
v___x_2615_ = lean_byte_array_size(v_array_2613_);
v___x_2616_ = lean_nat_dec_lt(v_idx_2614_, v___x_2615_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; lean_object* v___x_2619_; 
lean_dec(v_res_2609_);
lean_dec_ref(v_config_2605_);
v___x_2617_ = lean_box(0);
if (v_isShared_2612_ == 0)
{
lean_ctor_set_tag(v___x_2611_, 1);
lean_ctor_set(v___x_2611_, 1, v___x_2617_);
v___x_2619_ = v___x_2611_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_pos_2608_);
lean_ctor_set(v_reuseFailAlloc_2620_, 1, v___x_2617_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
else
{
uint8_t v___x_2621_; uint8_t v_got_2622_; uint8_t v___x_2623_; 
v___x_2621_ = 58;
v_got_2622_ = lean_byte_array_fget(v_array_2613_, v_idx_2614_);
v___x_2623_ = lean_uint8_dec_eq(v_got_2622_, v___x_2621_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2624_; lean_object* v___x_2626_; 
lean_dec(v_res_2609_);
lean_dec_ref(v_config_2605_);
v___x_2624_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_2612_ == 0)
{
lean_ctor_set_tag(v___x_2611_, 1);
lean_ctor_set(v___x_2611_, 1, v___x_2624_);
v___x_2626_ = v___x_2611_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_pos_2608_);
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
lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2737_; 
lean_inc(v_idx_2614_);
lean_inc_ref(v_array_2613_);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_pos_2608_);
if (v_isSharedCheck_2737_ == 0)
{
lean_object* v_unused_2738_; lean_object* v_unused_2739_; 
v_unused_2738_ = lean_ctor_get(v_pos_2608_, 1);
lean_dec(v_unused_2738_);
v_unused_2739_ = lean_ctor_get(v_pos_2608_, 0);
lean_dec(v_unused_2739_);
v___x_2629_ = v_pos_2608_;
v_isShared_2630_ = v_isSharedCheck_2737_;
goto v_resetjp_2628_;
}
else
{
lean_dec(v_pos_2608_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2737_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2634_; 
v___x_2631_ = lean_unsigned_to_nat(1u);
v___x_2632_ = lean_nat_add(v_idx_2614_, v___x_2631_);
lean_dec(v_idx_2614_);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 1, v___x_2632_);
v___x_2634_ = v___x_2629_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_array_2613_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v___x_2632_);
v___x_2634_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
lean_object* v___x_2635_; 
lean_inc_ref(v_config_2605_);
v___x_2635_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2605_, v___x_2634_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v_res_2636_; lean_object* v_pos_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2726_; 
v_res_2636_ = lean_ctor_get(v___x_2635_, 1);
v_pos_2637_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2639_ = v___x_2635_;
v_isShared_2640_ = v_isSharedCheck_2726_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_res_2636_);
lean_inc(v_pos_2637_);
lean_dec(v___x_2635_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2726_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v_fst_2641_; lean_object* v_snd_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2725_; 
v_fst_2641_ = lean_ctor_get(v_res_2636_, 0);
v_snd_2642_ = lean_ctor_get(v_res_2636_, 1);
v_isSharedCheck_2725_ = !lean_is_exclusive(v_res_2636_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2644_ = v_res_2636_;
v_isShared_2645_ = v_isSharedCheck_2725_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_snd_2642_);
lean_inc(v_fst_2641_);
lean_dec(v_res_2636_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2725_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___y_2647_; lean_object* v_pos_2648_; lean_object* v_res_2649_; lean_object* v_idx_2655_; lean_object* v___y_2656_; lean_object* v_pos_2657_; lean_object* v_err_2658_; lean_object* v_pos_2666_; lean_object* v_array_2667_; lean_object* v_idx_2668_; lean_object* v_res_2669_; lean_object* v_array_2688_; lean_object* v_idx_2689_; lean_object* v_pos_2691_; lean_object* v_array_2692_; lean_object* v_idx_2693_; lean_object* v_err_2694_; lean_object* v___x_2698_; uint8_t v___x_2699_; 
v_array_2688_ = lean_ctor_get(v_pos_2637_, 0);
lean_inc_ref(v_array_2688_);
v_idx_2689_ = lean_ctor_get(v_pos_2637_, 1);
lean_inc(v_idx_2689_);
v___x_2698_ = lean_byte_array_size(v_array_2688_);
v___x_2699_ = lean_nat_dec_lt(v_idx_2689_, v___x_2698_);
if (v___x_2699_ == 0)
{
lean_object* v___x_2700_; 
v___x_2700_ = lean_box(0);
lean_inc(v_idx_2689_);
v_pos_2691_ = v_pos_2637_;
v_array_2692_ = v_array_2688_;
v_idx_2693_ = v_idx_2689_;
v_err_2694_ = v___x_2700_;
goto v___jp_2690_;
}
else
{
uint8_t v___x_2701_; uint8_t v_got_2702_; uint8_t v___x_2703_; 
v___x_2701_ = 63;
v_got_2702_ = lean_byte_array_fget(v_array_2688_, v_idx_2689_);
v___x_2703_ = lean_uint8_dec_eq(v_got_2702_, v___x_2701_);
if (v___x_2703_ == 0)
{
lean_object* v___x_2704_; 
v___x_2704_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_2689_);
v_pos_2691_ = v_pos_2637_;
v_array_2692_ = v_array_2688_;
v_idx_2693_ = v_idx_2689_;
v_err_2694_ = v___x_2704_;
goto v___jp_2690_;
}
else
{
lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2722_; 
v_isSharedCheck_2722_ = !lean_is_exclusive(v_pos_2637_);
if (v_isSharedCheck_2722_ == 0)
{
lean_object* v_unused_2723_; lean_object* v_unused_2724_; 
v_unused_2723_ = lean_ctor_get(v_pos_2637_, 1);
lean_dec(v_unused_2723_);
v_unused_2724_ = lean_ctor_get(v_pos_2637_, 0);
lean_dec(v_unused_2724_);
v___x_2706_ = v_pos_2637_;
v_isShared_2707_ = v_isSharedCheck_2722_;
goto v_resetjp_2705_;
}
else
{
lean_dec(v_pos_2637_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2722_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2708_; lean_object* v___x_2710_; 
v___x_2708_ = lean_nat_add(v_idx_2689_, v___x_2631_);
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 1, v___x_2708_);
v___x_2710_ = v___x_2706_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_array_2688_);
lean_ctor_set(v_reuseFailAlloc_2721_, 1, v___x_2708_);
v___x_2710_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
lean_object* v___x_2711_; 
lean_inc_ref(v_config_2605_);
v___x_2711_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2605_, v___x_2710_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_pos_2712_; lean_object* v_res_2713_; lean_object* v_array_2714_; lean_object* v_idx_2715_; lean_object* v___x_2716_; 
lean_dec(v_idx_2689_);
v_pos_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_pos_2712_);
v_res_2713_ = lean_ctor_get(v___x_2711_, 1);
lean_inc(v_res_2713_);
lean_dec_ref_known(v___x_2711_, 2);
v_array_2714_ = lean_ctor_get(v_pos_2712_, 0);
lean_inc_ref(v_array_2714_);
v_idx_2715_ = lean_ctor_get(v_pos_2712_, 1);
lean_inc(v_idx_2715_);
v___x_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2716_, 0, v_res_2713_);
v_pos_2666_ = v_pos_2712_;
v_array_2667_ = v_array_2714_;
v_idx_2668_ = v_idx_2715_;
v_res_2669_ = v___x_2716_;
goto v___jp_2665_;
}
else
{
lean_object* v_pos_2717_; lean_object* v_err_2718_; lean_object* v_array_2719_; lean_object* v_idx_2720_; 
v_pos_2717_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_pos_2717_);
v_err_2718_ = lean_ctor_get(v___x_2711_, 1);
lean_inc(v_err_2718_);
lean_dec_ref_known(v___x_2711_, 2);
v_array_2719_ = lean_ctor_get(v_pos_2717_, 0);
lean_inc_ref(v_array_2719_);
v_idx_2720_ = lean_ctor_get(v_pos_2717_, 1);
lean_inc(v_idx_2720_);
v_pos_2691_ = v_pos_2717_;
v_array_2692_ = v_array_2719_;
v_idx_2693_ = v_idx_2720_;
v_err_2694_ = v_err_2718_;
goto v___jp_2690_;
}
}
}
}
}
v___jp_2646_:
{
lean_object* v___x_2650_; lean_object* v___x_2652_; 
v___x_2650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2650_, 0, v_res_2609_);
lean_ctor_set(v___x_2650_, 1, v_fst_2641_);
lean_ctor_set(v___x_2650_, 2, v_snd_2642_);
lean_ctor_set(v___x_2650_, 3, v___y_2647_);
lean_ctor_set(v___x_2650_, 4, v_res_2649_);
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 1, v___x_2650_);
lean_ctor_set(v___x_2639_, 0, v_pos_2648_);
v___x_2652_ = v___x_2639_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_pos_2648_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v___x_2650_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
v___jp_2654_:
{
lean_object* v_idx_2659_; uint8_t v___x_2660_; 
v_idx_2659_ = lean_ctor_get(v_pos_2657_, 1);
v___x_2660_ = lean_nat_dec_eq(v_idx_2655_, v_idx_2659_);
lean_dec(v_idx_2655_);
if (v___x_2660_ == 0)
{
lean_object* v___x_2662_; 
lean_dec(v___y_2656_);
lean_dec(v_snd_2642_);
lean_dec(v_fst_2641_);
lean_del_object(v___x_2639_);
lean_dec(v_res_2609_);
if (v_isShared_2612_ == 0)
{
lean_ctor_set_tag(v___x_2611_, 1);
lean_ctor_set(v___x_2611_, 1, v_err_2658_);
lean_ctor_set(v___x_2611_, 0, v_pos_2657_);
v___x_2662_ = v___x_2611_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_pos_2657_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v_err_2658_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
else
{
lean_object* v___x_2664_; 
lean_dec(v_err_2658_);
lean_del_object(v___x_2611_);
v___x_2664_ = lean_box(0);
v___y_2647_ = v___y_2656_;
v_pos_2648_ = v_pos_2657_;
v_res_2649_ = v___x_2664_;
goto v___jp_2646_;
}
}
v___jp_2665_:
{
lean_object* v___x_2670_; uint8_t v___x_2671_; 
v___x_2670_ = lean_byte_array_size(v_array_2667_);
v___x_2671_ = lean_nat_dec_lt(v_idx_2668_, v___x_2670_);
if (v___x_2671_ == 0)
{
lean_object* v___x_2672_; 
lean_dec_ref(v_array_2667_);
lean_del_object(v___x_2644_);
lean_dec_ref(v_config_2605_);
v___x_2672_ = lean_box(0);
v_idx_2655_ = v_idx_2668_;
v___y_2656_ = v_res_2669_;
v_pos_2657_ = v_pos_2666_;
v_err_2658_ = v___x_2672_;
goto v___jp_2654_;
}
else
{
uint8_t v___x_2673_; uint8_t v_got_2674_; uint8_t v___x_2675_; 
v___x_2673_ = 35;
v_got_2674_ = lean_byte_array_fget(v_array_2667_, v_idx_2668_);
v___x_2675_ = lean_uint8_dec_eq(v_got_2674_, v___x_2673_);
if (v___x_2675_ == 0)
{
lean_object* v___x_2676_; 
lean_dec_ref(v_array_2667_);
lean_del_object(v___x_2644_);
lean_dec_ref(v_config_2605_);
v___x_2676_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v_idx_2655_ = v_idx_2668_;
v___y_2656_ = v_res_2669_;
v_pos_2657_ = v_pos_2666_;
v_err_2658_ = v___x_2676_;
goto v___jp_2654_;
}
else
{
lean_object* v___x_2677_; lean_object* v___x_2679_; 
lean_dec_ref(v_pos_2666_);
v___x_2677_ = lean_nat_add(v_idx_2668_, v___x_2631_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 1, v___x_2677_);
lean_ctor_set(v___x_2644_, 0, v_array_2667_);
v___x_2679_ = v___x_2644_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_array_2667_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v___x_2677_);
v___x_2679_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
lean_object* v___x_2680_; 
v___x_2680_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2605_, v___x_2679_);
lean_dec_ref(v_config_2605_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_pos_2681_; lean_object* v_res_2682_; lean_object* v___x_2683_; 
v_pos_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_pos_2681_);
v_res_2682_ = lean_ctor_get(v___x_2680_, 1);
lean_inc(v_res_2682_);
lean_dec_ref_known(v___x_2680_, 2);
v___x_2683_ = l_Std_Http_URI_EncodedFragment_decode(v_res_2682_);
lean_dec(v_res_2682_);
if (lean_obj_tag(v___x_2683_) == 1)
{
lean_dec(v_idx_2668_);
lean_del_object(v___x_2611_);
v___y_2647_ = v_res_2669_;
v_pos_2648_ = v_pos_2681_;
v_res_2649_ = v___x_2683_;
goto v___jp_2646_;
}
else
{
lean_object* v___x_2684_; 
lean_dec(v___x_2683_);
v___x_2684_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__3));
v_idx_2655_ = v_idx_2668_;
v___y_2656_ = v_res_2669_;
v_pos_2657_ = v_pos_2681_;
v_err_2658_ = v___x_2684_;
goto v___jp_2654_;
}
}
else
{
lean_object* v_pos_2685_; lean_object* v_err_2686_; 
v_pos_2685_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_pos_2685_);
v_err_2686_ = lean_ctor_get(v___x_2680_, 1);
lean_inc(v_err_2686_);
lean_dec_ref_known(v___x_2680_, 2);
v_idx_2655_ = v_idx_2668_;
v___y_2656_ = v_res_2669_;
v_pos_2657_ = v_pos_2685_;
v_err_2658_ = v_err_2686_;
goto v___jp_2654_;
}
}
}
}
}
v___jp_2690_:
{
uint8_t v___x_2695_; 
v___x_2695_ = lean_nat_dec_eq(v_idx_2689_, v_idx_2693_);
lean_dec(v_idx_2689_);
if (v___x_2695_ == 0)
{
lean_object* v___x_2696_; 
lean_dec(v_idx_2693_);
lean_dec_ref(v_array_2692_);
lean_del_object(v___x_2644_);
lean_dec(v_snd_2642_);
lean_dec(v_fst_2641_);
lean_del_object(v___x_2639_);
lean_del_object(v___x_2611_);
lean_dec(v_res_2609_);
lean_dec_ref(v_config_2605_);
v___x_2696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2696_, 0, v_pos_2691_);
lean_ctor_set(v___x_2696_, 1, v_err_2694_);
return v___x_2696_;
}
else
{
lean_object* v___x_2697_; 
lean_dec(v_err_2694_);
v___x_2697_ = lean_box(0);
v_pos_2666_ = v_pos_2691_;
v_array_2667_ = v_array_2692_;
v_idx_2668_ = v_idx_2693_;
v_res_2669_ = v___x_2697_;
goto v___jp_2665_;
}
}
}
}
}
else
{
lean_object* v_pos_2727_; lean_object* v_err_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
lean_del_object(v___x_2611_);
lean_dec(v_res_2609_);
lean_dec_ref(v_config_2605_);
v_pos_2727_ = lean_ctor_get(v___x_2635_, 0);
v_err_2728_ = lean_ctor_get(v___x_2635_, 1);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2635_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_err_2728_);
lean_inc(v_pos_2727_);
lean_dec(v___x_2635_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_pos_2727_);
lean_ctor_set(v_reuseFailAlloc_2734_, 1, v_err_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
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
lean_object* v_pos_2741_; lean_object* v_err_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
lean_dec_ref(v_config_2605_);
v_pos_2741_ = lean_ctor_get(v___x_2607_, 0);
v_err_2742_ = lean_ctor_get(v___x_2607_, 1);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2744_ = v___x_2607_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_err_2742_);
lean_inc(v_pos_2741_);
lean_dec(v___x_2607_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(lean_object* v_a_2753_){
_start:
{
lean_object* v_array_2754_; lean_object* v_idx_2755_; lean_object* v___x_2756_; uint8_t v___x_2757_; 
v_array_2754_ = lean_ctor_get(v_a_2753_, 0);
v_idx_2755_ = lean_ctor_get(v_a_2753_, 1);
v___x_2756_ = lean_byte_array_size(v_array_2754_);
v___x_2757_ = lean_nat_dec_lt(v_idx_2755_, v___x_2756_);
if (v___x_2757_ == 0)
{
lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2758_ = lean_box(0);
v___x_2759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2759_, 0, v_a_2753_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
return v___x_2759_;
}
else
{
uint8_t v___x_2760_; uint8_t v_got_2761_; uint8_t v___x_2762_; 
v___x_2760_ = 42;
v_got_2761_ = lean_byte_array_fget(v_array_2754_, v_idx_2755_);
v___x_2762_ = lean_uint8_dec_eq(v_got_2761_, v___x_2760_);
if (v___x_2762_ == 0)
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2763_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1));
v___x_2764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2764_, 0, v_a_2753_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
return v___x_2764_;
}
else
{
lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2775_; 
lean_inc(v_idx_2755_);
lean_inc_ref(v_array_2754_);
v_isSharedCheck_2775_ = !lean_is_exclusive(v_a_2753_);
if (v_isSharedCheck_2775_ == 0)
{
lean_object* v_unused_2776_; lean_object* v_unused_2777_; 
v_unused_2776_ = lean_ctor_get(v_a_2753_, 1);
lean_dec(v_unused_2776_);
v_unused_2777_ = lean_ctor_get(v_a_2753_, 0);
lean_dec(v_unused_2777_);
v___x_2766_ = v_a_2753_;
v_isShared_2767_ = v_isSharedCheck_2775_;
goto v_resetjp_2765_;
}
else
{
lean_dec(v_a_2753_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2775_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2771_; 
v___x_2768_ = lean_unsigned_to_nat(1u);
v___x_2769_ = lean_nat_add(v_idx_2755_, v___x_2768_);
lean_dec(v_idx_2755_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 1, v___x_2769_);
v___x_2771_ = v___x_2766_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_array_2754_);
lean_ctor_set(v_reuseFailAlloc_2774_, 1, v___x_2769_);
v___x_2771_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2772_ = lean_box(3);
v___x_2773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2771_);
lean_ctor_set(v___x_2773_, 1, v___x_2772_);
return v___x_2773_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(lean_object* v_config_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v_array_2786_; lean_object* v_idx_2787_; lean_object* v___x_2788_; uint8_t v___x_2789_; 
v_array_2786_ = lean_ctor_get(v_a_2782_, 0);
v_idx_2787_ = lean_ctor_get(v_a_2782_, 1);
v___x_2788_ = lean_byte_array_size(v_array_2786_);
v___x_2789_ = lean_nat_dec_lt(v_idx_2787_, v___x_2788_);
if (v___x_2789_ == 0)
{
lean_dec_ref(v_config_2781_);
goto v___jp_2783_;
}
else
{
uint8_t v___x_2790_; uint8_t v___x_2791_; uint8_t v___x_2792_; 
v___x_2790_ = lean_byte_array_fget(v_array_2786_, v_idx_2787_);
v___x_2791_ = 47;
v___x_2792_ = lean_uint8_dec_eq(v___x_2790_, v___x_2791_);
if (v___x_2792_ == 0)
{
lean_dec_ref(v_config_2781_);
goto v___jp_2783_;
}
else
{
lean_object* v___x_2793_; 
lean_inc_ref(v_a_2782_);
lean_inc_ref(v_config_2781_);
v___x_2793_ = l_Std_Http_URI_Parser_parsePath(v_config_2781_, v___x_2792_, v___x_2792_, v_a_2782_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_pos_2794_; lean_object* v_res_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2840_; 
v_pos_2794_ = lean_ctor_get(v___x_2793_, 0);
v_res_2795_ = lean_ctor_get(v___x_2793_, 1);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2797_ = v___x_2793_;
v_isShared_2798_ = v_isSharedCheck_2840_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_res_2795_);
lean_inc(v_pos_2794_);
lean_dec(v___x_2793_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2840_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v_pos_2800_; lean_object* v_res_2801_; lean_object* v_array_2806_; lean_object* v_idx_2807_; lean_object* v_pos_2809_; lean_object* v_idx_2810_; lean_object* v_err_2811_; lean_object* v___x_2815_; uint8_t v___x_2816_; 
v_array_2806_ = lean_ctor_get(v_pos_2794_, 0);
v_idx_2807_ = lean_ctor_get(v_pos_2794_, 1);
lean_inc(v_idx_2807_);
v___x_2815_ = lean_byte_array_size(v_array_2806_);
v___x_2816_ = lean_nat_dec_lt(v_idx_2807_, v___x_2815_);
if (v___x_2816_ == 0)
{
lean_object* v___x_2817_; 
lean_dec_ref(v_config_2781_);
v___x_2817_ = lean_box(0);
lean_inc(v_idx_2807_);
v_pos_2809_ = v_pos_2794_;
v_idx_2810_ = v_idx_2807_;
v_err_2811_ = v___x_2817_;
goto v___jp_2808_;
}
else
{
uint8_t v___x_2818_; uint8_t v_got_2819_; uint8_t v___x_2820_; 
v___x_2818_ = 63;
v_got_2819_ = lean_byte_array_fget(v_array_2806_, v_idx_2807_);
v___x_2820_ = lean_uint8_dec_eq(v_got_2819_, v___x_2818_);
if (v___x_2820_ == 0)
{
lean_object* v___x_2821_; 
lean_dec_ref(v_config_2781_);
v___x_2821_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_2807_);
v_pos_2809_ = v_pos_2794_;
v_idx_2810_ = v_idx_2807_;
v_err_2811_ = v___x_2821_;
goto v___jp_2808_;
}
else
{
lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2837_; 
lean_inc_ref(v_array_2806_);
v_isSharedCheck_2837_ = !lean_is_exclusive(v_pos_2794_);
if (v_isSharedCheck_2837_ == 0)
{
lean_object* v_unused_2838_; lean_object* v_unused_2839_; 
v_unused_2838_ = lean_ctor_get(v_pos_2794_, 1);
lean_dec(v_unused_2838_);
v_unused_2839_ = lean_ctor_get(v_pos_2794_, 0);
lean_dec(v_unused_2839_);
v___x_2823_ = v_pos_2794_;
v_isShared_2824_ = v_isSharedCheck_2837_;
goto v_resetjp_2822_;
}
else
{
lean_dec(v_pos_2794_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2837_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2828_; 
v___x_2825_ = lean_unsigned_to_nat(1u);
v___x_2826_ = lean_nat_add(v_idx_2807_, v___x_2825_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 1, v___x_2826_);
v___x_2828_ = v___x_2823_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_array_2806_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v___x_2826_);
v___x_2828_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
lean_object* v___x_2829_; 
v___x_2829_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2781_, v___x_2828_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_pos_2830_; lean_object* v_res_2831_; lean_object* v___x_2832_; 
lean_dec(v_idx_2807_);
lean_dec_ref(v_a_2782_);
v_pos_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_pos_2830_);
v_res_2831_ = lean_ctor_get(v___x_2829_, 1);
lean_inc(v_res_2831_);
lean_dec_ref_known(v___x_2829_, 2);
v___x_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2832_, 0, v_res_2831_);
v_pos_2800_ = v_pos_2830_;
v_res_2801_ = v___x_2832_;
goto v___jp_2799_;
}
else
{
lean_object* v_pos_2833_; lean_object* v_err_2834_; lean_object* v_idx_2835_; 
v_pos_2833_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_pos_2833_);
v_err_2834_ = lean_ctor_get(v___x_2829_, 1);
lean_inc(v_err_2834_);
lean_dec_ref_known(v___x_2829_, 2);
v_idx_2835_ = lean_ctor_get(v_pos_2833_, 1);
lean_inc(v_idx_2835_);
v_pos_2809_ = v_pos_2833_;
v_idx_2810_ = v_idx_2835_;
v_err_2811_ = v_err_2834_;
goto v___jp_2808_;
}
}
}
}
}
v___jp_2799_:
{
lean_object* v___x_2802_; lean_object* v___x_2804_; 
v___x_2802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2802_, 0, v_res_2795_);
lean_ctor_set(v___x_2802_, 1, v_res_2801_);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 1, v___x_2802_);
lean_ctor_set(v___x_2797_, 0, v_pos_2800_);
v___x_2804_ = v___x_2797_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_pos_2800_);
lean_ctor_set(v_reuseFailAlloc_2805_, 1, v___x_2802_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
v___jp_2808_:
{
uint8_t v___x_2812_; 
v___x_2812_ = lean_nat_dec_eq(v_idx_2807_, v_idx_2810_);
lean_dec(v_idx_2810_);
lean_dec(v_idx_2807_);
if (v___x_2812_ == 0)
{
lean_object* v___x_2813_; 
lean_dec_ref(v_pos_2809_);
lean_del_object(v___x_2797_);
lean_dec(v_res_2795_);
v___x_2813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2813_, 0, v_a_2782_);
lean_ctor_set(v___x_2813_, 1, v_err_2811_);
return v___x_2813_;
}
else
{
lean_object* v___x_2814_; 
lean_dec(v_err_2811_);
lean_dec_ref(v_a_2782_);
v___x_2814_ = lean_box(0);
v_pos_2800_ = v_pos_2809_;
v_res_2801_ = v___x_2814_;
goto v___jp_2799_;
}
}
}
}
else
{
lean_object* v_err_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2848_; 
lean_dec_ref(v_config_2781_);
v_err_2841_ = lean_ctor_get(v___x_2793_, 1);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2848_ == 0)
{
lean_object* v_unused_2849_; 
v_unused_2849_ = lean_ctor_get(v___x_2793_, 0);
lean_dec(v_unused_2849_);
v___x_2843_ = v___x_2793_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_err_2841_);
lean_dec(v___x_2793_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 0, v_a_2782_);
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2782_);
lean_ctor_set(v_reuseFailAlloc_2847_, 1, v_err_2841_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
}
}
v___jp_2783_:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1));
v___x_2785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2785_, 0, v_a_2782_);
lean_ctor_set(v___x_2785_, 1, v___x_2784_);
return v___x_2785_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(lean_object* v_config_2850_, lean_object* v_scheme_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v_array_2853_; lean_object* v_idx_2854_; lean_object* v___x_2855_; uint8_t v___x_2856_; 
v_array_2853_ = lean_ctor_get(v_a_2852_, 0);
v_idx_2854_ = lean_ctor_get(v_a_2852_, 1);
v___x_2855_ = lean_byte_array_size(v_array_2853_);
v___x_2856_ = lean_nat_dec_lt(v_idx_2854_, v___x_2855_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; lean_object* v___x_2858_; 
lean_dec_ref(v_scheme_2851_);
lean_dec_ref(v_config_2850_);
v___x_2857_ = lean_box(0);
v___x_2858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2858_, 0, v_a_2852_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
return v___x_2858_;
}
else
{
uint8_t v___x_2859_; uint8_t v_got_2860_; uint8_t v___x_2861_; 
v___x_2859_ = 58;
v_got_2860_ = lean_byte_array_fget(v_array_2853_, v_idx_2854_);
v___x_2861_ = lean_uint8_dec_eq(v_got_2860_, v___x_2859_);
if (v___x_2861_ == 0)
{
lean_object* v___x_2862_; lean_object* v___x_2863_; 
lean_dec_ref(v_scheme_2851_);
lean_dec_ref(v_config_2850_);
v___x_2862_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
v___x_2863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2863_, 0, v_a_2852_);
lean_ctor_set(v___x_2863_, 1, v___x_2862_);
return v___x_2863_;
}
else
{
lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2938_; 
lean_inc(v_idx_2854_);
lean_inc_ref(v_array_2853_);
v_isSharedCheck_2938_ = !lean_is_exclusive(v_a_2852_);
if (v_isSharedCheck_2938_ == 0)
{
lean_object* v_unused_2939_; lean_object* v_unused_2940_; 
v_unused_2939_ = lean_ctor_get(v_a_2852_, 1);
lean_dec(v_unused_2939_);
v_unused_2940_ = lean_ctor_get(v_a_2852_, 0);
lean_dec(v_unused_2940_);
v___x_2865_ = v_a_2852_;
v_isShared_2866_ = v_isSharedCheck_2938_;
goto v_resetjp_2864_;
}
else
{
lean_dec(v_a_2852_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2938_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2870_; 
v___x_2867_ = lean_unsigned_to_nat(1u);
v___x_2868_ = lean_nat_add(v_idx_2854_, v___x_2867_);
lean_dec(v_idx_2854_);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 1, v___x_2868_);
v___x_2870_ = v___x_2865_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_array_2853_);
lean_ctor_set(v_reuseFailAlloc_2937_, 1, v___x_2868_);
v___x_2870_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
lean_object* v___x_2871_; 
lean_inc_ref(v_config_2850_);
v___x_2871_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2850_, v___x_2870_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_res_2872_; lean_object* v_pos_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2927_; 
v_res_2872_ = lean_ctor_get(v___x_2871_, 1);
v_pos_2873_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2875_ = v___x_2871_;
v_isShared_2876_ = v_isSharedCheck_2927_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_res_2872_);
lean_inc(v_pos_2873_);
lean_dec(v___x_2871_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2927_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v_fst_2877_; lean_object* v_snd_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2926_; 
v_fst_2877_ = lean_ctor_get(v_res_2872_, 0);
v_snd_2878_ = lean_ctor_get(v_res_2872_, 1);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_res_2872_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2880_ = v_res_2872_;
v_isShared_2881_ = v_isSharedCheck_2926_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_snd_2878_);
lean_inc(v_fst_2877_);
lean_dec(v_res_2872_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2926_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v_pos_2883_; lean_object* v_res_2884_; lean_object* v_array_2891_; lean_object* v_idx_2892_; lean_object* v_pos_2894_; lean_object* v_idx_2895_; lean_object* v_err_2896_; lean_object* v___x_2902_; uint8_t v___x_2903_; 
v_array_2891_ = lean_ctor_get(v_pos_2873_, 0);
v_idx_2892_ = lean_ctor_get(v_pos_2873_, 1);
lean_inc(v_idx_2892_);
v___x_2902_ = lean_byte_array_size(v_array_2891_);
v___x_2903_ = lean_nat_dec_lt(v_idx_2892_, v___x_2902_);
if (v___x_2903_ == 0)
{
lean_object* v___x_2904_; 
lean_dec_ref(v_config_2850_);
v___x_2904_ = lean_box(0);
lean_inc(v_idx_2892_);
v_pos_2894_ = v_pos_2873_;
v_idx_2895_ = v_idx_2892_;
v_err_2896_ = v___x_2904_;
goto v___jp_2893_;
}
else
{
uint8_t v___x_2905_; uint8_t v_got_2906_; uint8_t v___x_2907_; 
v___x_2905_ = 63;
v_got_2906_ = lean_byte_array_fget(v_array_2891_, v_idx_2892_);
v___x_2907_ = lean_uint8_dec_eq(v_got_2906_, v___x_2905_);
if (v___x_2907_ == 0)
{
lean_object* v___x_2908_; 
lean_dec_ref(v_config_2850_);
v___x_2908_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_2892_);
v_pos_2894_ = v_pos_2873_;
v_idx_2895_ = v_idx_2892_;
v_err_2896_ = v___x_2908_;
goto v___jp_2893_;
}
else
{
lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2923_; 
lean_inc_ref(v_array_2891_);
v_isSharedCheck_2923_ = !lean_is_exclusive(v_pos_2873_);
if (v_isSharedCheck_2923_ == 0)
{
lean_object* v_unused_2924_; lean_object* v_unused_2925_; 
v_unused_2924_ = lean_ctor_get(v_pos_2873_, 1);
lean_dec(v_unused_2924_);
v_unused_2925_ = lean_ctor_get(v_pos_2873_, 0);
lean_dec(v_unused_2925_);
v___x_2910_ = v_pos_2873_;
v_isShared_2911_ = v_isSharedCheck_2923_;
goto v_resetjp_2909_;
}
else
{
lean_dec(v_pos_2873_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2923_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2912_; lean_object* v___x_2914_; 
v___x_2912_ = lean_nat_add(v_idx_2892_, v___x_2867_);
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 1, v___x_2912_);
v___x_2914_ = v___x_2910_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_array_2891_);
lean_ctor_set(v_reuseFailAlloc_2922_, 1, v___x_2912_);
v___x_2914_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
lean_object* v___x_2915_; 
v___x_2915_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2850_, v___x_2914_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_pos_2916_; lean_object* v_res_2917_; lean_object* v___x_2918_; 
lean_dec(v_idx_2892_);
lean_del_object(v___x_2880_);
v_pos_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_pos_2916_);
v_res_2917_ = lean_ctor_get(v___x_2915_, 1);
lean_inc(v_res_2917_);
lean_dec_ref_known(v___x_2915_, 2);
v___x_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2918_, 0, v_res_2917_);
v_pos_2883_ = v_pos_2916_;
v_res_2884_ = v___x_2918_;
goto v___jp_2882_;
}
else
{
lean_object* v_pos_2919_; lean_object* v_err_2920_; lean_object* v_idx_2921_; 
v_pos_2919_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_pos_2919_);
v_err_2920_ = lean_ctor_get(v___x_2915_, 1);
lean_inc(v_err_2920_);
lean_dec_ref_known(v___x_2915_, 2);
v_idx_2921_ = lean_ctor_get(v_pos_2919_, 1);
lean_inc(v_idx_2921_);
v_pos_2894_ = v_pos_2919_;
v_idx_2895_ = v_idx_2921_;
v_err_2896_ = v_err_2920_;
goto v___jp_2893_;
}
}
}
}
}
v___jp_2882_:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2889_; 
v___x_2885_ = lean_box(0);
v___x_2886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2886_, 0, v_scheme_2851_);
lean_ctor_set(v___x_2886_, 1, v_fst_2877_);
lean_ctor_set(v___x_2886_, 2, v_snd_2878_);
lean_ctor_set(v___x_2886_, 3, v_res_2884_);
lean_ctor_set(v___x_2886_, 4, v___x_2885_);
v___x_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 1, v___x_2887_);
lean_ctor_set(v___x_2875_, 0, v_pos_2883_);
v___x_2889_ = v___x_2875_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_pos_2883_);
lean_ctor_set(v_reuseFailAlloc_2890_, 1, v___x_2887_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
v___jp_2893_:
{
uint8_t v___x_2897_; 
v___x_2897_ = lean_nat_dec_eq(v_idx_2892_, v_idx_2895_);
lean_dec(v_idx_2895_);
lean_dec(v_idx_2892_);
if (v___x_2897_ == 0)
{
lean_object* v___x_2899_; 
lean_dec(v_snd_2878_);
lean_dec(v_fst_2877_);
lean_del_object(v___x_2875_);
lean_dec_ref(v_scheme_2851_);
if (v_isShared_2881_ == 0)
{
lean_ctor_set_tag(v___x_2880_, 1);
lean_ctor_set(v___x_2880_, 1, v_err_2896_);
lean_ctor_set(v___x_2880_, 0, v_pos_2894_);
v___x_2899_ = v___x_2880_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_pos_2894_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v_err_2896_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
else
{
lean_object* v___x_2901_; 
lean_dec(v_err_2896_);
lean_del_object(v___x_2880_);
v___x_2901_ = lean_box(0);
v_pos_2883_ = v_pos_2894_;
v_res_2884_ = v___x_2901_;
goto v___jp_2882_;
}
}
}
}
}
else
{
lean_object* v_pos_2928_; lean_object* v_err_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
lean_dec_ref(v_scheme_2851_);
lean_dec_ref(v_config_2850_);
v_pos_2928_ = lean_ctor_get(v___x_2871_, 0);
v_err_2929_ = lean_ctor_get(v___x_2871_, 1);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2871_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_err_2929_);
lean_inc(v_pos_2928_);
lean_dec(v___x_2871_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_pos_2928_);
lean_ctor_set(v_reuseFailAlloc_2935_, 1, v_err_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(lean_object* v_config_2949_, lean_object* v_a_2950_){
_start:
{
lean_object* v___x_2954_; 
lean_inc_ref(v_a_2950_);
v___x_2954_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_2949_, v_a_2950_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_pos_2955_; lean_object* v_res_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_3052_; 
v_pos_2955_ = lean_ctor_get(v___x_2954_, 0);
v_res_2956_ = lean_ctor_get(v___x_2954_, 1);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_2958_ = v___x_2954_;
v_isShared_2959_ = v_isSharedCheck_3052_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_res_2956_);
lean_inc(v_pos_2955_);
lean_dec(v___x_2954_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_3052_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v_pos_2963_; lean_object* v_res_2964_; lean_object* v___y_2972_; lean_object* v_idx_2973_; lean_object* v___y_2974_; lean_object* v_pos_2975_; lean_object* v_idx_2976_; lean_object* v_err_2977_; lean_object* v___x_3046_; uint8_t v___x_3047_; 
v___x_3046_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2));
v___x_3047_ = lean_string_dec_eq(v_res_2956_, v___x_3046_);
if (v___x_3047_ == 0)
{
lean_object* v___x_3048_; uint8_t v___x_3049_; 
v___x_3048_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3));
v___x_3049_ = lean_string_dec_eq(v_res_2956_, v___x_3048_);
if (v___x_3049_ == 0)
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
lean_del_object(v___x_2958_);
lean_dec(v_res_2956_);
lean_dec(v_pos_2955_);
lean_dec_ref(v_config_2949_);
v___x_3050_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5));
v___x_3051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3051_, 0, v_a_2950_);
lean_ctor_set(v___x_3051_, 1, v___x_3050_);
return v___x_3051_;
}
else
{
goto v___jp_2981_;
}
}
else
{
goto v___jp_2981_;
}
v___jp_2960_:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2969_; 
v___x_2965_ = lean_box(0);
v___x_2966_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2966_, 0, v_res_2956_);
lean_ctor_set(v___x_2966_, 1, v___y_2961_);
lean_ctor_set(v___x_2966_, 2, v___y_2962_);
lean_ctor_set(v___x_2966_, 3, v_res_2964_);
lean_ctor_set(v___x_2966_, 4, v___x_2965_);
v___x_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2966_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 1, v___x_2967_);
lean_ctor_set(v___x_2958_, 0, v_pos_2963_);
v___x_2969_ = v___x_2958_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_pos_2963_);
lean_ctor_set(v_reuseFailAlloc_2970_, 1, v___x_2967_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
v___jp_2971_:
{
uint8_t v___x_2978_; 
v___x_2978_ = lean_nat_dec_eq(v_idx_2973_, v_idx_2976_);
lean_dec(v_idx_2976_);
lean_dec(v_idx_2973_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; 
lean_dec_ref(v_pos_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2972_);
lean_del_object(v___x_2958_);
lean_dec(v_res_2956_);
v___x_2979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2979_, 0, v_a_2950_);
lean_ctor_set(v___x_2979_, 1, v_err_2977_);
return v___x_2979_;
}
else
{
lean_object* v___x_2980_; 
lean_dec(v_err_2977_);
lean_dec_ref(v_a_2950_);
v___x_2980_ = lean_box(0);
v___y_2961_ = v___y_2972_;
v___y_2962_ = v___y_2974_;
v_pos_2963_ = v_pos_2975_;
v_res_2964_ = v___x_2980_;
goto v___jp_2960_;
}
}
v___jp_2981_:
{
lean_object* v_array_2982_; lean_object* v_idx_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_3045_; 
v_array_2982_ = lean_ctor_get(v_pos_2955_, 0);
v_idx_2983_ = lean_ctor_get(v_pos_2955_, 1);
v_isSharedCheck_3045_ = !lean_is_exclusive(v_pos_2955_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_2985_ = v_pos_2955_;
v_isShared_2986_ = v_isSharedCheck_3045_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_idx_2983_);
lean_inc(v_array_2982_);
lean_dec(v_pos_2955_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_3045_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2987_; uint8_t v___x_2988_; 
v___x_2987_ = lean_byte_array_size(v_array_2982_);
v___x_2988_ = lean_nat_dec_lt(v_idx_2983_, v___x_2987_);
if (v___x_2988_ == 0)
{
lean_object* v___x_2989_; lean_object* v___x_2990_; 
lean_del_object(v___x_2985_);
lean_dec(v_idx_2983_);
lean_dec_ref(v_array_2982_);
lean_del_object(v___x_2958_);
lean_dec(v_res_2956_);
lean_dec_ref(v_config_2949_);
v___x_2989_ = lean_box(0);
v___x_2990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2990_, 0, v_a_2950_);
lean_ctor_set(v___x_2990_, 1, v___x_2989_);
return v___x_2990_;
}
else
{
uint8_t v___x_2991_; uint8_t v_got_2992_; uint8_t v___x_2993_; 
v___x_2991_ = 58;
v_got_2992_ = lean_byte_array_fget(v_array_2982_, v_idx_2983_);
v___x_2993_ = lean_uint8_dec_eq(v_got_2992_, v___x_2991_);
if (v___x_2993_ == 0)
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
lean_del_object(v___x_2985_);
lean_dec(v_idx_2983_);
lean_dec_ref(v_array_2982_);
lean_del_object(v___x_2958_);
lean_dec(v_res_2956_);
lean_dec_ref(v_config_2949_);
v___x_2994_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
v___x_2995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2995_, 0, v_a_2950_);
lean_ctor_set(v___x_2995_, 1, v___x_2994_);
return v___x_2995_;
}
else
{
lean_object* v___x_2996_; lean_object* v___x_2997_; uint8_t v___x_2998_; 
v___x_2996_ = lean_unsigned_to_nat(1u);
v___x_2997_ = lean_nat_add(v_idx_2983_, v___x_2996_);
lean_dec(v_idx_2983_);
v___x_2998_ = lean_nat_dec_lt(v___x_2997_, v___x_2987_);
if (v___x_2998_ == 0)
{
lean_dec(v___x_2997_);
lean_del_object(v___x_2985_);
lean_dec_ref(v_array_2982_);
lean_del_object(v___x_2958_);
lean_dec(v_res_2956_);
lean_dec_ref(v_config_2949_);
goto v___jp_2951_;
}
else
{
uint8_t v___x_2999_; uint8_t v___x_3000_; uint8_t v___x_3001_; 
v___x_2999_ = lean_byte_array_fget(v_array_2982_, v___x_2997_);
v___x_3000_ = 47;
v___x_3001_ = lean_uint8_dec_eq(v___x_2999_, v___x_3000_);
if (v___x_3001_ == 0)
{
lean_dec(v___x_2997_);
lean_del_object(v___x_2985_);
lean_dec_ref(v_array_2982_);
lean_del_object(v___x_2958_);
lean_dec(v_res_2956_);
lean_dec_ref(v_config_2949_);
goto v___jp_2951_;
}
else
{
lean_object* v___x_3003_; 
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 1, v___x_2997_);
v___x_3003_ = v___x_2985_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_array_2982_);
lean_ctor_set(v_reuseFailAlloc_3044_, 1, v___x_2997_);
v___x_3003_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
lean_object* v___x_3004_; 
lean_inc_ref(v_config_2949_);
v___x_3004_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2949_, v___x_3003_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_res_3005_; lean_object* v_pos_3006_; lean_object* v_fst_3007_; lean_object* v_snd_3008_; lean_object* v_array_3009_; lean_object* v_idx_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; 
v_res_3005_ = lean_ctor_get(v___x_3004_, 1);
lean_inc(v_res_3005_);
v_pos_3006_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_pos_3006_);
lean_dec_ref_known(v___x_3004_, 2);
v_fst_3007_ = lean_ctor_get(v_res_3005_, 0);
lean_inc(v_fst_3007_);
v_snd_3008_ = lean_ctor_get(v_res_3005_, 1);
lean_inc(v_snd_3008_);
lean_dec(v_res_3005_);
v_array_3009_ = lean_ctor_get(v_pos_3006_, 0);
v_idx_3010_ = lean_ctor_get(v_pos_3006_, 1);
lean_inc(v_idx_3010_);
v___x_3011_ = lean_byte_array_size(v_array_3009_);
v___x_3012_ = lean_nat_dec_lt(v_idx_3010_, v___x_3011_);
if (v___x_3012_ == 0)
{
lean_object* v___x_3013_; 
lean_dec_ref(v_config_2949_);
v___x_3013_ = lean_box(0);
lean_inc(v_idx_3010_);
v___y_2972_ = v_fst_3007_;
v_idx_2973_ = v_idx_3010_;
v___y_2974_ = v_snd_3008_;
v_pos_2975_ = v_pos_3006_;
v_idx_2976_ = v_idx_3010_;
v_err_2977_ = v___x_3013_;
goto v___jp_2971_;
}
else
{
uint8_t v___x_3014_; uint8_t v_got_3015_; uint8_t v___x_3016_; 
v___x_3014_ = 63;
v_got_3015_ = lean_byte_array_fget(v_array_3009_, v_idx_3010_);
v___x_3016_ = lean_uint8_dec_eq(v_got_3015_, v___x_3014_);
if (v___x_3016_ == 0)
{
lean_object* v___x_3017_; 
lean_dec_ref(v_config_2949_);
v___x_3017_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_3010_);
v___y_2972_ = v_fst_3007_;
v_idx_2973_ = v_idx_3010_;
v___y_2974_ = v_snd_3008_;
v_pos_2975_ = v_pos_3006_;
v_idx_2976_ = v_idx_3010_;
v_err_2977_ = v___x_3017_;
goto v___jp_2971_;
}
else
{
lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3032_; 
lean_inc_ref(v_array_3009_);
v_isSharedCheck_3032_ = !lean_is_exclusive(v_pos_3006_);
if (v_isSharedCheck_3032_ == 0)
{
lean_object* v_unused_3033_; lean_object* v_unused_3034_; 
v_unused_3033_ = lean_ctor_get(v_pos_3006_, 1);
lean_dec(v_unused_3033_);
v_unused_3034_ = lean_ctor_get(v_pos_3006_, 0);
lean_dec(v_unused_3034_);
v___x_3019_ = v_pos_3006_;
v_isShared_3020_ = v_isSharedCheck_3032_;
goto v_resetjp_3018_;
}
else
{
lean_dec(v_pos_3006_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3032_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3021_; lean_object* v___x_3023_; 
v___x_3021_ = lean_nat_add(v_idx_3010_, v___x_2996_);
if (v_isShared_3020_ == 0)
{
lean_ctor_set(v___x_3019_, 1, v___x_3021_);
v___x_3023_ = v___x_3019_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_array_3009_);
lean_ctor_set(v_reuseFailAlloc_3031_, 1, v___x_3021_);
v___x_3023_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
lean_object* v___x_3024_; 
v___x_3024_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2949_, v___x_3023_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_pos_3025_; lean_object* v_res_3026_; lean_object* v___x_3027_; 
lean_dec(v_idx_3010_);
lean_dec_ref(v_a_2950_);
v_pos_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_pos_3025_);
v_res_3026_ = lean_ctor_get(v___x_3024_, 1);
lean_inc(v_res_3026_);
lean_dec_ref_known(v___x_3024_, 2);
v___x_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3027_, 0, v_res_3026_);
v___y_2961_ = v_fst_3007_;
v___y_2962_ = v_snd_3008_;
v_pos_2963_ = v_pos_3025_;
v_res_2964_ = v___x_3027_;
goto v___jp_2960_;
}
else
{
lean_object* v_pos_3028_; lean_object* v_err_3029_; lean_object* v_idx_3030_; 
v_pos_3028_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_pos_3028_);
v_err_3029_ = lean_ctor_get(v___x_3024_, 1);
lean_inc(v_err_3029_);
lean_dec_ref_known(v___x_3024_, 2);
v_idx_3030_ = lean_ctor_get(v_pos_3028_, 1);
lean_inc(v_idx_3030_);
v___y_2972_ = v_fst_3007_;
v_idx_2973_ = v_idx_3010_;
v___y_2974_ = v_snd_3008_;
v_pos_2975_ = v_pos_3028_;
v_idx_2976_ = v_idx_3030_;
v_err_2977_ = v_err_3029_;
goto v___jp_2971_;
}
}
}
}
}
}
else
{
lean_object* v_err_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
lean_del_object(v___x_2958_);
lean_dec(v_res_2956_);
lean_dec_ref(v_config_2949_);
v_err_3035_ = lean_ctor_get(v___x_3004_, 1);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3042_ == 0)
{
lean_object* v_unused_3043_; 
v_unused_3043_ = lean_ctor_get(v___x_3004_, 0);
lean_dec(v_unused_3043_);
v___x_3037_ = v___x_3004_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_err_3035_);
lean_dec(v___x_3004_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 0, v_a_2950_);
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_2950_);
lean_ctor_set(v_reuseFailAlloc_3041_, 1, v_err_3035_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
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
lean_object* v_err_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
lean_dec_ref(v_config_2949_);
v_err_3053_ = lean_ctor_get(v___x_2954_, 1);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_3060_ == 0)
{
lean_object* v_unused_3061_; 
v_unused_3061_ = lean_ctor_get(v___x_2954_, 0);
lean_dec(v_unused_3061_);
v___x_3055_ = v___x_2954_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_err_3053_);
lean_dec(v___x_2954_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
lean_ctor_set(v___x_3055_, 0, v_a_2950_);
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_2950_);
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
v___jp_2951_:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2952_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1));
v___x_2953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2953_, 0, v_a_2950_);
lean_ctor_set(v___x_2953_, 1, v___x_2952_);
return v___x_2953_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(lean_object* v_config_3062_, lean_object* v_a_3063_){
_start:
{
lean_object* v___x_3064_; 
lean_inc_ref(v_a_3063_);
v___x_3064_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3062_, v_a_3063_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_object* v_pos_3065_; lean_object* v_res_3066_; lean_object* v___x_3067_; 
v_pos_3065_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_pos_3065_);
v_res_3066_ = lean_ctor_get(v___x_3064_, 1);
lean_inc(v_res_3066_);
lean_dec_ref_known(v___x_3064_, 2);
v___x_3067_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(v_config_3062_, v_res_3066_, v_pos_3065_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_dec_ref(v_a_3063_);
return v___x_3067_;
}
else
{
lean_object* v_err_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
v_err_3068_ = lean_ctor_get(v___x_3067_, 1);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3075_ == 0)
{
lean_object* v_unused_3076_; 
v_unused_3076_ = lean_ctor_get(v___x_3067_, 0);
lean_dec(v_unused_3076_);
v___x_3070_ = v___x_3067_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_err_3068_);
lean_dec(v___x_3067_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
lean_ctor_set(v___x_3070_, 0, v_a_3063_);
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3063_);
lean_ctor_set(v_reuseFailAlloc_3074_, 1, v_err_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
else
{
lean_object* v_err_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
lean_dec_ref(v_config_3062_);
v_err_3077_ = lean_ctor_get(v___x_3064_, 1);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3084_ == 0)
{
lean_object* v_unused_3085_; 
v_unused_3085_ = lean_ctor_get(v___x_3064_, 0);
lean_dec(v_unused_3085_);
v___x_3079_ = v___x_3064_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_err_3077_);
lean_dec(v___x_3064_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
lean_ctor_set(v___x_3079_, 0, v_a_3063_);
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3063_);
lean_ctor_set(v_reuseFailAlloc_3083_, 1, v_err_3077_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(lean_object* v_config_3086_, lean_object* v_a_3087_){
_start:
{
lean_object* v___x_3088_; 
lean_inc_ref(v_a_3087_);
v___x_3088_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_3086_, v_a_3087_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v_pos_3089_; lean_object* v_res_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3142_; 
v_pos_3089_ = lean_ctor_get(v___x_3088_, 0);
v_res_3090_ = lean_ctor_get(v___x_3088_, 1);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3092_ = v___x_3088_;
v_isShared_3093_ = v_isSharedCheck_3142_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_res_3090_);
lean_inc(v_pos_3089_);
lean_dec(v___x_3088_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3142_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v_array_3094_; lean_object* v_idx_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3141_; 
v_array_3094_ = lean_ctor_get(v_pos_3089_, 0);
v_idx_3095_ = lean_ctor_get(v_pos_3089_, 1);
v_isSharedCheck_3141_ = !lean_is_exclusive(v_pos_3089_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3097_ = v_pos_3089_;
v_isShared_3098_ = v_isSharedCheck_3141_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_idx_3095_);
lean_inc(v_array_3094_);
lean_dec(v_pos_3089_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3141_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3099_; uint8_t v___x_3100_; 
v___x_3099_ = lean_byte_array_size(v_array_3094_);
v___x_3100_ = lean_nat_dec_lt(v_idx_3095_, v___x_3099_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3101_; lean_object* v___x_3103_; 
lean_del_object(v___x_3097_);
lean_dec(v_idx_3095_);
lean_dec_ref(v_array_3094_);
lean_dec(v_res_3090_);
v___x_3101_ = lean_box(0);
if (v_isShared_3093_ == 0)
{
lean_ctor_set_tag(v___x_3092_, 1);
lean_ctor_set(v___x_3092_, 1, v___x_3101_);
lean_ctor_set(v___x_3092_, 0, v_a_3087_);
v___x_3103_ = v___x_3092_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3087_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v___x_3101_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
else
{
uint8_t v___x_3105_; uint8_t v_got_3106_; uint8_t v___x_3107_; 
v___x_3105_ = 58;
v_got_3106_ = lean_byte_array_fget(v_array_3094_, v_idx_3095_);
v___x_3107_ = lean_uint8_dec_eq(v_got_3106_, v___x_3105_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3108_; lean_object* v___x_3110_; 
lean_del_object(v___x_3097_);
lean_dec(v_idx_3095_);
lean_dec_ref(v_array_3094_);
lean_dec(v_res_3090_);
v___x_3108_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_3093_ == 0)
{
lean_ctor_set_tag(v___x_3092_, 1);
lean_ctor_set(v___x_3092_, 1, v___x_3108_);
lean_ctor_set(v___x_3092_, 0, v_a_3087_);
v___x_3110_ = v___x_3092_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3087_);
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
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3115_; 
lean_del_object(v___x_3092_);
v___x_3112_ = lean_unsigned_to_nat(1u);
v___x_3113_ = lean_nat_add(v_idx_3095_, v___x_3112_);
lean_dec(v_idx_3095_);
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 1, v___x_3113_);
v___x_3115_ = v___x_3097_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_array_3094_);
lean_ctor_set(v_reuseFailAlloc_3140_, 1, v___x_3113_);
v___x_3115_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
lean_object* v___x_3116_; 
v___x_3116_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_3115_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_pos_3117_; lean_object* v_res_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3130_; 
lean_dec_ref(v_a_3087_);
v_pos_3117_ = lean_ctor_get(v___x_3116_, 0);
v_res_3118_ = lean_ctor_get(v___x_3116_, 1);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3120_ = v___x_3116_;
v_isShared_3121_ = v_isSharedCheck_3130_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_res_3118_);
lean_inc(v_pos_3117_);
lean_dec(v___x_3116_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3130_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; uint16_t v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3128_; 
v___x_3122_ = lean_box(0);
v___x_3123_ = lean_alloc_ctor(2, 0, 2);
v___x_3124_ = lean_unbox(v_res_3118_);
lean_dec(v_res_3118_);
lean_ctor_set_uint16(v___x_3123_, 0, v___x_3124_);
v___x_3125_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3122_);
lean_ctor_set(v___x_3125_, 1, v_res_3090_);
lean_ctor_set(v___x_3125_, 2, v___x_3123_);
v___x_3126_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3125_);
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 1, v___x_3126_);
v___x_3128_ = v___x_3120_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_pos_3117_);
lean_ctor_set(v_reuseFailAlloc_3129_, 1, v___x_3126_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
else
{
lean_object* v_err_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
lean_dec(v_res_3090_);
v_err_3131_ = lean_ctor_get(v___x_3116_, 1);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3138_ == 0)
{
lean_object* v_unused_3139_; 
v_unused_3139_ = lean_ctor_get(v___x_3116_, 0);
lean_dec(v_unused_3139_);
v___x_3133_ = v___x_3116_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_err_3131_);
lean_dec(v___x_3116_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 0, v_a_3087_);
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3087_);
lean_ctor_set(v_reuseFailAlloc_3137_, 1, v_err_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
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
lean_object* v_err_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
v_err_3143_ = lean_ctor_get(v___x_3088_, 1);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3150_ == 0)
{
lean_object* v_unused_3151_; 
v_unused_3151_ = lean_ctor_get(v___x_3088_, 0);
lean_dec(v_unused_3151_);
v___x_3145_ = v___x_3088_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_err_3143_);
lean_dec(v___x_3088_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
lean_ctor_set(v___x_3145_, 0, v_a_3087_);
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3087_);
lean_ctor_set(v_reuseFailAlloc_3149_, 1, v_err_3143_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority___boxed(lean_object* v_config_3152_, lean_object* v_a_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3152_, v_a_3153_);
lean_dec_ref(v_config_3152_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object* v_config_3155_, lean_object* v_a_3156_){
_start:
{
lean_object* v___x_3157_; 
lean_inc_ref(v_a_3156_);
v___x_3157_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(v_a_3156_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_dec_ref(v_a_3156_);
lean_dec_ref(v_config_3155_);
return v___x_3157_;
}
else
{
lean_object* v_pos_3158_; lean_object* v_idx_3159_; lean_object* v_idx_3160_; uint8_t v___x_3161_; 
v_pos_3158_ = lean_ctor_get(v___x_3157_, 0);
v_idx_3159_ = lean_ctor_get(v_a_3156_, 1);
lean_inc(v_idx_3159_);
lean_dec_ref(v_a_3156_);
v_idx_3160_ = lean_ctor_get(v_pos_3158_, 1);
v___x_3161_ = lean_nat_dec_eq(v_idx_3159_, v_idx_3160_);
lean_dec(v_idx_3159_);
if (v___x_3161_ == 0)
{
lean_dec_ref(v_config_3155_);
return v___x_3157_;
}
else
{
lean_object* v___x_3162_; 
lean_inc(v_idx_3160_);
lean_inc(v_pos_3158_);
lean_dec_ref_known(v___x_3157_, 2);
lean_inc_ref(v_config_3155_);
v___x_3162_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(v_config_3155_, v_pos_3158_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_dec(v_idx_3160_);
lean_dec_ref(v_config_3155_);
return v___x_3162_;
}
else
{
lean_object* v_pos_3163_; lean_object* v_idx_3164_; uint8_t v___x_3165_; 
v_pos_3163_ = lean_ctor_get(v___x_3162_, 0);
v_idx_3164_ = lean_ctor_get(v_pos_3163_, 1);
v___x_3165_ = lean_nat_dec_eq(v_idx_3160_, v_idx_3164_);
lean_dec(v_idx_3160_);
if (v___x_3165_ == 0)
{
lean_dec_ref(v_config_3155_);
return v___x_3162_;
}
else
{
lean_object* v___x_3166_; 
lean_inc(v_idx_3164_);
lean_inc(v_pos_3163_);
lean_dec_ref_known(v___x_3162_, 2);
lean_inc_ref(v_config_3155_);
v___x_3166_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(v_config_3155_, v_pos_3163_);
if (lean_obj_tag(v___x_3166_) == 0)
{
lean_dec(v_idx_3164_);
lean_dec_ref(v_config_3155_);
return v___x_3166_;
}
else
{
lean_object* v_pos_3167_; lean_object* v_idx_3168_; uint8_t v___x_3169_; 
v_pos_3167_ = lean_ctor_get(v___x_3166_, 0);
v_idx_3168_ = lean_ctor_get(v_pos_3167_, 1);
v___x_3169_ = lean_nat_dec_eq(v_idx_3164_, v_idx_3168_);
lean_dec(v_idx_3164_);
if (v___x_3169_ == 0)
{
lean_dec_ref(v_config_3155_);
return v___x_3166_;
}
else
{
lean_object* v___x_3170_; 
lean_inc(v_idx_3168_);
lean_inc(v_pos_3167_);
lean_dec_ref_known(v___x_3166_, 2);
v___x_3170_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3155_, v_pos_3167_);
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_dec(v_idx_3168_);
lean_dec_ref(v_config_3155_);
return v___x_3170_;
}
else
{
lean_object* v_pos_3171_; lean_object* v_idx_3172_; uint8_t v___x_3173_; 
v_pos_3171_ = lean_ctor_get(v___x_3170_, 0);
v_idx_3172_ = lean_ctor_get(v_pos_3171_, 1);
v___x_3173_ = lean_nat_dec_eq(v_idx_3168_, v_idx_3172_);
lean_dec(v_idx_3168_);
if (v___x_3173_ == 0)
{
lean_dec_ref(v_config_3155_);
return v___x_3170_;
}
else
{
lean_object* v___x_3174_; 
lean_inc(v_pos_3171_);
lean_dec_ref_known(v___x_3170_, 2);
v___x_3174_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(v_config_3155_, v_pos_3171_);
return v___x_3174_;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(lean_object* v_config_3178_, lean_object* v_a_3179_){
_start:
{
lean_object* v___x_3180_; 
v___x_3180_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_3178_, v_a_3179_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_object* v_pos_3181_; lean_object* v_res_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3195_; 
v_pos_3181_ = lean_ctor_get(v___x_3180_, 0);
v_res_3182_ = lean_ctor_get(v___x_3180_, 1);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3184_ = v___x_3180_;
v_isShared_3185_ = v_isSharedCheck_3195_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_res_3182_);
lean_inc(v_pos_3181_);
lean_dec(v___x_3180_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3195_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3186_; 
v___x_3186_ = l_Std_Http_URI_EncodedFragment_decode(v_res_3182_);
lean_dec(v_res_3182_);
if (lean_obj_tag(v___x_3186_) == 1)
{
lean_object* v_val_3187_; lean_object* v___x_3189_; 
v_val_3187_ = lean_ctor_get(v___x_3186_, 0);
lean_inc(v_val_3187_);
lean_dec_ref_known(v___x_3186_, 1);
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 1, v_val_3187_);
v___x_3189_ = v___x_3184_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_pos_3181_);
lean_ctor_set(v_reuseFailAlloc_3190_, 1, v_val_3187_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
else
{
lean_object* v___x_3191_; lean_object* v___x_3193_; 
lean_dec(v___x_3186_);
v___x_3191_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___closed__1));
if (v_isShared_3185_ == 0)
{
lean_ctor_set_tag(v___x_3184_, 1);
lean_ctor_set(v___x_3184_, 1, v___x_3191_);
v___x_3193_ = v___x_3184_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_pos_3181_);
lean_ctor_set(v_reuseFailAlloc_3194_, 1, v___x_3191_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
}
}
else
{
lean_object* v_pos_3196_; lean_object* v_err_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
v_pos_3196_ = lean_ctor_get(v___x_3180_, 0);
v_err_3197_ = lean_ctor_get(v___x_3180_, 1);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3180_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_err_3197_);
lean_inc(v_pos_3196_);
lean_dec(v___x_3180_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_pos_3196_);
lean_ctor_set(v_reuseFailAlloc_3203_, 1, v_err_3197_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___boxed(lean_object* v_config_3205_, lean_object* v_a_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3205_, v_a_3206_);
lean_dec_ref(v_config_3205_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_uri(lean_object* v_config_3208_, lean_object* v_a_3209_){
_start:
{
lean_object* v___x_3210_; 
lean_inc_ref(v_a_3209_);
v___x_3210_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3208_, v_a_3209_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_pos_3211_; lean_object* v_res_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3341_; 
v_pos_3211_ = lean_ctor_get(v___x_3210_, 0);
v_res_3212_ = lean_ctor_get(v___x_3210_, 1);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3214_ = v___x_3210_;
v_isShared_3215_ = v_isSharedCheck_3341_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_res_3212_);
lean_inc(v_pos_3211_);
lean_dec(v___x_3210_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3341_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v_array_3216_; lean_object* v_idx_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3340_; 
v_array_3216_ = lean_ctor_get(v_pos_3211_, 0);
v_idx_3217_ = lean_ctor_get(v_pos_3211_, 1);
v_isSharedCheck_3340_ = !lean_is_exclusive(v_pos_3211_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3219_ = v_pos_3211_;
v_isShared_3220_ = v_isSharedCheck_3340_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_idx_3217_);
lean_inc(v_array_3216_);
lean_dec(v_pos_3211_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3340_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3221_; uint8_t v___x_3222_; 
v___x_3221_ = lean_byte_array_size(v_array_3216_);
v___x_3222_ = lean_nat_dec_lt(v_idx_3217_, v___x_3221_);
if (v___x_3222_ == 0)
{
lean_object* v___x_3223_; lean_object* v___x_3225_; 
lean_del_object(v___x_3219_);
lean_dec(v_idx_3217_);
lean_dec_ref(v_array_3216_);
lean_dec(v_res_3212_);
lean_dec_ref(v_config_3208_);
v___x_3223_ = lean_box(0);
if (v_isShared_3215_ == 0)
{
lean_ctor_set_tag(v___x_3214_, 1);
lean_ctor_set(v___x_3214_, 1, v___x_3223_);
lean_ctor_set(v___x_3214_, 0, v_a_3209_);
v___x_3225_ = v___x_3214_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_a_3209_);
lean_ctor_set(v_reuseFailAlloc_3226_, 1, v___x_3223_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
else
{
uint8_t v___x_3227_; uint8_t v_got_3228_; uint8_t v___x_3229_; 
v___x_3227_ = 58;
v_got_3228_ = lean_byte_array_fget(v_array_3216_, v_idx_3217_);
v___x_3229_ = lean_uint8_dec_eq(v_got_3228_, v___x_3227_);
if (v___x_3229_ == 0)
{
lean_object* v___x_3230_; lean_object* v___x_3232_; 
lean_del_object(v___x_3219_);
lean_dec(v_idx_3217_);
lean_dec_ref(v_array_3216_);
lean_dec(v_res_3212_);
lean_dec_ref(v_config_3208_);
v___x_3230_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_3215_ == 0)
{
lean_ctor_set_tag(v___x_3214_, 1);
lean_ctor_set(v___x_3214_, 1, v___x_3230_);
lean_ctor_set(v___x_3214_, 0, v_a_3209_);
v___x_3232_ = v___x_3214_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3209_);
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
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3237_; 
v___x_3234_ = lean_unsigned_to_nat(1u);
v___x_3235_ = lean_nat_add(v_idx_3217_, v___x_3234_);
lean_dec(v_idx_3217_);
if (v_isShared_3220_ == 0)
{
lean_ctor_set(v___x_3219_, 1, v___x_3235_);
v___x_3237_ = v___x_3219_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_array_3216_);
lean_ctor_set(v_reuseFailAlloc_3339_, 1, v___x_3235_);
v___x_3237_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
lean_object* v___x_3238_; 
lean_inc_ref(v_config_3208_);
v___x_3238_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_3208_, v___x_3237_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v_res_3239_; lean_object* v_pos_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3329_; 
v_res_3239_ = lean_ctor_get(v___x_3238_, 1);
v_pos_3240_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3242_ = v___x_3238_;
v_isShared_3243_ = v_isSharedCheck_3329_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_res_3239_);
lean_inc(v_pos_3240_);
lean_dec(v___x_3238_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3329_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v_fst_3244_; lean_object* v_snd_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3328_; 
v_fst_3244_ = lean_ctor_get(v_res_3239_, 0);
v_snd_3245_ = lean_ctor_get(v_res_3239_, 1);
v_isSharedCheck_3328_ = !lean_is_exclusive(v_res_3239_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3247_ = v_res_3239_;
v_isShared_3248_ = v_isSharedCheck_3328_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_snd_3245_);
lean_inc(v_fst_3244_);
lean_dec(v_res_3239_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3328_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___y_3250_; lean_object* v_pos_3251_; lean_object* v_res_3252_; lean_object* v___y_3259_; lean_object* v_idx_3260_; lean_object* v_pos_3261_; lean_object* v_err_3262_; lean_object* v_pos_3270_; lean_object* v_array_3271_; lean_object* v_idx_3272_; lean_object* v_res_3273_; lean_object* v_array_3291_; lean_object* v_idx_3292_; lean_object* v_pos_3294_; lean_object* v_array_3295_; lean_object* v_idx_3296_; lean_object* v_err_3297_; lean_object* v___x_3301_; uint8_t v___x_3302_; 
v_array_3291_ = lean_ctor_get(v_pos_3240_, 0);
lean_inc_ref(v_array_3291_);
v_idx_3292_ = lean_ctor_get(v_pos_3240_, 1);
lean_inc(v_idx_3292_);
v___x_3301_ = lean_byte_array_size(v_array_3291_);
v___x_3302_ = lean_nat_dec_lt(v_idx_3292_, v___x_3301_);
if (v___x_3302_ == 0)
{
lean_object* v___x_3303_; 
v___x_3303_ = lean_box(0);
lean_inc(v_idx_3292_);
v_pos_3294_ = v_pos_3240_;
v_array_3295_ = v_array_3291_;
v_idx_3296_ = v_idx_3292_;
v_err_3297_ = v___x_3303_;
goto v___jp_3293_;
}
else
{
uint8_t v___x_3304_; uint8_t v_got_3305_; uint8_t v___x_3306_; 
v___x_3304_ = 63;
v_got_3305_ = lean_byte_array_fget(v_array_3291_, v_idx_3292_);
v___x_3306_ = lean_uint8_dec_eq(v_got_3305_, v___x_3304_);
if (v___x_3306_ == 0)
{
lean_object* v___x_3307_; 
v___x_3307_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_3292_);
v_pos_3294_ = v_pos_3240_;
v_array_3295_ = v_array_3291_;
v_idx_3296_ = v_idx_3292_;
v_err_3297_ = v___x_3307_;
goto v___jp_3293_;
}
else
{
lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3325_; 
v_isSharedCheck_3325_ = !lean_is_exclusive(v_pos_3240_);
if (v_isSharedCheck_3325_ == 0)
{
lean_object* v_unused_3326_; lean_object* v_unused_3327_; 
v_unused_3326_ = lean_ctor_get(v_pos_3240_, 1);
lean_dec(v_unused_3326_);
v_unused_3327_ = lean_ctor_get(v_pos_3240_, 0);
lean_dec(v_unused_3327_);
v___x_3309_ = v_pos_3240_;
v_isShared_3310_ = v_isSharedCheck_3325_;
goto v_resetjp_3308_;
}
else
{
lean_dec(v_pos_3240_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3325_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3311_; lean_object* v___x_3313_; 
v___x_3311_ = lean_nat_add(v_idx_3292_, v___x_3234_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 1, v___x_3311_);
v___x_3313_ = v___x_3309_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_array_3291_);
lean_ctor_set(v_reuseFailAlloc_3324_, 1, v___x_3311_);
v___x_3313_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
lean_object* v___x_3314_; 
lean_inc_ref(v_config_3208_);
v___x_3314_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3208_, v___x_3313_);
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_object* v_pos_3315_; lean_object* v_res_3316_; lean_object* v_array_3317_; lean_object* v_idx_3318_; lean_object* v___x_3319_; 
lean_dec(v_idx_3292_);
v_pos_3315_ = lean_ctor_get(v___x_3314_, 0);
lean_inc(v_pos_3315_);
v_res_3316_ = lean_ctor_get(v___x_3314_, 1);
lean_inc(v_res_3316_);
lean_dec_ref_known(v___x_3314_, 2);
v_array_3317_ = lean_ctor_get(v_pos_3315_, 0);
lean_inc_ref(v_array_3317_);
v_idx_3318_ = lean_ctor_get(v_pos_3315_, 1);
lean_inc(v_idx_3318_);
v___x_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3319_, 0, v_res_3316_);
v_pos_3270_ = v_pos_3315_;
v_array_3271_ = v_array_3317_;
v_idx_3272_ = v_idx_3318_;
v_res_3273_ = v___x_3319_;
goto v___jp_3269_;
}
else
{
lean_object* v_pos_3320_; lean_object* v_err_3321_; lean_object* v_array_3322_; lean_object* v_idx_3323_; 
v_pos_3320_ = lean_ctor_get(v___x_3314_, 0);
lean_inc(v_pos_3320_);
v_err_3321_ = lean_ctor_get(v___x_3314_, 1);
lean_inc(v_err_3321_);
lean_dec_ref_known(v___x_3314_, 2);
v_array_3322_ = lean_ctor_get(v_pos_3320_, 0);
lean_inc_ref(v_array_3322_);
v_idx_3323_ = lean_ctor_get(v_pos_3320_, 1);
lean_inc(v_idx_3323_);
v_pos_3294_ = v_pos_3320_;
v_array_3295_ = v_array_3322_;
v_idx_3296_ = v_idx_3323_;
v_err_3297_ = v_err_3321_;
goto v___jp_3293_;
}
}
}
}
}
v___jp_3249_:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3256_; 
v___x_3253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3253_, 0, v_res_3212_);
lean_ctor_set(v___x_3253_, 1, v_fst_3244_);
lean_ctor_set(v___x_3253_, 2, v_snd_3245_);
lean_ctor_set(v___x_3253_, 3, v___y_3250_);
lean_ctor_set(v___x_3253_, 4, v_res_3252_);
v___x_3254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3253_);
if (v_isShared_3243_ == 0)
{
lean_ctor_set(v___x_3242_, 1, v___x_3254_);
lean_ctor_set(v___x_3242_, 0, v_pos_3251_);
v___x_3256_ = v___x_3242_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_pos_3251_);
lean_ctor_set(v_reuseFailAlloc_3257_, 1, v___x_3254_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
v___jp_3258_:
{
lean_object* v_idx_3263_; uint8_t v___x_3264_; 
v_idx_3263_ = lean_ctor_get(v_pos_3261_, 1);
v___x_3264_ = lean_nat_dec_eq(v_idx_3260_, v_idx_3263_);
lean_dec(v_idx_3260_);
if (v___x_3264_ == 0)
{
lean_object* v___x_3266_; 
lean_dec_ref(v_pos_3261_);
lean_dec(v___y_3259_);
lean_dec(v_snd_3245_);
lean_dec(v_fst_3244_);
lean_del_object(v___x_3242_);
lean_dec(v_res_3212_);
if (v_isShared_3215_ == 0)
{
lean_ctor_set_tag(v___x_3214_, 1);
lean_ctor_set(v___x_3214_, 1, v_err_3262_);
lean_ctor_set(v___x_3214_, 0, v_a_3209_);
v___x_3266_ = v___x_3214_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_a_3209_);
lean_ctor_set(v_reuseFailAlloc_3267_, 1, v_err_3262_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
else
{
lean_object* v___x_3268_; 
lean_dec(v_err_3262_);
lean_del_object(v___x_3214_);
lean_dec_ref(v_a_3209_);
v___x_3268_ = lean_box(0);
v___y_3250_ = v___y_3259_;
v_pos_3251_ = v_pos_3261_;
v_res_3252_ = v___x_3268_;
goto v___jp_3249_;
}
}
v___jp_3269_:
{
lean_object* v___x_3274_; uint8_t v___x_3275_; 
v___x_3274_ = lean_byte_array_size(v_array_3271_);
v___x_3275_ = lean_nat_dec_lt(v_idx_3272_, v___x_3274_);
if (v___x_3275_ == 0)
{
lean_object* v___x_3276_; 
lean_dec_ref(v_array_3271_);
lean_del_object(v___x_3247_);
lean_dec_ref(v_config_3208_);
v___x_3276_ = lean_box(0);
v___y_3259_ = v_res_3273_;
v_idx_3260_ = v_idx_3272_;
v_pos_3261_ = v_pos_3270_;
v_err_3262_ = v___x_3276_;
goto v___jp_3258_;
}
else
{
uint8_t v___x_3277_; uint8_t v_got_3278_; uint8_t v___x_3279_; 
v___x_3277_ = 35;
v_got_3278_ = lean_byte_array_fget(v_array_3271_, v_idx_3272_);
v___x_3279_ = lean_uint8_dec_eq(v_got_3278_, v___x_3277_);
if (v___x_3279_ == 0)
{
lean_object* v___x_3280_; 
lean_dec_ref(v_array_3271_);
lean_del_object(v___x_3247_);
lean_dec_ref(v_config_3208_);
v___x_3280_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v___y_3259_ = v_res_3273_;
v_idx_3260_ = v_idx_3272_;
v_pos_3261_ = v_pos_3270_;
v_err_3262_ = v___x_3280_;
goto v___jp_3258_;
}
else
{
lean_object* v___x_3281_; lean_object* v___x_3283_; 
lean_dec_ref(v_pos_3270_);
v___x_3281_ = lean_nat_add(v_idx_3272_, v___x_3234_);
if (v_isShared_3248_ == 0)
{
lean_ctor_set(v___x_3247_, 1, v___x_3281_);
lean_ctor_set(v___x_3247_, 0, v_array_3271_);
v___x_3283_ = v___x_3247_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_array_3271_);
lean_ctor_set(v_reuseFailAlloc_3290_, 1, v___x_3281_);
v___x_3283_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
lean_object* v___x_3284_; 
v___x_3284_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3208_, v___x_3283_);
lean_dec_ref(v_config_3208_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_pos_3285_; lean_object* v_res_3286_; lean_object* v___x_3287_; 
lean_dec(v_idx_3272_);
lean_del_object(v___x_3214_);
lean_dec_ref(v_a_3209_);
v_pos_3285_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_pos_3285_);
v_res_3286_ = lean_ctor_get(v___x_3284_, 1);
lean_inc(v_res_3286_);
lean_dec_ref_known(v___x_3284_, 2);
v___x_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3287_, 0, v_res_3286_);
v___y_3250_ = v_res_3273_;
v_pos_3251_ = v_pos_3285_;
v_res_3252_ = v___x_3287_;
goto v___jp_3249_;
}
else
{
lean_object* v_pos_3288_; lean_object* v_err_3289_; 
v_pos_3288_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_pos_3288_);
v_err_3289_ = lean_ctor_get(v___x_3284_, 1);
lean_inc(v_err_3289_);
lean_dec_ref_known(v___x_3284_, 2);
v___y_3259_ = v_res_3273_;
v_idx_3260_ = v_idx_3272_;
v_pos_3261_ = v_pos_3288_;
v_err_3262_ = v_err_3289_;
goto v___jp_3258_;
}
}
}
}
}
v___jp_3293_:
{
uint8_t v___x_3298_; 
v___x_3298_ = lean_nat_dec_eq(v_idx_3292_, v_idx_3296_);
lean_dec(v_idx_3292_);
if (v___x_3298_ == 0)
{
lean_object* v___x_3299_; 
lean_dec(v_idx_3296_);
lean_dec_ref(v_array_3295_);
lean_dec_ref(v_pos_3294_);
lean_del_object(v___x_3247_);
lean_dec(v_snd_3245_);
lean_dec(v_fst_3244_);
lean_del_object(v___x_3242_);
lean_del_object(v___x_3214_);
lean_dec(v_res_3212_);
lean_dec_ref(v_config_3208_);
v___x_3299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3299_, 0, v_a_3209_);
lean_ctor_set(v___x_3299_, 1, v_err_3297_);
return v___x_3299_;
}
else
{
lean_object* v___x_3300_; 
lean_dec(v_err_3297_);
v___x_3300_ = lean_box(0);
v_pos_3270_ = v_pos_3294_;
v_array_3271_ = v_array_3295_;
v_idx_3272_ = v_idx_3296_;
v_res_3273_ = v___x_3300_;
goto v___jp_3269_;
}
}
}
}
}
else
{
lean_object* v_err_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
lean_del_object(v___x_3214_);
lean_dec(v_res_3212_);
lean_dec_ref(v_config_3208_);
v_err_3330_ = lean_ctor_get(v___x_3238_, 1);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3337_ == 0)
{
lean_object* v_unused_3338_; 
v_unused_3338_ = lean_ctor_get(v___x_3238_, 0);
lean_dec(v_unused_3338_);
v___x_3332_ = v___x_3238_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_err_3330_);
lean_dec(v___x_3238_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3335_; 
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 0, v_a_3209_);
v___x_3335_ = v___x_3332_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_a_3209_);
lean_ctor_set(v_reuseFailAlloc_3336_, 1, v_err_3330_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
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
lean_object* v_err_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3349_; 
lean_dec_ref(v_config_3208_);
v_err_3342_ = lean_ctor_get(v___x_3210_, 1);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3349_ == 0)
{
lean_object* v_unused_3350_; 
v_unused_3350_ = lean_ctor_get(v___x_3210_, 0);
lean_dec(v_unused_3350_);
v___x_3344_ = v___x_3210_;
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_err_3342_);
lean_dec(v___x_3210_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3347_; 
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 0, v_a_3209_);
v___x_3347_ = v___x_3344_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_a_3209_);
lean_ctor_set(v_reuseFailAlloc_3348_, 1, v_err_3342_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withAuthority(lean_object* v_config_3351_, lean_object* v_a_3352_){
_start:
{
lean_object* v_utf8_3353_; lean_object* v___x_3354_; 
v_utf8_3353_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1);
lean_inc_ref(v_a_3352_);
v___x_3354_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_3353_, v_a_3352_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v_pos_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3473_; 
v_pos_3355_ = lean_ctor_get(v___x_3354_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3354_);
if (v_isSharedCheck_3473_ == 0)
{
lean_object* v_unused_3474_; 
v_unused_3474_ = lean_ctor_get(v___x_3354_, 1);
lean_dec(v_unused_3474_);
v___x_3357_ = v___x_3354_;
v_isShared_3358_ = v_isSharedCheck_3473_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_pos_3355_);
lean_dec(v___x_3354_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3473_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3359_; 
v___x_3359_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_3351_, v_pos_3355_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_pos_3360_; lean_object* v_res_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3463_; 
v_pos_3360_ = lean_ctor_get(v___x_3359_, 0);
v_res_3361_ = lean_ctor_get(v___x_3359_, 1);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3363_ = v___x_3359_;
v_isShared_3364_ = v_isSharedCheck_3463_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_res_3361_);
lean_inc(v_pos_3360_);
lean_dec(v___x_3359_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3463_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
uint8_t v___x_3365_; lean_object* v___x_3366_; 
v___x_3365_ = 1;
lean_inc_ref(v_config_3351_);
v___x_3366_ = l_Std_Http_URI_Parser_parsePath(v_config_3351_, v___x_3365_, v___x_3365_, v_pos_3360_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_pos_3367_; lean_object* v_res_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3453_; 
v_pos_3367_ = lean_ctor_get(v___x_3366_, 0);
v_res_3368_ = lean_ctor_get(v___x_3366_, 1);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3370_ = v___x_3366_;
v_isShared_3371_ = v_isSharedCheck_3453_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_res_3368_);
lean_inc(v_pos_3367_);
lean_dec(v___x_3366_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3453_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___y_3373_; lean_object* v_pos_3374_; lean_object* v_res_3375_; lean_object* v___y_3382_; lean_object* v_idx_3383_; lean_object* v_pos_3384_; lean_object* v_err_3385_; lean_object* v_pos_3393_; lean_object* v_array_3394_; lean_object* v_idx_3395_; lean_object* v_res_3396_; lean_object* v_array_3413_; lean_object* v_idx_3414_; lean_object* v_pos_3416_; lean_object* v_array_3417_; lean_object* v_idx_3418_; lean_object* v_err_3419_; lean_object* v___x_3425_; uint8_t v___x_3426_; 
v_array_3413_ = lean_ctor_get(v_pos_3367_, 0);
lean_inc_ref(v_array_3413_);
v_idx_3414_ = lean_ctor_get(v_pos_3367_, 1);
lean_inc(v_idx_3414_);
v___x_3425_ = lean_byte_array_size(v_array_3413_);
v___x_3426_ = lean_nat_dec_lt(v_idx_3414_, v___x_3425_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; 
v___x_3427_ = lean_box(0);
lean_inc(v_idx_3414_);
v_pos_3416_ = v_pos_3367_;
v_array_3417_ = v_array_3413_;
v_idx_3418_ = v_idx_3414_;
v_err_3419_ = v___x_3427_;
goto v___jp_3415_;
}
else
{
uint8_t v___x_3428_; uint8_t v_got_3429_; uint8_t v___x_3430_; 
v___x_3428_ = 63;
v_got_3429_ = lean_byte_array_fget(v_array_3413_, v_idx_3414_);
v___x_3430_ = lean_uint8_dec_eq(v_got_3429_, v___x_3428_);
if (v___x_3430_ == 0)
{
lean_object* v___x_3431_; 
v___x_3431_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_3414_);
v_pos_3416_ = v_pos_3367_;
v_array_3417_ = v_array_3413_;
v_idx_3418_ = v_idx_3414_;
v_err_3419_ = v___x_3431_;
goto v___jp_3415_;
}
else
{
lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3450_; 
v_isSharedCheck_3450_ = !lean_is_exclusive(v_pos_3367_);
if (v_isSharedCheck_3450_ == 0)
{
lean_object* v_unused_3451_; lean_object* v_unused_3452_; 
v_unused_3451_ = lean_ctor_get(v_pos_3367_, 1);
lean_dec(v_unused_3451_);
v_unused_3452_ = lean_ctor_get(v_pos_3367_, 0);
lean_dec(v_unused_3452_);
v___x_3433_ = v_pos_3367_;
v_isShared_3434_ = v_isSharedCheck_3450_;
goto v_resetjp_3432_;
}
else
{
lean_dec(v_pos_3367_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3450_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3438_; 
v___x_3435_ = lean_unsigned_to_nat(1u);
v___x_3436_ = lean_nat_add(v_idx_3414_, v___x_3435_);
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 1, v___x_3436_);
v___x_3438_ = v___x_3433_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_array_3413_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v___x_3436_);
v___x_3438_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
lean_object* v___x_3439_; 
lean_inc_ref(v_config_3351_);
v___x_3439_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3351_, v___x_3438_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_pos_3440_; lean_object* v_res_3441_; lean_object* v_array_3442_; lean_object* v_idx_3443_; lean_object* v___x_3444_; 
lean_dec(v_idx_3414_);
lean_del_object(v___x_3357_);
v_pos_3440_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_pos_3440_);
v_res_3441_ = lean_ctor_get(v___x_3439_, 1);
lean_inc(v_res_3441_);
lean_dec_ref_known(v___x_3439_, 2);
v_array_3442_ = lean_ctor_get(v_pos_3440_, 0);
lean_inc_ref(v_array_3442_);
v_idx_3443_ = lean_ctor_get(v_pos_3440_, 1);
lean_inc(v_idx_3443_);
v___x_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3444_, 0, v_res_3441_);
v_pos_3393_ = v_pos_3440_;
v_array_3394_ = v_array_3442_;
v_idx_3395_ = v_idx_3443_;
v_res_3396_ = v___x_3444_;
goto v___jp_3392_;
}
else
{
lean_object* v_pos_3445_; lean_object* v_err_3446_; lean_object* v_array_3447_; lean_object* v_idx_3448_; 
v_pos_3445_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_pos_3445_);
v_err_3446_ = lean_ctor_get(v___x_3439_, 1);
lean_inc(v_err_3446_);
lean_dec_ref_known(v___x_3439_, 2);
v_array_3447_ = lean_ctor_get(v_pos_3445_, 0);
lean_inc_ref(v_array_3447_);
v_idx_3448_ = lean_ctor_get(v_pos_3445_, 1);
lean_inc(v_idx_3448_);
v_pos_3416_ = v_pos_3445_;
v_array_3417_ = v_array_3447_;
v_idx_3418_ = v_idx_3448_;
v_err_3419_ = v_err_3446_;
goto v___jp_3415_;
}
}
}
}
}
v___jp_3372_:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3379_; 
v___x_3376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3376_, 0, v_res_3361_);
v___x_3377_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3376_);
lean_ctor_set(v___x_3377_, 1, v_res_3368_);
lean_ctor_set(v___x_3377_, 2, v___y_3373_);
lean_ctor_set(v___x_3377_, 3, v_res_3375_);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 1, v___x_3377_);
lean_ctor_set(v___x_3370_, 0, v_pos_3374_);
v___x_3379_ = v___x_3370_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_pos_3374_);
lean_ctor_set(v_reuseFailAlloc_3380_, 1, v___x_3377_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
v___jp_3381_:
{
lean_object* v_idx_3386_; uint8_t v___x_3387_; 
v_idx_3386_ = lean_ctor_get(v_pos_3384_, 1);
v___x_3387_ = lean_nat_dec_eq(v_idx_3383_, v_idx_3386_);
lean_dec(v_idx_3383_);
if (v___x_3387_ == 0)
{
lean_object* v___x_3389_; 
lean_dec_ref(v_pos_3384_);
lean_dec(v___y_3382_);
lean_del_object(v___x_3370_);
lean_dec(v_res_3368_);
lean_dec(v_res_3361_);
if (v_isShared_3364_ == 0)
{
lean_ctor_set_tag(v___x_3363_, 1);
lean_ctor_set(v___x_3363_, 1, v_err_3385_);
lean_ctor_set(v___x_3363_, 0, v_a_3352_);
v___x_3389_ = v___x_3363_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_a_3352_);
lean_ctor_set(v_reuseFailAlloc_3390_, 1, v_err_3385_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
else
{
lean_object* v___x_3391_; 
lean_dec(v_err_3385_);
lean_del_object(v___x_3363_);
lean_dec_ref(v_a_3352_);
v___x_3391_ = lean_box(0);
v___y_3373_ = v___y_3382_;
v_pos_3374_ = v_pos_3384_;
v_res_3375_ = v___x_3391_;
goto v___jp_3372_;
}
}
v___jp_3392_:
{
lean_object* v___x_3397_; uint8_t v___x_3398_; 
v___x_3397_ = lean_byte_array_size(v_array_3394_);
v___x_3398_ = lean_nat_dec_lt(v_idx_3395_, v___x_3397_);
if (v___x_3398_ == 0)
{
lean_object* v___x_3399_; 
lean_dec_ref(v_array_3394_);
lean_dec_ref(v_config_3351_);
v___x_3399_ = lean_box(0);
v___y_3382_ = v_res_3396_;
v_idx_3383_ = v_idx_3395_;
v_pos_3384_ = v_pos_3393_;
v_err_3385_ = v___x_3399_;
goto v___jp_3381_;
}
else
{
uint8_t v___x_3400_; uint8_t v_got_3401_; uint8_t v___x_3402_; 
v___x_3400_ = 35;
v_got_3401_ = lean_byte_array_fget(v_array_3394_, v_idx_3395_);
v___x_3402_ = lean_uint8_dec_eq(v_got_3401_, v___x_3400_);
if (v___x_3402_ == 0)
{
lean_object* v___x_3403_; 
lean_dec_ref(v_array_3394_);
lean_dec_ref(v_config_3351_);
v___x_3403_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v___y_3382_ = v_res_3396_;
v_idx_3383_ = v_idx_3395_;
v_pos_3384_ = v_pos_3393_;
v_err_3385_ = v___x_3403_;
goto v___jp_3381_;
}
else
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
lean_dec_ref(v_pos_3393_);
v___x_3404_ = lean_unsigned_to_nat(1u);
v___x_3405_ = lean_nat_add(v_idx_3395_, v___x_3404_);
v___x_3406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3406_, 0, v_array_3394_);
lean_ctor_set(v___x_3406_, 1, v___x_3405_);
v___x_3407_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3351_, v___x_3406_);
lean_dec_ref(v_config_3351_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_pos_3408_; lean_object* v_res_3409_; lean_object* v___x_3410_; 
lean_dec(v_idx_3395_);
lean_del_object(v___x_3363_);
lean_dec_ref(v_a_3352_);
v_pos_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_pos_3408_);
v_res_3409_ = lean_ctor_get(v___x_3407_, 1);
lean_inc(v_res_3409_);
lean_dec_ref_known(v___x_3407_, 2);
v___x_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3410_, 0, v_res_3409_);
v___y_3373_ = v_res_3396_;
v_pos_3374_ = v_pos_3408_;
v_res_3375_ = v___x_3410_;
goto v___jp_3372_;
}
else
{
lean_object* v_pos_3411_; lean_object* v_err_3412_; 
v_pos_3411_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_pos_3411_);
v_err_3412_ = lean_ctor_get(v___x_3407_, 1);
lean_inc(v_err_3412_);
lean_dec_ref_known(v___x_3407_, 2);
v___y_3382_ = v_res_3396_;
v_idx_3383_ = v_idx_3395_;
v_pos_3384_ = v_pos_3411_;
v_err_3385_ = v_err_3412_;
goto v___jp_3381_;
}
}
}
}
v___jp_3415_:
{
uint8_t v___x_3420_; 
v___x_3420_ = lean_nat_dec_eq(v_idx_3414_, v_idx_3418_);
lean_dec(v_idx_3414_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3422_; 
lean_dec(v_idx_3418_);
lean_dec_ref(v_array_3417_);
lean_dec_ref(v_pos_3416_);
lean_del_object(v___x_3370_);
lean_dec(v_res_3368_);
lean_del_object(v___x_3363_);
lean_dec(v_res_3361_);
lean_dec_ref(v_config_3351_);
if (v_isShared_3358_ == 0)
{
lean_ctor_set_tag(v___x_3357_, 1);
lean_ctor_set(v___x_3357_, 1, v_err_3419_);
lean_ctor_set(v___x_3357_, 0, v_a_3352_);
v___x_3422_ = v___x_3357_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3352_);
lean_ctor_set(v_reuseFailAlloc_3423_, 1, v_err_3419_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
else
{
lean_object* v___x_3424_; 
lean_dec(v_err_3419_);
lean_del_object(v___x_3357_);
v___x_3424_ = lean_box(0);
v_pos_3393_ = v_pos_3416_;
v_array_3394_ = v_array_3417_;
v_idx_3395_ = v_idx_3418_;
v_res_3396_ = v___x_3424_;
goto v___jp_3392_;
}
}
}
}
else
{
lean_object* v_err_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3461_; 
lean_del_object(v___x_3363_);
lean_dec(v_res_3361_);
lean_del_object(v___x_3357_);
lean_dec_ref(v_config_3351_);
v_err_3454_ = lean_ctor_get(v___x_3366_, 1);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3461_ == 0)
{
lean_object* v_unused_3462_; 
v_unused_3462_ = lean_ctor_get(v___x_3366_, 0);
lean_dec(v_unused_3462_);
v___x_3456_ = v___x_3366_;
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_err_3454_);
lean_dec(v___x_3366_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3459_; 
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 0, v_a_3352_);
v___x_3459_ = v___x_3456_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_a_3352_);
lean_ctor_set(v_reuseFailAlloc_3460_, 1, v_err_3454_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
return v___x_3459_;
}
}
}
}
}
else
{
lean_object* v_err_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
lean_del_object(v___x_3357_);
lean_dec_ref(v_config_3351_);
v_err_3464_ = lean_ctor_get(v___x_3359_, 1);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3471_ == 0)
{
lean_object* v_unused_3472_; 
v_unused_3472_ = lean_ctor_get(v___x_3359_, 0);
lean_dec(v_unused_3472_);
v___x_3466_ = v___x_3359_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_err_3464_);
lean_dec(v___x_3359_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 0, v_a_3352_);
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3352_);
lean_ctor_set(v_reuseFailAlloc_3470_, 1, v_err_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
}
else
{
lean_object* v_err_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
lean_dec_ref(v_config_3351_);
v_err_3475_ = lean_ctor_get(v___x_3354_, 1);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3354_);
if (v_isSharedCheck_3482_ == 0)
{
lean_object* v_unused_3483_; 
v_unused_3483_ = lean_ctor_get(v___x_3354_, 0);
lean_dec(v_unused_3483_);
v___x_3477_ = v___x_3354_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_err_3475_);
lean_dec(v___x_3354_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 0, v_a_3352_);
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3352_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v_err_3475_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath(lean_object* v_config_3484_, lean_object* v_a_3485_){
_start:
{
uint8_t v___x_3486_; uint8_t v___x_3487_; lean_object* v___x_3488_; 
v___x_3486_ = 0;
v___x_3487_ = 1;
lean_inc_ref(v_config_3484_);
v___x_3488_ = l_Std_Http_URI_Parser_parsePath(v_config_3484_, v___x_3486_, v___x_3487_, v_a_3485_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_pos_3489_; lean_object* v_res_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3571_; 
v_pos_3489_ = lean_ctor_get(v___x_3488_, 0);
v_res_3490_ = lean_ctor_get(v___x_3488_, 1);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3492_ = v___x_3488_;
v_isShared_3493_ = v_isSharedCheck_3571_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_res_3490_);
lean_inc(v_pos_3489_);
lean_dec(v___x_3488_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3571_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___y_3495_; lean_object* v_pos_3496_; lean_object* v_res_3497_; lean_object* v_idx_3504_; lean_object* v___y_3505_; lean_object* v_pos_3506_; lean_object* v_err_3507_; lean_object* v_pos_3513_; lean_object* v_array_3514_; lean_object* v_idx_3515_; lean_object* v_res_3516_; lean_object* v_array_3533_; lean_object* v_idx_3534_; lean_object* v_pos_3536_; lean_object* v_array_3537_; lean_object* v_idx_3538_; lean_object* v_err_3539_; lean_object* v___x_3543_; uint8_t v___x_3544_; 
v_array_3533_ = lean_ctor_get(v_pos_3489_, 0);
lean_inc_ref(v_array_3533_);
v_idx_3534_ = lean_ctor_get(v_pos_3489_, 1);
lean_inc(v_idx_3534_);
v___x_3543_ = lean_byte_array_size(v_array_3533_);
v___x_3544_ = lean_nat_dec_lt(v_idx_3534_, v___x_3543_);
if (v___x_3544_ == 0)
{
lean_object* v___x_3545_; 
v___x_3545_ = lean_box(0);
lean_inc(v_idx_3534_);
v_pos_3536_ = v_pos_3489_;
v_array_3537_ = v_array_3533_;
v_idx_3538_ = v_idx_3534_;
v_err_3539_ = v___x_3545_;
goto v___jp_3535_;
}
else
{
uint8_t v___x_3546_; uint8_t v_got_3547_; uint8_t v___x_3548_; 
v___x_3546_ = 63;
v_got_3547_ = lean_byte_array_fget(v_array_3533_, v_idx_3534_);
v___x_3548_ = lean_uint8_dec_eq(v_got_3547_, v___x_3546_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3549_; 
v___x_3549_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__5));
lean_inc(v_idx_3534_);
v_pos_3536_ = v_pos_3489_;
v_array_3537_ = v_array_3533_;
v_idx_3538_ = v_idx_3534_;
v_err_3539_ = v___x_3549_;
goto v___jp_3535_;
}
else
{
lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3568_; 
v_isSharedCheck_3568_ = !lean_is_exclusive(v_pos_3489_);
if (v_isSharedCheck_3568_ == 0)
{
lean_object* v_unused_3569_; lean_object* v_unused_3570_; 
v_unused_3569_ = lean_ctor_get(v_pos_3489_, 1);
lean_dec(v_unused_3569_);
v_unused_3570_ = lean_ctor_get(v_pos_3489_, 0);
lean_dec(v_unused_3570_);
v___x_3551_ = v_pos_3489_;
v_isShared_3552_ = v_isSharedCheck_3568_;
goto v_resetjp_3550_;
}
else
{
lean_dec(v_pos_3489_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3568_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3556_; 
v___x_3553_ = lean_unsigned_to_nat(1u);
v___x_3554_ = lean_nat_add(v_idx_3534_, v___x_3553_);
if (v_isShared_3552_ == 0)
{
lean_ctor_set(v___x_3551_, 1, v___x_3554_);
v___x_3556_ = v___x_3551_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_array_3533_);
lean_ctor_set(v_reuseFailAlloc_3567_, 1, v___x_3554_);
v___x_3556_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
lean_object* v___x_3557_; 
lean_inc_ref(v_config_3484_);
v___x_3557_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3484_, v___x_3556_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v_pos_3558_; lean_object* v_res_3559_; lean_object* v_array_3560_; lean_object* v_idx_3561_; lean_object* v___x_3562_; 
lean_dec(v_idx_3534_);
v_pos_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_pos_3558_);
v_res_3559_ = lean_ctor_get(v___x_3557_, 1);
lean_inc(v_res_3559_);
lean_dec_ref_known(v___x_3557_, 2);
v_array_3560_ = lean_ctor_get(v_pos_3558_, 0);
lean_inc_ref(v_array_3560_);
v_idx_3561_ = lean_ctor_get(v_pos_3558_, 1);
lean_inc(v_idx_3561_);
v___x_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3562_, 0, v_res_3559_);
v_pos_3513_ = v_pos_3558_;
v_array_3514_ = v_array_3560_;
v_idx_3515_ = v_idx_3561_;
v_res_3516_ = v___x_3562_;
goto v___jp_3512_;
}
else
{
lean_object* v_pos_3563_; lean_object* v_err_3564_; lean_object* v_array_3565_; lean_object* v_idx_3566_; 
v_pos_3563_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_pos_3563_);
v_err_3564_ = lean_ctor_get(v___x_3557_, 1);
lean_inc(v_err_3564_);
lean_dec_ref_known(v___x_3557_, 2);
v_array_3565_ = lean_ctor_get(v_pos_3563_, 0);
lean_inc_ref(v_array_3565_);
v_idx_3566_ = lean_ctor_get(v_pos_3563_, 1);
lean_inc(v_idx_3566_);
v_pos_3536_ = v_pos_3563_;
v_array_3537_ = v_array_3565_;
v_idx_3538_ = v_idx_3566_;
v_err_3539_ = v_err_3564_;
goto v___jp_3535_;
}
}
}
}
}
v___jp_3494_:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3501_; 
v___x_3498_ = lean_box(0);
v___x_3499_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3498_);
lean_ctor_set(v___x_3499_, 1, v_res_3490_);
lean_ctor_set(v___x_3499_, 2, v___y_3495_);
lean_ctor_set(v___x_3499_, 3, v_res_3497_);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 1, v___x_3499_);
lean_ctor_set(v___x_3492_, 0, v_pos_3496_);
v___x_3501_ = v___x_3492_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_pos_3496_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v___x_3499_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
v___jp_3503_:
{
lean_object* v_idx_3508_; uint8_t v___x_3509_; 
v_idx_3508_ = lean_ctor_get(v_pos_3506_, 1);
v___x_3509_ = lean_nat_dec_eq(v_idx_3504_, v_idx_3508_);
lean_dec(v_idx_3504_);
if (v___x_3509_ == 0)
{
lean_object* v___x_3510_; 
lean_dec(v___y_3505_);
lean_del_object(v___x_3492_);
lean_dec(v_res_3490_);
v___x_3510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3510_, 0, v_pos_3506_);
lean_ctor_set(v___x_3510_, 1, v_err_3507_);
return v___x_3510_;
}
else
{
lean_object* v___x_3511_; 
lean_dec(v_err_3507_);
v___x_3511_ = lean_box(0);
v___y_3495_ = v___y_3505_;
v_pos_3496_ = v_pos_3506_;
v_res_3497_ = v___x_3511_;
goto v___jp_3494_;
}
}
v___jp_3512_:
{
lean_object* v___x_3517_; uint8_t v___x_3518_; 
v___x_3517_ = lean_byte_array_size(v_array_3514_);
v___x_3518_ = lean_nat_dec_lt(v_idx_3515_, v___x_3517_);
if (v___x_3518_ == 0)
{
lean_object* v___x_3519_; 
lean_dec_ref(v_array_3514_);
lean_dec_ref(v_config_3484_);
v___x_3519_ = lean_box(0);
v_idx_3504_ = v_idx_3515_;
v___y_3505_ = v_res_3516_;
v_pos_3506_ = v_pos_3513_;
v_err_3507_ = v___x_3519_;
goto v___jp_3503_;
}
else
{
uint8_t v___x_3520_; uint8_t v_got_3521_; uint8_t v___x_3522_; 
v___x_3520_ = 35;
v_got_3521_ = lean_byte_array_fget(v_array_3514_, v_idx_3515_);
v___x_3522_ = lean_uint8_dec_eq(v_got_3521_, v___x_3520_);
if (v___x_3522_ == 0)
{
lean_object* v___x_3523_; 
lean_dec_ref(v_array_3514_);
lean_dec_ref(v_config_3484_);
v___x_3523_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v_idx_3504_ = v_idx_3515_;
v___y_3505_ = v_res_3516_;
v_pos_3506_ = v_pos_3513_;
v_err_3507_ = v___x_3523_;
goto v___jp_3503_;
}
else
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
lean_dec_ref(v_pos_3513_);
v___x_3524_ = lean_unsigned_to_nat(1u);
v___x_3525_ = lean_nat_add(v_idx_3515_, v___x_3524_);
v___x_3526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3526_, 0, v_array_3514_);
lean_ctor_set(v___x_3526_, 1, v___x_3525_);
v___x_3527_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3484_, v___x_3526_);
lean_dec_ref(v_config_3484_);
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v_pos_3528_; lean_object* v_res_3529_; lean_object* v___x_3530_; 
lean_dec(v_idx_3515_);
v_pos_3528_ = lean_ctor_get(v___x_3527_, 0);
lean_inc(v_pos_3528_);
v_res_3529_ = lean_ctor_get(v___x_3527_, 1);
lean_inc(v_res_3529_);
lean_dec_ref_known(v___x_3527_, 2);
v___x_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3530_, 0, v_res_3529_);
v___y_3495_ = v_res_3516_;
v_pos_3496_ = v_pos_3528_;
v_res_3497_ = v___x_3530_;
goto v___jp_3494_;
}
else
{
lean_object* v_pos_3531_; lean_object* v_err_3532_; 
v_pos_3531_ = lean_ctor_get(v___x_3527_, 0);
lean_inc(v_pos_3531_);
v_err_3532_ = lean_ctor_get(v___x_3527_, 1);
lean_inc(v_err_3532_);
lean_dec_ref_known(v___x_3527_, 2);
v_idx_3504_ = v_idx_3515_;
v___y_3505_ = v_res_3516_;
v_pos_3506_ = v_pos_3531_;
v_err_3507_ = v_err_3532_;
goto v___jp_3503_;
}
}
}
}
v___jp_3535_:
{
uint8_t v___x_3540_; 
v___x_3540_ = lean_nat_dec_eq(v_idx_3534_, v_idx_3538_);
lean_dec(v_idx_3534_);
if (v___x_3540_ == 0)
{
lean_object* v___x_3541_; 
lean_dec(v_idx_3538_);
lean_dec_ref(v_array_3537_);
lean_del_object(v___x_3492_);
lean_dec(v_res_3490_);
lean_dec_ref(v_config_3484_);
v___x_3541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3541_, 0, v_pos_3536_);
lean_ctor_set(v___x_3541_, 1, v_err_3539_);
return v___x_3541_;
}
else
{
lean_object* v___x_3542_; 
lean_dec(v_err_3539_);
v___x_3542_ = lean_box(0);
v_pos_3513_ = v_pos_3536_;
v_array_3514_ = v_array_3537_;
v_idx_3515_ = v_idx_3538_;
v_res_3516_ = v___x_3542_;
goto v___jp_3512_;
}
}
}
}
else
{
lean_object* v_pos_3572_; lean_object* v_err_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3580_; 
lean_dec_ref(v_config_3484_);
v_pos_3572_ = lean_ctor_get(v___x_3488_, 0);
v_err_3573_ = lean_ctor_get(v___x_3488_, 1);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3575_ = v___x_3488_;
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_err_3573_);
lean_inc(v_pos_3572_);
lean_dec(v___x_3488_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3578_; 
if (v_isShared_3576_ == 0)
{
v___x_3578_ = v___x_3575_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_pos_3572_);
lean_ctor_set(v_reuseFailAlloc_3579_, 1, v_err_3573_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_relative(lean_object* v_config_3581_, lean_object* v_a_3582_){
_start:
{
lean_object* v_pos_3584_; lean_object* v_res_3585_; lean_object* v___x_3588_; 
lean_inc_ref(v_a_3582_);
lean_inc_ref(v_config_3581_);
v___x_3588_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withAuthority(v_config_3581_, v_a_3582_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v_pos_3589_; lean_object* v_res_3590_; 
lean_dec_ref(v_a_3582_);
lean_dec_ref(v_config_3581_);
v_pos_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_pos_3589_);
v_res_3590_ = lean_ctor_get(v___x_3588_, 1);
lean_inc(v_res_3590_);
lean_dec_ref_known(v___x_3588_, 2);
v_pos_3584_ = v_pos_3589_;
v_res_3585_ = v_res_3590_;
goto v___jp_3583_;
}
else
{
lean_object* v_pos_3591_; lean_object* v_err_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3614_; 
v_pos_3591_ = lean_ctor_get(v___x_3588_, 0);
v_err_3592_ = lean_ctor_get(v___x_3588_, 1);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3594_ = v___x_3588_;
v_isShared_3595_ = v_isSharedCheck_3614_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_err_3592_);
lean_inc(v_pos_3591_);
lean_dec(v___x_3588_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3614_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v_idx_3596_; lean_object* v_idx_3597_; uint8_t v___x_3598_; 
v_idx_3596_ = lean_ctor_get(v_a_3582_, 1);
lean_inc(v_idx_3596_);
lean_dec_ref(v_a_3582_);
v_idx_3597_ = lean_ctor_get(v_pos_3591_, 1);
v___x_3598_ = lean_nat_dec_eq(v_idx_3596_, v_idx_3597_);
lean_dec(v_idx_3596_);
if (v___x_3598_ == 0)
{
lean_object* v___x_3600_; 
lean_dec_ref(v_config_3581_);
if (v_isShared_3595_ == 0)
{
v___x_3600_ = v___x_3594_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_pos_3591_);
lean_ctor_set(v_reuseFailAlloc_3601_, 1, v_err_3592_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
else
{
lean_object* v___x_3602_; 
lean_del_object(v___x_3594_);
lean_dec(v_err_3592_);
v___x_3602_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath(v_config_3581_, v_pos_3591_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v_pos_3603_; lean_object* v_res_3604_; 
v_pos_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_pos_3603_);
v_res_3604_ = lean_ctor_get(v___x_3602_, 1);
lean_inc(v_res_3604_);
lean_dec_ref_known(v___x_3602_, 2);
v_pos_3584_ = v_pos_3603_;
v_res_3585_ = v_res_3604_;
goto v___jp_3583_;
}
else
{
lean_object* v_pos_3605_; lean_object* v_err_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3613_; 
v_pos_3605_ = lean_ctor_get(v___x_3602_, 0);
v_err_3606_ = lean_ctor_get(v___x_3602_, 1);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3608_ = v___x_3602_;
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_err_3606_);
lean_inc(v_pos_3605_);
lean_dec(v___x_3602_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
if (v_isShared_3609_ == 0)
{
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_pos_3605_);
lean_ctor_set(v_reuseFailAlloc_3612_, 1, v_err_3606_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
}
}
}
v___jp_3583_:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3586_, 0, v_res_3585_);
v___x_3587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3587_, 0, v_pos_3584_);
lean_ctor_set(v___x_3587_, 1, v___x_3586_);
return v___x_3587_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURIReference(lean_object* v_config_3615_, lean_object* v_a_3616_){
_start:
{
lean_object* v___x_3617_; 
lean_inc_ref(v_a_3616_);
lean_inc_ref(v_config_3615_);
v___x_3617_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_uri(v_config_3615_, v_a_3616_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_dec_ref(v_a_3616_);
lean_dec_ref(v_config_3615_);
return v___x_3617_;
}
else
{
lean_object* v_err_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3628_; 
v_err_3618_ = lean_ctor_get(v___x_3617_, 1);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3628_ == 0)
{
lean_object* v_unused_3629_; 
v_unused_3629_ = lean_ctor_get(v___x_3617_, 0);
lean_dec(v_unused_3629_);
v___x_3620_ = v___x_3617_;
v_isShared_3621_ = v_isSharedCheck_3628_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_err_3618_);
lean_dec(v___x_3617_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3628_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v_idx_3622_; uint8_t v___x_3623_; 
v_idx_3622_ = lean_ctor_get(v_a_3616_, 1);
v___x_3623_ = lean_nat_dec_eq(v_idx_3622_, v_idx_3622_);
if (v___x_3623_ == 0)
{
lean_object* v___x_3625_; 
lean_dec_ref(v_config_3615_);
if (v_isShared_3621_ == 0)
{
lean_ctor_set(v___x_3620_, 0, v_a_3616_);
v___x_3625_ = v___x_3620_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_a_3616_);
lean_ctor_set(v_reuseFailAlloc_3626_, 1, v_err_3618_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
else
{
lean_object* v___x_3627_; 
lean_del_object(v___x_3620_);
lean_dec(v_err_3618_);
v___x_3627_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_relative(v_config_3615_, v_a_3616_);
return v___x_3627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader(lean_object* v_config_3636_, lean_object* v_a_3637_){
_start:
{
lean_object* v___x_3638_; 
v___x_3638_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_3636_, v_a_3637_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v_pos_3639_; lean_object* v_res_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3709_; 
v_pos_3639_ = lean_ctor_get(v___x_3638_, 0);
v_res_3640_ = lean_ctor_get(v___x_3638_, 1);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3642_ = v___x_3638_;
v_isShared_3643_ = v_isSharedCheck_3709_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_res_3640_);
lean_inc(v_pos_3639_);
lean_dec(v___x_3638_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3709_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v_port_3645_; lean_object* v___y_3646_; lean_object* v_pos_3660_; lean_object* v_pos_3663_; lean_object* v_array_3664_; lean_object* v_idx_3665_; lean_object* v_array_3671_; lean_object* v_idx_3672_; lean_object* v___x_3673_; uint8_t v___x_3674_; 
v_array_3671_ = lean_ctor_get(v_pos_3639_, 0);
v_idx_3672_ = lean_ctor_get(v_pos_3639_, 1);
v___x_3673_ = lean_byte_array_size(v_array_3671_);
v___x_3674_ = lean_nat_dec_lt(v_idx_3672_, v___x_3673_);
if (v___x_3674_ == 0)
{
v_pos_3660_ = v_pos_3639_;
goto v___jp_3659_;
}
else
{
uint8_t v___x_3675_; uint8_t v___x_3676_; uint8_t v___x_3677_; 
v___x_3675_ = lean_byte_array_fget(v_array_3671_, v_idx_3672_);
v___x_3676_ = 58;
v___x_3677_ = lean_uint8_dec_eq(v___x_3675_, v___x_3676_);
if (v___x_3677_ == 0)
{
v_pos_3660_ = v_pos_3639_;
goto v___jp_3659_;
}
else
{
lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3706_; 
lean_inc(v_idx_3672_);
lean_inc_ref(v_array_3671_);
v_isSharedCheck_3706_ = !lean_is_exclusive(v_pos_3639_);
if (v_isSharedCheck_3706_ == 0)
{
lean_object* v_unused_3707_; lean_object* v_unused_3708_; 
v_unused_3707_ = lean_ctor_get(v_pos_3639_, 1);
lean_dec(v_unused_3707_);
v_unused_3708_ = lean_ctor_get(v_pos_3639_, 0);
lean_dec(v_unused_3708_);
v___x_3679_ = v_pos_3639_;
v_isShared_3680_ = v_isSharedCheck_3706_;
goto v_resetjp_3678_;
}
else
{
lean_dec(v_pos_3639_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3706_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3684_; 
v___x_3681_ = lean_unsigned_to_nat(1u);
v___x_3682_ = lean_nat_add(v_idx_3672_, v___x_3681_);
lean_dec(v_idx_3672_);
lean_inc(v___x_3682_);
lean_inc_ref(v_array_3671_);
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
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_array_3671_);
lean_ctor_set(v_reuseFailAlloc_3705_, 1, v___x_3682_);
v___x_3684_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
uint8_t v___x_3685_; 
v___x_3685_ = lean_nat_dec_lt(v___x_3682_, v___x_3673_);
if (v___x_3685_ == 0)
{
v_pos_3663_ = v___x_3684_;
v_array_3664_ = v_array_3671_;
v_idx_3665_ = v___x_3682_;
goto v___jp_3662_;
}
else
{
uint8_t v___x_3686_; uint8_t v___x_3687_; uint8_t v___x_3688_; 
v___x_3686_ = lean_byte_array_fget(v_array_3671_, v___x_3682_);
v___x_3687_ = 48;
v___x_3688_ = lean_uint8_dec_le(v___x_3687_, v___x_3686_);
if (v___x_3688_ == 0)
{
v_pos_3663_ = v___x_3684_;
v_array_3664_ = v_array_3671_;
v_idx_3665_ = v___x_3682_;
goto v___jp_3662_;
}
else
{
uint8_t v___x_3689_; uint8_t v___x_3690_; 
v___x_3689_ = 57;
v___x_3690_ = lean_uint8_dec_le(v___x_3686_, v___x_3689_);
if (v___x_3690_ == 0)
{
v_pos_3663_ = v___x_3684_;
v_array_3664_ = v_array_3671_;
v_idx_3665_ = v___x_3682_;
goto v___jp_3662_;
}
else
{
lean_object* v___x_3691_; 
lean_dec(v___x_3682_);
lean_dec_ref(v_array_3671_);
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
v_port_3645_ = v___x_3694_;
v___y_3646_ = v_pos_3692_;
goto v___jp_3644_;
}
else
{
lean_object* v_pos_3696_; lean_object* v_err_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3704_; 
lean_del_object(v___x_3642_);
lean_dec(v_res_3640_);
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
v___jp_3644_:
{
lean_object* v_array_3647_; lean_object* v_idx_3648_; lean_object* v___x_3649_; uint8_t v___x_3650_; 
v_array_3647_ = lean_ctor_get(v___y_3646_, 0);
v_idx_3648_ = lean_ctor_get(v___y_3646_, 1);
v___x_3649_ = lean_byte_array_size(v_array_3647_);
v___x_3650_ = lean_nat_dec_lt(v_idx_3648_, v___x_3649_);
if (v___x_3650_ == 0)
{
lean_object* v___x_3651_; lean_object* v___x_3653_; 
v___x_3651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3651_, 0, v_res_3640_);
lean_ctor_set(v___x_3651_, 1, v_port_3645_);
if (v_isShared_3643_ == 0)
{
lean_ctor_set(v___x_3642_, 1, v___x_3651_);
lean_ctor_set(v___x_3642_, 0, v___y_3646_);
v___x_3653_ = v___x_3642_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v___y_3646_);
lean_ctor_set(v_reuseFailAlloc_3654_, 1, v___x_3651_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
else
{
lean_object* v___x_3655_; lean_object* v___x_3657_; 
lean_dec(v_port_3645_);
lean_dec(v_res_3640_);
v___x_3655_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__1));
if (v_isShared_3643_ == 0)
{
lean_ctor_set_tag(v___x_3642_, 1);
lean_ctor_set(v___x_3642_, 1, v___x_3655_);
lean_ctor_set(v___x_3642_, 0, v___y_3646_);
v___x_3657_ = v___x_3642_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v___y_3646_);
lean_ctor_set(v_reuseFailAlloc_3658_, 1, v___x_3655_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
}
v___jp_3659_:
{
lean_object* v___x_3661_; 
v___x_3661_ = lean_box(0);
v_port_3645_ = v___x_3661_;
v___y_3646_ = v_pos_3660_;
goto v___jp_3644_;
}
v___jp_3662_:
{
lean_object* v___x_3666_; uint8_t v___x_3667_; 
v___x_3666_ = lean_byte_array_size(v_array_3664_);
lean_dec_ref(v_array_3664_);
v___x_3667_ = lean_nat_dec_lt(v_idx_3665_, v___x_3666_);
lean_dec(v_idx_3665_);
if (v___x_3667_ == 0)
{
lean_object* v___x_3668_; 
v___x_3668_ = lean_box(1);
v_port_3645_ = v___x_3668_;
v___y_3646_ = v_pos_3663_;
goto v___jp_3644_;
}
else
{
lean_object* v___x_3669_; lean_object* v___x_3670_; 
lean_del_object(v___x_3642_);
lean_dec(v_res_3640_);
v___x_3669_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__3));
v___x_3670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3670_, 0, v_pos_3663_);
lean_ctor_set(v___x_3670_, 1, v___x_3669_);
return v___x_3670_;
}
}
}
}
else
{
lean_object* v_pos_3710_; lean_object* v_err_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
v_pos_3710_ = lean_ctor_get(v___x_3638_, 0);
v_err_3711_ = lean_ctor_get(v___x_3638_, 1);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___x_3638_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_err_3711_);
lean_inc(v_pos_3710_);
lean_dec(v___x_3638_);
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
