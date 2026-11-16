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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
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
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Http_URI_isValidDomainLabel(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Http_URI_endsInNumber(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* lean_uv_pton_v4(lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x3f(lean_object*, lean_object*);
lean_object* l_Std_Http_URI_EncodedString_decode___redArg(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_uv_pton_v6(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_ByteArray_Iterator_remainingBytes(lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_byte_array_uget(lean_object*, size_t);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
lean_object* lean_uint8_to_nat(uint8_t);
size_t lean_usize_add(size_t, size_t);
uint8_t l_ByteArray_isEmpty(lean_object*);
lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Std_Http_URI_Query_empty;
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f(lean_object*);
lean_object* l_Std_Http_URI_Query_insertEncoded(lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(lean_object*);
lean_object* l_Std_Http_URI_EncodedString_decodeLossy___redArg(lean_object*);
uint8_t l_Std_Http_Internal_instDecidableIsLowerCase(lean_object*);
lean_object* l_String_toListImpl(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_List_head_x3f___redArg(lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber_spec__1(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__0_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "port number too large: "};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__1 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__1_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "port number too large"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__2 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__2_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__2_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__3 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__3_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "expected a port number"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__4 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__4_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__4_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__5 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__5_value;
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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___boxed(lean_object*);
static const lean_string_object l_String_dropSuffix_x3f___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_String_dropSuffix_x3f___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__3___redArg___closed__0 = (const lean_object*)&l_String_dropSuffix_x3f___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__1(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__4___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "invalid host"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "invalid domain name: "};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "host too long (limit: "};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " bytes)"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__4 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__4_value;
static const lean_closure_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__5 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__5_value;
static const lean_closure_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__6 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__6_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "invalid percent encoding in path segment"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3_value)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4_value;
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
static const lean_string_object l_Std_Http_URI_Parser_parseURI___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '63'"};
static const lean_object* l_Std_Http_URI_Parser_parseURI___closed__2 = (const lean_object*)&l_Std_Http_URI_Parser_parseURI___closed__2_value;
static const lean_ctor_object l_Std_Http_URI_Parser_parseURI___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_URI_Parser_parseURI___closed__2_value)}};
static const lean_object* l_Std_Http_URI_Parser_parseURI___closed__3 = (const lean_object*)&l_Std_Http_URI_Parser_parseURI___closed__3_value;
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
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_requireHttpHost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "empty host in an http(s) URI"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_requireHttpHost___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_requireHttpHost___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_requireHttpHost___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_requireHttpHost___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_requireHttpHost___closed__1 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_requireHttpHost___closed__1_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_requireHttpHost___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "http"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_requireHttpHost___closed__2 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_requireHttpHost___closed__2_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_requireHttpHost___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "https"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_requireHttpHost___closed__3 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_requireHttpHost___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_requireHttpHost(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_requireHttpHost___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "not http absolute uri with path"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "not http absolute uri"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_uri(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withAuthority(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "the first segment of a relative path cannot contain ':'"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath___closed__1 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath(lean_object*, lean_object*);
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
uint8_t v___y_1152__boxed_308_; uint8_t v_res_309_; lean_object* v_r_310_; 
v___y_1152__boxed_308_ = lean_unbox(v___y_307_);
v_res_309_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0(v___y_1152__boxed_308_);
v_r_310_ = lean_box(v_res_309_);
return v_r_310_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber_spec__1(uint8_t v___x_311_, lean_object* v_a_312_, lean_object* v_i_313_){
_start:
{
lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_314_ = lean_byte_array_size(v_a_312_);
v___x_315_ = lean_nat_dec_lt(v_i_313_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; 
lean_dec(v_i_313_);
v___x_316_ = lean_box(0);
return v___x_316_;
}
else
{
uint8_t v___x_317_; uint8_t v___x_318_; uint8_t v___x_319_; 
v___x_317_ = lean_byte_array_fget(v_a_312_, v_i_313_);
v___x_318_ = 48;
v___x_319_ = lean_uint8_dec_eq(v___x_317_, v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; 
v___x_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_320_, 0, v_i_313_);
return v___x_320_;
}
else
{
if (v___x_311_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_unsigned_to_nat(1u);
v___x_322_ = lean_nat_add(v_i_313_, v___x_321_);
lean_dec(v_i_313_);
v_i_313_ = v___x_322_;
goto _start;
}
else
{
lean_object* v___x_324_; 
v___x_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_324_, 0, v_i_313_);
return v___x_324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber_spec__1___boxed(lean_object* v___x_325_, lean_object* v_a_326_, lean_object* v_i_327_){
_start:
{
uint8_t v___x_1163__boxed_328_; lean_object* v_res_329_; 
v___x_1163__boxed_328_ = lean_unbox(v___x_325_);
v_res_329_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber_spec__1(v___x_1163__boxed_328_, v_a_326_, v_i_327_);
lean_dec_ref(v_a_326_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber_spec__0(lean_object* v_as_330_, size_t v_i_331_, size_t v_stop_332_, lean_object* v_b_333_){
_start:
{
uint8_t v___x_334_; 
v___x_334_ = lean_usize_dec_eq(v_i_331_, v_stop_332_);
if (v___x_334_ == 0)
{
uint8_t v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; uint8_t v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; size_t v___x_342_; size_t v___x_343_; 
v___x_335_ = lean_byte_array_uget(v_as_330_, v_i_331_);
v___x_336_ = lean_unsigned_to_nat(10u);
v___x_337_ = lean_nat_mul(v_b_333_, v___x_336_);
lean_dec(v_b_333_);
v___x_338_ = 48;
v___x_339_ = lean_uint8_sub(v___x_335_, v___x_338_);
v___x_340_ = lean_uint8_to_nat(v___x_339_);
v___x_341_ = lean_nat_add(v___x_337_, v___x_340_);
lean_dec(v___x_337_);
v___x_342_ = ((size_t)1ULL);
v___x_343_ = lean_usize_add(v_i_331_, v___x_342_);
v_i_331_ = v___x_343_;
v_b_333_ = v___x_341_;
goto _start;
}
else
{
return v_b_333_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber_spec__0___boxed(lean_object* v_as_345_, lean_object* v_i_346_, lean_object* v_stop_347_, lean_object* v_b_348_){
_start:
{
size_t v_i_boxed_349_; size_t v_stop_boxed_350_; lean_object* v_res_351_; 
v_i_boxed_349_ = lean_unbox_usize(v_i_346_);
lean_dec(v_i_346_);
v_stop_boxed_350_ = lean_unbox_usize(v_stop_347_);
lean_dec(v_stop_347_);
v_res_351_ = l_ByteArray_foldlMUnsafe_fold___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber_spec__0(v_as_345_, v_i_boxed_349_, v_stop_boxed_350_, v_b_348_);
lean_dec_ref(v_as_345_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(lean_object* v_a_360_){
_start:
{
lean_object* v___f_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v_snd_365_; lean_object* v_fst_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_432_; 
v___f_361_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__0));
v___x_362_ = l_ByteArray_Iterator_remainingBytes(v_a_360_);
v___x_363_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_360_);
v___x_364_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_361_, v___x_362_, v___x_363_, v_a_360_);
lean_dec(v___x_362_);
v_snd_365_ = lean_ctor_get(v___x_364_, 1);
v_fst_366_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_432_ == 0)
{
v___x_368_ = v___x_364_;
v_isShared_369_ = v_isSharedCheck_432_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_snd_365_);
lean_inc(v_fst_366_);
lean_dec(v___x_364_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_432_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v_fst_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_430_; 
v_fst_370_ = lean_ctor_get(v_snd_365_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v_snd_365_);
if (v_isSharedCheck_430_ == 0)
{
lean_object* v_unused_431_; 
v_unused_431_ = lean_ctor_get(v_snd_365_, 1);
lean_dec(v_unused_431_);
v___x_372_ = v_snd_365_;
v_isShared_373_ = v_isSharedCheck_430_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_fst_370_);
lean_dec(v_snd_365_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_430_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___y_375_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v_array_405_; lean_object* v_idx_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_429_; 
v_array_405_ = lean_ctor_get(v_a_360_, 0);
v_idx_406_ = lean_ctor_get(v_a_360_, 1);
v_isSharedCheck_429_ = !lean_is_exclusive(v_a_360_);
if (v_isSharedCheck_429_ == 0)
{
v___x_408_ = v_a_360_;
v_isShared_409_ = v_isSharedCheck_429_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_idx_406_);
lean_inc(v_array_405_);
lean_dec(v_a_360_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_429_;
goto v_resetjp_407_;
}
v___jp_374_:
{
lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_376_ = lean_unsigned_to_nat(65535u);
v___x_377_ = lean_nat_dec_lt(v___x_376_, v___y_375_);
if (v___x_377_ == 0)
{
uint16_t v___x_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_378_ = lean_uint16_of_nat(v___y_375_);
lean_dec(v___y_375_);
v___x_379_ = lean_box(v___x_378_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 1, v___x_379_);
v___x_381_ = v___x_372_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_fst_370_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
else
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_383_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__1));
v___x_384_ = l_Nat_reprFast(v___y_375_);
v___x_385_ = lean_string_append(v___x_383_, v___x_384_);
lean_dec_ref(v___x_384_);
v___x_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
if (v_isShared_373_ == 0)
{
lean_ctor_set_tag(v___x_372_, 1);
lean_ctor_set(v___x_372_, 1, v___x_386_);
v___x_388_ = v___x_372_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_fst_370_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
v___jp_390_:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_393_ = lean_unsigned_to_nat(5u);
v___x_394_ = lean_byte_array_size(v___y_391_);
v___x_395_ = lean_nat_sub(v___x_394_, v___y_392_);
v___x_396_ = lean_nat_dec_lt(v___x_393_, v___x_395_);
lean_dec(v___x_395_);
if (v___x_396_ == 0)
{
uint8_t v___x_397_; 
lean_del_object(v___x_368_);
v___x_397_ = lean_nat_dec_lt(v___y_392_, v___x_394_);
if (v___x_397_ == 0)
{
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
v___y_375_ = v___x_363_;
goto v___jp_374_;
}
else
{
size_t v___x_398_; size_t v___x_399_; lean_object* v___x_400_; 
v___x_398_ = lean_usize_of_nat(v___y_392_);
lean_dec(v___y_392_);
v___x_399_ = lean_usize_of_nat(v___x_394_);
v___x_400_ = l_ByteArray_foldlMUnsafe_fold___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber_spec__0(v___y_391_, v___x_398_, v___x_399_, v___x_363_);
lean_dec_ref(v___y_391_);
v___y_375_ = v___x_400_;
goto v___jp_374_;
}
}
else
{
lean_object* v___x_401_; lean_object* v___x_403_; 
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_del_object(v___x_372_);
v___x_401_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__3));
if (v_isShared_369_ == 0)
{
lean_ctor_set_tag(v___x_368_, 1);
lean_ctor_set(v___x_368_, 1, v___x_401_);
lean_ctor_set(v___x_368_, 0, v_fst_370_);
v___x_403_ = v___x_368_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_fst_370_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v___x_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
v_resetjp_407_:
{
lean_object* v_lower_411_; lean_object* v_upper_412_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___y_426_; uint8_t v___x_428_; 
v___x_423_ = lean_nat_add(v_idx_406_, v_fst_366_);
lean_dec(v_fst_366_);
v___x_424_ = lean_byte_array_size(v_array_405_);
v___x_428_ = lean_nat_dec_le(v_idx_406_, v___x_363_);
if (v___x_428_ == 0)
{
v___y_426_ = v_idx_406_;
goto v___jp_425_;
}
else
{
lean_dec(v_idx_406_);
v___y_426_ = v___x_363_;
goto v___jp_425_;
}
v___jp_410_:
{
lean_object* v___x_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_413_ = l_ByteArray_toByteSlice(v_array_405_, v_lower_411_, v_upper_412_);
v___x_414_ = l_ByteSlice_toByteArray(v___x_413_);
v___x_415_ = l_ByteArray_isEmpty(v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; 
lean_del_object(v___x_408_);
v___x_416_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber_spec__1(v___x_415_, v___x_414_, v___x_363_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v___x_417_; 
v___x_417_ = lean_byte_array_size(v___x_414_);
v___y_391_ = v___x_414_;
v___y_392_ = v___x_417_;
goto v___jp_390_;
}
else
{
lean_object* v_val_418_; 
v_val_418_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_val_418_);
lean_dec_ref_known(v___x_416_, 1);
v___y_391_ = v___x_414_;
v___y_392_ = v_val_418_;
goto v___jp_390_;
}
}
else
{
lean_object* v___x_419_; lean_object* v___x_421_; 
lean_dec_ref(v___x_414_);
lean_del_object(v___x_372_);
lean_del_object(v___x_368_);
v___x_419_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__5));
if (v_isShared_409_ == 0)
{
lean_ctor_set_tag(v___x_408_, 1);
lean_ctor_set(v___x_408_, 1, v___x_419_);
lean_ctor_set(v___x_408_, 0, v_fst_370_);
v___x_421_ = v___x_408_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_fst_370_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
v___jp_425_:
{
uint8_t v___x_427_; 
v___x_427_ = lean_nat_dec_le(v___x_423_, v___x_424_);
if (v___x_427_ == 0)
{
lean_dec(v___x_423_);
v_lower_411_ = v___y_426_;
v_upper_412_ = v___x_424_;
goto v___jp_410_;
}
else
{
v_lower_411_ = v___y_426_;
v_upper_412_ = v___x_423_;
goto v___jp_410_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0(uint8_t v_x_433_){
_start:
{
uint8_t v___x_479_; uint8_t v___x_480_; 
v___x_479_ = 58;
v___x_480_ = lean_uint8_dec_eq(v_x_433_, v___x_479_);
if (v___x_480_ == 0)
{
uint8_t v___x_481_; uint8_t v___x_482_; 
v___x_481_ = 48;
v___x_482_ = lean_uint8_dec_le(v___x_481_, v_x_433_);
if (v___x_482_ == 0)
{
goto v___jp_474_;
}
else
{
uint8_t v___x_483_; uint8_t v___x_484_; 
v___x_483_ = 57;
v___x_484_ = lean_uint8_dec_le(v_x_433_, v___x_483_);
if (v___x_484_ == 0)
{
goto v___jp_474_;
}
else
{
return v___x_484_;
}
}
}
else
{
uint8_t v___x_485_; 
v___x_485_ = 0;
return v___x_485_;
}
v___jp_434_:
{
uint8_t v___x_435_; uint8_t v___x_436_; 
v___x_435_ = 45;
v___x_436_ = lean_uint8_dec_eq(v_x_433_, v___x_435_);
if (v___x_436_ == 0)
{
uint8_t v___x_437_; uint8_t v___x_438_; 
v___x_437_ = 46;
v___x_438_ = lean_uint8_dec_eq(v_x_433_, v___x_437_);
if (v___x_438_ == 0)
{
uint8_t v___x_439_; uint8_t v___x_440_; 
v___x_439_ = 95;
v___x_440_ = lean_uint8_dec_eq(v_x_433_, v___x_439_);
if (v___x_440_ == 0)
{
uint8_t v___x_441_; uint8_t v___x_442_; 
v___x_441_ = 126;
v___x_442_ = lean_uint8_dec_eq(v_x_433_, v___x_441_);
if (v___x_442_ == 0)
{
uint8_t v___x_443_; uint8_t v___x_444_; 
v___x_443_ = 33;
v___x_444_ = lean_uint8_dec_eq(v_x_433_, v___x_443_);
if (v___x_444_ == 0)
{
uint8_t v___x_445_; uint8_t v___x_446_; 
v___x_445_ = 36;
v___x_446_ = lean_uint8_dec_eq(v_x_433_, v___x_445_);
if (v___x_446_ == 0)
{
uint8_t v___x_447_; uint8_t v___x_448_; 
v___x_447_ = 38;
v___x_448_ = lean_uint8_dec_eq(v_x_433_, v___x_447_);
if (v___x_448_ == 0)
{
uint8_t v___x_449_; uint8_t v___x_450_; 
v___x_449_ = 39;
v___x_450_ = lean_uint8_dec_eq(v_x_433_, v___x_449_);
if (v___x_450_ == 0)
{
uint8_t v___x_451_; uint8_t v___x_452_; 
v___x_451_ = 40;
v___x_452_ = lean_uint8_dec_eq(v_x_433_, v___x_451_);
if (v___x_452_ == 0)
{
uint8_t v___x_453_; uint8_t v___x_454_; 
v___x_453_ = 41;
v___x_454_ = lean_uint8_dec_eq(v_x_433_, v___x_453_);
if (v___x_454_ == 0)
{
uint8_t v___x_455_; uint8_t v___x_456_; 
v___x_455_ = 42;
v___x_456_ = lean_uint8_dec_eq(v_x_433_, v___x_455_);
if (v___x_456_ == 0)
{
uint8_t v___x_457_; uint8_t v___x_458_; 
v___x_457_ = 43;
v___x_458_ = lean_uint8_dec_eq(v_x_433_, v___x_457_);
if (v___x_458_ == 0)
{
uint8_t v___x_459_; uint8_t v___x_460_; 
v___x_459_ = 44;
v___x_460_ = lean_uint8_dec_eq(v_x_433_, v___x_459_);
if (v___x_460_ == 0)
{
uint8_t v___x_461_; uint8_t v___x_462_; 
v___x_461_ = 59;
v___x_462_ = lean_uint8_dec_eq(v_x_433_, v___x_461_);
if (v___x_462_ == 0)
{
uint8_t v___x_463_; uint8_t v___x_464_; 
v___x_463_ = 61;
v___x_464_ = lean_uint8_dec_eq(v_x_433_, v___x_463_);
if (v___x_464_ == 0)
{
uint8_t v___x_465_; uint8_t v___x_466_; 
v___x_465_ = 58;
v___x_466_ = lean_uint8_dec_eq(v_x_433_, v___x_465_);
if (v___x_466_ == 0)
{
uint8_t v___x_467_; uint8_t v___x_468_; 
v___x_467_ = 37;
v___x_468_ = lean_uint8_dec_eq(v_x_433_, v___x_467_);
return v___x_468_;
}
else
{
return v___x_466_;
}
}
else
{
return v___x_464_;
}
}
else
{
return v___x_462_;
}
}
else
{
return v___x_460_;
}
}
else
{
return v___x_458_;
}
}
else
{
return v___x_456_;
}
}
else
{
return v___x_454_;
}
}
else
{
return v___x_452_;
}
}
else
{
return v___x_450_;
}
}
else
{
return v___x_448_;
}
}
else
{
return v___x_446_;
}
}
else
{
return v___x_444_;
}
}
else
{
return v___x_442_;
}
}
else
{
return v___x_440_;
}
}
else
{
return v___x_438_;
}
}
else
{
return v___x_436_;
}
}
v___jp_469_:
{
uint8_t v___x_470_; uint8_t v___x_471_; 
v___x_470_ = 65;
v___x_471_ = lean_uint8_dec_le(v___x_470_, v_x_433_);
if (v___x_471_ == 0)
{
goto v___jp_434_;
}
else
{
uint8_t v___x_472_; uint8_t v___x_473_; 
v___x_472_ = 90;
v___x_473_ = lean_uint8_dec_le(v_x_433_, v___x_472_);
if (v___x_473_ == 0)
{
goto v___jp_434_;
}
else
{
return v___x_473_;
}
}
}
v___jp_474_:
{
uint8_t v___x_475_; uint8_t v___x_476_; 
v___x_475_ = 97;
v___x_476_ = lean_uint8_dec_le(v___x_475_, v_x_433_);
if (v___x_476_ == 0)
{
goto v___jp_469_;
}
else
{
uint8_t v___x_477_; uint8_t v___x_478_; 
v___x_477_ = 122;
v___x_478_ = lean_uint8_dec_le(v_x_433_, v___x_477_);
if (v___x_478_ == 0)
{
goto v___jp_469_;
}
else
{
return v___x_478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___boxed(lean_object* v_x_486_){
_start:
{
uint8_t v_x_boxed_487_; uint8_t v_res_488_; lean_object* v_r_489_; 
v_x_boxed_487_ = lean_unbox(v_x_486_);
v_res_488_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0(v_x_boxed_487_);
v_r_489_ = lean_box(v_res_488_);
return v_r_489_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1(uint8_t v___x_490_, uint8_t v___x_491_, uint8_t v_x_492_){
_start:
{
uint8_t v___x_537_; uint8_t v___x_538_; 
v___x_537_ = 48;
v___x_538_ = lean_uint8_dec_le(v___x_537_, v_x_492_);
if (v___x_538_ == 0)
{
goto v___jp_532_;
}
else
{
uint8_t v___x_539_; uint8_t v___x_540_; 
v___x_539_ = 57;
v___x_540_ = lean_uint8_dec_le(v_x_492_, v___x_539_);
if (v___x_540_ == 0)
{
goto v___jp_532_;
}
else
{
return v___x_491_;
}
}
v___jp_493_:
{
uint8_t v___x_494_; uint8_t v___x_495_; 
v___x_494_ = 45;
v___x_495_ = lean_uint8_dec_eq(v_x_492_, v___x_494_);
if (v___x_495_ == 0)
{
uint8_t v___x_496_; uint8_t v___x_497_; 
v___x_496_ = 46;
v___x_497_ = lean_uint8_dec_eq(v_x_492_, v___x_496_);
if (v___x_497_ == 0)
{
uint8_t v___x_498_; uint8_t v___x_499_; 
v___x_498_ = 95;
v___x_499_ = lean_uint8_dec_eq(v_x_492_, v___x_498_);
if (v___x_499_ == 0)
{
uint8_t v___x_500_; uint8_t v___x_501_; 
v___x_500_ = 126;
v___x_501_ = lean_uint8_dec_eq(v_x_492_, v___x_500_);
if (v___x_501_ == 0)
{
uint8_t v___x_502_; uint8_t v___x_503_; 
v___x_502_ = 33;
v___x_503_ = lean_uint8_dec_eq(v_x_492_, v___x_502_);
if (v___x_503_ == 0)
{
uint8_t v___x_504_; uint8_t v___x_505_; 
v___x_504_ = 36;
v___x_505_ = lean_uint8_dec_eq(v_x_492_, v___x_504_);
if (v___x_505_ == 0)
{
uint8_t v___x_506_; uint8_t v___x_507_; 
v___x_506_ = 38;
v___x_507_ = lean_uint8_dec_eq(v_x_492_, v___x_506_);
if (v___x_507_ == 0)
{
uint8_t v___x_508_; uint8_t v___x_509_; 
v___x_508_ = 39;
v___x_509_ = lean_uint8_dec_eq(v_x_492_, v___x_508_);
if (v___x_509_ == 0)
{
uint8_t v___x_510_; uint8_t v___x_511_; 
v___x_510_ = 40;
v___x_511_ = lean_uint8_dec_eq(v_x_492_, v___x_510_);
if (v___x_511_ == 0)
{
uint8_t v___x_512_; uint8_t v___x_513_; 
v___x_512_ = 41;
v___x_513_ = lean_uint8_dec_eq(v_x_492_, v___x_512_);
if (v___x_513_ == 0)
{
uint8_t v___x_514_; uint8_t v___x_515_; 
v___x_514_ = 42;
v___x_515_ = lean_uint8_dec_eq(v_x_492_, v___x_514_);
if (v___x_515_ == 0)
{
uint8_t v___x_516_; uint8_t v___x_517_; 
v___x_516_ = 43;
v___x_517_ = lean_uint8_dec_eq(v_x_492_, v___x_516_);
if (v___x_517_ == 0)
{
uint8_t v___x_518_; uint8_t v___x_519_; 
v___x_518_ = 44;
v___x_519_ = lean_uint8_dec_eq(v_x_492_, v___x_518_);
if (v___x_519_ == 0)
{
uint8_t v___x_520_; uint8_t v___x_521_; 
v___x_520_ = 59;
v___x_521_ = lean_uint8_dec_eq(v_x_492_, v___x_520_);
if (v___x_521_ == 0)
{
uint8_t v___x_522_; uint8_t v___x_523_; 
v___x_522_ = 61;
v___x_523_ = lean_uint8_dec_eq(v_x_492_, v___x_522_);
if (v___x_523_ == 0)
{
uint8_t v___x_524_; 
v___x_524_ = lean_uint8_dec_eq(v_x_492_, v___x_490_);
if (v___x_524_ == 0)
{
uint8_t v___x_525_; uint8_t v___x_526_; 
v___x_525_ = 37;
v___x_526_ = lean_uint8_dec_eq(v_x_492_, v___x_525_);
return v___x_526_;
}
else
{
return v___x_491_;
}
}
else
{
return v___x_491_;
}
}
else
{
return v___x_491_;
}
}
else
{
return v___x_491_;
}
}
else
{
return v___x_491_;
}
}
else
{
return v___x_491_;
}
}
else
{
return v___x_491_;
}
}
else
{
return v___x_491_;
}
}
else
{
return v___x_491_;
}
}
else
{
return v___x_491_;
}
}
else
{
return v___x_491_;
}
}
else
{
return v___x_491_;
}
}
else
{
return v___x_491_;
}
}
else
{
return v___x_491_;
}
}
else
{
return v___x_491_;
}
}
else
{
return v___x_491_;
}
}
v___jp_527_:
{
uint8_t v___x_528_; uint8_t v___x_529_; 
v___x_528_ = 65;
v___x_529_ = lean_uint8_dec_le(v___x_528_, v_x_492_);
if (v___x_529_ == 0)
{
goto v___jp_493_;
}
else
{
uint8_t v___x_530_; uint8_t v___x_531_; 
v___x_530_ = 90;
v___x_531_ = lean_uint8_dec_le(v_x_492_, v___x_530_);
if (v___x_531_ == 0)
{
goto v___jp_493_;
}
else
{
return v___x_491_;
}
}
}
v___jp_532_:
{
uint8_t v___x_533_; uint8_t v___x_534_; 
v___x_533_ = 97;
v___x_534_ = lean_uint8_dec_le(v___x_533_, v_x_492_);
if (v___x_534_ == 0)
{
goto v___jp_527_;
}
else
{
uint8_t v___x_535_; uint8_t v___x_536_; 
v___x_535_ = 122;
v___x_536_ = lean_uint8_dec_le(v_x_492_, v___x_535_);
if (v___x_536_ == 0)
{
goto v___jp_527_;
}
else
{
return v___x_491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1___boxed(lean_object* v___x_541_, lean_object* v___x_542_, lean_object* v_x_543_){
_start:
{
uint8_t v___x_4638__boxed_544_; uint8_t v___x_4639__boxed_545_; uint8_t v_x_boxed_546_; uint8_t v_res_547_; lean_object* v_r_548_; 
v___x_4638__boxed_544_ = lean_unbox(v___x_541_);
v___x_4639__boxed_545_ = lean_unbox(v___x_542_);
v_x_boxed_546_ = lean_unbox(v_x_543_);
v_res_547_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1(v___x_4638__boxed_544_, v___x_4639__boxed_545_, v_x_boxed_546_);
v_r_548_ = lean_box(v_res_547_);
return v_r_548_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(lean_object* v_config_553_, lean_object* v_a_554_){
_start:
{
lean_object* v___y_556_; lean_object* v_userPassEncoded_557_; lean_object* v___y_558_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v_lower_565_; lean_object* v_upper_566_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_581_; lean_object* v_pos_582_; lean_object* v_maxUserInfoLength_584_; lean_object* v___f_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v_snd_588_; lean_object* v_fst_589_; lean_object* v_fst_590_; lean_object* v_array_591_; lean_object* v_idx_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_640_; 
v_maxUserInfoLength_584_ = lean_ctor_get(v_config_553_, 2);
v___f_585_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__2));
v___x_586_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_554_);
v___x_587_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_585_, v_maxUserInfoLength_584_, v___x_586_, v_a_554_);
v_snd_588_ = lean_ctor_get(v___x_587_, 1);
lean_inc(v_snd_588_);
v_fst_589_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_fst_589_);
lean_dec_ref(v___x_587_);
v_fst_590_ = lean_ctor_get(v_snd_588_, 0);
lean_inc(v_fst_590_);
lean_dec(v_snd_588_);
v_array_591_ = lean_ctor_get(v_a_554_, 0);
v_idx_592_ = lean_ctor_get(v_a_554_, 1);
v_isSharedCheck_640_ = !lean_is_exclusive(v_a_554_);
if (v_isSharedCheck_640_ == 0)
{
v___x_594_ = v_a_554_;
v_isShared_595_ = v_isSharedCheck_640_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_idx_592_);
lean_inc(v_array_591_);
lean_dec(v_a_554_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_640_;
goto v_resetjp_593_;
}
v___jp_555_:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_559_, 0, v___y_556_);
lean_ctor_set(v___x_559_, 1, v_userPassEncoded_557_);
v___x_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_560_, 0, v___y_558_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
return v___x_560_;
}
v___jp_561_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = l_ByteArray_toByteSlice(v___y_562_, v_lower_565_, v_upper_566_);
v___x_568_ = l_ByteSlice_toByteArray(v___x_567_);
v___x_569_ = l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(v___x_568_);
if (lean_obj_tag(v___x_569_) == 1)
{
v___y_556_ = v___y_564_;
v_userPassEncoded_557_ = v___x_569_;
v___y_558_ = v___y_563_;
goto v___jp_555_;
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec(v___x_569_);
lean_dec_ref(v___y_564_);
v___x_570_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1));
v___x_571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_571_, 0, v___y_563_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
return v___x_571_;
}
}
v___jp_572_:
{
uint8_t v___x_579_; 
v___x_579_ = lean_nat_dec_le(v___y_577_, v___y_573_);
if (v___x_579_ == 0)
{
lean_dec(v___y_577_);
v___y_562_ = v___y_574_;
v___y_563_ = v___y_575_;
v___y_564_ = v___y_576_;
v_lower_565_ = v___y_578_;
v_upper_566_ = v___y_573_;
goto v___jp_561_;
}
else
{
lean_dec(v___y_573_);
v___y_562_ = v___y_574_;
v___y_563_ = v___y_575_;
v___y_564_ = v___y_576_;
v_lower_565_ = v___y_578_;
v_upper_566_ = v___y_577_;
goto v___jp_561_;
}
}
v___jp_580_:
{
lean_object* v___x_583_; 
v___x_583_ = lean_box(0);
v___y_556_ = v___y_581_;
v_userPassEncoded_557_ = v___x_583_;
v___y_558_ = v_pos_582_;
goto v___jp_555_;
}
v_resetjp_593_:
{
lean_object* v_lower_597_; lean_object* v_upper_598_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___y_637_; uint8_t v___x_639_; 
v___x_634_ = lean_nat_add(v_idx_592_, v_fst_589_);
lean_dec(v_fst_589_);
v___x_635_ = lean_byte_array_size(v_array_591_);
v___x_639_ = lean_nat_dec_le(v_idx_592_, v___x_586_);
if (v___x_639_ == 0)
{
v___y_637_ = v_idx_592_;
goto v___jp_636_;
}
else
{
lean_dec(v_idx_592_);
v___y_637_ = v___x_586_;
goto v___jp_636_;
}
v___jp_596_:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_599_ = l_ByteArray_toByteSlice(v_array_591_, v_lower_597_, v_upper_598_);
v___x_600_ = l_ByteSlice_toByteArray(v___x_599_);
v___x_601_ = l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(v___x_600_);
if (lean_obj_tag(v___x_601_) == 1)
{
lean_object* v_val_602_; lean_object* v_array_603_; lean_object* v_idx_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
lean_del_object(v___x_594_);
v_val_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_val_602_);
lean_dec_ref_known(v___x_601_, 1);
v_array_603_ = lean_ctor_get(v_fst_590_, 0);
v_idx_604_ = lean_ctor_get(v_fst_590_, 1);
v___x_605_ = lean_byte_array_size(v_array_603_);
v___x_606_ = lean_nat_dec_lt(v_idx_604_, v___x_605_);
if (v___x_606_ == 0)
{
v___y_581_ = v_val_602_;
v_pos_582_ = v_fst_590_;
goto v___jp_580_;
}
else
{
uint8_t v___x_607_; uint8_t v___x_608_; uint8_t v___x_609_; 
v___x_607_ = lean_byte_array_fget(v_array_603_, v_idx_604_);
v___x_608_ = 58;
v___x_609_ = lean_uint8_dec_eq(v___x_607_, v___x_608_);
if (v___x_609_ == 0)
{
v___y_581_ = v_val_602_;
v_pos_582_ = v_fst_590_;
goto v___jp_580_;
}
else
{
lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_627_; 
lean_inc(v_idx_604_);
lean_inc_ref(v_array_603_);
v_isSharedCheck_627_ = !lean_is_exclusive(v_fst_590_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; lean_object* v_unused_629_; 
v_unused_628_ = lean_ctor_get(v_fst_590_, 1);
lean_dec(v_unused_628_);
v_unused_629_ = lean_ctor_get(v_fst_590_, 0);
lean_dec(v_unused_629_);
v___x_611_ = v_fst_590_;
v_isShared_612_ = v_isSharedCheck_627_;
goto v_resetjp_610_;
}
else
{
lean_dec(v_fst_590_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_627_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___f_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_613_ = lean_box(v___x_608_);
v___x_614_ = lean_box(v___x_606_);
v___f_615_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1___boxed), 3, 2);
lean_closure_set(v___f_615_, 0, v___x_613_);
lean_closure_set(v___f_615_, 1, v___x_614_);
v___x_616_ = lean_unsigned_to_nat(1u);
v___x_617_ = lean_nat_add(v_idx_604_, v___x_616_);
lean_dec(v_idx_604_);
lean_inc(v___x_617_);
lean_inc_ref(v_array_603_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 1, v___x_617_);
v___x_619_ = v___x_611_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_array_603_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v___x_617_);
v___x_619_ = v_reuseFailAlloc_626_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_620_; lean_object* v_snd_621_; lean_object* v_fst_622_; lean_object* v_fst_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_620_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_615_, v_maxUserInfoLength_584_, v___x_586_, v___x_619_);
v_snd_621_ = lean_ctor_get(v___x_620_, 1);
lean_inc(v_snd_621_);
v_fst_622_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_fst_622_);
lean_dec_ref(v___x_620_);
v_fst_623_ = lean_ctor_get(v_snd_621_, 0);
lean_inc(v_fst_623_);
lean_dec(v_snd_621_);
v___x_624_ = lean_nat_add(v___x_617_, v_fst_622_);
lean_dec(v_fst_622_);
v___x_625_ = lean_nat_dec_le(v___x_617_, v___x_586_);
if (v___x_625_ == 0)
{
v___y_573_ = v___x_605_;
v___y_574_ = v_array_603_;
v___y_575_ = v_fst_623_;
v___y_576_ = v_val_602_;
v___y_577_ = v___x_624_;
v___y_578_ = v___x_617_;
goto v___jp_572_;
}
else
{
lean_dec(v___x_617_);
v___y_573_ = v___x_605_;
v___y_574_ = v_array_603_;
v___y_575_ = v_fst_623_;
v___y_576_ = v_val_602_;
v___y_577_ = v___x_624_;
v___y_578_ = v___x_586_;
goto v___jp_572_;
}
}
}
}
}
}
else
{
lean_object* v___x_630_; lean_object* v___x_632_; 
lean_dec(v___x_601_);
v___x_630_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1));
if (v_isShared_595_ == 0)
{
lean_ctor_set_tag(v___x_594_, 1);
lean_ctor_set(v___x_594_, 1, v___x_630_);
lean_ctor_set(v___x_594_, 0, v_fst_590_);
v___x_632_ = v___x_594_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_fst_590_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v___x_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
v___jp_636_:
{
uint8_t v___x_638_; 
v___x_638_ = lean_nat_dec_le(v___x_634_, v___x_635_);
if (v___x_638_ == 0)
{
lean_dec(v___x_634_);
v_lower_597_ = v___y_637_;
v_upper_598_ = v___x_635_;
goto v___jp_596_;
}
else
{
v_lower_597_ = v___y_637_;
v_upper_598_ = v___x_634_;
goto v___jp_596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___boxed(lean_object* v_config_641_, lean_object* v_a_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(v_config_641_, v_a_642_);
lean_dec_ref(v_config_641_);
return v_res_643_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(uint8_t v_x_644_){
_start:
{
uint8_t v___x_655_; uint8_t v___x_656_; 
v___x_655_ = 58;
v___x_656_ = lean_uint8_dec_eq(v_x_644_, v___x_655_);
if (v___x_656_ == 0)
{
uint8_t v___x_657_; uint8_t v___x_658_; 
v___x_657_ = 46;
v___x_658_ = lean_uint8_dec_eq(v_x_644_, v___x_657_);
if (v___x_658_ == 0)
{
uint8_t v___x_659_; uint8_t v___x_660_; 
v___x_659_ = 48;
v___x_660_ = lean_uint8_dec_le(v___x_659_, v_x_644_);
if (v___x_660_ == 0)
{
goto v___jp_650_;
}
else
{
uint8_t v___x_661_; uint8_t v___x_662_; 
v___x_661_ = 57;
v___x_662_ = lean_uint8_dec_le(v_x_644_, v___x_661_);
if (v___x_662_ == 0)
{
goto v___jp_650_;
}
else
{
return v___x_662_;
}
}
}
else
{
return v___x_658_;
}
}
else
{
return v___x_656_;
}
v___jp_645_:
{
uint8_t v___x_646_; uint8_t v___x_647_; 
v___x_646_ = 65;
v___x_647_ = lean_uint8_dec_le(v___x_646_, v_x_644_);
if (v___x_647_ == 0)
{
return v___x_647_;
}
else
{
uint8_t v___x_648_; uint8_t v___x_649_; 
v___x_648_ = 70;
v___x_649_ = lean_uint8_dec_le(v_x_644_, v___x_648_);
return v___x_649_;
}
}
v___jp_650_:
{
uint8_t v___x_651_; uint8_t v___x_652_; 
v___x_651_ = 97;
v___x_652_ = lean_uint8_dec_le(v___x_651_, v_x_644_);
if (v___x_652_ == 0)
{
goto v___jp_645_;
}
else
{
uint8_t v___x_653_; uint8_t v___x_654_; 
v___x_653_ = 102;
v___x_654_ = lean_uint8_dec_le(v_x_644_, v___x_653_);
if (v___x_654_ == 0)
{
goto v___jp_645_;
}
else
{
return v___x_654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___boxed(lean_object* v_x_663_){
_start:
{
uint8_t v_x_boxed_664_; uint8_t v_res_665_; lean_object* v_r_666_; 
v_x_boxed_664_ = lean_unbox(v_x_663_);
v_res_665_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(v_x_boxed_664_);
v_r_666_ = lean_box(v_res_665_);
return v_r_666_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(lean_object* v_a_678_){
_start:
{
lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v_array_689_; lean_object* v_idx_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v_array_689_ = lean_ctor_get(v_a_678_, 0);
v_idx_690_ = lean_ctor_get(v_a_678_, 1);
v___x_691_ = lean_byte_array_size(v_array_689_);
v___x_692_ = lean_nat_dec_lt(v_idx_690_, v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_box(0);
v___x_694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_694_, 0, v_a_678_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
return v___x_694_;
}
else
{
uint8_t v___x_695_; uint8_t v_got_696_; uint8_t v___x_697_; 
v___x_695_ = 91;
v_got_696_ = lean_byte_array_fget(v_array_689_, v_idx_690_);
v___x_697_ = lean_uint8_dec_eq(v_got_696_, v___x_695_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_699_, 0, v_a_678_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
return v___x_699_;
}
else
{
lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_775_; 
lean_inc(v_idx_690_);
lean_inc_ref(v_array_689_);
v_isSharedCheck_775_ = !lean_is_exclusive(v_a_678_);
if (v_isSharedCheck_775_ == 0)
{
lean_object* v_unused_776_; lean_object* v_unused_777_; 
v_unused_776_ = lean_ctor_get(v_a_678_, 1);
lean_dec(v_unused_776_);
v_unused_777_ = lean_ctor_get(v_a_678_, 0);
lean_dec(v_unused_777_);
v___x_701_ = v_a_678_;
v_isShared_702_ = v_isSharedCheck_775_;
goto v_resetjp_700_;
}
else
{
lean_dec(v_a_678_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_775_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___f_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_707_; 
v___f_703_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3));
v___x_704_ = lean_unsigned_to_nat(1u);
v___x_705_ = lean_nat_add(v_idx_690_, v___x_704_);
lean_dec(v_idx_690_);
lean_inc(v___x_705_);
lean_inc_ref(v_array_689_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 1, v___x_705_);
v___x_707_ = v___x_701_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_array_689_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v___x_705_);
v___x_707_ = v_reuseFailAlloc_774_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v_snd_711_; lean_object* v_fst_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_773_; 
v___x_708_ = lean_unsigned_to_nat(256u);
v___x_709_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___x_707_);
v___x_710_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_703_, v___x_708_, v___x_709_, v___x_707_);
v_snd_711_ = lean_ctor_get(v___x_710_, 1);
v_fst_712_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_773_ == 0)
{
v___x_714_ = v___x_710_;
v_isShared_715_ = v_isSharedCheck_773_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_snd_711_);
lean_inc(v_fst_712_);
lean_dec(v___x_710_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_773_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v_fst_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_771_; 
v_fst_716_ = lean_ctor_get(v_snd_711_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v_snd_711_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; 
v_unused_772_ = lean_ctor_get(v_snd_711_, 1);
lean_dec(v_unused_772_);
v___x_718_ = v_snd_711_;
v_isShared_719_ = v_isSharedCheck_771_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_fst_716_);
lean_dec(v_snd_711_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_771_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___y_721_; uint8_t v___x_755_; 
v___x_755_ = lean_nat_dec_eq(v_fst_712_, v___x_709_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; lean_object* v___y_758_; uint8_t v___x_766_; 
lean_dec_ref(v___x_707_);
v___x_756_ = lean_nat_add(v___x_705_, v_fst_712_);
lean_dec(v_fst_712_);
v___x_766_ = lean_nat_dec_le(v___x_705_, v___x_709_);
if (v___x_766_ == 0)
{
v___y_758_ = v___x_705_;
goto v___jp_757_;
}
else
{
lean_dec(v___x_705_);
v___y_758_ = v___x_709_;
goto v___jp_757_;
}
v___jp_757_:
{
uint8_t v___x_759_; 
v___x_759_ = lean_nat_dec_le(v___x_756_, v___x_691_);
if (v___x_759_ == 0)
{
lean_object* v___x_761_; 
lean_dec(v___x_756_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 1, v___x_691_);
lean_ctor_set(v___x_714_, 0, v___y_758_);
v___x_761_ = v___x_714_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___y_758_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v___x_691_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
v___y_721_ = v___x_761_;
goto v___jp_720_;
}
}
else
{
lean_object* v___x_764_; 
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 1, v___x_756_);
lean_ctor_set(v___x_714_, 0, v___y_758_);
v___x_764_ = v___x_714_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___y_758_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v___x_756_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
v___y_721_ = v___x_764_;
goto v___jp_720_;
}
}
}
}
else
{
lean_object* v___x_767_; lean_object* v___x_769_; 
lean_del_object(v___x_718_);
lean_dec(v_fst_716_);
lean_dec(v_fst_712_);
lean_dec(v___x_705_);
lean_dec_ref(v_array_689_);
v___x_767_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7));
if (v_isShared_715_ == 0)
{
lean_ctor_set_tag(v___x_714_, 1);
lean_ctor_set(v___x_714_, 1, v___x_767_);
lean_ctor_set(v___x_714_, 0, v___x_707_);
v___x_769_ = v___x_714_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
v___jp_720_:
{
lean_object* v_array_722_; lean_object* v_idx_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v_array_722_ = lean_ctor_get(v_fst_716_, 0);
v_idx_723_ = lean_ctor_get(v_fst_716_, 1);
v___x_724_ = lean_byte_array_size(v_array_722_);
v___x_725_ = lean_nat_dec_lt(v_idx_723_, v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; lean_object* v___x_728_; 
lean_dec_ref(v___y_721_);
lean_dec_ref(v_array_689_);
v___x_726_ = lean_box(0);
if (v_isShared_719_ == 0)
{
lean_ctor_set_tag(v___x_718_, 1);
lean_ctor_set(v___x_718_, 1, v___x_726_);
v___x_728_ = v___x_718_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_fst_716_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
else
{
uint8_t v___x_730_; uint8_t v_got_731_; uint8_t v___x_732_; 
v___x_730_ = 93;
v_got_731_ = lean_byte_array_fget(v_array_722_, v_idx_723_);
v___x_732_ = lean_uint8_dec_eq(v_got_731_, v___x_730_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; lean_object* v___x_735_; 
lean_dec_ref(v___y_721_);
lean_dec_ref(v_array_689_);
v___x_733_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5));
if (v_isShared_719_ == 0)
{
lean_ctor_set_tag(v___x_718_, 1);
lean_ctor_set(v___x_718_, 1, v___x_733_);
v___x_735_ = v___x_718_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_fst_716_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
else
{
lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_752_; 
lean_inc(v_idx_723_);
lean_inc_ref(v_array_722_);
lean_del_object(v___x_718_);
v_isSharedCheck_752_ = !lean_is_exclusive(v_fst_716_);
if (v_isSharedCheck_752_ == 0)
{
lean_object* v_unused_753_; lean_object* v_unused_754_; 
v_unused_753_ = lean_ctor_get(v_fst_716_, 1);
lean_dec(v_unused_753_);
v_unused_754_ = lean_ctor_get(v_fst_716_, 0);
lean_dec(v_unused_754_);
v___x_738_ = v_fst_716_;
v_isShared_739_ = v_isSharedCheck_752_;
goto v_resetjp_737_;
}
else
{
lean_dec(v_fst_716_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_752_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v_lower_740_; lean_object* v_upper_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_745_; 
v_lower_740_ = lean_ctor_get(v___y_721_, 0);
lean_inc(v_lower_740_);
v_upper_741_ = lean_ctor_get(v___y_721_, 1);
lean_inc(v_upper_741_);
lean_dec_ref(v___y_721_);
v___x_742_ = l_ByteArray_toByteSlice(v_array_689_, v_lower_740_, v_upper_741_);
v___x_743_ = lean_nat_add(v_idx_723_, v___x_704_);
lean_dec(v_idx_723_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 1, v___x_743_);
v___x_745_ = v___x_738_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_array_722_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v___x_743_);
v___x_745_ = v_reuseFailAlloc_751_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_746_ = l_ByteSlice_toByteArray(v___x_742_);
v___x_747_ = lean_string_validate_utf8(v___x_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; lean_object* v___x_749_; 
lean_dec_ref(v___x_746_);
v___x_748_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_749_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_748_);
v___y_680_ = v___x_745_;
v___y_681_ = v___x_749_;
goto v___jp_679_;
}
else
{
lean_object* v___x_750_; 
v___x_750_ = lean_string_from_utf8_unchecked(v___x_746_);
v___y_680_ = v___x_745_;
v___y_681_ = v___x_750_;
goto v___jp_679_;
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
v___jp_679_:
{
lean_object* v___x_682_; 
v___x_682_ = lean_uv_pton_v6(v___y_681_);
if (lean_obj_tag(v___x_682_) == 1)
{
lean_object* v_val_683_; lean_object* v___x_684_; 
lean_dec_ref(v___y_681_);
v_val_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_val_683_);
lean_dec_ref_known(v___x_682_, 1);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v___y_680_);
lean_ctor_set(v___x_684_, 1, v_val_683_);
return v___x_684_;
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
lean_dec(v___x_682_);
v___x_685_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__0));
v___x_686_ = lean_string_append(v___x_685_, v___y_681_);
lean_dec_ref(v___y_681_);
v___x_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
v___x_688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_688_, 0, v___y_680_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
return v___x_688_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg(){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0));
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___boxed(lean_object* v___dummy_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg();
return v_res_783_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0(void){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg();
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(lean_object* v_s_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___boxed(lean_object* v_s_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(v_s_787_);
lean_dec_ref(v_s_787_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__3___redArg(lean_object* v_s_790_){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_791_ = lean_string_utf8_byte_size(v_s_790_);
v___x_792_ = lean_unsigned_to_nat(1u);
v___x_793_ = lean_nat_dec_le(v___x_792_, v___x_791_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; 
lean_dec_ref(v_s_790_);
v___x_794_ = lean_box(0);
return v___x_794_;
}
else
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; 
v___x_795_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__3___redArg___closed__0));
v___x_796_ = lean_unsigned_to_nat(0u);
v___x_797_ = lean_nat_sub(v___x_791_, v___x_792_);
v___x_798_ = lean_string_memcmp(v_s_790_, v___x_795_, v___x_797_, v___x_796_, v___x_792_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; 
lean_dec(v___x_797_);
lean_dec_ref(v_s_790_);
v___x_799_ = lean_box(0);
return v___x_799_;
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
lean_inc_ref(v_s_790_);
v___x_800_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_800_, 0, v_s_790_);
lean_ctor_set(v___x_800_, 1, v___x_796_);
lean_ctor_set(v___x_800_, 2, v___x_791_);
v___x_801_ = l_String_Slice_pos_x21(v___x_800_, v___x_797_);
lean_dec(v___x_797_);
lean_dec_ref_known(v___x_800_, 3);
v___x_802_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_802_, 0, v_s_790_);
lean_ctor_set(v___x_802_, 1, v___x_796_);
lean_ctor_set(v___x_802_, 2, v___x_801_);
v___x_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
return v___x_803_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__3(lean_object* v_s_804_, lean_object* v_pat_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_String_dropSuffix_x3f___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__3___redArg(v_s_804_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__3___boxed(lean_object* v_s_807_, lean_object* v_pat_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_String_dropSuffix_x3f___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__3(v_s_807_, v_pat_808_);
lean_dec_ref(v_pat_808_);
return v_res_809_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(uint8_t v___y_810_){
_start:
{
uint8_t v___x_830_; uint8_t v___x_831_; 
v___x_830_ = 48;
v___x_831_ = lean_uint8_dec_le(v___x_830_, v___y_810_);
if (v___x_831_ == 0)
{
goto v___jp_825_;
}
else
{
uint8_t v___x_832_; uint8_t v___x_833_; 
v___x_832_ = 57;
v___x_833_ = lean_uint8_dec_le(v___y_810_, v___x_832_);
if (v___x_833_ == 0)
{
goto v___jp_825_;
}
else
{
return v___x_833_;
}
}
v___jp_811_:
{
uint8_t v___x_812_; uint8_t v___x_813_; 
v___x_812_ = 45;
v___x_813_ = lean_uint8_dec_eq(v___y_810_, v___x_812_);
if (v___x_813_ == 0)
{
uint8_t v___x_814_; uint8_t v___x_815_; 
v___x_814_ = 46;
v___x_815_ = lean_uint8_dec_eq(v___y_810_, v___x_814_);
if (v___x_815_ == 0)
{
uint8_t v___x_816_; uint8_t v___x_817_; 
v___x_816_ = 95;
v___x_817_ = lean_uint8_dec_eq(v___y_810_, v___x_816_);
if (v___x_817_ == 0)
{
uint8_t v___x_818_; uint8_t v___x_819_; 
v___x_818_ = 126;
v___x_819_ = lean_uint8_dec_eq(v___y_810_, v___x_818_);
return v___x_819_;
}
else
{
return v___x_817_;
}
}
else
{
return v___x_815_;
}
}
else
{
return v___x_813_;
}
}
v___jp_820_:
{
uint8_t v___x_821_; uint8_t v___x_822_; 
v___x_821_ = 65;
v___x_822_ = lean_uint8_dec_le(v___x_821_, v___y_810_);
if (v___x_822_ == 0)
{
goto v___jp_811_;
}
else
{
uint8_t v___x_823_; uint8_t v___x_824_; 
v___x_823_ = 90;
v___x_824_ = lean_uint8_dec_le(v___y_810_, v___x_823_);
if (v___x_824_ == 0)
{
goto v___jp_811_;
}
else
{
return v___x_824_;
}
}
}
v___jp_825_:
{
uint8_t v___x_826_; uint8_t v___x_827_; 
v___x_826_ = 97;
v___x_827_ = lean_uint8_dec_le(v___x_826_, v___y_810_);
if (v___x_827_ == 0)
{
goto v___jp_820_;
}
else
{
uint8_t v___x_828_; uint8_t v___x_829_; 
v___x_828_ = 122;
v___x_829_ = lean_uint8_dec_le(v___y_810_, v___x_828_);
if (v___x_829_ == 0)
{
goto v___jp_820_;
}
else
{
return v___x_829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed(lean_object* v___y_834_){
_start:
{
uint8_t v___y_13020__boxed_835_; uint8_t v_res_836_; lean_object* v_r_837_; 
v___y_13020__boxed_835_ = lean_unbox(v___y_834_);
v_res_836_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(v___y_13020__boxed_835_);
v_r_837_ = lean_box(v_res_836_);
return v_r_837_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__1(uint8_t v___x_838_, uint8_t v_x_839_){
_start:
{
uint8_t v___x_861_; uint8_t v___x_862_; 
v___x_861_ = 48;
v___x_862_ = lean_uint8_dec_le(v___x_861_, v_x_839_);
if (v___x_862_ == 0)
{
goto v___jp_856_;
}
else
{
uint8_t v___x_863_; uint8_t v___x_864_; 
v___x_863_ = 57;
v___x_864_ = lean_uint8_dec_le(v_x_839_, v___x_863_);
if (v___x_864_ == 0)
{
goto v___jp_856_;
}
else
{
return v___x_838_;
}
}
v___jp_840_:
{
uint8_t v___x_841_; uint8_t v___x_842_; 
v___x_841_ = 45;
v___x_842_ = lean_uint8_dec_eq(v_x_839_, v___x_841_);
if (v___x_842_ == 0)
{
uint8_t v___x_843_; uint8_t v___x_844_; 
v___x_843_ = 46;
v___x_844_ = lean_uint8_dec_eq(v_x_839_, v___x_843_);
if (v___x_844_ == 0)
{
uint8_t v___x_845_; uint8_t v___x_846_; 
v___x_845_ = 95;
v___x_846_ = lean_uint8_dec_eq(v_x_839_, v___x_845_);
if (v___x_846_ == 0)
{
uint8_t v___x_847_; uint8_t v___x_848_; 
v___x_847_ = 126;
v___x_848_ = lean_uint8_dec_eq(v_x_839_, v___x_847_);
if (v___x_848_ == 0)
{
uint8_t v___x_849_; uint8_t v___x_850_; 
v___x_849_ = 37;
v___x_850_ = lean_uint8_dec_eq(v_x_839_, v___x_849_);
return v___x_850_;
}
else
{
return v___x_838_;
}
}
else
{
return v___x_838_;
}
}
else
{
return v___x_838_;
}
}
else
{
return v___x_838_;
}
}
v___jp_851_:
{
uint8_t v___x_852_; uint8_t v___x_853_; 
v___x_852_ = 65;
v___x_853_ = lean_uint8_dec_le(v___x_852_, v_x_839_);
if (v___x_853_ == 0)
{
goto v___jp_840_;
}
else
{
uint8_t v___x_854_; uint8_t v___x_855_; 
v___x_854_ = 90;
v___x_855_ = lean_uint8_dec_le(v_x_839_, v___x_854_);
if (v___x_855_ == 0)
{
goto v___jp_840_;
}
else
{
return v___x_838_;
}
}
}
v___jp_856_:
{
uint8_t v___x_857_; uint8_t v___x_858_; 
v___x_857_ = 97;
v___x_858_ = lean_uint8_dec_le(v___x_857_, v_x_839_);
if (v___x_858_ == 0)
{
goto v___jp_851_;
}
else
{
uint8_t v___x_859_; uint8_t v___x_860_; 
v___x_859_ = 122;
v___x_860_ = lean_uint8_dec_le(v_x_839_, v___x_859_);
if (v___x_860_ == 0)
{
goto v___jp_851_;
}
else
{
return v___x_838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__1___boxed(lean_object* v___x_865_, lean_object* v_x_866_){
_start:
{
uint8_t v___x_13069__boxed_867_; uint8_t v_x_boxed_868_; uint8_t v_res_869_; lean_object* v_r_870_; 
v___x_13069__boxed_867_ = lean_unbox(v___x_865_);
v_x_boxed_868_ = lean_unbox(v_x_866_);
v_res_869_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__1(v___x_13069__boxed_867_, v_x_boxed_868_);
v_r_870_ = lean_box(v_res_869_);
return v_r_870_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(lean_object* v_fst_871_, lean_object* v___y_872_, lean_object* v___x_873_, lean_object* v_a_874_, uint8_t v_b_875_){
_start:
{
if (lean_obj_tag(v_a_874_) == 0)
{
lean_object* v_currPos_876_; lean_object* v_searcher_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_892_; 
v_currPos_876_ = lean_ctor_get(v_a_874_, 0);
v_searcher_877_ = lean_ctor_get(v_a_874_, 1);
v_isSharedCheck_892_ = !lean_is_exclusive(v_a_874_);
if (v_isSharedCheck_892_ == 0)
{
v___x_879_ = v_a_874_;
v_isShared_880_ = v_isSharedCheck_892_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_searcher_877_);
lean_inc(v_currPos_876_);
lean_dec(v_a_874_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_892_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_881_; uint8_t v___x_882_; uint8_t v_decide_883_; 
v___x_881_ = lean_unsigned_to_nat(0u);
v___x_882_ = lean_nat_dec_eq(v_fst_871_, v___x_881_);
v_decide_883_ = lean_nat_dec_eq(v_searcher_877_, v___x_873_);
if (v_decide_883_ == 0)
{
uint32_t v___x_884_; uint32_t v___x_885_; uint8_t v___x_886_; 
v___x_884_ = 46;
v___x_885_ = lean_string_utf8_get_fast(v___y_872_, v_searcher_877_);
v___x_886_ = lean_uint32_dec_eq(v___x_885_, v___x_884_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_887_ = lean_string_utf8_next_fast(v___y_872_, v_searcher_877_);
lean_dec(v_searcher_877_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 1, v___x_887_);
v___x_889_ = v___x_879_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_currPos_876_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v___x_887_);
v___x_889_ = v_reuseFailAlloc_891_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
v_a_874_ = v___x_889_;
goto _start;
}
}
else
{
lean_del_object(v___x_879_);
lean_dec(v_searcher_877_);
lean_dec(v_currPos_876_);
return v___x_882_;
}
}
else
{
lean_del_object(v___x_879_);
lean_dec(v_searcher_877_);
lean_dec(v_currPos_876_);
return v___x_882_;
}
}
}
else
{
return v_b_875_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg___boxed(lean_object* v_fst_893_, lean_object* v___y_894_, lean_object* v___x_895_, lean_object* v_a_896_, lean_object* v_b_897_){
_start:
{
uint8_t v_b_boxed_898_; uint8_t v_res_899_; lean_object* v_r_900_; 
v_b_boxed_898_ = lean_unbox(v_b_897_);
v_res_899_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v_fst_893_, v___y_894_, v___x_895_, v_a_896_, v_b_boxed_898_);
lean_dec(v___x_895_);
lean_dec_ref(v___y_894_);
lean_dec(v_fst_893_);
v_r_900_ = lean_box(v_res_899_);
return v_r_900_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(uint8_t v___x_901_, lean_object* v___y_902_, lean_object* v___x_903_, lean_object* v___x_904_, lean_object* v_a_905_, uint8_t v_b_906_){
_start:
{
uint8_t v___y_908_; lean_object* v_it_909_; lean_object* v_startInclusive_910_; lean_object* v_endExclusive_911_; uint8_t v___y_916_; 
if (v___x_901_ == 0)
{
uint8_t v___x_942_; 
v___x_942_ = 1;
v___y_916_ = v___x_942_;
goto v___jp_915_;
}
else
{
uint8_t v___x_943_; 
v___x_943_ = 0;
v___y_916_ = v___x_943_;
goto v___jp_915_;
}
v___jp_907_:
{
lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_912_ = lean_string_utf8_extract_fast(v___y_902_, v_startInclusive_910_, v_endExclusive_911_);
lean_dec(v_endExclusive_911_);
lean_dec(v_startInclusive_910_);
v___x_913_ = l_Std_Http_URI_isValidDomainLabel(v___x_912_);
if (v___x_913_ == 0)
{
lean_dec(v_it_909_);
lean_dec(v___x_904_);
return v___x_913_;
}
else
{
v_a_905_ = v_it_909_;
v_b_906_ = v___y_908_;
goto _start;
}
}
v___jp_915_:
{
if (lean_obj_tag(v_a_905_) == 0)
{
lean_object* v_currPos_917_; lean_object* v_searcher_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_941_; 
v_currPos_917_ = lean_ctor_get(v_a_905_, 0);
v_searcher_918_ = lean_ctor_get(v_a_905_, 1);
v_isSharedCheck_941_ = !lean_is_exclusive(v_a_905_);
if (v_isSharedCheck_941_ == 0)
{
v___x_920_ = v_a_905_;
v_isShared_921_ = v_isSharedCheck_941_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_searcher_918_);
lean_inc(v_currPos_917_);
lean_dec(v_a_905_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_941_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
uint8_t v_decide_922_; 
v_decide_922_ = lean_nat_dec_eq(v_searcher_918_, v___x_904_);
if (v_decide_922_ == 0)
{
uint32_t v___x_923_; uint32_t v___x_924_; uint8_t v___x_925_; 
v___x_923_ = 46;
v___x_924_ = lean_string_utf8_get_fast(v___y_902_, v_searcher_918_);
v___x_925_ = lean_uint32_dec_eq(v___x_924_, v___x_923_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_926_ = lean_string_utf8_next_fast(v___y_902_, v_searcher_918_);
lean_dec(v_searcher_918_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 1, v___x_926_);
v___x_928_ = v___x_920_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_currPos_917_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v___x_926_);
v___x_928_ = v_reuseFailAlloc_930_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
v_a_905_ = v___x_928_;
goto _start;
}
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v_slice_934_; lean_object* v_nextIt_936_; 
v___x_931_ = lean_string_utf8_next_fast(v___y_902_, v_searcher_918_);
v___x_932_ = lean_nat_sub(v___x_931_, v_searcher_918_);
v___x_933_ = lean_nat_add(v_searcher_918_, v___x_932_);
lean_dec(v___x_932_);
v_slice_934_ = l_String_Slice_subslice_x21(v___x_903_, v_currPos_917_, v_searcher_918_);
lean_inc(v___x_933_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 1, v___x_933_);
lean_ctor_set(v___x_920_, 0, v___x_933_);
v_nextIt_936_ = v___x_920_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_933_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v___x_933_);
v_nextIt_936_ = v_reuseFailAlloc_939_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v_startInclusive_937_; lean_object* v_endExclusive_938_; 
v_startInclusive_937_ = lean_ctor_get(v_slice_934_, 0);
lean_inc(v_startInclusive_937_);
v_endExclusive_938_ = lean_ctor_get(v_slice_934_, 1);
lean_inc(v_endExclusive_938_);
lean_dec_ref(v_slice_934_);
v___y_908_ = v___y_916_;
v_it_909_ = v_nextIt_936_;
v_startInclusive_910_ = v_startInclusive_937_;
v_endExclusive_911_ = v_endExclusive_938_;
goto v___jp_907_;
}
}
}
else
{
lean_object* v___x_940_; 
lean_del_object(v___x_920_);
lean_dec(v_searcher_918_);
v___x_940_ = lean_box(1);
lean_inc(v___x_904_);
v___y_908_ = v___y_916_;
v_it_909_ = v___x_940_;
v_startInclusive_910_ = v_currPos_917_;
v_endExclusive_911_ = v___x_904_;
goto v___jp_907_;
}
}
}
else
{
lean_dec(v___x_904_);
return v_b_906_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg___boxed(lean_object* v___x_944_, lean_object* v___y_945_, lean_object* v___x_946_, lean_object* v___x_947_, lean_object* v_a_948_, lean_object* v_b_949_){
_start:
{
uint8_t v___x_13165__boxed_950_; uint8_t v_b_boxed_951_; uint8_t v_res_952_; lean_object* v_r_953_; 
v___x_13165__boxed_950_ = lean_unbox(v___x_944_);
v_b_boxed_951_ = lean_unbox(v_b_949_);
v_res_952_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_13165__boxed_950_, v___y_945_, v___x_946_, v___x_947_, v_a_948_, v_b_boxed_951_);
lean_dec_ref(v___x_946_);
lean_dec_ref(v___y_945_);
v_r_953_ = lean_box(v_res_952_);
return v_r_953_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__4(lean_object* v_a_954_, lean_object* v_i_955_){
_start:
{
lean_object* v___x_956_; uint8_t v___x_957_; 
v___x_956_ = lean_byte_array_size(v_a_954_);
v___x_957_ = lean_nat_dec_lt(v_i_955_, v___x_956_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; 
lean_dec(v_i_955_);
v___x_958_ = lean_box(0);
return v___x_958_;
}
else
{
uint8_t v___x_959_; uint8_t v___x_960_; uint8_t v___x_961_; 
v___x_959_ = lean_byte_array_fget(v_a_954_, v_i_955_);
v___x_960_ = 37;
v___x_961_ = lean_uint8_dec_eq(v___x_959_, v___x_960_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = lean_unsigned_to_nat(1u);
v___x_963_ = lean_nat_add(v_i_955_, v___x_962_);
lean_dec(v_i_955_);
v_i_955_ = v___x_963_;
goto _start;
}
else
{
lean_object* v___x_965_; 
v___x_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_965_, 0, v_i_955_);
return v___x_965_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__4___boxed(lean_object* v_a_966_, lean_object* v_i_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__4(v_a_966_, v_i_967_);
lean_dec_ref(v_a_966_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(lean_object* v_config_979_, lean_object* v_a_980_){
_start:
{
lean_object* v___y_982_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_993_; uint8_t v___y_994_; uint8_t v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1013_; uint8_t v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; uint8_t v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; uint8_t v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; uint32_t v___y_1049_; uint8_t v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; uint8_t v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; uint8_t v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v_val_1101_; lean_object* v_array_1107_; lean_object* v_idx_1108_; lean_object* v___f_1109_; uint8_t v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v_lower_1118_; lean_object* v_upper_1119_; lean_object* v___y_1130_; uint8_t v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v_pos_1142_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
v_array_1107_ = lean_ctor_get(v_a_980_, 0);
v_idx_1108_ = lean_ctor_get(v_a_980_, 1);
v___f_1109_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__5));
v___x_1170_ = lean_byte_array_size(v_array_1107_);
v___x_1171_ = lean_nat_dec_lt(v_idx_1108_, v___x_1170_);
if (v___x_1171_ == 0)
{
v_pos_1142_ = v_a_980_;
goto v___jp_1141_;
}
else
{
uint8_t v___x_1172_; uint8_t v___x_1173_; uint8_t v___x_1174_; 
v___x_1172_ = lean_byte_array_fget(v_array_1107_, v_idx_1108_);
v___x_1173_ = 91;
v___x_1174_ = lean_uint8_dec_eq(v___x_1172_, v___x_1173_);
if (v___x_1174_ == 0)
{
v_pos_1142_ = v_a_980_;
goto v___jp_1141_;
}
else
{
lean_object* v___x_1175_; 
lean_dec_ref(v_config_979_);
v___x_1175_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(v_a_980_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_pos_1176_; lean_object* v_res_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1185_; 
v_pos_1176_ = lean_ctor_get(v___x_1175_, 0);
v_res_1177_ = lean_ctor_get(v___x_1175_, 1);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1179_ = v___x_1175_;
v_isShared_1180_ = v_isSharedCheck_1185_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_res_1177_);
lean_inc(v_pos_1176_);
lean_dec(v___x_1175_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1185_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1181_; lean_object* v___x_1183_; 
v___x_1181_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1181_, 0, v_res_1177_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 1, v___x_1181_);
v___x_1183_ = v___x_1179_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_pos_1176_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
else
{
lean_object* v_pos_1186_; lean_object* v_err_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
v_pos_1186_ = lean_ctor_get(v___x_1175_, 0);
v_err_1187_ = lean_ctor_get(v___x_1175_, 1);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1175_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_err_1187_);
lean_inc(v_pos_1186_);
lean_dec(v___x_1175_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_pos_1186_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_err_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
v___jp_981_:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1));
v___x_984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_984_, 0, v___y_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
return v___x_984_;
}
v___jp_985_:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_988_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2));
v___x_989_ = lean_string_append(v___x_988_, v___y_986_);
lean_dec_ref(v___y_986_);
v___x_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
v___x_991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_991_, 0, v___y_987_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
return v___x_991_;
}
v___jp_992_:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; 
v___x_1000_ = lean_string_utf8_byte_size(v___y_999_);
lean_inc(v___y_997_);
lean_inc_ref(v___y_999_);
v___x_1001_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1001_, 0, v___y_999_);
lean_ctor_set(v___x_1001_, 1, v___y_997_);
lean_ctor_set(v___x_1001_, 2, v___x_1000_);
v___x_1002_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0);
v___x_1003_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___y_994_, v___y_999_, v___x_1001_, v___x_1000_, v___x_1002_, v___y_995_);
lean_dec_ref_known(v___x_1001_, 3);
lean_dec_ref(v___y_999_);
if (v___x_1003_ == 0)
{
lean_dec(v___y_997_);
lean_dec_ref(v___y_993_);
v___y_986_ = v___y_996_;
v___y_987_ = v___y_998_;
goto v___jp_985_;
}
else
{
uint8_t v___x_1004_; 
lean_inc_ref(v___y_993_);
v___x_1004_ = l_Std_Http_URI_endsInNumber(v___y_993_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v___x_1005_ = lean_string_length(v___y_993_);
v___x_1006_ = lean_unsigned_to_nat(255u);
v___x_1007_ = lean_nat_dec_le(v___x_1005_, v___x_1006_);
if (v___x_1007_ == 0)
{
lean_dec(v___y_997_);
lean_dec_ref(v___y_993_);
v___y_986_ = v___y_996_;
v___y_987_ = v___y_998_;
goto v___jp_985_;
}
else
{
lean_object* v___x_1008_; uint8_t v___x_1009_; 
v___x_1008_ = lean_string_utf8_byte_size(v___y_993_);
v___x_1009_ = lean_nat_dec_eq(v___x_1008_, v___y_997_);
lean_dec(v___y_997_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_dec_ref(v___y_996_);
v___x_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___y_993_);
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___y_998_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
return v___x_1011_;
}
else
{
lean_dec_ref(v___y_993_);
v___y_986_ = v___y_996_;
v___y_987_ = v___y_998_;
goto v___jp_985_;
}
}
}
else
{
lean_dec(v___y_997_);
lean_dec_ref(v___y_993_);
v___y_986_ = v___y_996_;
v___y_987_ = v___y_998_;
goto v___jp_985_;
}
}
}
v___jp_1012_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; 
v___x_1020_ = lean_string_utf8_byte_size(v___y_1019_);
v___x_1021_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0);
v___x_1022_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___y_1018_, v___y_1019_, v___x_1020_, v___x_1021_, v___y_1014_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
if (v___x_1022_ == 0)
{
uint8_t v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = 1;
lean_inc_ref(v___y_1013_);
v___x_1024_ = l_String_dropSuffix_x3f___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__3___redArg(v___y_1013_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_inc_ref(v___y_1013_);
v___y_993_ = v___y_1013_;
v___y_994_ = v___x_1022_;
v___y_995_ = v___x_1023_;
v___y_996_ = v___y_1015_;
v___y_997_ = v___y_1016_;
v___y_998_ = v___y_1017_;
v___y_999_ = v___y_1013_;
goto v___jp_992_;
}
else
{
lean_object* v_val_1025_; lean_object* v_str_1026_; lean_object* v_endExclusive_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v_val_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_val_1025_);
lean_dec_ref_known(v___x_1024_, 1);
v_str_1026_ = lean_ctor_get(v_val_1025_, 0);
lean_inc_ref(v_str_1026_);
v_endExclusive_1027_ = lean_ctor_get(v_val_1025_, 2);
lean_inc(v_endExclusive_1027_);
lean_dec(v_val_1025_);
v___x_1028_ = lean_unsigned_to_nat(0u);
v___x_1029_ = lean_string_utf8_extract_fast(v_str_1026_, v___x_1028_, v_endExclusive_1027_);
lean_dec(v_endExclusive_1027_);
lean_dec_ref(v_str_1026_);
v___y_993_ = v___y_1013_;
v___y_994_ = v___x_1022_;
v___y_995_ = v___x_1023_;
v___y_996_ = v___y_1015_;
v___y_997_ = v___y_1016_;
v___y_998_ = v___y_1017_;
v___y_999_ = v___x_1029_;
goto v___jp_992_;
}
}
else
{
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1013_);
v___y_986_ = v___y_1015_;
v___y_987_ = v___y_1017_;
goto v___jp_985_;
}
}
v___jp_1030_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
lean_inc(v___y_1033_);
lean_inc_ref(v___y_1032_);
v___x_1036_ = l_String_mapAux___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(v___y_1032_, v___y_1033_);
lean_inc_ref(v___x_1036_);
v___x_1037_ = l_String_dropSuffix_x3f___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__3___redArg(v___x_1036_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_inc_ref(v___x_1036_);
v___y_1013_ = v___x_1036_;
v___y_1014_ = v___y_1031_;
v___y_1015_ = v___y_1032_;
v___y_1016_ = v___y_1033_;
v___y_1017_ = v___y_1035_;
v___y_1018_ = v___y_1034_;
v___y_1019_ = v___x_1036_;
goto v___jp_1012_;
}
else
{
lean_object* v_val_1038_; lean_object* v_str_1039_; lean_object* v_endExclusive_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v_val_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_val_1038_);
lean_dec_ref_known(v___x_1037_, 1);
v_str_1039_ = lean_ctor_get(v_val_1038_, 0);
lean_inc_ref(v_str_1039_);
v_endExclusive_1040_ = lean_ctor_get(v_val_1038_, 2);
lean_inc(v_endExclusive_1040_);
lean_dec(v_val_1038_);
v___x_1041_ = lean_unsigned_to_nat(0u);
v___x_1042_ = lean_string_utf8_extract_fast(v_str_1039_, v___x_1041_, v_endExclusive_1040_);
lean_dec(v_endExclusive_1040_);
lean_dec_ref(v_str_1039_);
v___y_1013_ = v___x_1036_;
v___y_1014_ = v___y_1031_;
v___y_1015_ = v___y_1032_;
v___y_1016_ = v___y_1033_;
v___y_1017_ = v___y_1035_;
v___y_1018_ = v___y_1034_;
v___y_1019_ = v___x_1042_;
goto v___jp_1012_;
}
}
v___jp_1043_:
{
uint32_t v___x_1050_; uint8_t v___x_1051_; 
v___x_1050_ = 48;
v___x_1051_ = lean_uint32_dec_le(v___x_1050_, v___y_1049_);
if (v___x_1051_ == 0)
{
v___y_1031_ = v___y_1044_;
v___y_1032_ = v___y_1045_;
v___y_1033_ = v___y_1046_;
v___y_1034_ = v___y_1048_;
v___y_1035_ = v___y_1047_;
goto v___jp_1030_;
}
else
{
uint32_t v___x_1052_; uint8_t v___x_1053_; 
v___x_1052_ = 57;
v___x_1053_ = lean_uint32_dec_le(v___y_1049_, v___x_1052_);
if (v___x_1053_ == 0)
{
v___y_1031_ = v___y_1044_;
v___y_1032_ = v___y_1045_;
v___y_1033_ = v___y_1046_;
v___y_1034_ = v___y_1048_;
v___y_1035_ = v___y_1047_;
goto v___jp_1030_;
}
else
{
lean_object* v___x_1054_; 
v___x_1054_ = lean_uv_pton_v4(v___y_1045_);
if (lean_obj_tag(v___x_1054_) == 1)
{
lean_object* v_val_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1063_; 
lean_dec(v___y_1048_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
v_val_1055_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1057_ = v___x_1054_;
v_isShared_1058_ = v_isSharedCheck_1063_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_val_1055_);
lean_dec(v___x_1054_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1063_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_val_1055_);
v___x_1060_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1061_; 
v___x_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___y_1047_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
return v___x_1061_;
}
}
}
else
{
lean_dec(v___x_1054_);
v___y_1031_ = v___y_1044_;
v___y_1032_ = v___y_1045_;
v___y_1033_ = v___y_1046_;
v___y_1034_ = v___y_1048_;
v___y_1035_ = v___y_1047_;
goto v___jp_1030_;
}
}
}
}
v___jp_1064_:
{
uint8_t v___x_1072_; 
v___x_1072_ = lean_nat_dec_lt(v___y_1068_, v___y_1071_);
lean_dec(v___y_1071_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
lean_dec(v___y_1068_);
v___x_1073_ = lean_string_utf8_byte_size(v___y_1066_);
lean_inc(v___y_1067_);
lean_inc_ref(v___y_1066_);
v___x_1074_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1074_, 0, v___y_1066_);
lean_ctor_set(v___x_1074_, 1, v___y_1067_);
lean_ctor_set(v___x_1074_, 2, v___x_1073_);
v___x_1075_ = l_String_Slice_Pos_get_x3f(v___x_1074_, v___y_1067_);
lean_dec_ref_known(v___x_1074_, 3);
if (lean_obj_tag(v___x_1075_) == 0)
{
uint32_t v___x_1076_; 
v___x_1076_ = 65;
v___y_1044_ = v___y_1065_;
v___y_1045_ = v___y_1066_;
v___y_1046_ = v___y_1067_;
v___y_1047_ = v___y_1069_;
v___y_1048_ = v___y_1070_;
v___y_1049_ = v___x_1076_;
goto v___jp_1043_;
}
else
{
lean_object* v_val_1077_; uint32_t v___x_1078_; 
v_val_1077_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_val_1077_);
lean_dec_ref_known(v___x_1075_, 1);
v___x_1078_ = lean_unbox_uint32(v_val_1077_);
lean_dec(v_val_1077_);
v___y_1044_ = v___y_1065_;
v___y_1045_ = v___y_1066_;
v___y_1046_ = v___y_1067_;
v___y_1047_ = v___y_1069_;
v___y_1048_ = v___y_1070_;
v___y_1049_ = v___x_1078_;
goto v___jp_1043_;
}
}
else
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_dec(v___y_1070_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
v___x_1079_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3));
v___x_1080_ = l_Nat_reprFast(v___y_1068_);
v___x_1081_ = lean_string_append(v___x_1079_, v___x_1080_);
lean_dec_ref(v___x_1080_);
v___x_1082_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__4));
v___x_1083_ = lean_string_append(v___x_1081_, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
v___x_1085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___y_1069_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
return v___x_1085_;
}
}
v___jp_1086_:
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_string_utf8_byte_size(v___y_1088_);
v___y_1065_ = v___y_1087_;
v___y_1066_ = v___y_1088_;
v___y_1067_ = v___y_1089_;
v___y_1068_ = v___y_1090_;
v___y_1069_ = v___y_1091_;
v___y_1070_ = v___y_1092_;
v___y_1071_ = v___x_1093_;
goto v___jp_1064_;
}
v___jp_1094_:
{
lean_object* v___x_1102_; uint8_t v___x_1103_; 
v___x_1102_ = lean_string_utf8_byte_size(v_val_1101_);
v___x_1103_ = lean_nat_dec_le(v___y_1097_, v___x_1102_);
if (v___x_1103_ == 0)
{
v___y_1087_ = v___y_1095_;
v___y_1088_ = v_val_1101_;
v___y_1089_ = v___y_1096_;
v___y_1090_ = v___y_1098_;
v___y_1091_ = v___y_1099_;
v___y_1092_ = v___y_1100_;
goto v___jp_1086_;
}
else
{
lean_object* v___x_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1104_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__3___redArg___closed__0));
v___x_1105_ = lean_nat_sub(v___x_1102_, v___y_1097_);
v___x_1106_ = lean_string_memcmp(v_val_1101_, v___x_1104_, v___x_1105_, v___y_1096_, v___y_1097_);
if (v___x_1106_ == 0)
{
lean_dec(v___x_1105_);
v___y_1087_ = v___y_1095_;
v___y_1088_ = v_val_1101_;
v___y_1089_ = v___y_1096_;
v___y_1090_ = v___y_1098_;
v___y_1091_ = v___y_1099_;
v___y_1092_ = v___y_1100_;
goto v___jp_1086_;
}
else
{
v___y_1065_ = v___y_1095_;
v___y_1066_ = v_val_1101_;
v___y_1067_ = v___y_1096_;
v___y_1068_ = v___y_1098_;
v___y_1069_ = v___y_1099_;
v___y_1070_ = v___y_1100_;
v___y_1071_ = v___x_1105_;
goto v___jp_1064_;
}
}
}
v___jp_1110_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1120_ = l_ByteArray_toByteSlice(v___y_1115_, v_lower_1118_, v_upper_1119_);
v___x_1121_ = l_ByteSlice_toByteArray(v___x_1120_);
lean_inc(v___y_1112_);
v___x_1122_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__4(v___x_1121_, v___y_1112_);
if (lean_obj_tag(v___x_1122_) == 0)
{
uint8_t v___x_1123_; 
v___x_1123_ = lean_string_validate_utf8(v___x_1121_);
if (v___x_1123_ == 0)
{
lean_dec_ref(v___x_1121_);
lean_dec(v___y_1117_);
lean_dec(v___y_1113_);
lean_dec(v___y_1112_);
v___y_982_ = v___y_1116_;
goto v___jp_981_;
}
else
{
lean_object* v___x_1124_; 
v___x_1124_ = lean_string_from_utf8_unchecked(v___x_1121_);
v___y_1095_ = v___y_1111_;
v___y_1096_ = v___y_1112_;
v___y_1097_ = v___y_1114_;
v___y_1098_ = v___y_1113_;
v___y_1099_ = v___y_1116_;
v___y_1100_ = v___y_1117_;
v_val_1101_ = v___x_1124_;
goto v___jp_1094_;
}
}
else
{
lean_object* v___x_1125_; 
lean_dec_ref_known(v___x_1122_, 1);
v___x_1125_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_1109_, v___x_1121_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_dec(v___y_1117_);
lean_dec(v___y_1113_);
lean_dec(v___y_1112_);
v___y_982_ = v___y_1116_;
goto v___jp_981_;
}
else
{
lean_object* v_val_1126_; lean_object* v___x_1127_; 
v_val_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_val_1126_);
lean_dec_ref_known(v___x_1125_, 1);
v___x_1127_ = l_Std_Http_URI_EncodedString_decode___redArg(v_val_1126_);
lean_dec(v_val_1126_);
if (lean_obj_tag(v___x_1127_) == 1)
{
lean_object* v_val_1128_; 
v_val_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_val_1128_);
lean_dec_ref_known(v___x_1127_, 1);
v___y_1095_ = v___y_1111_;
v___y_1096_ = v___y_1112_;
v___y_1097_ = v___y_1114_;
v___y_1098_ = v___y_1113_;
v___y_1099_ = v___y_1116_;
v___y_1100_ = v___y_1117_;
v_val_1101_ = v_val_1128_;
goto v___jp_1094_;
}
else
{
lean_dec(v___x_1127_);
lean_dec(v___y_1117_);
lean_dec(v___y_1113_);
lean_dec(v___y_1112_);
v___y_982_ = v___y_1116_;
goto v___jp_981_;
}
}
}
}
v___jp_1129_:
{
uint8_t v___x_1140_; 
v___x_1140_ = lean_nat_dec_le(v___y_1130_, v___y_1138_);
if (v___x_1140_ == 0)
{
lean_dec(v___y_1130_);
v___y_1111_ = v___y_1131_;
v___y_1112_ = v___y_1132_;
v___y_1113_ = v___y_1134_;
v___y_1114_ = v___y_1133_;
v___y_1115_ = v___y_1135_;
v___y_1116_ = v___y_1136_;
v___y_1117_ = v___y_1137_;
v_lower_1118_ = v___y_1139_;
v_upper_1119_ = v___y_1138_;
goto v___jp_1110_;
}
else
{
lean_dec(v___y_1138_);
v___y_1111_ = v___y_1131_;
v___y_1112_ = v___y_1132_;
v___y_1113_ = v___y_1134_;
v___y_1114_ = v___y_1133_;
v___y_1115_ = v___y_1135_;
v___y_1116_ = v___y_1136_;
v___y_1117_ = v___y_1137_;
v_lower_1118_ = v___y_1139_;
v_upper_1119_ = v___y_1130_;
goto v___jp_1110_;
}
}
v___jp_1141_:
{
lean_object* v_maxHostLength_1143_; uint8_t v___x_1144_; lean_object* v___f_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v_snd_1152_; lean_object* v_fst_1153_; lean_object* v_fst_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1168_; 
v_maxHostLength_1143_ = lean_ctor_get(v_config_979_, 1);
lean_inc(v_maxHostLength_1143_);
lean_dec_ref(v_config_979_);
v___x_1144_ = 1;
v___f_1145_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__6));
v___x_1146_ = lean_unsigned_to_nat(3u);
v___x_1147_ = lean_unsigned_to_nat(1u);
v___x_1148_ = lean_nat_add(v_maxHostLength_1143_, v___x_1147_);
v___x_1149_ = lean_nat_mul(v___x_1146_, v___x_1148_);
lean_dec(v___x_1148_);
v___x_1150_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pos_1142_);
v___x_1151_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1145_, v___x_1149_, v___x_1150_, v_pos_1142_);
lean_dec(v___x_1149_);
v_snd_1152_ = lean_ctor_get(v___x_1151_, 1);
lean_inc(v_snd_1152_);
v_fst_1153_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_fst_1153_);
lean_dec_ref(v___x_1151_);
v_fst_1154_ = lean_ctor_get(v_snd_1152_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_snd_1152_);
if (v_isSharedCheck_1168_ == 0)
{
lean_object* v_unused_1169_; 
v_unused_1169_ = lean_ctor_get(v_snd_1152_, 1);
lean_dec(v_unused_1169_);
v___x_1156_ = v_snd_1152_;
v_isShared_1157_ = v_isSharedCheck_1168_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_fst_1154_);
lean_dec(v_snd_1152_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1168_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
uint8_t v___x_1158_; 
v___x_1158_ = lean_nat_dec_eq(v_fst_1153_, v___x_1150_);
if (v___x_1158_ == 0)
{
lean_object* v_array_1159_; lean_object* v_idx_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; uint8_t v___x_1163_; 
lean_del_object(v___x_1156_);
v_array_1159_ = lean_ctor_get(v_pos_1142_, 0);
lean_inc_ref(v_array_1159_);
v_idx_1160_ = lean_ctor_get(v_pos_1142_, 1);
lean_inc(v_idx_1160_);
lean_dec_ref(v_pos_1142_);
v___x_1161_ = lean_nat_add(v_idx_1160_, v_fst_1153_);
v___x_1162_ = lean_byte_array_size(v_array_1159_);
v___x_1163_ = lean_nat_dec_le(v_idx_1160_, v___x_1150_);
if (v___x_1163_ == 0)
{
v___y_1130_ = v___x_1161_;
v___y_1131_ = v___x_1144_;
v___y_1132_ = v___x_1150_;
v___y_1133_ = v___x_1147_;
v___y_1134_ = v_maxHostLength_1143_;
v___y_1135_ = v_array_1159_;
v___y_1136_ = v_fst_1154_;
v___y_1137_ = v_fst_1153_;
v___y_1138_ = v___x_1162_;
v___y_1139_ = v_idx_1160_;
goto v___jp_1129_;
}
else
{
lean_dec(v_idx_1160_);
v___y_1130_ = v___x_1161_;
v___y_1131_ = v___x_1144_;
v___y_1132_ = v___x_1150_;
v___y_1133_ = v___x_1147_;
v___y_1134_ = v_maxHostLength_1143_;
v___y_1135_ = v_array_1159_;
v___y_1136_ = v_fst_1154_;
v___y_1137_ = v_fst_1153_;
v___y_1138_ = v___x_1162_;
v___y_1139_ = v___x_1150_;
goto v___jp_1129_;
}
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1166_; 
lean_dec(v_fst_1154_);
lean_dec(v_fst_1153_);
lean_dec(v_maxHostLength_1143_);
v___x_1164_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7));
if (v_isShared_1157_ == 0)
{
lean_ctor_set_tag(v___x_1156_, 1);
lean_ctor_set(v___x_1156_, 1, v___x_1164_);
lean_ctor_set(v___x_1156_, 0, v_pos_1142_);
v___x_1166_ = v___x_1156_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_pos_1142_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(lean_object* v_fst_1195_, lean_object* v___y_1196_, lean_object* v___x_1197_, lean_object* v___x_1198_, lean_object* v_inst_1199_, lean_object* v_R_1200_, lean_object* v_a_1201_, uint8_t v_b_1202_, lean_object* v_c_1203_){
_start:
{
uint8_t v___x_1204_; 
v___x_1204_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v_fst_1195_, v___y_1196_, v___x_1198_, v_a_1201_, v_b_1202_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___boxed(lean_object* v_fst_1205_, lean_object* v___y_1206_, lean_object* v___x_1207_, lean_object* v___x_1208_, lean_object* v_inst_1209_, lean_object* v_R_1210_, lean_object* v_a_1211_, lean_object* v_b_1212_, lean_object* v_c_1213_){
_start:
{
uint8_t v_b_boxed_1214_; uint8_t v_res_1215_; lean_object* v_r_1216_; 
v_b_boxed_1214_ = lean_unbox(v_b_1212_);
v_res_1215_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(v_fst_1205_, v___y_1206_, v___x_1207_, v___x_1208_, v_inst_1209_, v_R_1210_, v_a_1211_, v_b_boxed_1214_, v_c_1213_);
lean_dec(v___x_1208_);
lean_dec_ref(v___x_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v_fst_1205_);
v_r_1216_ = lean_box(v_res_1215_);
return v_r_1216_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(uint8_t v___x_1217_, lean_object* v___y_1218_, lean_object* v___x_1219_, lean_object* v___x_1220_, lean_object* v_inst_1221_, lean_object* v_R_1222_, lean_object* v_a_1223_, uint8_t v_b_1224_, lean_object* v_c_1225_){
_start:
{
uint8_t v___x_1226_; 
v___x_1226_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_1217_, v___y_1218_, v___x_1219_, v___x_1220_, v_a_1223_, v_b_1224_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___boxed(lean_object* v___x_1227_, lean_object* v___y_1228_, lean_object* v___x_1229_, lean_object* v___x_1230_, lean_object* v_inst_1231_, lean_object* v_R_1232_, lean_object* v_a_1233_, lean_object* v_b_1234_, lean_object* v_c_1235_){
_start:
{
uint8_t v___x_13727__boxed_1236_; uint8_t v_b_boxed_1237_; uint8_t v_res_1238_; lean_object* v_r_1239_; 
v___x_13727__boxed_1236_ = lean_unbox(v___x_1227_);
v_b_boxed_1237_ = lean_unbox(v_b_1234_);
v_res_1238_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(v___x_13727__boxed_1236_, v___y_1228_, v___x_1229_, v___x_1230_, v_inst_1231_, v_R_1232_, v_a_1233_, v_b_boxed_1237_, v_c_1235_);
lean_dec_ref(v___x_1229_);
lean_dec_ref(v___y_1228_);
v_r_1239_ = lean_box(v_res_1238_);
return v_r_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(lean_object* v_config_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v_port_1254_; lean_object* v___y_1255_; lean_object* v___y_1259_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1268_; lean_object* v___y_1269_; uint8_t v_val_1270_; lean_object* v___y_1271_; lean_object* v___y_1279_; lean_object* v___y_1280_; uint8_t v___y_1281_; lean_object* v_pos_1282_; lean_object* v_array_1283_; lean_object* v_idx_1284_; lean_object* v_res_1285_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; uint8_t v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1298_; lean_object* v___y_1299_; lean_object* v_pos_1300_; lean_object* v_pos_1303_; lean_object* v_res_1304_; lean_object* v_err_1369_; lean_object* v___x_1374_; 
lean_inc_ref(v_a_1250_);
v___x_1374_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(v_config_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_pos_1375_; lean_object* v_res_1376_; lean_object* v_array_1377_; lean_object* v_idx_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1395_; 
v_pos_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_pos_1375_);
v_res_1376_ = lean_ctor_get(v___x_1374_, 1);
lean_inc(v_res_1376_);
lean_dec_ref_known(v___x_1374_, 2);
v_array_1377_ = lean_ctor_get(v_pos_1375_, 0);
v_idx_1378_ = lean_ctor_get(v_pos_1375_, 1);
v_isSharedCheck_1395_ = !lean_is_exclusive(v_pos_1375_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1380_ = v_pos_1375_;
v_isShared_1381_ = v_isSharedCheck_1395_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_idx_1378_);
lean_inc(v_array_1377_);
lean_dec(v_pos_1375_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1395_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; uint8_t v___x_1383_; 
v___x_1382_ = lean_byte_array_size(v_array_1377_);
v___x_1383_ = lean_nat_dec_lt(v_idx_1378_, v___x_1382_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1384_; 
lean_del_object(v___x_1380_);
lean_dec(v_idx_1378_);
lean_dec_ref(v_array_1377_);
lean_dec(v_res_1376_);
v___x_1384_ = lean_box(0);
v_err_1369_ = v___x_1384_;
goto v___jp_1368_;
}
else
{
uint8_t v___x_1385_; uint8_t v_got_1386_; uint8_t v___x_1387_; 
v___x_1385_ = 64;
v_got_1386_ = lean_byte_array_fget(v_array_1377_, v_idx_1378_);
v___x_1387_ = lean_uint8_dec_eq(v_got_1386_, v___x_1385_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; 
lean_del_object(v___x_1380_);
lean_dec(v_idx_1378_);
lean_dec_ref(v_array_1377_);
lean_dec(v_res_1376_);
v___x_1388_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5));
v_err_1369_ = v___x_1388_;
goto v___jp_1368_;
}
else
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
lean_dec_ref(v_a_1250_);
v___x_1389_ = lean_unsigned_to_nat(1u);
v___x_1390_ = lean_nat_add(v_idx_1378_, v___x_1389_);
lean_dec(v_idx_1378_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 1, v___x_1390_);
v___x_1392_ = v___x_1380_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_array_1377_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1393_; 
v___x_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1393_, 0, v_res_1376_);
v_pos_1303_ = v___x_1392_;
v_res_1304_ = v___x_1393_;
goto v___jp_1302_;
}
}
}
}
}
else
{
lean_object* v_err_1396_; 
v_err_1396_ = lean_ctor_get(v___x_1374_, 1);
lean_inc(v_err_1396_);
lean_dec_ref_known(v___x_1374_, 2);
v_err_1369_ = v_err_1396_;
goto v___jp_1368_;
}
v___jp_1251_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1256_, 0, v___y_1253_);
lean_ctor_set(v___x_1256_, 1, v___y_1252_);
lean_ctor_set(v___x_1256_, 2, v_port_1254_);
v___x_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___y_1255_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
return v___x_1257_;
}
v___jp_1258_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__1));
v___x_1261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___y_1259_);
lean_ctor_set(v___x_1261_, 1, v___x_1260_);
return v___x_1261_;
}
v___jp_1262_:
{
lean_object* v___x_1266_; 
v___x_1266_ = lean_box(1);
v___y_1252_ = v___y_1263_;
v___y_1253_ = v___y_1265_;
v_port_1254_ = v___x_1266_;
v___y_1255_ = v___y_1264_;
goto v___jp_1251_;
}
v___jp_1267_:
{
uint8_t v___x_1272_; uint8_t v___x_1273_; 
v___x_1272_ = 47;
v___x_1273_ = lean_uint8_dec_eq(v_val_1270_, v___x_1272_);
if (v___x_1273_ == 0)
{
uint8_t v___x_1274_; uint8_t v___x_1275_; 
v___x_1274_ = 63;
v___x_1275_ = lean_uint8_dec_eq(v_val_1270_, v___x_1274_);
if (v___x_1275_ == 0)
{
uint8_t v___x_1276_; uint8_t v___x_1277_; 
v___x_1276_ = 35;
v___x_1277_ = lean_uint8_dec_eq(v_val_1270_, v___x_1276_);
if (v___x_1277_ == 0)
{
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1268_);
v___y_1259_ = v___y_1269_;
goto v___jp_1258_;
}
else
{
v___y_1263_ = v___y_1268_;
v___y_1264_ = v___y_1269_;
v___y_1265_ = v___y_1271_;
goto v___jp_1262_;
}
}
else
{
v___y_1263_ = v___y_1268_;
v___y_1264_ = v___y_1269_;
v___y_1265_ = v___y_1271_;
goto v___jp_1262_;
}
}
else
{
v___y_1263_ = v___y_1268_;
v___y_1264_ = v___y_1269_;
v___y_1265_ = v___y_1271_;
goto v___jp_1262_;
}
}
v___jp_1278_:
{
lean_object* v___x_1286_; uint8_t v___x_1287_; 
v___x_1286_ = lean_byte_array_size(v_array_1283_);
v___x_1287_ = lean_nat_dec_lt(v_idx_1284_, v___x_1286_);
if (v___x_1287_ == 0)
{
lean_dec(v_idx_1284_);
lean_dec_ref(v_array_1283_);
if (v___y_1281_ == 0)
{
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
v___y_1259_ = v_pos_1282_;
goto v___jp_1258_;
}
else
{
v___y_1263_ = v___y_1279_;
v___y_1264_ = v_pos_1282_;
v___y_1265_ = v___y_1280_;
goto v___jp_1262_;
}
}
else
{
uint8_t v___x_1288_; 
v___x_1288_ = lean_byte_array_fget(v_array_1283_, v_idx_1284_);
lean_dec(v_idx_1284_);
lean_dec_ref(v_array_1283_);
v___y_1268_ = v___y_1279_;
v___y_1269_ = v_pos_1282_;
v_val_1270_ = v___x_1288_;
v___y_1271_ = v___y_1280_;
goto v___jp_1267_;
}
}
v___jp_1289_:
{
lean_object* v___x_1296_; 
v___x_1296_ = lean_box(0);
v___y_1279_ = v___y_1290_;
v___y_1280_ = v___y_1295_;
v___y_1281_ = v___y_1294_;
v_pos_1282_ = v___y_1292_;
v_array_1283_ = v___y_1293_;
v_idx_1284_ = v___y_1291_;
v_res_1285_ = v___x_1296_;
goto v___jp_1278_;
}
v___jp_1297_:
{
lean_object* v___x_1301_; 
v___x_1301_ = lean_box(0);
v___y_1252_ = v___y_1298_;
v___y_1253_ = v___y_1299_;
v_port_1254_ = v___x_1301_;
v___y_1255_ = v_pos_1300_;
goto v___jp_1251_;
}
v___jp_1302_:
{
lean_object* v___x_1305_; 
v___x_1305_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_1249_, v_pos_1303_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_pos_1306_; lean_object* v_res_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1358_; 
v_pos_1306_ = lean_ctor_get(v___x_1305_, 0);
v_res_1307_ = lean_ctor_get(v___x_1305_, 1);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1309_ = v___x_1305_;
v_isShared_1310_ = v_isSharedCheck_1358_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_res_1307_);
lean_inc(v_pos_1306_);
lean_dec(v___x_1305_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1358_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v_array_1311_; lean_object* v_idx_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v_array_1311_ = lean_ctor_get(v_pos_1306_, 0);
v_idx_1312_ = lean_ctor_get(v_pos_1306_, 1);
v___x_1313_ = lean_byte_array_size(v_array_1311_);
v___x_1314_ = lean_nat_dec_lt(v_idx_1312_, v___x_1313_);
if (v___x_1314_ == 0)
{
lean_del_object(v___x_1309_);
v___y_1298_ = v_res_1307_;
v___y_1299_ = v_res_1304_;
v_pos_1300_ = v_pos_1306_;
goto v___jp_1297_;
}
else
{
uint8_t v___x_1315_; uint8_t v___x_1316_; uint8_t v___x_1317_; 
v___x_1315_ = lean_byte_array_fget(v_array_1311_, v_idx_1312_);
v___x_1316_ = 58;
v___x_1317_ = lean_uint8_dec_eq(v___x_1315_, v___x_1316_);
if (v___x_1317_ == 0)
{
lean_del_object(v___x_1309_);
v___y_1298_ = v_res_1307_;
v___y_1299_ = v_res_1304_;
v_pos_1300_ = v_pos_1306_;
goto v___jp_1297_;
}
else
{
if (v___x_1314_ == 0)
{
lean_object* v___x_1318_; lean_object* v___x_1320_; 
lean_dec(v_res_1307_);
lean_dec(v_res_1304_);
v___x_1318_ = lean_box(0);
if (v_isShared_1310_ == 0)
{
lean_ctor_set_tag(v___x_1309_, 1);
lean_ctor_set(v___x_1309_, 1, v___x_1318_);
v___x_1320_ = v___x_1309_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_pos_1306_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v___x_1318_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
else
{
if (v___x_1317_ == 0)
{
lean_object* v___x_1322_; lean_object* v___x_1324_; 
lean_dec(v_res_1307_);
lean_dec(v_res_1304_);
v___x_1322_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_1310_ == 0)
{
lean_ctor_set_tag(v___x_1309_, 1);
lean_ctor_set(v___x_1309_, 1, v___x_1322_);
v___x_1324_ = v___x_1309_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_pos_1306_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
else
{
lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1355_; 
lean_inc(v_idx_1312_);
lean_inc_ref(v_array_1311_);
lean_del_object(v___x_1309_);
v_isSharedCheck_1355_ = !lean_is_exclusive(v_pos_1306_);
if (v_isSharedCheck_1355_ == 0)
{
lean_object* v_unused_1356_; lean_object* v_unused_1357_; 
v_unused_1356_ = lean_ctor_get(v_pos_1306_, 1);
lean_dec(v_unused_1356_);
v_unused_1357_ = lean_ctor_get(v_pos_1306_, 0);
lean_dec(v_unused_1357_);
v___x_1327_ = v_pos_1306_;
v_isShared_1328_ = v_isSharedCheck_1355_;
goto v_resetjp_1326_;
}
else
{
lean_dec(v_pos_1306_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1355_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1332_; 
v___x_1329_ = lean_unsigned_to_nat(1u);
v___x_1330_ = lean_nat_add(v_idx_1312_, v___x_1329_);
lean_dec(v_idx_1312_);
lean_inc(v___x_1330_);
lean_inc_ref(v_array_1311_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 1, v___x_1330_);
v___x_1332_ = v___x_1327_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_array_1311_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
uint8_t v___x_1333_; 
v___x_1333_ = lean_nat_dec_lt(v___x_1330_, v___x_1313_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_box(0);
v___y_1279_ = v_res_1307_;
v___y_1280_ = v_res_1304_;
v___y_1281_ = v___x_1317_;
v_pos_1282_ = v___x_1332_;
v_array_1283_ = v_array_1311_;
v_idx_1284_ = v___x_1330_;
v_res_1285_ = v___x_1334_;
goto v___jp_1278_;
}
else
{
uint8_t v___x_1335_; uint8_t v___x_1336_; uint8_t v___x_1337_; 
v___x_1335_ = lean_byte_array_fget(v_array_1311_, v___x_1330_);
v___x_1336_ = 48;
v___x_1337_ = lean_uint8_dec_le(v___x_1336_, v___x_1335_);
if (v___x_1337_ == 0)
{
v___y_1290_ = v_res_1307_;
v___y_1291_ = v___x_1330_;
v___y_1292_ = v___x_1332_;
v___y_1293_ = v_array_1311_;
v___y_1294_ = v___x_1317_;
v___y_1295_ = v_res_1304_;
goto v___jp_1289_;
}
else
{
uint8_t v___x_1338_; uint8_t v___x_1339_; 
v___x_1338_ = 57;
v___x_1339_ = lean_uint8_dec_le(v___x_1335_, v___x_1338_);
if (v___x_1339_ == 0)
{
v___y_1290_ = v_res_1307_;
v___y_1291_ = v___x_1330_;
v___y_1292_ = v___x_1332_;
v___y_1293_ = v_array_1311_;
v___y_1294_ = v___x_1317_;
v___y_1295_ = v_res_1304_;
goto v___jp_1289_;
}
else
{
lean_object* v___x_1340_; 
lean_dec(v___x_1330_);
lean_dec_ref(v_array_1311_);
v___x_1340_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_1332_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_pos_1341_; lean_object* v_res_1342_; lean_object* v___x_1343_; uint16_t v___x_1344_; 
v_pos_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_pos_1341_);
v_res_1342_ = lean_ctor_get(v___x_1340_, 1);
lean_inc(v_res_1342_);
lean_dec_ref_known(v___x_1340_, 2);
v___x_1343_ = lean_alloc_ctor(2, 0, 2);
v___x_1344_ = lean_unbox(v_res_1342_);
lean_dec(v_res_1342_);
lean_ctor_set_uint16(v___x_1343_, 0, v___x_1344_);
v___y_1252_ = v_res_1307_;
v___y_1253_ = v_res_1304_;
v_port_1254_ = v___x_1343_;
v___y_1255_ = v_pos_1341_;
goto v___jp_1251_;
}
else
{
lean_object* v_pos_1345_; lean_object* v_err_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_dec(v_res_1307_);
lean_dec(v_res_1304_);
v_pos_1345_ = lean_ctor_get(v___x_1340_, 0);
v_err_1346_ = lean_ctor_get(v___x_1340_, 1);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1340_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_err_1346_);
lean_inc(v_pos_1345_);
lean_dec(v___x_1340_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_pos_1345_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_err_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
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
lean_object* v_pos_1359_; lean_object* v_err_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec(v_res_1304_);
v_pos_1359_ = lean_ctor_get(v___x_1305_, 0);
v_err_1360_ = lean_ctor_get(v___x_1305_, 1);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1305_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_err_1360_);
lean_inc(v_pos_1359_);
lean_dec(v___x_1305_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_pos_1359_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_err_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
v___jp_1368_:
{
lean_object* v_idx_1370_; uint8_t v___x_1371_; 
v_idx_1370_ = lean_ctor_get(v_a_1250_, 1);
v___x_1371_ = lean_nat_dec_eq(v_idx_1370_, v_idx_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; 
lean_dec_ref(v_config_1249_);
v___x_1372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1372_, 0, v_a_1250_);
lean_ctor_set(v___x_1372_, 1, v_err_1369_);
return v___x_1372_;
}
else
{
lean_object* v___x_1373_; 
lean_dec(v_err_1369_);
v___x_1373_ = lean_box(0);
v_pos_1303_ = v_a_1250_;
v_res_1304_ = v___x_1373_;
goto v___jp_1302_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(uint8_t v_c_1397_){
_start:
{
uint8_t v___x_1445_; uint8_t v___x_1446_; 
v___x_1445_ = 48;
v___x_1446_ = lean_uint8_dec_le(v___x_1445_, v_c_1397_);
if (v___x_1446_ == 0)
{
goto v___jp_1440_;
}
else
{
uint8_t v___x_1447_; uint8_t v___x_1448_; 
v___x_1447_ = 57;
v___x_1448_ = lean_uint8_dec_le(v_c_1397_, v___x_1447_);
if (v___x_1448_ == 0)
{
goto v___jp_1440_;
}
else
{
return v___x_1448_;
}
}
v___jp_1398_:
{
uint8_t v___x_1399_; uint8_t v___x_1400_; 
v___x_1399_ = 45;
v___x_1400_ = lean_uint8_dec_eq(v_c_1397_, v___x_1399_);
if (v___x_1400_ == 0)
{
uint8_t v___x_1401_; uint8_t v___x_1402_; 
v___x_1401_ = 46;
v___x_1402_ = lean_uint8_dec_eq(v_c_1397_, v___x_1401_);
if (v___x_1402_ == 0)
{
uint8_t v___x_1403_; uint8_t v___x_1404_; 
v___x_1403_ = 95;
v___x_1404_ = lean_uint8_dec_eq(v_c_1397_, v___x_1403_);
if (v___x_1404_ == 0)
{
uint8_t v___x_1405_; uint8_t v___x_1406_; 
v___x_1405_ = 126;
v___x_1406_ = lean_uint8_dec_eq(v_c_1397_, v___x_1405_);
if (v___x_1406_ == 0)
{
uint8_t v___x_1407_; uint8_t v___x_1408_; 
v___x_1407_ = 33;
v___x_1408_ = lean_uint8_dec_eq(v_c_1397_, v___x_1407_);
if (v___x_1408_ == 0)
{
uint8_t v___x_1409_; uint8_t v___x_1410_; 
v___x_1409_ = 36;
v___x_1410_ = lean_uint8_dec_eq(v_c_1397_, v___x_1409_);
if (v___x_1410_ == 0)
{
uint8_t v___x_1411_; uint8_t v___x_1412_; 
v___x_1411_ = 38;
v___x_1412_ = lean_uint8_dec_eq(v_c_1397_, v___x_1411_);
if (v___x_1412_ == 0)
{
uint8_t v___x_1413_; uint8_t v___x_1414_; 
v___x_1413_ = 39;
v___x_1414_ = lean_uint8_dec_eq(v_c_1397_, v___x_1413_);
if (v___x_1414_ == 0)
{
uint8_t v___x_1415_; uint8_t v___x_1416_; 
v___x_1415_ = 40;
v___x_1416_ = lean_uint8_dec_eq(v_c_1397_, v___x_1415_);
if (v___x_1416_ == 0)
{
uint8_t v___x_1417_; uint8_t v___x_1418_; 
v___x_1417_ = 41;
v___x_1418_ = lean_uint8_dec_eq(v_c_1397_, v___x_1417_);
if (v___x_1418_ == 0)
{
uint8_t v___x_1419_; uint8_t v___x_1420_; 
v___x_1419_ = 42;
v___x_1420_ = lean_uint8_dec_eq(v_c_1397_, v___x_1419_);
if (v___x_1420_ == 0)
{
uint8_t v___x_1421_; uint8_t v___x_1422_; 
v___x_1421_ = 43;
v___x_1422_ = lean_uint8_dec_eq(v_c_1397_, v___x_1421_);
if (v___x_1422_ == 0)
{
uint8_t v___x_1423_; uint8_t v___x_1424_; 
v___x_1423_ = 44;
v___x_1424_ = lean_uint8_dec_eq(v_c_1397_, v___x_1423_);
if (v___x_1424_ == 0)
{
uint8_t v___x_1425_; uint8_t v___x_1426_; 
v___x_1425_ = 59;
v___x_1426_ = lean_uint8_dec_eq(v_c_1397_, v___x_1425_);
if (v___x_1426_ == 0)
{
uint8_t v___x_1427_; uint8_t v___x_1428_; 
v___x_1427_ = 61;
v___x_1428_ = lean_uint8_dec_eq(v_c_1397_, v___x_1427_);
if (v___x_1428_ == 0)
{
uint8_t v___x_1429_; uint8_t v___x_1430_; 
v___x_1429_ = 58;
v___x_1430_ = lean_uint8_dec_eq(v_c_1397_, v___x_1429_);
if (v___x_1430_ == 0)
{
uint8_t v___x_1431_; uint8_t v___x_1432_; 
v___x_1431_ = 64;
v___x_1432_ = lean_uint8_dec_eq(v_c_1397_, v___x_1431_);
if (v___x_1432_ == 0)
{
uint8_t v___x_1433_; uint8_t v___x_1434_; 
v___x_1433_ = 37;
v___x_1434_ = lean_uint8_dec_eq(v_c_1397_, v___x_1433_);
return v___x_1434_;
}
else
{
return v___x_1432_;
}
}
else
{
return v___x_1430_;
}
}
else
{
return v___x_1428_;
}
}
else
{
return v___x_1426_;
}
}
else
{
return v___x_1424_;
}
}
else
{
return v___x_1422_;
}
}
else
{
return v___x_1420_;
}
}
else
{
return v___x_1418_;
}
}
else
{
return v___x_1416_;
}
}
else
{
return v___x_1414_;
}
}
else
{
return v___x_1412_;
}
}
else
{
return v___x_1410_;
}
}
else
{
return v___x_1408_;
}
}
else
{
return v___x_1406_;
}
}
else
{
return v___x_1404_;
}
}
else
{
return v___x_1402_;
}
}
else
{
return v___x_1400_;
}
}
v___jp_1435_:
{
uint8_t v___x_1436_; uint8_t v___x_1437_; 
v___x_1436_ = 65;
v___x_1437_ = lean_uint8_dec_le(v___x_1436_, v_c_1397_);
if (v___x_1437_ == 0)
{
goto v___jp_1398_;
}
else
{
uint8_t v___x_1438_; uint8_t v___x_1439_; 
v___x_1438_ = 90;
v___x_1439_ = lean_uint8_dec_le(v_c_1397_, v___x_1438_);
if (v___x_1439_ == 0)
{
goto v___jp_1398_;
}
else
{
return v___x_1439_;
}
}
}
v___jp_1440_:
{
uint8_t v___x_1441_; uint8_t v___x_1442_; 
v___x_1441_ = 97;
v___x_1442_ = lean_uint8_dec_le(v___x_1441_, v_c_1397_);
if (v___x_1442_ == 0)
{
goto v___jp_1435_;
}
else
{
uint8_t v___x_1443_; uint8_t v___x_1444_; 
v___x_1443_ = 122;
v___x_1444_ = lean_uint8_dec_le(v_c_1397_, v___x_1443_);
if (v___x_1444_ == 0)
{
goto v___jp_1435_;
}
else
{
return v___x_1444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0___boxed(lean_object* v_c_1449_){
_start:
{
uint8_t v_c_boxed_1450_; uint8_t v_res_1451_; lean_object* v_r_1452_; 
v_c_boxed_1450_ = lean_unbox(v_c_1449_);
v_res_1451_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(v_c_boxed_1450_);
v_r_1452_ = lean_box(v_res_1451_);
return v_r_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(lean_object* v_config_1454_, lean_object* v_a_1455_){
_start:
{
lean_object* v_maxSegmentLength_1456_; lean_object* v___f_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v_snd_1460_; lean_object* v_fst_1461_; lean_object* v_fst_1462_; lean_object* v_array_1463_; lean_object* v_idx_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1481_; 
v_maxSegmentLength_1456_ = lean_ctor_get(v_config_1454_, 3);
v___f_1457_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___closed__0));
v___x_1458_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1455_);
v___x_1459_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1457_, v_maxSegmentLength_1456_, v___x_1458_, v_a_1455_);
v_snd_1460_ = lean_ctor_get(v___x_1459_, 1);
lean_inc(v_snd_1460_);
v_fst_1461_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_fst_1461_);
lean_dec_ref(v___x_1459_);
v_fst_1462_ = lean_ctor_get(v_snd_1460_, 0);
lean_inc(v_fst_1462_);
lean_dec(v_snd_1460_);
v_array_1463_ = lean_ctor_get(v_a_1455_, 0);
v_idx_1464_ = lean_ctor_get(v_a_1455_, 1);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_a_1455_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1466_ = v_a_1455_;
v_isShared_1467_ = v_isSharedCheck_1481_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_idx_1464_);
lean_inc(v_array_1463_);
lean_dec(v_a_1455_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1481_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v_lower_1469_; lean_object* v_upper_1470_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___y_1478_; uint8_t v___x_1480_; 
v___x_1475_ = lean_nat_add(v_idx_1464_, v_fst_1461_);
lean_dec(v_fst_1461_);
v___x_1476_ = lean_byte_array_size(v_array_1463_);
v___x_1480_ = lean_nat_dec_le(v_idx_1464_, v___x_1458_);
if (v___x_1480_ == 0)
{
v___y_1478_ = v_idx_1464_;
goto v___jp_1477_;
}
else
{
lean_dec(v_idx_1464_);
v___y_1478_ = v___x_1458_;
goto v___jp_1477_;
}
v___jp_1468_:
{
lean_object* v___x_1471_; lean_object* v___x_1473_; 
v___x_1471_ = l_ByteArray_toByteSlice(v_array_1463_, v_lower_1469_, v_upper_1470_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 1, v___x_1471_);
lean_ctor_set(v___x_1466_, 0, v_fst_1462_);
v___x_1473_ = v___x_1466_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_fst_1462_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v___x_1471_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
v___jp_1477_:
{
uint8_t v___x_1479_; 
v___x_1479_ = lean_nat_dec_le(v___x_1475_, v___x_1476_);
if (v___x_1479_ == 0)
{
lean_dec(v___x_1475_);
v_lower_1469_ = v___y_1478_;
v_upper_1470_ = v___x_1476_;
goto v___jp_1468_;
}
else
{
v_lower_1469_ = v___y_1478_;
v_upper_1470_ = v___x_1475_;
goto v___jp_1468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___boxed(lean_object* v_config_1482_, lean_object* v_a_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1482_, v_a_1483_);
lean_dec_ref(v_config_1482_);
return v_res_1484_;
}
}
LEAN_EXPORT uint8_t l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(uint8_t v_c_1485_){
_start:
{
uint8_t v___x_1486_; uint8_t v___x_1487_; 
v___x_1486_ = 63;
v___x_1487_ = lean_uint8_dec_eq(v_c_1485_, v___x_1486_);
if (v___x_1487_ == 0)
{
uint8_t v___x_1488_; uint8_t v___x_1489_; 
v___x_1488_ = 35;
v___x_1489_ = lean_uint8_dec_eq(v_c_1485_, v___x_1488_);
return v___x_1489_;
}
else
{
return v___x_1487_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0___boxed(lean_object* v_c_1490_){
_start:
{
uint8_t v_c_boxed_1491_; uint8_t v_res_1492_; lean_object* v_r_1493_; 
v_c_boxed_1491_ = lean_unbox(v_c_1490_);
v_res_1492_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v_c_boxed_1491_);
v_r_1493_ = lean_box(v_res_1492_);
return v_r_1493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(lean_object* v_config_1500_, lean_object* v_a_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v_array_1527_; lean_object* v_idx_1528_; lean_object* v_fst_1529_; lean_object* v_snd_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1695_; 
v_array_1527_ = lean_ctor_get(v___y_1502_, 0);
v_idx_1528_ = lean_ctor_get(v___y_1502_, 1);
v_fst_1529_ = lean_ctor_get(v_a_1501_, 0);
v_snd_1530_ = lean_ctor_get(v_a_1501_, 1);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_a_1501_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1532_ = v_a_1501_;
v_isShared_1533_ = v_isSharedCheck_1695_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_snd_1530_);
lean_inc(v_fst_1529_);
lean_dec(v_a_1501_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1695_;
goto v_resetjp_1531_;
}
v___jp_1503_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___y_1505_);
lean_ctor_set(v___x_1507_, 1, v___y_1506_);
v___x_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___y_1504_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
return v___x_1508_;
}
v___jp_1509_:
{
lean_object* v___x_1514_; uint8_t v___x_1515_; 
v___x_1514_ = lean_array_get_size(v___y_1512_);
v___x_1515_ = lean_nat_dec_le(v___y_1511_, v___x_1514_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
lean_dec(v___y_1511_);
v___x_1516_ = l_ByteArray_empty;
v___x_1517_ = lean_array_push(v___y_1512_, v___x_1516_);
v___x_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1517_);
lean_ctor_set(v___x_1518_, 1, v___y_1513_);
v_a_1501_ = v___x_1518_;
v___y_1502_ = v___y_1510_;
goto _start;
}
else
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec_ref(v_config_1500_);
v___x_1520_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1521_ = l_Nat_reprFast(v___y_1511_);
v___x_1522_ = lean_string_append(v___x_1520_, v___x_1521_);
lean_dec_ref(v___x_1521_);
v___x_1523_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1524_ = lean_string_append(v___x_1522_, v___x_1523_);
v___x_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
v___x_1526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___y_1510_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
return v___x_1526_;
}
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; uint8_t v___x_1535_; 
v___x_1534_ = lean_byte_array_size(v_array_1527_);
v___x_1535_ = lean_nat_dec_lt(v_idx_1528_, v___x_1534_);
if (v___x_1535_ == 0)
{
lean_object* v___x_1537_; 
lean_dec_ref(v_config_1500_);
if (v_isShared_1533_ == 0)
{
v___x_1537_ = v___x_1532_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_fst_1529_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_snd_1530_);
v___x_1537_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
lean_object* v___x_1538_; 
v___x_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___y_1502_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
return v___x_1538_;
}
}
else
{
uint8_t v___x_1636_; uint8_t v___x_1686_; 
v___x_1636_ = lean_byte_array_fget(v_array_1527_, v_idx_1528_);
v___x_1686_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1636_);
if (v___x_1686_ == 0)
{
uint8_t v___x_1687_; uint8_t v___x_1688_; 
v___x_1687_ = 47;
v___x_1688_ = lean_uint8_dec_eq(v___x_1636_, v___x_1687_);
if (v___x_1688_ == 0)
{
uint8_t v___x_1689_; uint8_t v___x_1690_; 
v___x_1689_ = 48;
v___x_1690_ = lean_uint8_dec_le(v___x_1689_, v___x_1636_);
if (v___x_1690_ == 0)
{
goto v___jp_1681_;
}
else
{
uint8_t v___x_1691_; uint8_t v___x_1692_; 
v___x_1691_ = 57;
v___x_1692_ = lean_uint8_dec_le(v___x_1636_, v___x_1691_);
if (v___x_1692_ == 0)
{
goto v___jp_1681_;
}
else
{
goto v___jp_1540_;
}
}
}
else
{
goto v___jp_1540_;
}
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
lean_del_object(v___x_1532_);
lean_dec_ref(v_config_1500_);
v___x_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1693_, 0, v_fst_1529_);
lean_ctor_set(v___x_1693_, 1, v_snd_1530_);
v___x_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___y_1502_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
return v___x_1694_;
}
v___jp_1540_:
{
lean_object* v_maxPathSegments_1541_; lean_object* v_maxTotalPathLength_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; 
v_maxPathSegments_1541_ = lean_ctor_get(v_config_1500_, 6);
v_maxTotalPathLength_1542_ = lean_ctor_get(v_config_1500_, 7);
v___x_1543_ = lean_array_get_size(v_fst_1529_);
v___x_1544_ = lean_nat_dec_le(v_maxPathSegments_1541_, v___x_1543_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; 
v___x_1545_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1500_, v___y_1502_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_pos_1546_; lean_object* v_res_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1619_; 
v_pos_1546_ = lean_ctor_get(v___x_1545_, 0);
v_res_1547_ = lean_ctor_get(v___x_1545_, 1);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1549_ = v___x_1545_;
v_isShared_1550_ = v_isSharedCheck_1619_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_res_1547_);
lean_inc(v_pos_1546_);
lean_dec(v___x_1545_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1619_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
lean_inc(v_res_1547_);
v___x_1551_ = l_ByteSlice_toByteArray(v_res_1547_);
v___x_1552_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_1551_);
if (lean_obj_tag(v___x_1552_) == 1)
{
lean_object* v_val_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1614_; 
v_val_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1614_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_val_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1614_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; 
v___x_1557_ = l_ByteSlice_size(v_res_1547_);
lean_dec(v_res_1547_);
v___x_1558_ = lean_nat_add(v_snd_1530_, v___x_1557_);
lean_dec(v___x_1557_);
lean_dec(v_snd_1530_);
v___x_1559_ = lean_nat_dec_lt(v_maxTotalPathLength_1542_, v___x_1558_);
if (v___x_1559_ == 0)
{
lean_object* v_array_1560_; lean_object* v_idx_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v_array_1560_ = lean_ctor_get(v_pos_1546_, 0);
v_idx_1561_ = lean_ctor_get(v_pos_1546_, 1);
v___x_1562_ = lean_array_push(v_fst_1529_, v_val_1553_);
v___x_1563_ = lean_byte_array_size(v_array_1560_);
v___x_1564_ = lean_nat_dec_lt(v_idx_1561_, v___x_1563_);
if (v___x_1564_ == 0)
{
lean_del_object(v___x_1555_);
lean_del_object(v___x_1549_);
lean_del_object(v___x_1532_);
lean_dec_ref(v_config_1500_);
v___y_1504_ = v_pos_1546_;
v___y_1505_ = v___x_1562_;
v___y_1506_ = v___x_1558_;
goto v___jp_1503_;
}
else
{
uint8_t v___x_1565_; uint8_t v___x_1566_; uint8_t v___x_1567_; 
v___x_1565_ = lean_byte_array_fget(v_array_1560_, v_idx_1561_);
v___x_1566_ = 47;
v___x_1567_ = lean_uint8_dec_eq(v___x_1565_, v___x_1566_);
if (v___x_1567_ == 0)
{
lean_del_object(v___x_1555_);
lean_del_object(v___x_1549_);
lean_del_object(v___x_1532_);
lean_dec_ref(v_config_1500_);
v___y_1504_ = v_pos_1546_;
v___y_1505_ = v___x_1562_;
v___y_1506_ = v___x_1558_;
goto v___jp_1503_;
}
else
{
lean_object* v___x_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
v___x_1568_ = lean_unsigned_to_nat(1u);
v___x_1569_ = lean_nat_add(v___x_1558_, v___x_1568_);
lean_dec(v___x_1558_);
v___x_1570_ = lean_nat_dec_lt(v_maxTotalPathLength_1542_, v___x_1569_);
if (v___x_1570_ == 0)
{
lean_del_object(v___x_1555_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1571_; lean_object* v___x_1573_; 
lean_dec(v___x_1569_);
lean_dec_ref(v___x_1562_);
lean_del_object(v___x_1532_);
lean_dec_ref(v_config_1500_);
v___x_1571_ = lean_box(0);
if (v_isShared_1550_ == 0)
{
lean_ctor_set_tag(v___x_1549_, 1);
lean_ctor_set(v___x_1549_, 1, v___x_1571_);
v___x_1573_ = v___x_1549_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_pos_1546_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
else
{
lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1589_; 
lean_inc(v_idx_1561_);
lean_inc_ref(v_array_1560_);
lean_del_object(v___x_1549_);
v_isSharedCheck_1589_ = !lean_is_exclusive(v_pos_1546_);
if (v_isSharedCheck_1589_ == 0)
{
lean_object* v_unused_1590_; lean_object* v_unused_1591_; 
v_unused_1590_ = lean_ctor_get(v_pos_1546_, 1);
lean_dec(v_unused_1590_);
v_unused_1591_ = lean_ctor_get(v_pos_1546_, 0);
lean_dec(v_unused_1591_);
v___x_1576_ = v_pos_1546_;
v_isShared_1577_ = v_isSharedCheck_1589_;
goto v_resetjp_1575_;
}
else
{
lean_dec(v_pos_1546_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1589_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1578_; lean_object* v___x_1580_; 
v___x_1578_ = lean_nat_add(v_idx_1561_, v___x_1568_);
lean_dec(v_idx_1561_);
lean_inc(v___x_1578_);
lean_inc_ref(v_array_1560_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 1, v___x_1578_);
v___x_1580_ = v___x_1576_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_array_1560_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v___x_1578_);
v___x_1580_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
uint8_t v___x_1581_; 
v___x_1581_ = lean_nat_dec_lt(v___x_1578_, v___x_1563_);
if (v___x_1581_ == 0)
{
lean_dec(v___x_1578_);
lean_dec_ref(v_array_1560_);
lean_del_object(v___x_1532_);
lean_inc(v_maxPathSegments_1541_);
v___y_1510_ = v___x_1580_;
v___y_1511_ = v_maxPathSegments_1541_;
v___y_1512_ = v___x_1562_;
v___y_1513_ = v___x_1569_;
goto v___jp_1509_;
}
else
{
uint8_t v___x_1582_; uint8_t v___x_1583_; 
v___x_1582_ = lean_byte_array_fget(v_array_1560_, v___x_1578_);
lean_dec(v___x_1578_);
lean_dec_ref(v_array_1560_);
v___x_1583_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1582_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1585_; 
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 1, v___x_1569_);
lean_ctor_set(v___x_1532_, 0, v___x_1562_);
v___x_1585_ = v___x_1532_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1562_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v___x_1569_);
v___x_1585_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
v_a_1501_ = v___x_1585_;
v___y_1502_ = v___x_1580_;
goto _start;
}
}
else
{
lean_del_object(v___x_1532_);
lean_inc(v_maxPathSegments_1541_);
v___y_1510_ = v___x_1580_;
v___y_1511_ = v_maxPathSegments_1541_;
v___y_1512_ = v___x_1562_;
v___y_1513_ = v___x_1569_;
goto v___jp_1509_;
}
}
}
}
}
}
else
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
lean_inc(v_maxTotalPathLength_1542_);
lean_dec(v___x_1569_);
lean_dec_ref(v___x_1562_);
lean_del_object(v___x_1532_);
lean_dec_ref(v_config_1500_);
v___x_1592_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1593_ = l_Nat_reprFast(v_maxTotalPathLength_1542_);
v___x_1594_ = lean_string_append(v___x_1592_, v___x_1593_);
lean_dec_ref(v___x_1593_);
v___x_1595_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__4));
v___x_1596_ = lean_string_append(v___x_1594_, v___x_1595_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1596_);
v___x_1598_ = v___x_1555_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1600_; 
if (v_isShared_1550_ == 0)
{
lean_ctor_set_tag(v___x_1549_, 1);
lean_ctor_set(v___x_1549_, 1, v___x_1598_);
v___x_1600_ = v___x_1549_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_pos_1546_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
}
}
else
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1609_; 
lean_inc(v_maxTotalPathLength_1542_);
lean_dec(v___x_1558_);
lean_dec(v_val_1553_);
lean_del_object(v___x_1532_);
lean_dec(v_fst_1529_);
lean_dec_ref(v_config_1500_);
v___x_1603_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1604_ = l_Nat_reprFast(v_maxTotalPathLength_1542_);
v___x_1605_ = lean_string_append(v___x_1603_, v___x_1604_);
lean_dec_ref(v___x_1604_);
v___x_1606_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__4));
v___x_1607_ = lean_string_append(v___x_1605_, v___x_1606_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1607_);
v___x_1609_ = v___x_1555_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1607_);
v___x_1609_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1611_; 
if (v_isShared_1550_ == 0)
{
lean_ctor_set_tag(v___x_1549_, 1);
lean_ctor_set(v___x_1549_, 1, v___x_1609_);
v___x_1611_ = v___x_1549_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_pos_1546_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v___x_1609_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
}
else
{
lean_object* v___x_1615_; lean_object* v___x_1617_; 
lean_dec(v___x_1552_);
lean_dec(v_res_1547_);
lean_del_object(v___x_1532_);
lean_dec(v_snd_1530_);
lean_dec(v_fst_1529_);
lean_dec_ref(v_config_1500_);
v___x_1615_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4));
if (v_isShared_1550_ == 0)
{
lean_ctor_set_tag(v___x_1549_, 1);
lean_ctor_set(v___x_1549_, 1, v___x_1615_);
v___x_1617_ = v___x_1549_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_pos_1546_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v___x_1615_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
else
{
lean_object* v_pos_1620_; lean_object* v_err_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_del_object(v___x_1532_);
lean_dec(v_snd_1530_);
lean_dec(v_fst_1529_);
lean_dec_ref(v_config_1500_);
v_pos_1620_ = lean_ctor_get(v___x_1545_, 0);
v_err_1621_ = lean_ctor_get(v___x_1545_, 1);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1545_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_err_1621_);
lean_inc(v_pos_1620_);
lean_dec(v___x_1545_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_pos_1620_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_err_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
else
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
lean_inc(v_maxPathSegments_1541_);
lean_del_object(v___x_1532_);
lean_dec(v_snd_1530_);
lean_dec(v_fst_1529_);
lean_dec_ref(v_config_1500_);
v___x_1629_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1630_ = l_Nat_reprFast(v_maxPathSegments_1541_);
v___x_1631_ = lean_string_append(v___x_1629_, v___x_1630_);
lean_dec_ref(v___x_1630_);
v___x_1632_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1633_ = lean_string_append(v___x_1631_, v___x_1632_);
v___x_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
v___x_1635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___y_1502_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
return v___x_1635_;
}
}
v___jp_1637_:
{
uint8_t v___x_1638_; uint8_t v___x_1639_; 
v___x_1638_ = 45;
v___x_1639_ = lean_uint8_dec_eq(v___x_1636_, v___x_1638_);
if (v___x_1639_ == 0)
{
uint8_t v___x_1640_; uint8_t v___x_1641_; 
v___x_1640_ = 46;
v___x_1641_ = lean_uint8_dec_eq(v___x_1636_, v___x_1640_);
if (v___x_1641_ == 0)
{
uint8_t v___x_1642_; uint8_t v___x_1643_; 
v___x_1642_ = 95;
v___x_1643_ = lean_uint8_dec_eq(v___x_1636_, v___x_1642_);
if (v___x_1643_ == 0)
{
uint8_t v___x_1644_; uint8_t v___x_1645_; 
v___x_1644_ = 126;
v___x_1645_ = lean_uint8_dec_eq(v___x_1636_, v___x_1644_);
if (v___x_1645_ == 0)
{
uint8_t v___x_1646_; uint8_t v___x_1647_; 
v___x_1646_ = 33;
v___x_1647_ = lean_uint8_dec_eq(v___x_1636_, v___x_1646_);
if (v___x_1647_ == 0)
{
uint8_t v___x_1648_; uint8_t v___x_1649_; 
v___x_1648_ = 36;
v___x_1649_ = lean_uint8_dec_eq(v___x_1636_, v___x_1648_);
if (v___x_1649_ == 0)
{
uint8_t v___x_1650_; uint8_t v___x_1651_; 
v___x_1650_ = 38;
v___x_1651_ = lean_uint8_dec_eq(v___x_1636_, v___x_1650_);
if (v___x_1651_ == 0)
{
uint8_t v___x_1652_; uint8_t v___x_1653_; 
v___x_1652_ = 39;
v___x_1653_ = lean_uint8_dec_eq(v___x_1636_, v___x_1652_);
if (v___x_1653_ == 0)
{
uint8_t v___x_1654_; uint8_t v___x_1655_; 
v___x_1654_ = 40;
v___x_1655_ = lean_uint8_dec_eq(v___x_1636_, v___x_1654_);
if (v___x_1655_ == 0)
{
uint8_t v___x_1656_; uint8_t v___x_1657_; 
v___x_1656_ = 41;
v___x_1657_ = lean_uint8_dec_eq(v___x_1636_, v___x_1656_);
if (v___x_1657_ == 0)
{
uint8_t v___x_1658_; uint8_t v___x_1659_; 
v___x_1658_ = 42;
v___x_1659_ = lean_uint8_dec_eq(v___x_1636_, v___x_1658_);
if (v___x_1659_ == 0)
{
uint8_t v___x_1660_; uint8_t v___x_1661_; 
v___x_1660_ = 43;
v___x_1661_ = lean_uint8_dec_eq(v___x_1636_, v___x_1660_);
if (v___x_1661_ == 0)
{
uint8_t v___x_1662_; uint8_t v___x_1663_; 
v___x_1662_ = 44;
v___x_1663_ = lean_uint8_dec_eq(v___x_1636_, v___x_1662_);
if (v___x_1663_ == 0)
{
uint8_t v___x_1664_; uint8_t v___x_1665_; 
v___x_1664_ = 59;
v___x_1665_ = lean_uint8_dec_eq(v___x_1636_, v___x_1664_);
if (v___x_1665_ == 0)
{
uint8_t v___x_1666_; uint8_t v___x_1667_; 
v___x_1666_ = 61;
v___x_1667_ = lean_uint8_dec_eq(v___x_1636_, v___x_1666_);
if (v___x_1667_ == 0)
{
uint8_t v___x_1668_; uint8_t v___x_1669_; 
v___x_1668_ = 58;
v___x_1669_ = lean_uint8_dec_eq(v___x_1636_, v___x_1668_);
if (v___x_1669_ == 0)
{
uint8_t v___x_1670_; uint8_t v___x_1671_; 
v___x_1670_ = 64;
v___x_1671_ = lean_uint8_dec_eq(v___x_1636_, v___x_1670_);
if (v___x_1671_ == 0)
{
uint8_t v___x_1672_; uint8_t v___x_1673_; 
v___x_1672_ = 37;
v___x_1673_ = lean_uint8_dec_eq(v___x_1636_, v___x_1672_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
lean_del_object(v___x_1532_);
lean_dec_ref(v_config_1500_);
v___x_1674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1674_, 0, v_fst_1529_);
lean_ctor_set(v___x_1674_, 1, v_snd_1530_);
v___x_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___y_1502_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
return v___x_1675_;
}
else
{
goto v___jp_1540_;
}
}
else
{
goto v___jp_1540_;
}
}
else
{
goto v___jp_1540_;
}
}
else
{
goto v___jp_1540_;
}
}
else
{
goto v___jp_1540_;
}
}
else
{
goto v___jp_1540_;
}
}
else
{
goto v___jp_1540_;
}
}
else
{
goto v___jp_1540_;
}
}
else
{
goto v___jp_1540_;
}
}
else
{
goto v___jp_1540_;
}
}
else
{
goto v___jp_1540_;
}
}
else
{
goto v___jp_1540_;
}
}
else
{
goto v___jp_1540_;
}
}
else
{
goto v___jp_1540_;
}
}
else
{
goto v___jp_1540_;
}
}
else
{
goto v___jp_1540_;
}
}
else
{
goto v___jp_1540_;
}
}
else
{
goto v___jp_1540_;
}
}
v___jp_1676_:
{
uint8_t v___x_1677_; uint8_t v___x_1678_; 
v___x_1677_ = 65;
v___x_1678_ = lean_uint8_dec_le(v___x_1677_, v___x_1636_);
if (v___x_1678_ == 0)
{
goto v___jp_1637_;
}
else
{
uint8_t v___x_1679_; uint8_t v___x_1680_; 
v___x_1679_ = 90;
v___x_1680_ = lean_uint8_dec_le(v___x_1636_, v___x_1679_);
if (v___x_1680_ == 0)
{
goto v___jp_1637_;
}
else
{
goto v___jp_1540_;
}
}
}
v___jp_1681_:
{
uint8_t v___x_1682_; uint8_t v___x_1683_; 
v___x_1682_ = 97;
v___x_1683_ = lean_uint8_dec_le(v___x_1682_, v___x_1636_);
if (v___x_1683_ == 0)
{
goto v___jp_1676_;
}
else
{
uint8_t v___x_1684_; uint8_t v___x_1685_; 
v___x_1684_ = 122;
v___x_1685_ = lean_uint8_dec_le(v___x_1636_, v___x_1684_);
if (v___x_1685_ == 0)
{
goto v___jp_1676_;
}
else
{
goto v___jp_1540_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(lean_object* v_config_1696_, lean_object* v_a_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v_array_1723_; lean_object* v_idx_1724_; lean_object* v_fst_1725_; lean_object* v_snd_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1891_; 
v_array_1723_ = lean_ctor_get(v___y_1698_, 0);
v_idx_1724_ = lean_ctor_get(v___y_1698_, 1);
v_fst_1725_ = lean_ctor_get(v_a_1697_, 0);
v_snd_1726_ = lean_ctor_get(v_a_1697_, 1);
v_isSharedCheck_1891_ = !lean_is_exclusive(v_a_1697_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1728_ = v_a_1697_;
v_isShared_1729_ = v_isSharedCheck_1891_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_snd_1726_);
lean_inc(v_fst_1725_);
lean_dec(v_a_1697_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1891_;
goto v_resetjp_1727_;
}
v___jp_1699_:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___y_1700_);
lean_ctor_set(v___x_1703_, 1, v___y_1702_);
v___x_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___y_1701_);
lean_ctor_set(v___x_1704_, 1, v___x_1703_);
return v___x_1704_;
}
v___jp_1705_:
{
lean_object* v___x_1710_; uint8_t v___x_1711_; 
v___x_1710_ = lean_array_get_size(v___y_1706_);
v___x_1711_ = lean_nat_dec_le(v___y_1709_, v___x_1710_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
lean_dec(v___y_1709_);
v___x_1712_ = l_ByteArray_empty;
v___x_1713_ = lean_array_push(v___y_1706_, v___x_1712_);
v___x_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1713_);
lean_ctor_set(v___x_1714_, 1, v___y_1708_);
v___x_1715_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_1696_, v___x_1714_, v___y_1707_);
return v___x_1715_;
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1706_);
lean_dec_ref(v_config_1696_);
v___x_1716_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1717_ = l_Nat_reprFast(v___y_1709_);
v___x_1718_ = lean_string_append(v___x_1716_, v___x_1717_);
lean_dec_ref(v___x_1717_);
v___x_1719_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1720_ = lean_string_append(v___x_1718_, v___x_1719_);
v___x_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
v___x_1722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1722_, 0, v___y_1707_);
lean_ctor_set(v___x_1722_, 1, v___x_1721_);
return v___x_1722_;
}
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; uint8_t v___x_1731_; 
v___x_1730_ = lean_byte_array_size(v_array_1723_);
v___x_1731_ = lean_nat_dec_lt(v_idx_1724_, v___x_1730_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1733_; 
lean_dec_ref(v_config_1696_);
if (v_isShared_1729_ == 0)
{
v___x_1733_ = v___x_1728_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_fst_1725_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_snd_1726_);
v___x_1733_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
lean_object* v___x_1734_; 
v___x_1734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1734_, 0, v___y_1698_);
lean_ctor_set(v___x_1734_, 1, v___x_1733_);
return v___x_1734_;
}
}
else
{
uint8_t v___x_1832_; uint8_t v___x_1882_; 
v___x_1832_ = lean_byte_array_fget(v_array_1723_, v_idx_1724_);
v___x_1882_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1832_);
if (v___x_1882_ == 0)
{
uint8_t v___x_1883_; uint8_t v___x_1884_; 
v___x_1883_ = 47;
v___x_1884_ = lean_uint8_dec_eq(v___x_1832_, v___x_1883_);
if (v___x_1884_ == 0)
{
uint8_t v___x_1885_; uint8_t v___x_1886_; 
v___x_1885_ = 48;
v___x_1886_ = lean_uint8_dec_le(v___x_1885_, v___x_1832_);
if (v___x_1886_ == 0)
{
goto v___jp_1877_;
}
else
{
uint8_t v___x_1887_; uint8_t v___x_1888_; 
v___x_1887_ = 57;
v___x_1888_ = lean_uint8_dec_le(v___x_1832_, v___x_1887_);
if (v___x_1888_ == 0)
{
goto v___jp_1877_;
}
else
{
goto v___jp_1736_;
}
}
}
else
{
goto v___jp_1736_;
}
}
else
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
lean_del_object(v___x_1728_);
lean_dec_ref(v_config_1696_);
v___x_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1889_, 0, v_fst_1725_);
lean_ctor_set(v___x_1889_, 1, v_snd_1726_);
v___x_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___y_1698_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
return v___x_1890_;
}
v___jp_1736_:
{
lean_object* v_maxPathSegments_1737_; lean_object* v_maxTotalPathLength_1738_; lean_object* v___x_1739_; uint8_t v___x_1740_; 
v_maxPathSegments_1737_ = lean_ctor_get(v_config_1696_, 6);
v_maxTotalPathLength_1738_ = lean_ctor_get(v_config_1696_, 7);
v___x_1739_ = lean_array_get_size(v_fst_1725_);
v___x_1740_ = lean_nat_dec_le(v_maxPathSegments_1737_, v___x_1739_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; 
v___x_1741_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1696_, v___y_1698_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_pos_1742_; lean_object* v_res_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1815_; 
v_pos_1742_ = lean_ctor_get(v___x_1741_, 0);
v_res_1743_ = lean_ctor_get(v___x_1741_, 1);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1745_ = v___x_1741_;
v_isShared_1746_ = v_isSharedCheck_1815_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_res_1743_);
lean_inc(v_pos_1742_);
lean_dec(v___x_1741_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1815_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
lean_inc(v_res_1743_);
v___x_1747_ = l_ByteSlice_toByteArray(v_res_1743_);
v___x_1748_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_1747_);
if (lean_obj_tag(v___x_1748_) == 1)
{
lean_object* v_val_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1810_; 
v_val_1749_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1751_ = v___x_1748_;
v_isShared_1752_ = v_isSharedCheck_1810_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_val_1749_);
lean_dec(v___x_1748_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1810_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1753_ = l_ByteSlice_size(v_res_1743_);
lean_dec(v_res_1743_);
v___x_1754_ = lean_nat_add(v_snd_1726_, v___x_1753_);
lean_dec(v___x_1753_);
lean_dec(v_snd_1726_);
v___x_1755_ = lean_nat_dec_lt(v_maxTotalPathLength_1738_, v___x_1754_);
if (v___x_1755_ == 0)
{
lean_object* v_array_1756_; lean_object* v_idx_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
v_array_1756_ = lean_ctor_get(v_pos_1742_, 0);
v_idx_1757_ = lean_ctor_get(v_pos_1742_, 1);
v___x_1758_ = lean_array_push(v_fst_1725_, v_val_1749_);
v___x_1759_ = lean_byte_array_size(v_array_1756_);
v___x_1760_ = lean_nat_dec_lt(v_idx_1757_, v___x_1759_);
if (v___x_1760_ == 0)
{
lean_del_object(v___x_1751_);
lean_del_object(v___x_1745_);
lean_del_object(v___x_1728_);
lean_dec_ref(v_config_1696_);
v___y_1700_ = v___x_1758_;
v___y_1701_ = v_pos_1742_;
v___y_1702_ = v___x_1754_;
goto v___jp_1699_;
}
else
{
uint8_t v___x_1761_; uint8_t v___x_1762_; uint8_t v___x_1763_; 
v___x_1761_ = lean_byte_array_fget(v_array_1756_, v_idx_1757_);
v___x_1762_ = 47;
v___x_1763_ = lean_uint8_dec_eq(v___x_1761_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_del_object(v___x_1751_);
lean_del_object(v___x_1745_);
lean_del_object(v___x_1728_);
lean_dec_ref(v_config_1696_);
v___y_1700_ = v___x_1758_;
v___y_1701_ = v_pos_1742_;
v___y_1702_ = v___x_1754_;
goto v___jp_1699_;
}
else
{
lean_object* v___x_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1764_ = lean_unsigned_to_nat(1u);
v___x_1765_ = lean_nat_add(v___x_1754_, v___x_1764_);
lean_dec(v___x_1754_);
v___x_1766_ = lean_nat_dec_lt(v_maxTotalPathLength_1738_, v___x_1765_);
if (v___x_1766_ == 0)
{
lean_del_object(v___x_1751_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1767_; lean_object* v___x_1769_; 
lean_dec(v___x_1765_);
lean_dec_ref(v___x_1758_);
lean_del_object(v___x_1728_);
lean_dec_ref(v_config_1696_);
v___x_1767_ = lean_box(0);
if (v_isShared_1746_ == 0)
{
lean_ctor_set_tag(v___x_1745_, 1);
lean_ctor_set(v___x_1745_, 1, v___x_1767_);
v___x_1769_ = v___x_1745_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_pos_1742_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v___x_1767_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
else
{
lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1785_; 
lean_inc(v_idx_1757_);
lean_inc_ref(v_array_1756_);
lean_del_object(v___x_1745_);
v_isSharedCheck_1785_ = !lean_is_exclusive(v_pos_1742_);
if (v_isSharedCheck_1785_ == 0)
{
lean_object* v_unused_1786_; lean_object* v_unused_1787_; 
v_unused_1786_ = lean_ctor_get(v_pos_1742_, 1);
lean_dec(v_unused_1786_);
v_unused_1787_ = lean_ctor_get(v_pos_1742_, 0);
lean_dec(v_unused_1787_);
v___x_1772_ = v_pos_1742_;
v_isShared_1773_ = v_isSharedCheck_1785_;
goto v_resetjp_1771_;
}
else
{
lean_dec(v_pos_1742_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1785_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; lean_object* v___x_1776_; 
v___x_1774_ = lean_nat_add(v_idx_1757_, v___x_1764_);
lean_dec(v_idx_1757_);
lean_inc(v___x_1774_);
lean_inc_ref(v_array_1756_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 1, v___x_1774_);
v___x_1776_ = v___x_1772_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_array_1756_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v___x_1774_);
v___x_1776_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
uint8_t v___x_1777_; 
v___x_1777_ = lean_nat_dec_lt(v___x_1774_, v___x_1759_);
if (v___x_1777_ == 0)
{
lean_dec(v___x_1774_);
lean_dec_ref(v_array_1756_);
lean_del_object(v___x_1728_);
lean_inc(v_maxPathSegments_1737_);
v___y_1706_ = v___x_1758_;
v___y_1707_ = v___x_1776_;
v___y_1708_ = v___x_1765_;
v___y_1709_ = v_maxPathSegments_1737_;
goto v___jp_1705_;
}
else
{
uint8_t v___x_1778_; uint8_t v___x_1779_; 
v___x_1778_ = lean_byte_array_fget(v_array_1756_, v___x_1774_);
lean_dec(v___x_1774_);
lean_dec_ref(v_array_1756_);
v___x_1779_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1778_);
if (v___x_1779_ == 0)
{
lean_object* v___x_1781_; 
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 1, v___x_1765_);
lean_ctor_set(v___x_1728_, 0, v___x_1758_);
v___x_1781_ = v___x_1728_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1758_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v___x_1765_);
v___x_1781_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1782_; 
v___x_1782_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_1696_, v___x_1781_, v___x_1776_);
return v___x_1782_;
}
}
else
{
lean_del_object(v___x_1728_);
lean_inc(v_maxPathSegments_1737_);
v___y_1706_ = v___x_1758_;
v___y_1707_ = v___x_1776_;
v___y_1708_ = v___x_1765_;
v___y_1709_ = v_maxPathSegments_1737_;
goto v___jp_1705_;
}
}
}
}
}
}
else
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1794_; 
lean_inc(v_maxTotalPathLength_1738_);
lean_dec(v___x_1765_);
lean_dec_ref(v___x_1758_);
lean_del_object(v___x_1728_);
lean_dec_ref(v_config_1696_);
v___x_1788_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1789_ = l_Nat_reprFast(v_maxTotalPathLength_1738_);
v___x_1790_ = lean_string_append(v___x_1788_, v___x_1789_);
lean_dec_ref(v___x_1789_);
v___x_1791_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__4));
v___x_1792_ = lean_string_append(v___x_1790_, v___x_1791_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v___x_1792_);
v___x_1794_ = v___x_1751_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1792_);
v___x_1794_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
lean_object* v___x_1796_; 
if (v_isShared_1746_ == 0)
{
lean_ctor_set_tag(v___x_1745_, 1);
lean_ctor_set(v___x_1745_, 1, v___x_1794_);
v___x_1796_ = v___x_1745_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_pos_1742_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v___x_1794_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
}
}
else
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1805_; 
lean_inc(v_maxTotalPathLength_1738_);
lean_dec(v___x_1754_);
lean_dec(v_val_1749_);
lean_del_object(v___x_1728_);
lean_dec(v_fst_1725_);
lean_dec_ref(v_config_1696_);
v___x_1799_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1800_ = l_Nat_reprFast(v_maxTotalPathLength_1738_);
v___x_1801_ = lean_string_append(v___x_1799_, v___x_1800_);
lean_dec_ref(v___x_1800_);
v___x_1802_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__4));
v___x_1803_ = lean_string_append(v___x_1801_, v___x_1802_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v___x_1803_);
v___x_1805_ = v___x_1751_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_object* v___x_1807_; 
if (v_isShared_1746_ == 0)
{
lean_ctor_set_tag(v___x_1745_, 1);
lean_ctor_set(v___x_1745_, 1, v___x_1805_);
v___x_1807_ = v___x_1745_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_pos_1742_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v___x_1805_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
}
else
{
lean_object* v___x_1811_; lean_object* v___x_1813_; 
lean_dec(v___x_1748_);
lean_dec(v_res_1743_);
lean_del_object(v___x_1728_);
lean_dec(v_snd_1726_);
lean_dec(v_fst_1725_);
lean_dec_ref(v_config_1696_);
v___x_1811_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4));
if (v_isShared_1746_ == 0)
{
lean_ctor_set_tag(v___x_1745_, 1);
lean_ctor_set(v___x_1745_, 1, v___x_1811_);
v___x_1813_ = v___x_1745_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_pos_1742_);
lean_ctor_set(v_reuseFailAlloc_1814_, 1, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
else
{
lean_object* v_pos_1816_; lean_object* v_err_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
lean_del_object(v___x_1728_);
lean_dec(v_snd_1726_);
lean_dec(v_fst_1725_);
lean_dec_ref(v_config_1696_);
v_pos_1816_ = lean_ctor_get(v___x_1741_, 0);
v_err_1817_ = lean_ctor_get(v___x_1741_, 1);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1741_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_err_1817_);
lean_inc(v_pos_1816_);
lean_dec(v___x_1741_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_pos_1816_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_err_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
else
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_inc(v_maxPathSegments_1737_);
lean_del_object(v___x_1728_);
lean_dec(v_snd_1726_);
lean_dec(v_fst_1725_);
lean_dec_ref(v_config_1696_);
v___x_1825_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1826_ = l_Nat_reprFast(v_maxPathSegments_1737_);
v___x_1827_ = lean_string_append(v___x_1825_, v___x_1826_);
lean_dec_ref(v___x_1826_);
v___x_1828_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1829_ = lean_string_append(v___x_1827_, v___x_1828_);
v___x_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
v___x_1831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___y_1698_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
return v___x_1831_;
}
}
v___jp_1833_:
{
uint8_t v___x_1834_; uint8_t v___x_1835_; 
v___x_1834_ = 45;
v___x_1835_ = lean_uint8_dec_eq(v___x_1832_, v___x_1834_);
if (v___x_1835_ == 0)
{
uint8_t v___x_1836_; uint8_t v___x_1837_; 
v___x_1836_ = 46;
v___x_1837_ = lean_uint8_dec_eq(v___x_1832_, v___x_1836_);
if (v___x_1837_ == 0)
{
uint8_t v___x_1838_; uint8_t v___x_1839_; 
v___x_1838_ = 95;
v___x_1839_ = lean_uint8_dec_eq(v___x_1832_, v___x_1838_);
if (v___x_1839_ == 0)
{
uint8_t v___x_1840_; uint8_t v___x_1841_; 
v___x_1840_ = 126;
v___x_1841_ = lean_uint8_dec_eq(v___x_1832_, v___x_1840_);
if (v___x_1841_ == 0)
{
uint8_t v___x_1842_; uint8_t v___x_1843_; 
v___x_1842_ = 33;
v___x_1843_ = lean_uint8_dec_eq(v___x_1832_, v___x_1842_);
if (v___x_1843_ == 0)
{
uint8_t v___x_1844_; uint8_t v___x_1845_; 
v___x_1844_ = 36;
v___x_1845_ = lean_uint8_dec_eq(v___x_1832_, v___x_1844_);
if (v___x_1845_ == 0)
{
uint8_t v___x_1846_; uint8_t v___x_1847_; 
v___x_1846_ = 38;
v___x_1847_ = lean_uint8_dec_eq(v___x_1832_, v___x_1846_);
if (v___x_1847_ == 0)
{
uint8_t v___x_1848_; uint8_t v___x_1849_; 
v___x_1848_ = 39;
v___x_1849_ = lean_uint8_dec_eq(v___x_1832_, v___x_1848_);
if (v___x_1849_ == 0)
{
uint8_t v___x_1850_; uint8_t v___x_1851_; 
v___x_1850_ = 40;
v___x_1851_ = lean_uint8_dec_eq(v___x_1832_, v___x_1850_);
if (v___x_1851_ == 0)
{
uint8_t v___x_1852_; uint8_t v___x_1853_; 
v___x_1852_ = 41;
v___x_1853_ = lean_uint8_dec_eq(v___x_1832_, v___x_1852_);
if (v___x_1853_ == 0)
{
uint8_t v___x_1854_; uint8_t v___x_1855_; 
v___x_1854_ = 42;
v___x_1855_ = lean_uint8_dec_eq(v___x_1832_, v___x_1854_);
if (v___x_1855_ == 0)
{
uint8_t v___x_1856_; uint8_t v___x_1857_; 
v___x_1856_ = 43;
v___x_1857_ = lean_uint8_dec_eq(v___x_1832_, v___x_1856_);
if (v___x_1857_ == 0)
{
uint8_t v___x_1858_; uint8_t v___x_1859_; 
v___x_1858_ = 44;
v___x_1859_ = lean_uint8_dec_eq(v___x_1832_, v___x_1858_);
if (v___x_1859_ == 0)
{
uint8_t v___x_1860_; uint8_t v___x_1861_; 
v___x_1860_ = 59;
v___x_1861_ = lean_uint8_dec_eq(v___x_1832_, v___x_1860_);
if (v___x_1861_ == 0)
{
uint8_t v___x_1862_; uint8_t v___x_1863_; 
v___x_1862_ = 61;
v___x_1863_ = lean_uint8_dec_eq(v___x_1832_, v___x_1862_);
if (v___x_1863_ == 0)
{
uint8_t v___x_1864_; uint8_t v___x_1865_; 
v___x_1864_ = 58;
v___x_1865_ = lean_uint8_dec_eq(v___x_1832_, v___x_1864_);
if (v___x_1865_ == 0)
{
uint8_t v___x_1866_; uint8_t v___x_1867_; 
v___x_1866_ = 64;
v___x_1867_ = lean_uint8_dec_eq(v___x_1832_, v___x_1866_);
if (v___x_1867_ == 0)
{
uint8_t v___x_1868_; uint8_t v___x_1869_; 
v___x_1868_ = 37;
v___x_1869_ = lean_uint8_dec_eq(v___x_1832_, v___x_1868_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
lean_del_object(v___x_1728_);
lean_dec_ref(v_config_1696_);
v___x_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1870_, 0, v_fst_1725_);
lean_ctor_set(v___x_1870_, 1, v_snd_1726_);
v___x_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___y_1698_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
return v___x_1871_;
}
else
{
goto v___jp_1736_;
}
}
else
{
goto v___jp_1736_;
}
}
else
{
goto v___jp_1736_;
}
}
else
{
goto v___jp_1736_;
}
}
else
{
goto v___jp_1736_;
}
}
else
{
goto v___jp_1736_;
}
}
else
{
goto v___jp_1736_;
}
}
else
{
goto v___jp_1736_;
}
}
else
{
goto v___jp_1736_;
}
}
else
{
goto v___jp_1736_;
}
}
else
{
goto v___jp_1736_;
}
}
else
{
goto v___jp_1736_;
}
}
else
{
goto v___jp_1736_;
}
}
else
{
goto v___jp_1736_;
}
}
else
{
goto v___jp_1736_;
}
}
else
{
goto v___jp_1736_;
}
}
else
{
goto v___jp_1736_;
}
}
else
{
goto v___jp_1736_;
}
}
v___jp_1872_:
{
uint8_t v___x_1873_; uint8_t v___x_1874_; 
v___x_1873_ = 65;
v___x_1874_ = lean_uint8_dec_le(v___x_1873_, v___x_1832_);
if (v___x_1874_ == 0)
{
goto v___jp_1833_;
}
else
{
uint8_t v___x_1875_; uint8_t v___x_1876_; 
v___x_1875_ = 90;
v___x_1876_ = lean_uint8_dec_le(v___x_1832_, v___x_1875_);
if (v___x_1876_ == 0)
{
goto v___jp_1833_;
}
else
{
goto v___jp_1736_;
}
}
}
v___jp_1877_:
{
uint8_t v___x_1878_; uint8_t v___x_1879_; 
v___x_1878_ = 97;
v___x_1879_ = lean_uint8_dec_le(v___x_1878_, v___x_1832_);
if (v___x_1879_ == 0)
{
goto v___jp_1872_;
}
else
{
uint8_t v___x_1880_; uint8_t v___x_1881_; 
v___x_1880_ = 122;
v___x_1881_ = lean_uint8_dec_le(v___x_1832_, v___x_1880_);
if (v___x_1881_ == 0)
{
goto v___jp_1872_;
}
else
{
goto v___jp_1736_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath(lean_object* v_config_1903_, uint8_t v_forceAbsolute_1904_, uint8_t v_allowEmpty_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v___y_1908_; lean_object* v___y_1912_; lean_object* v_array_1915_; lean_object* v_idx_1916_; uint8_t v_isAbsolute_1917_; lean_object* v___x_1918_; lean_object* v_segments_1919_; uint8_t v_isAbsolute_1921_; lean_object* v_totalLength_1922_; lean_object* v___y_1923_; lean_object* v_pos_1947_; lean_object* v_array_1948_; lean_object* v_idx_1949_; lean_object* v___y_1958_; uint8_t v___y_1962_; lean_object* v_pos_1963_; uint8_t v_res_1964_; uint8_t v___y_1966_; lean_object* v_pos_1967_; uint8_t v_res_1968_; lean_object* v___y_1976_; uint8_t v___y_1977_; uint8_t v___y_1978_; uint8_t v___y_1987_; lean_object* v_pos_1988_; uint8_t v_res_1989_; lean_object* v_pos_1991_; lean_object* v_array_1992_; lean_object* v_idx_1993_; uint8_t v_res_1994_; lean_object* v___x_1998_; uint8_t v___x_1999_; 
v_array_1915_ = lean_ctor_get(v_a_1906_, 0);
lean_inc_ref(v_array_1915_);
v_idx_1916_ = lean_ctor_get(v_a_1906_, 1);
lean_inc(v_idx_1916_);
v_isAbsolute_1917_ = 0;
v___x_1918_ = lean_unsigned_to_nat(0u);
v_segments_1919_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__4));
v___x_1998_ = lean_byte_array_size(v_array_1915_);
v___x_1999_ = lean_nat_dec_lt(v_idx_1916_, v___x_1998_);
if (v___x_1999_ == 0)
{
v_pos_1991_ = v_a_1906_;
v_array_1992_ = v_array_1915_;
v_idx_1993_ = v_idx_1916_;
v_res_1994_ = v_isAbsolute_1917_;
goto v___jp_1990_;
}
else
{
uint8_t v___x_2000_; uint8_t v___x_2050_; uint8_t v___x_2051_; 
v___x_2000_ = lean_byte_array_fget(v_array_1915_, v_idx_1916_);
v___x_2050_ = 48;
v___x_2051_ = lean_uint8_dec_le(v___x_2050_, v___x_2000_);
if (v___x_2051_ == 0)
{
goto v___jp_2045_;
}
else
{
uint8_t v___x_2052_; uint8_t v___x_2053_; 
v___x_2052_ = 57;
v___x_2053_ = lean_uint8_dec_le(v___x_2000_, v___x_2052_);
if (v___x_2053_ == 0)
{
goto v___jp_2045_;
}
else
{
v_pos_1991_ = v_a_1906_;
v_array_1992_ = v_array_1915_;
v_idx_1993_ = v_idx_1916_;
v_res_1994_ = v___x_2053_;
goto v___jp_1990_;
}
}
v___jp_2001_:
{
uint8_t v___x_2002_; uint8_t v___x_2003_; 
v___x_2002_ = 45;
v___x_2003_ = lean_uint8_dec_eq(v___x_2000_, v___x_2002_);
if (v___x_2003_ == 0)
{
uint8_t v___x_2004_; uint8_t v___x_2005_; 
v___x_2004_ = 46;
v___x_2005_ = lean_uint8_dec_eq(v___x_2000_, v___x_2004_);
if (v___x_2005_ == 0)
{
uint8_t v___x_2006_; uint8_t v___x_2007_; 
v___x_2006_ = 95;
v___x_2007_ = lean_uint8_dec_eq(v___x_2000_, v___x_2006_);
if (v___x_2007_ == 0)
{
uint8_t v___x_2008_; uint8_t v___x_2009_; 
v___x_2008_ = 126;
v___x_2009_ = lean_uint8_dec_eq(v___x_2000_, v___x_2008_);
if (v___x_2009_ == 0)
{
uint8_t v___x_2010_; uint8_t v___x_2011_; 
v___x_2010_ = 33;
v___x_2011_ = lean_uint8_dec_eq(v___x_2000_, v___x_2010_);
if (v___x_2011_ == 0)
{
uint8_t v___x_2012_; uint8_t v___x_2013_; 
v___x_2012_ = 36;
v___x_2013_ = lean_uint8_dec_eq(v___x_2000_, v___x_2012_);
if (v___x_2013_ == 0)
{
uint8_t v___x_2014_; uint8_t v___x_2015_; 
v___x_2014_ = 38;
v___x_2015_ = lean_uint8_dec_eq(v___x_2000_, v___x_2014_);
if (v___x_2015_ == 0)
{
uint8_t v___x_2016_; uint8_t v___x_2017_; 
v___x_2016_ = 39;
v___x_2017_ = lean_uint8_dec_eq(v___x_2000_, v___x_2016_);
if (v___x_2017_ == 0)
{
uint8_t v___x_2018_; uint8_t v___x_2019_; 
v___x_2018_ = 40;
v___x_2019_ = lean_uint8_dec_eq(v___x_2000_, v___x_2018_);
if (v___x_2019_ == 0)
{
uint8_t v___x_2020_; uint8_t v___x_2021_; 
v___x_2020_ = 41;
v___x_2021_ = lean_uint8_dec_eq(v___x_2000_, v___x_2020_);
if (v___x_2021_ == 0)
{
uint8_t v___x_2022_; uint8_t v___x_2023_; 
v___x_2022_ = 42;
v___x_2023_ = lean_uint8_dec_eq(v___x_2000_, v___x_2022_);
if (v___x_2023_ == 0)
{
uint8_t v___x_2024_; uint8_t v___x_2025_; 
v___x_2024_ = 43;
v___x_2025_ = lean_uint8_dec_eq(v___x_2000_, v___x_2024_);
if (v___x_2025_ == 0)
{
uint8_t v___x_2026_; uint8_t v___x_2027_; 
v___x_2026_ = 44;
v___x_2027_ = lean_uint8_dec_eq(v___x_2000_, v___x_2026_);
if (v___x_2027_ == 0)
{
uint8_t v___x_2028_; uint8_t v___x_2029_; 
v___x_2028_ = 59;
v___x_2029_ = lean_uint8_dec_eq(v___x_2000_, v___x_2028_);
if (v___x_2029_ == 0)
{
uint8_t v___x_2030_; uint8_t v___x_2031_; 
v___x_2030_ = 61;
v___x_2031_ = lean_uint8_dec_eq(v___x_2000_, v___x_2030_);
if (v___x_2031_ == 0)
{
uint8_t v___x_2032_; uint8_t v___x_2033_; 
v___x_2032_ = 58;
v___x_2033_ = lean_uint8_dec_eq(v___x_2000_, v___x_2032_);
if (v___x_2033_ == 0)
{
uint8_t v___x_2034_; uint8_t v___x_2035_; 
v___x_2034_ = 64;
v___x_2035_ = lean_uint8_dec_eq(v___x_2000_, v___x_2034_);
if (v___x_2035_ == 0)
{
uint8_t v___x_2036_; uint8_t v___x_2037_; 
v___x_2036_ = 37;
v___x_2037_ = lean_uint8_dec_eq(v___x_2000_, v___x_2036_);
if (v___x_2037_ == 0)
{
uint8_t v___x_2038_; uint8_t v___x_2039_; 
v___x_2038_ = 47;
v___x_2039_ = lean_uint8_dec_eq(v___x_2000_, v___x_2038_);
if (v___x_2039_ == 0)
{
v_pos_1991_ = v_a_1906_;
v_array_1992_ = v_array_1915_;
v_idx_1993_ = v_idx_1916_;
v_res_1994_ = v_isAbsolute_1917_;
goto v___jp_1990_;
}
else
{
v_pos_1991_ = v_a_1906_;
v_array_1992_ = v_array_1915_;
v_idx_1993_ = v_idx_1916_;
v_res_1994_ = v___x_2039_;
goto v___jp_1990_;
}
}
else
{
v_pos_1991_ = v_a_1906_;
v_array_1992_ = v_array_1915_;
v_idx_1993_ = v_idx_1916_;
v_res_1994_ = v___x_2037_;
goto v___jp_1990_;
}
}
else
{
v_pos_1991_ = v_a_1906_;
v_array_1992_ = v_array_1915_;
v_idx_1993_ = v_idx_1916_;
v_res_1994_ = v___x_2035_;
goto v___jp_1990_;
}
}
else
{
v_pos_1991_ = v_a_1906_;
v_array_1992_ = v_array_1915_;
v_idx_1993_ = v_idx_1916_;
v_res_1994_ = v___x_2033_;
goto v___jp_1990_;
}
}
else
{
v_pos_1991_ = v_a_1906_;
v_array_1992_ = v_array_1915_;
v_idx_1993_ = v_idx_1916_;
v_res_1994_ = v___x_2031_;
goto v___jp_1990_;
}
}
else
{
v_pos_1991_ = v_a_1906_;
v_array_1992_ = v_array_1915_;
v_idx_1993_ = v_idx_1916_;
v_res_1994_ = v___x_2029_;
goto v___jp_1990_;
}
}
else
{
v_pos_1991_ = v_a_1906_;
v_array_1992_ = v_array_1915_;
v_idx_1993_ = v_idx_1916_;
v_res_1994_ = v___x_2027_;
goto v___jp_1990_;
}
}
else
{
v_pos_1991_ = v_a_1906_;
v_array_1992_ = v_array_1915_;
v_idx_1993_ = v_idx_1916_;
v_res_1994_ = v___x_2025_;
goto v___jp_1990_;
}
}
else
{
v_pos_1991_ = v_a_1906_;
v_array_1992_ = v_array_1915_;
v_idx_1993_ = v_idx_1916_;
v_res_1994_ = v___x_2023_;
goto v___jp_1990_;
}
}
else
{
v_pos_1991_ = v_a_1906_;
v_array_1992_ = v_array_1915_;
v_idx_1993_ = v_idx_1916_;
v_res_1994_ = v___x_2021_;
goto v___jp_1990_;
}
}
else
{
v_pos_1991_ = v_a_1906_;
v_array_1992_ = v_array_1915_;
v_idx_1993_ = v_idx_1916_;
v_res_1994_ = v___x_2019_;
goto v___jp_1990_;
}
}
else
{
v_pos_1991_ = v_a_1906_;
v_array_1992_ = v_array_1915_;
v_idx_1993_ = v_idx_1916_;
v_res_1994_ = v___x_2017_;
goto v___jp_1990_;
}
}
else
{
v_pos_1991_ = v_a_1906_;
v_array_1992_ = v_array_1915_;
v_idx_1993_ = v_idx_1916_;
v_res_1994_ = v___x_2015_;
goto v___jp_1990_;
}
}
else
{
v_pos_1991_ = v_a_1906_;
v_array_1992_ = v_array_1915_;
v_idx_1993_ = v_idx_1916_;
v_res_1994_ = v___x_2013_;
goto v___jp_1990_;
}
}
else
{
v_pos_1991_ = v_a_1906_;
v_array_1992_ = v_array_1915_;
v_idx_1993_ = v_idx_1916_;
v_res_1994_ = v___x_2011_;
goto v___jp_1990_;
}
}
else
{
v_pos_1991_ = v_a_1906_;
v_array_1992_ = v_array_1915_;
v_idx_1993_ = v_idx_1916_;
v_res_1994_ = v___x_2009_;
goto v___jp_1990_;
}
}
else
{
v_pos_1991_ = v_a_1906_;
v_array_1992_ = v_array_1915_;
v_idx_1993_ = v_idx_1916_;
v_res_1994_ = v___x_2007_;
goto v___jp_1990_;
}
}
else
{
v_pos_1991_ = v_a_1906_;
v_array_1992_ = v_array_1915_;
v_idx_1993_ = v_idx_1916_;
v_res_1994_ = v___x_2005_;
goto v___jp_1990_;
}
}
else
{
v_pos_1991_ = v_a_1906_;
v_array_1992_ = v_array_1915_;
v_idx_1993_ = v_idx_1916_;
v_res_1994_ = v___x_2003_;
goto v___jp_1990_;
}
}
v___jp_2040_:
{
uint8_t v___x_2041_; uint8_t v___x_2042_; 
v___x_2041_ = 65;
v___x_2042_ = lean_uint8_dec_le(v___x_2041_, v___x_2000_);
if (v___x_2042_ == 0)
{
goto v___jp_2001_;
}
else
{
uint8_t v___x_2043_; uint8_t v___x_2044_; 
v___x_2043_ = 90;
v___x_2044_ = lean_uint8_dec_le(v___x_2000_, v___x_2043_);
if (v___x_2044_ == 0)
{
goto v___jp_2001_;
}
else
{
v_pos_1991_ = v_a_1906_;
v_array_1992_ = v_array_1915_;
v_idx_1993_ = v_idx_1916_;
v_res_1994_ = v___x_2044_;
goto v___jp_1990_;
}
}
}
v___jp_2045_:
{
uint8_t v___x_2046_; uint8_t v___x_2047_; 
v___x_2046_ = 97;
v___x_2047_ = lean_uint8_dec_le(v___x_2046_, v___x_2000_);
if (v___x_2047_ == 0)
{
goto v___jp_2040_;
}
else
{
uint8_t v___x_2048_; uint8_t v___x_2049_; 
v___x_2048_ = 122;
v___x_2049_ = lean_uint8_dec_le(v___x_2000_, v___x_2048_);
if (v___x_2049_ == 0)
{
goto v___jp_2040_;
}
else
{
v_pos_1991_ = v_a_1906_;
v_array_1992_ = v_array_1915_;
v_idx_1993_ = v_idx_1916_;
v_res_1994_ = v___x_2049_;
goto v___jp_1990_;
}
}
}
}
v___jp_1907_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__1));
v___x_1910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___y_1908_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
return v___x_1910_;
}
v___jp_1911_:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1913_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__3));
v___x_1914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___y_1912_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
return v___x_1914_;
}
v___jp_1920_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1924_, 0, v_segments_1919_);
lean_ctor_set(v___x_1924_, 1, v_totalLength_1922_);
v___x_1925_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(v_config_1903_, v___x_1924_, v___y_1923_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_res_1926_; lean_object* v_pos_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1936_; 
v_res_1926_ = lean_ctor_get(v___x_1925_, 1);
v_pos_1927_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1929_ = v___x_1925_;
v_isShared_1930_ = v_isSharedCheck_1936_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_res_1926_);
lean_inc(v_pos_1927_);
lean_dec(v___x_1925_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1936_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v_fst_1931_; lean_object* v___x_1932_; lean_object* v___x_1934_; 
v_fst_1931_ = lean_ctor_get(v_res_1926_, 0);
lean_inc(v_fst_1931_);
lean_dec(v_res_1926_);
v___x_1932_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1932_, 0, v_fst_1931_);
lean_ctor_set_uint8(v___x_1932_, sizeof(void*)*1, v_isAbsolute_1921_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 1, v___x_1932_);
v___x_1934_ = v___x_1929_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_pos_1927_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v___x_1932_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
else
{
lean_object* v_pos_1937_; lean_object* v_err_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
v_pos_1937_ = lean_ctor_get(v___x_1925_, 0);
v_err_1938_ = lean_ctor_get(v___x_1925_, 1);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1925_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_err_1938_);
lean_inc(v_pos_1937_);
lean_dec(v___x_1925_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_pos_1937_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v_err_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
v___jp_1946_:
{
lean_object* v___x_1950_; uint8_t v___x_1951_; 
v___x_1950_ = lean_byte_array_size(v_array_1948_);
v___x_1951_ = lean_nat_dec_lt(v_idx_1949_, v___x_1950_);
if (v___x_1951_ == 0)
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
lean_dec(v_idx_1949_);
lean_dec_ref(v_array_1948_);
lean_dec_ref(v_config_1903_);
v___x_1952_ = lean_box(0);
v___x_1953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1953_, 0, v_pos_1947_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
return v___x_1953_;
}
else
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
lean_dec_ref(v_pos_1947_);
v___x_1954_ = lean_unsigned_to_nat(1u);
v___x_1955_ = lean_nat_add(v_idx_1949_, v___x_1954_);
lean_dec(v_idx_1949_);
v___x_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1956_, 0, v_array_1948_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
v_isAbsolute_1921_ = v___x_1951_;
v_totalLength_1922_ = v___x_1954_;
v___y_1923_ = v___x_1956_;
goto v___jp_1920_;
}
}
v___jp_1957_:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__5));
v___x_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___y_1958_);
lean_ctor_set(v___x_1960_, 1, v___x_1959_);
return v___x_1960_;
}
v___jp_1961_:
{
if (v_allowEmpty_1905_ == 0)
{
v___y_1908_ = v_pos_1963_;
goto v___jp_1907_;
}
else
{
if (v_res_1964_ == 0)
{
if (v___y_1962_ == 0)
{
v___y_1958_ = v_pos_1963_;
goto v___jp_1957_;
}
else
{
v___y_1908_ = v_pos_1963_;
goto v___jp_1907_;
}
}
else
{
v___y_1958_ = v_pos_1963_;
goto v___jp_1957_;
}
}
}
v___jp_1965_:
{
if (v_res_1968_ == 0)
{
if (v_forceAbsolute_1904_ == 0)
{
v_isAbsolute_1921_ = v_isAbsolute_1917_;
v_totalLength_1922_ = v___x_1918_;
v___y_1923_ = v_pos_1967_;
goto v___jp_1920_;
}
else
{
lean_object* v_array_1969_; lean_object* v_idx_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
lean_dec_ref(v_config_1903_);
v_array_1969_ = lean_ctor_get(v_pos_1967_, 0);
v_idx_1970_ = lean_ctor_get(v_pos_1967_, 1);
v___x_1971_ = lean_byte_array_size(v_array_1969_);
v___x_1972_ = lean_nat_dec_lt(v_idx_1970_, v___x_1971_);
if (v___x_1972_ == 0)
{
v___y_1962_ = v___y_1966_;
v_pos_1963_ = v_pos_1967_;
v_res_1964_ = v_forceAbsolute_1904_;
goto v___jp_1961_;
}
else
{
v___y_1962_ = v___y_1966_;
v_pos_1963_ = v_pos_1967_;
v_res_1964_ = v_res_1968_;
goto v___jp_1961_;
}
}
}
else
{
lean_object* v_array_1973_; lean_object* v_idx_1974_; 
v_array_1973_ = lean_ctor_get(v_pos_1967_, 0);
lean_inc_ref(v_array_1973_);
v_idx_1974_ = lean_ctor_get(v_pos_1967_, 1);
lean_inc(v_idx_1974_);
v_pos_1947_ = v_pos_1967_;
v_array_1948_ = v_array_1973_;
v_idx_1949_ = v_idx_1974_;
goto v___jp_1946_;
}
}
v___jp_1975_:
{
lean_object* v_array_1979_; lean_object* v_idx_1980_; lean_object* v___x_1981_; uint8_t v___x_1982_; 
v_array_1979_ = lean_ctor_get(v___y_1976_, 0);
v_idx_1980_ = lean_ctor_get(v___y_1976_, 1);
v___x_1981_ = lean_byte_array_size(v_array_1979_);
v___x_1982_ = lean_nat_dec_lt(v_idx_1980_, v___x_1981_);
if (v___x_1982_ == 0)
{
v___y_1966_ = v___y_1977_;
v_pos_1967_ = v___y_1976_;
v_res_1968_ = v___y_1978_;
goto v___jp_1965_;
}
else
{
uint8_t v___x_1983_; uint8_t v___x_1984_; uint8_t v___x_1985_; 
v___x_1983_ = lean_byte_array_fget(v_array_1979_, v_idx_1980_);
v___x_1984_ = 47;
v___x_1985_ = lean_uint8_dec_eq(v___x_1983_, v___x_1984_);
if (v___x_1985_ == 0)
{
v___y_1966_ = v___y_1977_;
v_pos_1967_ = v___y_1976_;
v_res_1968_ = v___y_1978_;
goto v___jp_1965_;
}
else
{
lean_inc(v_idx_1980_);
lean_inc_ref(v_array_1979_);
v_pos_1947_ = v___y_1976_;
v_array_1948_ = v_array_1979_;
v_idx_1949_ = v_idx_1980_;
goto v___jp_1946_;
}
}
}
v___jp_1986_:
{
if (v_allowEmpty_1905_ == 0)
{
if (v_res_1989_ == 0)
{
if (v___y_1987_ == 0)
{
lean_dec_ref(v_config_1903_);
v___y_1912_ = v_pos_1988_;
goto v___jp_1911_;
}
else
{
v___y_1976_ = v_pos_1988_;
v___y_1977_ = v___y_1987_;
v___y_1978_ = v_res_1989_;
goto v___jp_1975_;
}
}
else
{
lean_dec_ref(v_config_1903_);
v___y_1912_ = v_pos_1988_;
goto v___jp_1911_;
}
}
else
{
v___y_1976_ = v_pos_1988_;
v___y_1977_ = v___y_1987_;
v___y_1978_ = v_isAbsolute_1917_;
goto v___jp_1975_;
}
}
v___jp_1990_:
{
lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1995_ = lean_byte_array_size(v_array_1992_);
lean_dec_ref(v_array_1992_);
v___x_1996_ = lean_nat_dec_lt(v_idx_1993_, v___x_1995_);
lean_dec(v_idx_1993_);
if (v___x_1996_ == 0)
{
uint8_t v___x_1997_; 
v___x_1997_ = 1;
v___y_1987_ = v_res_1994_;
v_pos_1988_ = v_pos_1991_;
v_res_1989_ = v___x_1997_;
goto v___jp_1986_;
}
else
{
v___y_1987_ = v_res_1994_;
v_pos_1988_ = v_pos_1991_;
v_res_1989_ = v_isAbsolute_1917_;
goto v___jp_1986_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath___boxed(lean_object* v_config_2054_, lean_object* v_forceAbsolute_2055_, lean_object* v_allowEmpty_2056_, lean_object* v_a_2057_){
_start:
{
uint8_t v_forceAbsolute_boxed_2058_; uint8_t v_allowEmpty_boxed_2059_; lean_object* v_res_2060_; 
v_forceAbsolute_boxed_2058_ = lean_unbox(v_forceAbsolute_2055_);
v_allowEmpty_boxed_2059_ = lean_unbox(v_allowEmpty_2056_);
v_res_2060_ = l_Std_Http_URI_Parser_parsePath(v_config_2054_, v_forceAbsolute_boxed_2058_, v_allowEmpty_boxed_2059_, v_a_2057_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0(lean_object* v_config_2061_, lean_object* v_inst_2062_, lean_object* v_a_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v___x_2065_; 
v___x_2065_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(v_config_2061_, v_a_2063_, v___y_2064_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0(lean_object* v_config_2066_, lean_object* v_inst_2067_, lean_object* v_a_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v___x_2070_; 
v___x_2070_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_2066_, v_a_2068_, v___y_2069_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg(){
_start:
{
lean_object* v___x_2072_; 
v___x_2072_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0));
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg___boxed(lean_object* v___dummy_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg();
return v_res_2074_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2075_; 
v___x_2075_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg();
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(lean_object* v_s_2076_){
_start:
{
lean_object* v___x_2077_; 
v___x_2077_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___boxed(lean_object* v_s_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(v_s_2078_);
lean_dec_ref(v_s_2078_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg(){
_start:
{
lean_object* v___x_2081_; 
v___x_2081_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0));
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg___boxed(lean_object* v___dummy_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg();
return v_res_2083_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2084_; 
v___x_2084_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg();
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(lean_object* v_s_2085_){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___boxed(lean_object* v_s_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(v_s_2087_);
lean_dec_ref(v_s_2087_);
return v_res_2088_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(uint8_t v_c_2089_){
_start:
{
uint8_t v___x_2141_; uint8_t v___x_2142_; 
v___x_2141_ = 48;
v___x_2142_ = lean_uint8_dec_le(v___x_2141_, v_c_2089_);
if (v___x_2142_ == 0)
{
goto v___jp_2136_;
}
else
{
uint8_t v___x_2143_; uint8_t v___x_2144_; 
v___x_2143_ = 57;
v___x_2144_ = lean_uint8_dec_le(v_c_2089_, v___x_2143_);
if (v___x_2144_ == 0)
{
goto v___jp_2136_;
}
else
{
return v___x_2144_;
}
}
v___jp_2090_:
{
uint8_t v___x_2091_; uint8_t v___x_2092_; 
v___x_2091_ = 45;
v___x_2092_ = lean_uint8_dec_eq(v_c_2089_, v___x_2091_);
if (v___x_2092_ == 0)
{
uint8_t v___x_2093_; uint8_t v___x_2094_; 
v___x_2093_ = 46;
v___x_2094_ = lean_uint8_dec_eq(v_c_2089_, v___x_2093_);
if (v___x_2094_ == 0)
{
uint8_t v___x_2095_; uint8_t v___x_2096_; 
v___x_2095_ = 95;
v___x_2096_ = lean_uint8_dec_eq(v_c_2089_, v___x_2095_);
if (v___x_2096_ == 0)
{
uint8_t v___x_2097_; uint8_t v___x_2098_; 
v___x_2097_ = 126;
v___x_2098_ = lean_uint8_dec_eq(v_c_2089_, v___x_2097_);
if (v___x_2098_ == 0)
{
uint8_t v___x_2099_; uint8_t v___x_2100_; 
v___x_2099_ = 33;
v___x_2100_ = lean_uint8_dec_eq(v_c_2089_, v___x_2099_);
if (v___x_2100_ == 0)
{
uint8_t v___x_2101_; uint8_t v___x_2102_; 
v___x_2101_ = 36;
v___x_2102_ = lean_uint8_dec_eq(v_c_2089_, v___x_2101_);
if (v___x_2102_ == 0)
{
uint8_t v___x_2103_; uint8_t v___x_2104_; 
v___x_2103_ = 38;
v___x_2104_ = lean_uint8_dec_eq(v_c_2089_, v___x_2103_);
if (v___x_2104_ == 0)
{
uint8_t v___x_2105_; uint8_t v___x_2106_; 
v___x_2105_ = 39;
v___x_2106_ = lean_uint8_dec_eq(v_c_2089_, v___x_2105_);
if (v___x_2106_ == 0)
{
uint8_t v___x_2107_; uint8_t v___x_2108_; 
v___x_2107_ = 40;
v___x_2108_ = lean_uint8_dec_eq(v_c_2089_, v___x_2107_);
if (v___x_2108_ == 0)
{
uint8_t v___x_2109_; uint8_t v___x_2110_; 
v___x_2109_ = 41;
v___x_2110_ = lean_uint8_dec_eq(v_c_2089_, v___x_2109_);
if (v___x_2110_ == 0)
{
uint8_t v___x_2111_; uint8_t v___x_2112_; 
v___x_2111_ = 42;
v___x_2112_ = lean_uint8_dec_eq(v_c_2089_, v___x_2111_);
if (v___x_2112_ == 0)
{
uint8_t v___x_2113_; uint8_t v___x_2114_; 
v___x_2113_ = 43;
v___x_2114_ = lean_uint8_dec_eq(v_c_2089_, v___x_2113_);
if (v___x_2114_ == 0)
{
uint8_t v___x_2115_; uint8_t v___x_2116_; 
v___x_2115_ = 44;
v___x_2116_ = lean_uint8_dec_eq(v_c_2089_, v___x_2115_);
if (v___x_2116_ == 0)
{
uint8_t v___x_2117_; uint8_t v___x_2118_; 
v___x_2117_ = 59;
v___x_2118_ = lean_uint8_dec_eq(v_c_2089_, v___x_2117_);
if (v___x_2118_ == 0)
{
uint8_t v___x_2119_; uint8_t v___x_2120_; 
v___x_2119_ = 61;
v___x_2120_ = lean_uint8_dec_eq(v_c_2089_, v___x_2119_);
if (v___x_2120_ == 0)
{
uint8_t v___x_2121_; uint8_t v___x_2122_; 
v___x_2121_ = 58;
v___x_2122_ = lean_uint8_dec_eq(v_c_2089_, v___x_2121_);
if (v___x_2122_ == 0)
{
uint8_t v___x_2123_; uint8_t v___x_2124_; 
v___x_2123_ = 64;
v___x_2124_ = lean_uint8_dec_eq(v_c_2089_, v___x_2123_);
if (v___x_2124_ == 0)
{
uint8_t v___x_2125_; uint8_t v___x_2126_; 
v___x_2125_ = 47;
v___x_2126_ = lean_uint8_dec_eq(v_c_2089_, v___x_2125_);
if (v___x_2126_ == 0)
{
uint8_t v___x_2127_; uint8_t v___x_2128_; 
v___x_2127_ = 63;
v___x_2128_ = lean_uint8_dec_eq(v_c_2089_, v___x_2127_);
if (v___x_2128_ == 0)
{
uint8_t v___x_2129_; uint8_t v___x_2130_; 
v___x_2129_ = 37;
v___x_2130_ = lean_uint8_dec_eq(v_c_2089_, v___x_2129_);
return v___x_2130_;
}
else
{
return v___x_2128_;
}
}
else
{
return v___x_2126_;
}
}
else
{
return v___x_2124_;
}
}
else
{
return v___x_2122_;
}
}
else
{
return v___x_2120_;
}
}
else
{
return v___x_2118_;
}
}
else
{
return v___x_2116_;
}
}
else
{
return v___x_2114_;
}
}
else
{
return v___x_2112_;
}
}
else
{
return v___x_2110_;
}
}
else
{
return v___x_2108_;
}
}
else
{
return v___x_2106_;
}
}
else
{
return v___x_2104_;
}
}
else
{
return v___x_2102_;
}
}
else
{
return v___x_2100_;
}
}
else
{
return v___x_2098_;
}
}
else
{
return v___x_2096_;
}
}
else
{
return v___x_2094_;
}
}
else
{
return v___x_2092_;
}
}
v___jp_2131_:
{
uint8_t v___x_2132_; uint8_t v___x_2133_; 
v___x_2132_ = 65;
v___x_2133_ = lean_uint8_dec_le(v___x_2132_, v_c_2089_);
if (v___x_2133_ == 0)
{
goto v___jp_2090_;
}
else
{
uint8_t v___x_2134_; uint8_t v___x_2135_; 
v___x_2134_ = 90;
v___x_2135_ = lean_uint8_dec_le(v_c_2089_, v___x_2134_);
if (v___x_2135_ == 0)
{
goto v___jp_2090_;
}
else
{
return v___x_2135_;
}
}
}
v___jp_2136_:
{
uint8_t v___x_2137_; uint8_t v___x_2138_; 
v___x_2137_ = 97;
v___x_2138_ = lean_uint8_dec_le(v___x_2137_, v_c_2089_);
if (v___x_2138_ == 0)
{
goto v___jp_2131_;
}
else
{
uint8_t v___x_2139_; uint8_t v___x_2140_; 
v___x_2139_ = 122;
v___x_2140_ = lean_uint8_dec_le(v_c_2089_, v___x_2139_);
if (v___x_2140_ == 0)
{
goto v___jp_2131_;
}
else
{
return v___x_2140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0___boxed(lean_object* v_c_2145_){
_start:
{
uint8_t v_c_boxed_2146_; uint8_t v_res_2147_; lean_object* v_r_2148_; 
v_c_boxed_2146_ = lean_unbox(v_c_2145_);
v_res_2147_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(v_c_boxed_2146_);
v_r_2148_ = lean_box(v_res_2147_);
return v_r_2148_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(lean_object* v___x_2149_, lean_object* v___x_2150_, lean_object* v_a_2151_, lean_object* v_b_2152_){
_start:
{
lean_object* v_it_2154_; 
if (lean_obj_tag(v_a_2151_) == 0)
{
lean_object* v_currPos_2158_; lean_object* v_searcher_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2185_; 
v_currPos_2158_ = lean_ctor_get(v_a_2151_, 0);
v_searcher_2159_ = lean_ctor_get(v_a_2151_, 1);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_a_2151_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2161_ = v_a_2151_;
v_isShared_2162_ = v_isSharedCheck_2185_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_searcher_2159_);
lean_inc(v_currPos_2158_);
lean_dec(v_a_2151_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2185_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v_str_2163_; lean_object* v_startInclusive_2164_; lean_object* v_endExclusive_2165_; lean_object* v___x_2166_; uint8_t v_decide_2167_; 
v_str_2163_ = lean_ctor_get(v___x_2149_, 0);
v_startInclusive_2164_ = lean_ctor_get(v___x_2149_, 1);
v_endExclusive_2165_ = lean_ctor_get(v___x_2149_, 2);
v___x_2166_ = lean_nat_sub(v_endExclusive_2165_, v_startInclusive_2164_);
v_decide_2167_ = lean_nat_dec_eq(v_searcher_2159_, v___x_2166_);
lean_dec(v___x_2166_);
if (v_decide_2167_ == 0)
{
uint32_t v___x_2168_; lean_object* v___x_2169_; uint32_t v___x_2170_; uint8_t v___x_2171_; 
v___x_2168_ = 38;
v___x_2169_ = lean_nat_add(v_startInclusive_2164_, v_searcher_2159_);
v___x_2170_ = lean_string_utf8_get_fast(v_str_2163_, v___x_2169_);
v___x_2171_ = lean_uint32_dec_eq(v___x_2170_, v___x_2168_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2175_; 
lean_dec(v_searcher_2159_);
v___x_2172_ = lean_string_utf8_next_fast(v_str_2163_, v___x_2169_);
lean_dec(v___x_2169_);
v___x_2173_ = lean_nat_sub(v___x_2172_, v_startInclusive_2164_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 1, v___x_2173_);
v___x_2175_ = v___x_2161_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_currPos_2158_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v___x_2173_);
v___x_2175_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
v_a_2151_ = v___x_2175_;
goto _start;
}
}
else
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v_nextIt_2182_; 
lean_dec(v_currPos_2158_);
v___x_2178_ = lean_string_utf8_next_fast(v_str_2163_, v___x_2169_);
v___x_2179_ = lean_nat_sub(v___x_2178_, v___x_2169_);
lean_dec(v___x_2169_);
v___x_2180_ = lean_nat_add(v_searcher_2159_, v___x_2179_);
lean_dec(v___x_2179_);
lean_dec(v_searcher_2159_);
lean_inc(v___x_2180_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 1, v___x_2180_);
lean_ctor_set(v___x_2161_, 0, v___x_2180_);
v_nextIt_2182_ = v___x_2161_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v___x_2180_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v___x_2180_);
v_nextIt_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
v_it_2154_ = v_nextIt_2182_;
goto v___jp_2153_;
}
}
}
else
{
lean_object* v___x_2184_; 
lean_del_object(v___x_2161_);
lean_dec(v_searcher_2159_);
lean_dec(v_currPos_2158_);
v___x_2184_ = lean_box(1);
v_it_2154_ = v___x_2184_;
goto v___jp_2153_;
}
}
}
else
{
return v_b_2152_;
}
v___jp_2153_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = lean_unsigned_to_nat(1u);
v___x_2156_ = lean_nat_add(v_b_2152_, v___x_2155_);
lean_dec(v_b_2152_);
v_a_2151_ = v_it_2154_;
v_b_2152_ = v___x_2156_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg___boxed(lean_object* v___x_2186_, lean_object* v___x_2187_, lean_object* v_a_2188_, lean_object* v_b_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2186_, v___x_2187_, v_a_2188_, v_b_2189_);
lean_dec(v___x_2187_);
lean_dec_ref(v___x_2186_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(lean_object* v___x_2191_, lean_object* v___x_2192_, lean_object* v___x_2193_, lean_object* v_a_2194_, lean_object* v_b_2195_){
_start:
{
lean_object* v_it_2197_; 
if (lean_obj_tag(v_a_2194_) == 0)
{
lean_object* v_currPos_2201_; lean_object* v_searcher_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2228_; 
v_currPos_2201_ = lean_ctor_get(v_a_2194_, 0);
v_searcher_2202_ = lean_ctor_get(v_a_2194_, 1);
v_isSharedCheck_2228_ = !lean_is_exclusive(v_a_2194_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2204_ = v_a_2194_;
v_isShared_2205_ = v_isSharedCheck_2228_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_searcher_2202_);
lean_inc(v_currPos_2201_);
lean_dec(v_a_2194_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2228_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v_str_2206_; lean_object* v_startInclusive_2207_; lean_object* v_endExclusive_2208_; lean_object* v___x_2209_; uint8_t v_decide_2210_; 
v_str_2206_ = lean_ctor_get(v___x_2192_, 0);
v_startInclusive_2207_ = lean_ctor_get(v___x_2192_, 1);
v_endExclusive_2208_ = lean_ctor_get(v___x_2192_, 2);
v___x_2209_ = lean_nat_sub(v_endExclusive_2208_, v_startInclusive_2207_);
v_decide_2210_ = lean_nat_dec_eq(v_searcher_2202_, v___x_2209_);
lean_dec(v___x_2209_);
if (v_decide_2210_ == 0)
{
lean_object* v___x_2211_; uint32_t v___x_2212_; uint32_t v___x_2213_; uint8_t v___x_2214_; 
v___x_2211_ = lean_nat_add(v_startInclusive_2207_, v_searcher_2202_);
v___x_2212_ = lean_string_utf8_get_fast(v_str_2206_, v___x_2211_);
v___x_2213_ = 38;
v___x_2214_ = lean_uint32_dec_eq(v___x_2212_, v___x_2213_);
if (v___x_2214_ == 0)
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2218_; 
lean_dec(v_searcher_2202_);
v___x_2215_ = lean_string_utf8_next_fast(v_str_2206_, v___x_2211_);
lean_dec(v___x_2211_);
v___x_2216_ = lean_nat_sub(v___x_2215_, v_startInclusive_2207_);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 1, v___x_2216_);
v___x_2218_ = v___x_2204_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_currPos_2201_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v___x_2216_);
v___x_2218_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
lean_object* v___x_2219_; 
v___x_2219_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2192_, v___x_2193_, v___x_2218_, v_b_2195_);
return v___x_2219_;
}
}
else
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v_nextIt_2225_; 
lean_dec(v_currPos_2201_);
v___x_2221_ = lean_string_utf8_next_fast(v_str_2206_, v___x_2211_);
v___x_2222_ = lean_nat_sub(v___x_2221_, v___x_2211_);
lean_dec(v___x_2211_);
v___x_2223_ = lean_nat_add(v_searcher_2202_, v___x_2222_);
lean_dec(v___x_2222_);
lean_dec(v_searcher_2202_);
lean_inc(v___x_2223_);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 1, v___x_2223_);
lean_ctor_set(v___x_2204_, 0, v___x_2223_);
v_nextIt_2225_ = v___x_2204_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2223_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v___x_2223_);
v_nextIt_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
v_it_2197_ = v_nextIt_2225_;
goto v___jp_2196_;
}
}
}
else
{
lean_object* v___x_2227_; 
lean_del_object(v___x_2204_);
lean_dec(v_searcher_2202_);
lean_dec(v_currPos_2201_);
v___x_2227_ = lean_box(1);
v_it_2197_ = v___x_2227_;
goto v___jp_2196_;
}
}
}
else
{
return v_b_2195_;
}
v___jp_2196_:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2198_ = lean_unsigned_to_nat(1u);
v___x_2199_ = lean_nat_add(v_b_2195_, v___x_2198_);
lean_dec(v_b_2195_);
v___x_2200_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2192_, v___x_2193_, v_it_2197_, v___x_2199_);
return v___x_2200_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg___boxed(lean_object* v___x_2229_, lean_object* v___x_2230_, lean_object* v___x_2231_, lean_object* v_a_2232_, lean_object* v_b_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2229_, v___x_2230_, v___x_2231_, v_a_2232_, v_b_2233_);
lean_dec(v___x_2231_);
lean_dec_ref(v___x_2230_);
lean_dec_ref(v___x_2229_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(lean_object* v_out_2235_, lean_object* v_a_2236_, lean_object* v_b_2237_){
_start:
{
if (lean_obj_tag(v_a_2236_) == 0)
{
lean_object* v_currPos_2238_; lean_object* v_searcher_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2278_; 
v_currPos_2238_ = lean_ctor_get(v_a_2236_, 0);
v_searcher_2239_ = lean_ctor_get(v_a_2236_, 1);
v_isSharedCheck_2278_ = !lean_is_exclusive(v_a_2236_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2241_ = v_a_2236_;
v_isShared_2242_ = v_isSharedCheck_2278_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_searcher_2239_);
lean_inc(v_currPos_2238_);
lean_dec(v_a_2236_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2278_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v_str_2243_; lean_object* v_startInclusive_2244_; lean_object* v_endExclusive_2245_; lean_object* v_it_2247_; lean_object* v_startInclusive_2248_; lean_object* v_endExclusive_2249_; lean_object* v___x_2256_; uint8_t v_decide_2257_; 
v_str_2243_ = lean_ctor_get(v_out_2235_, 0);
v_startInclusive_2244_ = lean_ctor_get(v_out_2235_, 1);
v_endExclusive_2245_ = lean_ctor_get(v_out_2235_, 2);
v___x_2256_ = lean_nat_sub(v_endExclusive_2245_, v_startInclusive_2244_);
v_decide_2257_ = lean_nat_dec_eq(v_searcher_2239_, v___x_2256_);
if (v_decide_2257_ == 0)
{
uint32_t v___x_2258_; lean_object* v___x_2259_; uint32_t v___x_2260_; uint8_t v___x_2261_; 
lean_dec(v___x_2256_);
v___x_2258_ = 61;
v___x_2259_ = lean_nat_add(v_startInclusive_2244_, v_searcher_2239_);
v___x_2260_ = lean_string_utf8_get_fast(v_str_2243_, v___x_2259_);
v___x_2261_ = lean_uint32_dec_eq(v___x_2260_, v___x_2258_);
if (v___x_2261_ == 0)
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2265_; 
lean_dec(v_searcher_2239_);
v___x_2262_ = lean_string_utf8_next_fast(v_str_2243_, v___x_2259_);
lean_dec(v___x_2259_);
v___x_2263_ = lean_nat_sub(v___x_2262_, v_startInclusive_2244_);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 1, v___x_2263_);
v___x_2265_ = v___x_2241_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_currPos_2238_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v___x_2263_);
v___x_2265_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
v_a_2236_ = v___x_2265_;
goto _start;
}
}
else
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v_slice_2271_; lean_object* v_nextIt_2273_; 
v___x_2268_ = lean_string_utf8_next_fast(v_str_2243_, v___x_2259_);
v___x_2269_ = lean_nat_sub(v___x_2268_, v___x_2259_);
lean_dec(v___x_2259_);
v___x_2270_ = lean_nat_add(v_searcher_2239_, v___x_2269_);
lean_dec(v___x_2269_);
v_slice_2271_ = l_String_Slice_subslice_x21(v_out_2235_, v_currPos_2238_, v_searcher_2239_);
lean_inc(v___x_2270_);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 1, v___x_2270_);
lean_ctor_set(v___x_2241_, 0, v___x_2270_);
v_nextIt_2273_ = v___x_2241_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2270_);
lean_ctor_set(v_reuseFailAlloc_2276_, 1, v___x_2270_);
v_nextIt_2273_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
lean_object* v_startInclusive_2274_; lean_object* v_endExclusive_2275_; 
v_startInclusive_2274_ = lean_ctor_get(v_slice_2271_, 0);
lean_inc(v_startInclusive_2274_);
v_endExclusive_2275_ = lean_ctor_get(v_slice_2271_, 1);
lean_inc(v_endExclusive_2275_);
lean_dec_ref(v_slice_2271_);
v_it_2247_ = v_nextIt_2273_;
v_startInclusive_2248_ = v_startInclusive_2274_;
v_endExclusive_2249_ = v_endExclusive_2275_;
goto v___jp_2246_;
}
}
}
else
{
lean_object* v___x_2277_; 
lean_del_object(v___x_2241_);
lean_dec(v_searcher_2239_);
v___x_2277_ = lean_box(1);
v_it_2247_ = v___x_2277_;
v_startInclusive_2248_ = v_currPos_2238_;
v_endExclusive_2249_ = v___x_2256_;
goto v___jp_2246_;
}
v___jp_2246_:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2250_ = lean_nat_add(v_startInclusive_2244_, v_startInclusive_2248_);
lean_dec(v_startInclusive_2248_);
v___x_2251_ = lean_nat_add(v_startInclusive_2244_, v_endExclusive_2249_);
lean_dec(v_endExclusive_2249_);
lean_inc_ref(v_str_2243_);
v___x_2252_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2252_, 0, v_str_2243_);
lean_ctor_set(v___x_2252_, 1, v___x_2250_);
lean_ctor_set(v___x_2252_, 2, v___x_2251_);
v___x_2253_ = l_String_Slice_toString(v___x_2252_);
lean_dec_ref_known(v___x_2252_, 3);
v___x_2254_ = lean_array_push(v_b_2237_, v___x_2253_);
v_a_2236_ = v_it_2247_;
v_b_2237_ = v___x_2254_;
goto _start;
}
}
}
else
{
return v_b_2237_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg___boxed(lean_object* v_out_2279_, lean_object* v_a_2280_, lean_object* v_b_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_2279_, v_a_2280_, v_b_2281_);
lean_dec_ref(v_out_2279_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(lean_object* v___x_2286_, lean_object* v___x_2287_, lean_object* v___x_2288_, lean_object* v_a_2289_, lean_object* v_b_2290_){
_start:
{
lean_object* v_it_2292_; lean_object* v_startInclusive_2293_; lean_object* v_endExclusive_2294_; 
if (lean_obj_tag(v_a_2289_) == 0)
{
lean_object* v_currPos_2319_; lean_object* v_searcher_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2349_; 
v_currPos_2319_ = lean_ctor_get(v_a_2289_, 0);
v_searcher_2320_ = lean_ctor_get(v_a_2289_, 1);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_a_2289_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2322_ = v_a_2289_;
v_isShared_2323_ = v_isSharedCheck_2349_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_searcher_2320_);
lean_inc(v_currPos_2319_);
lean_dec(v_a_2289_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2349_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v_str_2324_; lean_object* v_startInclusive_2325_; lean_object* v_endExclusive_2326_; lean_object* v___x_2327_; uint8_t v_decide_2328_; 
v_str_2324_ = lean_ctor_get(v___x_2287_, 0);
v_startInclusive_2325_ = lean_ctor_get(v___x_2287_, 1);
v_endExclusive_2326_ = lean_ctor_get(v___x_2287_, 2);
v___x_2327_ = lean_nat_sub(v_endExclusive_2326_, v_startInclusive_2325_);
v_decide_2328_ = lean_nat_dec_eq(v_searcher_2320_, v___x_2327_);
lean_dec(v___x_2327_);
if (v_decide_2328_ == 0)
{
uint32_t v___x_2329_; lean_object* v___x_2330_; uint32_t v___x_2331_; uint8_t v___x_2332_; 
v___x_2329_ = 38;
v___x_2330_ = lean_nat_add(v_startInclusive_2325_, v_searcher_2320_);
v___x_2331_ = lean_string_utf8_get_fast(v_str_2324_, v___x_2330_);
v___x_2332_ = lean_uint32_dec_eq(v___x_2331_, v___x_2329_);
if (v___x_2332_ == 0)
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2336_; 
lean_dec(v_searcher_2320_);
v___x_2333_ = lean_string_utf8_next_fast(v_str_2324_, v___x_2330_);
lean_dec(v___x_2330_);
v___x_2334_ = lean_nat_sub(v___x_2333_, v_startInclusive_2325_);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 1, v___x_2334_);
v___x_2336_ = v___x_2322_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_currPos_2319_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v___x_2334_);
v___x_2336_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
v_a_2289_ = v___x_2336_;
goto _start;
}
}
else
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v_slice_2342_; lean_object* v_nextIt_2344_; 
v___x_2339_ = lean_string_utf8_next_fast(v_str_2324_, v___x_2330_);
v___x_2340_ = lean_nat_sub(v___x_2339_, v___x_2330_);
lean_dec(v___x_2330_);
v___x_2341_ = lean_nat_add(v_searcher_2320_, v___x_2340_);
lean_dec(v___x_2340_);
v_slice_2342_ = l_String_Slice_subslice_x21(v___x_2287_, v_currPos_2319_, v_searcher_2320_);
lean_inc(v___x_2341_);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 1, v___x_2341_);
lean_ctor_set(v___x_2322_, 0, v___x_2341_);
v_nextIt_2344_ = v___x_2322_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2341_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v___x_2341_);
v_nextIt_2344_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
lean_object* v_startInclusive_2345_; lean_object* v_endExclusive_2346_; 
v_startInclusive_2345_ = lean_ctor_get(v_slice_2342_, 0);
lean_inc(v_startInclusive_2345_);
v_endExclusive_2346_ = lean_ctor_get(v_slice_2342_, 1);
lean_inc(v_endExclusive_2346_);
lean_dec_ref(v_slice_2342_);
v_it_2292_ = v_nextIt_2344_;
v_startInclusive_2293_ = v_startInclusive_2345_;
v_endExclusive_2294_ = v_endExclusive_2346_;
goto v___jp_2291_;
}
}
}
else
{
lean_object* v___x_2348_; 
lean_del_object(v___x_2322_);
lean_dec(v_searcher_2320_);
v___x_2348_ = lean_box(1);
lean_inc(v___x_2288_);
v_it_2292_ = v___x_2348_;
v_startInclusive_2293_ = v_currPos_2319_;
v_endExclusive_2294_ = v___x_2288_;
goto v___jp_2291_;
}
}
}
else
{
lean_object* v___x_2350_; 
lean_dec(v___x_2288_);
lean_dec_ref(v___x_2286_);
v___x_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2350_, 0, v_b_2290_);
return v___x_2350_;
}
v___jp_2291_:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
lean_inc_ref(v___x_2286_);
v___x_2295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2286_);
lean_ctor_set(v___x_2295_, 1, v_startInclusive_2293_);
lean_ctor_set(v___x_2295_, 2, v_endExclusive_2294_);
v___x_2296_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
v___x_2297_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0));
v___x_2298_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_2295_, v___x_2296_, v___x_2297_);
lean_dec_ref_known(v___x_2295_, 3);
v___x_2299_ = lean_array_to_list(v___x_2298_);
if (lean_obj_tag(v___x_2299_) == 0)
{
v_a_2289_ = v_it_2292_;
goto _start;
}
else
{
lean_object* v_tail_2301_; 
v_tail_2301_ = lean_ctor_get(v___x_2299_, 1);
if (lean_obj_tag(v_tail_2301_) == 0)
{
lean_object* v_head_2302_; lean_object* v___x_2303_; 
v_head_2302_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_head_2302_);
lean_dec_ref_known(v___x_2299_, 2);
v___x_2303_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2302_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v___x_2304_; 
lean_dec(v_it_2292_);
lean_dec_ref(v_b_2290_);
lean_dec(v___x_2288_);
lean_dec_ref(v___x_2286_);
v___x_2304_ = lean_box(0);
return v___x_2304_;
}
else
{
lean_object* v_val_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v_val_2305_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_val_2305_);
lean_dec_ref_known(v___x_2303_, 1);
v___x_2306_ = lean_box(0);
v___x_2307_ = l_Std_Http_URI_Query_insertEncoded(v_b_2290_, v_val_2305_, v___x_2306_);
v_a_2289_ = v_it_2292_;
v_b_2290_ = v___x_2307_;
goto _start;
}
}
else
{
lean_object* v_head_2309_; lean_object* v___x_2310_; 
lean_inc(v_tail_2301_);
v_head_2309_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_head_2309_);
lean_dec_ref_known(v___x_2299_, 2);
v___x_2310_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2309_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v___x_2311_; 
lean_dec(v_tail_2301_);
lean_dec(v_it_2292_);
lean_dec_ref(v_b_2290_);
lean_dec(v___x_2288_);
lean_dec_ref(v___x_2286_);
v___x_2311_ = lean_box(0);
return v___x_2311_;
}
else
{
lean_object* v_val_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v_val_2312_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_val_2312_);
lean_dec_ref_known(v___x_2310_, 1);
v___x_2313_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1));
v___x_2314_ = l_String_intercalate(v___x_2313_, v_tail_2301_);
v___x_2315_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2314_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v___x_2316_; 
lean_dec(v_val_2312_);
lean_dec(v_it_2292_);
lean_dec_ref(v_b_2290_);
lean_dec(v___x_2288_);
lean_dec_ref(v___x_2286_);
v___x_2316_ = lean_box(0);
return v___x_2316_;
}
else
{
lean_object* v___x_2317_; 
v___x_2317_ = l_Std_Http_URI_Query_insertEncoded(v_b_2290_, v_val_2312_, v___x_2315_);
v_a_2289_ = v_it_2292_;
v_b_2290_ = v___x_2317_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___boxed(lean_object* v___x_2351_, lean_object* v___x_2352_, lean_object* v___x_2353_, lean_object* v_a_2354_, lean_object* v_b_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2351_, v___x_2352_, v___x_2353_, v_a_2354_, v_b_2355_);
lean_dec_ref(v___x_2352_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(lean_object* v___x_2357_, lean_object* v___x_2358_, lean_object* v___x_2359_, lean_object* v_a_2360_, lean_object* v_b_2361_){
_start:
{
lean_object* v_it_2363_; lean_object* v_startInclusive_2364_; lean_object* v_endExclusive_2365_; 
if (lean_obj_tag(v_a_2360_) == 0)
{
lean_object* v_currPos_2390_; lean_object* v_searcher_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2420_; 
v_currPos_2390_ = lean_ctor_get(v_a_2360_, 0);
v_searcher_2391_ = lean_ctor_get(v_a_2360_, 1);
v_isSharedCheck_2420_ = !lean_is_exclusive(v_a_2360_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2393_ = v_a_2360_;
v_isShared_2394_ = v_isSharedCheck_2420_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_searcher_2391_);
lean_inc(v_currPos_2390_);
lean_dec(v_a_2360_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2420_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v_str_2395_; lean_object* v_startInclusive_2396_; lean_object* v_endExclusive_2397_; lean_object* v___x_2398_; uint8_t v_decide_2399_; 
v_str_2395_ = lean_ctor_get(v___x_2358_, 0);
v_startInclusive_2396_ = lean_ctor_get(v___x_2358_, 1);
v_endExclusive_2397_ = lean_ctor_get(v___x_2358_, 2);
v___x_2398_ = lean_nat_sub(v_endExclusive_2397_, v_startInclusive_2396_);
v_decide_2399_ = lean_nat_dec_eq(v_searcher_2391_, v___x_2398_);
lean_dec(v___x_2398_);
if (v_decide_2399_ == 0)
{
lean_object* v___x_2400_; uint32_t v___x_2401_; uint32_t v___x_2402_; uint8_t v___x_2403_; 
v___x_2400_ = lean_nat_add(v_startInclusive_2396_, v_searcher_2391_);
v___x_2401_ = lean_string_utf8_get_fast(v_str_2395_, v___x_2400_);
v___x_2402_ = 38;
v___x_2403_ = lean_uint32_dec_eq(v___x_2401_, v___x_2402_);
if (v___x_2403_ == 0)
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2407_; 
lean_dec(v_searcher_2391_);
v___x_2404_ = lean_string_utf8_next_fast(v_str_2395_, v___x_2400_);
lean_dec(v___x_2400_);
v___x_2405_ = lean_nat_sub(v___x_2404_, v_startInclusive_2396_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 1, v___x_2405_);
v___x_2407_ = v___x_2393_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_currPos_2390_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v___x_2405_);
v___x_2407_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
lean_object* v___x_2408_; 
v___x_2408_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2357_, v___x_2358_, v___x_2359_, v___x_2407_, v_b_2361_);
return v___x_2408_;
}
}
else
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v_slice_2413_; lean_object* v_nextIt_2415_; 
v___x_2410_ = lean_string_utf8_next_fast(v_str_2395_, v___x_2400_);
v___x_2411_ = lean_nat_sub(v___x_2410_, v___x_2400_);
lean_dec(v___x_2400_);
v___x_2412_ = lean_nat_add(v_searcher_2391_, v___x_2411_);
lean_dec(v___x_2411_);
v_slice_2413_ = l_String_Slice_subslice_x21(v___x_2358_, v_currPos_2390_, v_searcher_2391_);
lean_inc(v___x_2412_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 1, v___x_2412_);
lean_ctor_set(v___x_2393_, 0, v___x_2412_);
v_nextIt_2415_ = v___x_2393_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2412_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v___x_2412_);
v_nextIt_2415_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
lean_object* v_startInclusive_2416_; lean_object* v_endExclusive_2417_; 
v_startInclusive_2416_ = lean_ctor_get(v_slice_2413_, 0);
lean_inc(v_startInclusive_2416_);
v_endExclusive_2417_ = lean_ctor_get(v_slice_2413_, 1);
lean_inc(v_endExclusive_2417_);
lean_dec_ref(v_slice_2413_);
v_it_2363_ = v_nextIt_2415_;
v_startInclusive_2364_ = v_startInclusive_2416_;
v_endExclusive_2365_ = v_endExclusive_2417_;
goto v___jp_2362_;
}
}
}
else
{
lean_object* v___x_2419_; 
lean_del_object(v___x_2393_);
lean_dec(v_searcher_2391_);
v___x_2419_ = lean_box(1);
lean_inc(v___x_2359_);
v_it_2363_ = v___x_2419_;
v_startInclusive_2364_ = v_currPos_2390_;
v_endExclusive_2365_ = v___x_2359_;
goto v___jp_2362_;
}
}
}
else
{
lean_object* v___x_2421_; 
lean_dec(v___x_2359_);
lean_dec_ref(v___x_2357_);
v___x_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2421_, 0, v_b_2361_);
return v___x_2421_;
}
v___jp_2362_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
lean_inc_ref(v___x_2357_);
v___x_2366_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2357_);
lean_ctor_set(v___x_2366_, 1, v_startInclusive_2364_);
lean_ctor_set(v___x_2366_, 2, v_endExclusive_2365_);
v___x_2367_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
v___x_2368_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0));
v___x_2369_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_2366_, v___x_2367_, v___x_2368_);
lean_dec_ref_known(v___x_2366_, 3);
v___x_2370_ = lean_array_to_list(v___x_2369_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v___x_2371_; 
v___x_2371_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2357_, v___x_2358_, v___x_2359_, v_it_2363_, v_b_2361_);
return v___x_2371_;
}
else
{
lean_object* v_tail_2372_; 
v_tail_2372_ = lean_ctor_get(v___x_2370_, 1);
if (lean_obj_tag(v_tail_2372_) == 0)
{
lean_object* v_head_2373_; lean_object* v___x_2374_; 
v_head_2373_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_head_2373_);
lean_dec_ref_known(v___x_2370_, 2);
v___x_2374_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2373_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v___x_2375_; 
lean_dec(v_it_2363_);
lean_dec_ref(v_b_2361_);
lean_dec(v___x_2359_);
lean_dec_ref(v___x_2357_);
v___x_2375_ = lean_box(0);
return v___x_2375_;
}
else
{
lean_object* v_val_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v_val_2376_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_val_2376_);
lean_dec_ref_known(v___x_2374_, 1);
v___x_2377_ = lean_box(0);
v___x_2378_ = l_Std_Http_URI_Query_insertEncoded(v_b_2361_, v_val_2376_, v___x_2377_);
v___x_2379_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2357_, v___x_2358_, v___x_2359_, v_it_2363_, v___x_2378_);
return v___x_2379_;
}
}
else
{
lean_object* v_head_2380_; lean_object* v___x_2381_; 
lean_inc(v_tail_2372_);
v_head_2380_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_head_2380_);
lean_dec_ref_known(v___x_2370_, 2);
v___x_2381_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2380_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v___x_2382_; 
lean_dec(v_tail_2372_);
lean_dec(v_it_2363_);
lean_dec_ref(v_b_2361_);
lean_dec(v___x_2359_);
lean_dec_ref(v___x_2357_);
v___x_2382_ = lean_box(0);
return v___x_2382_;
}
else
{
lean_object* v_val_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v_val_2383_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_val_2383_);
lean_dec_ref_known(v___x_2381_, 1);
v___x_2384_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1));
v___x_2385_ = l_String_intercalate(v___x_2384_, v_tail_2372_);
v___x_2386_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2385_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v___x_2387_; 
lean_dec(v_val_2383_);
lean_dec(v_it_2363_);
lean_dec_ref(v_b_2361_);
lean_dec(v___x_2359_);
lean_dec_ref(v___x_2357_);
v___x_2387_ = lean_box(0);
return v___x_2387_;
}
else
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = l_Std_Http_URI_Query_insertEncoded(v_b_2361_, v_val_2383_, v___x_2386_);
v___x_2389_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2357_, v___x_2358_, v___x_2359_, v_it_2363_, v___x_2388_);
return v___x_2389_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg___boxed(lean_object* v___x_2422_, lean_object* v___x_2423_, lean_object* v___x_2424_, lean_object* v_a_2425_, lean_object* v_b_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2422_, v___x_2423_, v___x_2424_, v_a_2425_, v_b_2426_);
lean_dec_ref(v___x_2423_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(lean_object* v_config_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v_maxQueryLength_2435_; lean_object* v_maxQueryParams_2436_; lean_object* v___f_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v_snd_2440_; lean_object* v_fst_2441_; lean_object* v_fst_2442_; lean_object* v_array_2443_; lean_object* v_idx_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2494_; 
v_maxQueryLength_2435_ = lean_ctor_get(v_config_2433_, 4);
lean_inc(v_maxQueryLength_2435_);
v_maxQueryParams_2436_ = lean_ctor_get(v_config_2433_, 8);
lean_inc(v_maxQueryParams_2436_);
lean_dec_ref(v_config_2433_);
v___f_2437_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2438_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2434_);
v___x_2439_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2437_, v_maxQueryLength_2435_, v___x_2438_, v_a_2434_);
lean_dec(v_maxQueryLength_2435_);
v_snd_2440_ = lean_ctor_get(v___x_2439_, 1);
lean_inc(v_snd_2440_);
v_fst_2441_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_fst_2441_);
lean_dec_ref(v___x_2439_);
v_fst_2442_ = lean_ctor_get(v_snd_2440_, 0);
lean_inc(v_fst_2442_);
lean_dec(v_snd_2440_);
v_array_2443_ = lean_ctor_get(v_a_2434_, 0);
v_idx_2444_ = lean_ctor_get(v_a_2434_, 1);
v_isSharedCheck_2494_ = !lean_is_exclusive(v_a_2434_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2446_ = v_a_2434_;
v_isShared_2447_ = v_isSharedCheck_2494_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_idx_2444_);
lean_inc(v_array_2443_);
lean_dec(v_a_2434_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2494_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v_lower_2449_; lean_object* v_upper_2450_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___y_2491_; uint8_t v___x_2493_; 
v___x_2488_ = lean_nat_add(v_idx_2444_, v_fst_2441_);
lean_dec(v_fst_2441_);
v___x_2489_ = lean_byte_array_size(v_array_2443_);
v___x_2493_ = lean_nat_dec_le(v_idx_2444_, v___x_2438_);
if (v___x_2493_ == 0)
{
v___y_2491_ = v_idx_2444_;
goto v___jp_2490_;
}
else
{
lean_dec(v_idx_2444_);
v___y_2491_ = v___x_2438_;
goto v___jp_2490_;
}
v___jp_2448_:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; uint8_t v___x_2453_; 
v___x_2451_ = l_ByteArray_toByteSlice(v_array_2443_, v_lower_2449_, v_upper_2450_);
v___x_2452_ = l_ByteSlice_toByteArray(v___x_2451_);
v___x_2453_ = lean_string_validate_utf8(v___x_2452_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2454_; lean_object* v___x_2456_; 
lean_dec_ref(v___x_2452_);
lean_dec(v_maxQueryParams_2436_);
v___x_2454_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2447_ == 0)
{
lean_ctor_set_tag(v___x_2446_, 1);
lean_ctor_set(v___x_2446_, 1, v___x_2454_);
lean_ctor_set(v___x_2446_, 0, v_fst_2442_);
v___x_2456_ = v___x_2446_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_fst_2442_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v___x_2454_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
else
{
lean_object* v___x_2458_; lean_object* v___x_2459_; uint8_t v___x_2460_; 
v___x_2458_ = lean_string_from_utf8_unchecked(v___x_2452_);
v___x_2459_ = lean_string_utf8_byte_size(v___x_2458_);
v___x_2460_ = lean_nat_dec_eq(v___x_2459_, v___x_2438_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; uint8_t v___x_2464_; 
lean_inc_ref(v___x_2458_);
v___x_2461_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2458_);
lean_ctor_set(v___x_2461_, 1, v___x_2438_);
lean_ctor_set(v___x_2461_, 2, v___x_2459_);
v___x_2462_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0);
v___x_2463_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2458_, v___x_2461_, v___x_2459_, v___x_2462_, v___x_2438_);
v___x_2464_ = lean_nat_dec_lt(v_maxQueryParams_2436_, v___x_2463_);
lean_dec(v___x_2463_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2465_; lean_object* v___x_2466_; 
lean_dec(v_maxQueryParams_2436_);
v___x_2465_ = l_Std_Http_URI_Query_empty;
v___x_2466_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2458_, v___x_2461_, v___x_2459_, v___x_2462_, v___x_2465_);
lean_dec_ref_known(v___x_2461_, 3);
if (lean_obj_tag(v___x_2466_) == 1)
{
lean_object* v_val_2467_; lean_object* v___x_2469_; 
v_val_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_val_2467_);
lean_dec_ref_known(v___x_2466_, 1);
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 1, v_val_2467_);
lean_ctor_set(v___x_2446_, 0, v_fst_2442_);
v___x_2469_ = v___x_2446_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_fst_2442_);
lean_ctor_set(v_reuseFailAlloc_2470_, 1, v_val_2467_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
else
{
lean_object* v___x_2471_; lean_object* v___x_2473_; 
lean_dec(v___x_2466_);
v___x_2471_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2447_ == 0)
{
lean_ctor_set_tag(v___x_2446_, 1);
lean_ctor_set(v___x_2446_, 1, v___x_2471_);
lean_ctor_set(v___x_2446_, 0, v_fst_2442_);
v___x_2473_ = v___x_2446_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_fst_2442_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v___x_2471_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
else
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2482_; 
lean_dec_ref_known(v___x_2461_, 3);
lean_dec_ref(v___x_2458_);
v___x_2475_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3));
v___x_2476_ = l_Nat_reprFast(v_maxQueryParams_2436_);
v___x_2477_ = lean_string_append(v___x_2475_, v___x_2476_);
lean_dec_ref(v___x_2476_);
v___x_2478_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_2479_ = lean_string_append(v___x_2477_, v___x_2478_);
v___x_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
if (v_isShared_2447_ == 0)
{
lean_ctor_set_tag(v___x_2446_, 1);
lean_ctor_set(v___x_2446_, 1, v___x_2480_);
lean_ctor_set(v___x_2446_, 0, v_fst_2442_);
v___x_2482_ = v___x_2446_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_fst_2442_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v___x_2480_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
else
{
lean_object* v___x_2484_; lean_object* v___x_2486_; 
lean_dec_ref(v___x_2458_);
lean_dec(v_maxQueryParams_2436_);
v___x_2484_ = l_Std_Http_URI_Query_empty;
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 1, v___x_2484_);
lean_ctor_set(v___x_2446_, 0, v_fst_2442_);
v___x_2486_ = v___x_2446_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_fst_2442_);
lean_ctor_set(v_reuseFailAlloc_2487_, 1, v___x_2484_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
v___jp_2490_:
{
uint8_t v___x_2492_; 
v___x_2492_ = lean_nat_dec_le(v___x_2488_, v___x_2489_);
if (v___x_2492_ == 0)
{
lean_dec(v___x_2488_);
v_lower_2449_ = v___y_2491_;
v_upper_2450_ = v___x_2489_;
goto v___jp_2448_;
}
else
{
v_lower_2449_ = v___y_2491_;
v_upper_2450_ = v___x_2488_;
goto v___jp_2448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(lean_object* v___x_2495_, lean_object* v___x_2496_, lean_object* v___x_2497_, lean_object* v_inst_2498_, lean_object* v_R_2499_, lean_object* v_a_2500_, lean_object* v_b_2501_, lean_object* v_c_2502_){
_start:
{
lean_object* v___x_2503_; 
v___x_2503_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2495_, v___x_2496_, v___x_2497_, v_a_2500_, v_b_2501_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___boxed(lean_object* v___x_2504_, lean_object* v___x_2505_, lean_object* v___x_2506_, lean_object* v_inst_2507_, lean_object* v_R_2508_, lean_object* v_a_2509_, lean_object* v_b_2510_, lean_object* v_c_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(v___x_2504_, v___x_2505_, v___x_2506_, v_inst_2507_, v_R_2508_, v_a_2509_, v_b_2510_, v_c_2511_);
lean_dec(v___x_2506_);
lean_dec_ref(v___x_2505_);
lean_dec_ref(v___x_2504_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(lean_object* v_out_2513_, lean_object* v_inst_2514_, lean_object* v_R_2515_, lean_object* v_a_2516_, lean_object* v_b_2517_){
_start:
{
lean_object* v___x_2518_; 
v___x_2518_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_2513_, v_a_2516_, v_b_2517_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___boxed(lean_object* v_out_2519_, lean_object* v_inst_2520_, lean_object* v_R_2521_, lean_object* v_a_2522_, lean_object* v_b_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(v_out_2519_, v_inst_2520_, v_R_2521_, v_a_2522_, v_b_2523_);
lean_dec_ref(v_out_2519_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(lean_object* v___x_2525_, lean_object* v___x_2526_, lean_object* v___x_2527_, lean_object* v_inst_2528_, lean_object* v_R_2529_, lean_object* v_a_2530_, lean_object* v_b_2531_, lean_object* v_c_2532_){
_start:
{
lean_object* v___x_2533_; 
v___x_2533_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2525_, v___x_2526_, v___x_2527_, v_a_2530_, v_b_2531_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___boxed(lean_object* v___x_2534_, lean_object* v___x_2535_, lean_object* v___x_2536_, lean_object* v_inst_2537_, lean_object* v_R_2538_, lean_object* v_a_2539_, lean_object* v_b_2540_, lean_object* v_c_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(v___x_2534_, v___x_2535_, v___x_2536_, v_inst_2537_, v_R_2538_, v_a_2539_, v_b_2540_, v_c_2541_);
lean_dec_ref(v___x_2535_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(lean_object* v___x_2543_, lean_object* v___x_2544_, lean_object* v___x_2545_, lean_object* v_inst_2546_, lean_object* v_R_2547_, lean_object* v_a_2548_, lean_object* v_b_2549_, lean_object* v_c_2550_){
_start:
{
lean_object* v___x_2551_; 
v___x_2551_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2544_, v___x_2545_, v_a_2548_, v_b_2549_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___boxed(lean_object* v___x_2552_, lean_object* v___x_2553_, lean_object* v___x_2554_, lean_object* v_inst_2555_, lean_object* v_R_2556_, lean_object* v_a_2557_, lean_object* v_b_2558_, lean_object* v_c_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(v___x_2552_, v___x_2553_, v___x_2554_, v_inst_2555_, v_R_2556_, v_a_2557_, v_b_2558_, v_c_2559_);
lean_dec(v___x_2554_);
lean_dec_ref(v___x_2553_);
lean_dec_ref(v___x_2552_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(lean_object* v___x_2561_, lean_object* v___x_2562_, lean_object* v___x_2563_, lean_object* v_inst_2564_, lean_object* v_R_2565_, lean_object* v_a_2566_, lean_object* v_b_2567_, lean_object* v_c_2568_){
_start:
{
lean_object* v___x_2569_; 
v___x_2569_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2561_, v___x_2562_, v___x_2563_, v_a_2566_, v_b_2567_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___boxed(lean_object* v___x_2570_, lean_object* v___x_2571_, lean_object* v___x_2572_, lean_object* v_inst_2573_, lean_object* v_R_2574_, lean_object* v_a_2575_, lean_object* v_b_2576_, lean_object* v_c_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(v___x_2570_, v___x_2571_, v___x_2572_, v_inst_2573_, v_R_2574_, v_a_2575_, v_b_2576_, v_c_2577_);
lean_dec_ref(v___x_2571_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(lean_object* v_config_2582_, lean_object* v_a_2583_){
_start:
{
lean_object* v_maxFragmentLength_2584_; lean_object* v___f_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v_snd_2588_; lean_object* v_fst_2589_; lean_object* v_fst_2590_; lean_object* v_array_2591_; lean_object* v_idx_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2616_; 
v_maxFragmentLength_2584_ = lean_ctor_get(v_config_2582_, 5);
v___f_2585_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2586_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2583_);
v___x_2587_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2585_, v_maxFragmentLength_2584_, v___x_2586_, v_a_2583_);
v_snd_2588_ = lean_ctor_get(v___x_2587_, 1);
lean_inc(v_snd_2588_);
v_fst_2589_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_fst_2589_);
lean_dec_ref(v___x_2587_);
v_fst_2590_ = lean_ctor_get(v_snd_2588_, 0);
lean_inc(v_fst_2590_);
lean_dec(v_snd_2588_);
v_array_2591_ = lean_ctor_get(v_a_2583_, 0);
v_idx_2592_ = lean_ctor_get(v_a_2583_, 1);
v_isSharedCheck_2616_ = !lean_is_exclusive(v_a_2583_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2594_ = v_a_2583_;
v_isShared_2595_ = v_isSharedCheck_2616_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_idx_2592_);
lean_inc(v_array_2591_);
lean_dec(v_a_2583_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2616_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v_lower_2597_; lean_object* v_upper_2598_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___y_2613_; uint8_t v___x_2615_; 
v___x_2610_ = lean_nat_add(v_idx_2592_, v_fst_2589_);
lean_dec(v_fst_2589_);
v___x_2611_ = lean_byte_array_size(v_array_2591_);
v___x_2615_ = lean_nat_dec_le(v_idx_2592_, v___x_2586_);
if (v___x_2615_ == 0)
{
v___y_2613_ = v_idx_2592_;
goto v___jp_2612_;
}
else
{
lean_dec(v_idx_2592_);
v___y_2613_ = v___x_2586_;
goto v___jp_2612_;
}
v___jp_2596_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2599_ = l_ByteArray_toByteSlice(v_array_2591_, v_lower_2597_, v_upper_2598_);
v___x_2600_ = l_ByteSlice_toByteArray(v___x_2599_);
v___x_2601_ = l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(v___x_2600_);
if (lean_obj_tag(v___x_2601_) == 1)
{
lean_object* v_val_2602_; lean_object* v___x_2604_; 
v_val_2602_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_val_2602_);
lean_dec_ref_known(v___x_2601_, 1);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 1, v_val_2602_);
lean_ctor_set(v___x_2594_, 0, v_fst_2590_);
v___x_2604_ = v___x_2594_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_fst_2590_);
lean_ctor_set(v_reuseFailAlloc_2605_, 1, v_val_2602_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
else
{
lean_object* v___x_2606_; lean_object* v___x_2608_; 
lean_dec(v___x_2601_);
v___x_2606_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1));
if (v_isShared_2595_ == 0)
{
lean_ctor_set_tag(v___x_2594_, 1);
lean_ctor_set(v___x_2594_, 1, v___x_2606_);
lean_ctor_set(v___x_2594_, 0, v_fst_2590_);
v___x_2608_ = v___x_2594_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_fst_2590_);
lean_ctor_set(v_reuseFailAlloc_2609_, 1, v___x_2606_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
v___jp_2612_:
{
uint8_t v___x_2614_; 
v___x_2614_ = lean_nat_dec_le(v___x_2610_, v___x_2611_);
if (v___x_2614_ == 0)
{
lean_dec(v___x_2610_);
v_lower_2597_ = v___y_2613_;
v_upper_2598_ = v___x_2611_;
goto v___jp_2596_;
}
else
{
v_lower_2597_ = v___y_2613_;
v_upper_2598_ = v___x_2610_;
goto v___jp_2596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___boxed(lean_object* v_config_2617_, lean_object* v_a_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2617_, v_a_2618_);
lean_dec_ref(v_config_2617_);
return v_res_2619_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1(void){
_start:
{
lean_object* v___x_2621_; lean_object* v_utf8_2622_; 
v___x_2621_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0));
v_utf8_2622_ = lean_string_to_utf8(v___x_2621_);
return v_utf8_2622_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(lean_object* v_config_2623_, lean_object* v_a_2624_){
_start:
{
lean_object* v_utf8_2625_; lean_object* v___x_2626_; 
v_utf8_2625_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1);
lean_inc_ref(v_a_2624_);
v___x_2626_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_2625_, v_a_2624_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_pos_2627_; uint8_t v___x_2628_; lean_object* v_pos_2630_; lean_object* v_res_2631_; lean_object* v___x_2652_; 
lean_dec_ref(v_a_2624_);
v_pos_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc_n(v_pos_2627_, 2);
lean_dec_ref_known(v___x_2626_, 2);
v___x_2628_ = 1;
lean_inc_ref(v_config_2623_);
v___x_2652_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_2623_, v_pos_2627_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_pos_2653_; lean_object* v_res_2654_; lean_object* v___x_2655_; 
lean_dec(v_pos_2627_);
v_pos_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_pos_2653_);
v_res_2654_ = lean_ctor_get(v___x_2652_, 1);
lean_inc(v_res_2654_);
lean_dec_ref_known(v___x_2652_, 2);
v___x_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2655_, 0, v_res_2654_);
v_pos_2630_ = v_pos_2653_;
v_res_2631_ = v___x_2655_;
goto v___jp_2629_;
}
else
{
lean_object* v_err_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2666_; 
v_err_2656_ = lean_ctor_get(v___x_2652_, 1);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2666_ == 0)
{
lean_object* v_unused_2667_; 
v_unused_2667_ = lean_ctor_get(v___x_2652_, 0);
lean_dec(v_unused_2667_);
v___x_2658_ = v___x_2652_;
v_isShared_2659_ = v_isSharedCheck_2666_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_err_2656_);
lean_dec(v___x_2652_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2666_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v_idx_2660_; uint8_t v___x_2661_; 
v_idx_2660_ = lean_ctor_get(v_pos_2627_, 1);
v___x_2661_ = lean_nat_dec_eq(v_idx_2660_, v_idx_2660_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2663_; 
lean_dec_ref(v_config_2623_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 0, v_pos_2627_);
v___x_2663_ = v___x_2658_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_pos_2627_);
lean_ctor_set(v_reuseFailAlloc_2664_, 1, v_err_2656_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
else
{
lean_object* v___x_2665_; 
lean_del_object(v___x_2658_);
lean_dec(v_err_2656_);
v___x_2665_ = lean_box(0);
v_pos_2630_ = v_pos_2627_;
v_res_2631_ = v___x_2665_;
goto v___jp_2629_;
}
}
}
v___jp_2629_:
{
lean_object* v___x_2632_; 
v___x_2632_ = l_Std_Http_URI_Parser_parsePath(v_config_2623_, v___x_2628_, v___x_2628_, v_pos_2630_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_pos_2633_; lean_object* v_res_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2642_; 
v_pos_2633_ = lean_ctor_get(v___x_2632_, 0);
v_res_2634_ = lean_ctor_get(v___x_2632_, 1);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2636_ = v___x_2632_;
v_isShared_2637_ = v_isSharedCheck_2642_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_res_2634_);
lean_inc(v_pos_2633_);
lean_dec(v___x_2632_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2642_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2638_; lean_object* v___x_2640_; 
v___x_2638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2638_, 0, v_res_2631_);
lean_ctor_set(v___x_2638_, 1, v_res_2634_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 1, v___x_2638_);
v___x_2640_ = v___x_2636_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_pos_2633_);
lean_ctor_set(v_reuseFailAlloc_2641_, 1, v___x_2638_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
else
{
lean_object* v_pos_2643_; lean_object* v_err_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec(v_res_2631_);
v_pos_2643_ = lean_ctor_get(v___x_2632_, 0);
v_err_2644_ = lean_ctor_get(v___x_2632_, 1);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2632_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_err_2644_);
lean_inc(v_pos_2643_);
lean_dec(v___x_2632_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_pos_2643_);
lean_ctor_set(v_reuseFailAlloc_2650_, 1, v_err_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
}
else
{
lean_object* v_err_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2699_; 
v_err_2668_ = lean_ctor_get(v___x_2626_, 1);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2699_ == 0)
{
lean_object* v_unused_2700_; 
v_unused_2700_ = lean_ctor_get(v___x_2626_, 0);
lean_dec(v_unused_2700_);
v___x_2670_ = v___x_2626_;
v_isShared_2671_ = v_isSharedCheck_2699_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_err_2668_);
lean_dec(v___x_2626_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2699_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v_idx_2672_; uint8_t v___x_2673_; 
v_idx_2672_ = lean_ctor_get(v_a_2624_, 1);
v___x_2673_ = lean_nat_dec_eq(v_idx_2672_, v_idx_2672_);
if (v___x_2673_ == 0)
{
lean_object* v___x_2675_; 
lean_dec_ref(v_config_2623_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 0, v_a_2624_);
v___x_2675_ = v___x_2670_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2624_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v_err_2668_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
else
{
uint8_t v___x_2677_; lean_object* v___x_2678_; 
lean_del_object(v___x_2670_);
lean_dec(v_err_2668_);
v___x_2677_ = 0;
v___x_2678_ = l_Std_Http_URI_Parser_parsePath(v_config_2623_, v___x_2677_, v___x_2673_, v_a_2624_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_pos_2679_; lean_object* v_res_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2689_; 
v_pos_2679_ = lean_ctor_get(v___x_2678_, 0);
v_res_2680_ = lean_ctor_get(v___x_2678_, 1);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2682_ = v___x_2678_;
v_isShared_2683_ = v_isSharedCheck_2689_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_res_2680_);
lean_inc(v_pos_2679_);
lean_dec(v___x_2678_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2689_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2687_; 
v___x_2684_ = lean_box(0);
v___x_2685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
lean_ctor_set(v___x_2685_, 1, v_res_2680_);
if (v_isShared_2683_ == 0)
{
lean_ctor_set(v___x_2682_, 1, v___x_2685_);
v___x_2687_ = v___x_2682_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_pos_2679_);
lean_ctor_set(v_reuseFailAlloc_2688_, 1, v___x_2685_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
else
{
lean_object* v_pos_2690_; lean_object* v_err_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
v_pos_2690_ = lean_ctor_get(v___x_2678_, 0);
v_err_2691_ = lean_ctor_get(v___x_2678_, 1);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2678_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_err_2691_);
lean_inc(v_pos_2690_);
lean_dec(v___x_2678_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_pos_2690_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v_err_2691_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURI(lean_object* v_config_2707_, lean_object* v_a_2708_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_2707_, v_a_2708_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_pos_2710_; lean_object* v_res_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2842_; 
v_pos_2710_ = lean_ctor_get(v___x_2709_, 0);
v_res_2711_ = lean_ctor_get(v___x_2709_, 1);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2713_ = v___x_2709_;
v_isShared_2714_ = v_isSharedCheck_2842_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_res_2711_);
lean_inc(v_pos_2710_);
lean_dec(v___x_2709_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2842_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v_array_2715_; lean_object* v_idx_2716_; lean_object* v___x_2717_; uint8_t v___x_2718_; 
v_array_2715_ = lean_ctor_get(v_pos_2710_, 0);
v_idx_2716_ = lean_ctor_get(v_pos_2710_, 1);
v___x_2717_ = lean_byte_array_size(v_array_2715_);
v___x_2718_ = lean_nat_dec_lt(v_idx_2716_, v___x_2717_);
if (v___x_2718_ == 0)
{
lean_object* v___x_2719_; lean_object* v___x_2721_; 
lean_dec(v_res_2711_);
lean_dec_ref(v_config_2707_);
v___x_2719_ = lean_box(0);
if (v_isShared_2714_ == 0)
{
lean_ctor_set_tag(v___x_2713_, 1);
lean_ctor_set(v___x_2713_, 1, v___x_2719_);
v___x_2721_ = v___x_2713_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_pos_2710_);
lean_ctor_set(v_reuseFailAlloc_2722_, 1, v___x_2719_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
else
{
uint8_t v___x_2723_; uint8_t v_got_2724_; uint8_t v___x_2725_; 
v___x_2723_ = 58;
v_got_2724_ = lean_byte_array_fget(v_array_2715_, v_idx_2716_);
v___x_2725_ = lean_uint8_dec_eq(v_got_2724_, v___x_2723_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2726_; lean_object* v___x_2728_; 
lean_dec(v_res_2711_);
lean_dec_ref(v_config_2707_);
v___x_2726_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_2714_ == 0)
{
lean_ctor_set_tag(v___x_2713_, 1);
lean_ctor_set(v___x_2713_, 1, v___x_2726_);
v___x_2728_ = v___x_2713_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_pos_2710_);
lean_ctor_set(v_reuseFailAlloc_2729_, 1, v___x_2726_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
else
{
lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2839_; 
lean_inc(v_idx_2716_);
lean_inc_ref(v_array_2715_);
v_isSharedCheck_2839_ = !lean_is_exclusive(v_pos_2710_);
if (v_isSharedCheck_2839_ == 0)
{
lean_object* v_unused_2840_; lean_object* v_unused_2841_; 
v_unused_2840_ = lean_ctor_get(v_pos_2710_, 1);
lean_dec(v_unused_2840_);
v_unused_2841_ = lean_ctor_get(v_pos_2710_, 0);
lean_dec(v_unused_2841_);
v___x_2731_ = v_pos_2710_;
v_isShared_2732_ = v_isSharedCheck_2839_;
goto v_resetjp_2730_;
}
else
{
lean_dec(v_pos_2710_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2839_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2736_; 
v___x_2733_ = lean_unsigned_to_nat(1u);
v___x_2734_ = lean_nat_add(v_idx_2716_, v___x_2733_);
lean_dec(v_idx_2716_);
if (v_isShared_2732_ == 0)
{
lean_ctor_set(v___x_2731_, 1, v___x_2734_);
v___x_2736_ = v___x_2731_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_array_2715_);
lean_ctor_set(v_reuseFailAlloc_2838_, 1, v___x_2734_);
v___x_2736_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
lean_object* v___x_2737_; 
lean_inc_ref(v_config_2707_);
v___x_2737_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2707_, v___x_2736_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_res_2738_; lean_object* v_pos_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2828_; 
v_res_2738_ = lean_ctor_get(v___x_2737_, 1);
v_pos_2739_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2741_ = v___x_2737_;
v_isShared_2742_ = v_isSharedCheck_2828_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_res_2738_);
lean_inc(v_pos_2739_);
lean_dec(v___x_2737_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2828_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v_fst_2743_; lean_object* v_snd_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2827_; 
v_fst_2743_ = lean_ctor_get(v_res_2738_, 0);
v_snd_2744_ = lean_ctor_get(v_res_2738_, 1);
v_isSharedCheck_2827_ = !lean_is_exclusive(v_res_2738_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2746_ = v_res_2738_;
v_isShared_2747_ = v_isSharedCheck_2827_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_snd_2744_);
lean_inc(v_fst_2743_);
lean_dec(v_res_2738_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2827_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___y_2749_; lean_object* v_pos_2750_; lean_object* v_res_2751_; lean_object* v_idx_2757_; lean_object* v___y_2758_; lean_object* v_pos_2759_; lean_object* v_err_2760_; lean_object* v_pos_2768_; lean_object* v_array_2769_; lean_object* v_idx_2770_; lean_object* v_res_2771_; lean_object* v_array_2790_; lean_object* v_idx_2791_; lean_object* v_pos_2793_; lean_object* v_array_2794_; lean_object* v_idx_2795_; lean_object* v_err_2796_; lean_object* v___x_2800_; uint8_t v___x_2801_; 
v_array_2790_ = lean_ctor_get(v_pos_2739_, 0);
lean_inc_ref(v_array_2790_);
v_idx_2791_ = lean_ctor_get(v_pos_2739_, 1);
lean_inc(v_idx_2791_);
v___x_2800_ = lean_byte_array_size(v_array_2790_);
v___x_2801_ = lean_nat_dec_lt(v_idx_2791_, v___x_2800_);
if (v___x_2801_ == 0)
{
lean_object* v___x_2802_; 
v___x_2802_ = lean_box(0);
lean_inc(v_idx_2791_);
v_pos_2793_ = v_pos_2739_;
v_array_2794_ = v_array_2790_;
v_idx_2795_ = v_idx_2791_;
v_err_2796_ = v___x_2802_;
goto v___jp_2792_;
}
else
{
uint8_t v___x_2803_; uint8_t v_got_2804_; uint8_t v___x_2805_; 
v___x_2803_ = 63;
v_got_2804_ = lean_byte_array_fget(v_array_2790_, v_idx_2791_);
v___x_2805_ = lean_uint8_dec_eq(v_got_2804_, v___x_2803_);
if (v___x_2805_ == 0)
{
lean_object* v___x_2806_; 
v___x_2806_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__3));
lean_inc(v_idx_2791_);
v_pos_2793_ = v_pos_2739_;
v_array_2794_ = v_array_2790_;
v_idx_2795_ = v_idx_2791_;
v_err_2796_ = v___x_2806_;
goto v___jp_2792_;
}
else
{
lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2824_; 
v_isSharedCheck_2824_ = !lean_is_exclusive(v_pos_2739_);
if (v_isSharedCheck_2824_ == 0)
{
lean_object* v_unused_2825_; lean_object* v_unused_2826_; 
v_unused_2825_ = lean_ctor_get(v_pos_2739_, 1);
lean_dec(v_unused_2825_);
v_unused_2826_ = lean_ctor_get(v_pos_2739_, 0);
lean_dec(v_unused_2826_);
v___x_2808_ = v_pos_2739_;
v_isShared_2809_ = v_isSharedCheck_2824_;
goto v_resetjp_2807_;
}
else
{
lean_dec(v_pos_2739_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2824_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2810_; lean_object* v___x_2812_; 
v___x_2810_ = lean_nat_add(v_idx_2791_, v___x_2733_);
if (v_isShared_2809_ == 0)
{
lean_ctor_set(v___x_2808_, 1, v___x_2810_);
v___x_2812_ = v___x_2808_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_array_2790_);
lean_ctor_set(v_reuseFailAlloc_2823_, 1, v___x_2810_);
v___x_2812_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
lean_object* v___x_2813_; 
lean_inc_ref(v_config_2707_);
v___x_2813_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2707_, v___x_2812_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_pos_2814_; lean_object* v_res_2815_; lean_object* v_array_2816_; lean_object* v_idx_2817_; lean_object* v___x_2818_; 
lean_dec(v_idx_2791_);
v_pos_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_pos_2814_);
v_res_2815_ = lean_ctor_get(v___x_2813_, 1);
lean_inc(v_res_2815_);
lean_dec_ref_known(v___x_2813_, 2);
v_array_2816_ = lean_ctor_get(v_pos_2814_, 0);
lean_inc_ref(v_array_2816_);
v_idx_2817_ = lean_ctor_get(v_pos_2814_, 1);
lean_inc(v_idx_2817_);
v___x_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2818_, 0, v_res_2815_);
v_pos_2768_ = v_pos_2814_;
v_array_2769_ = v_array_2816_;
v_idx_2770_ = v_idx_2817_;
v_res_2771_ = v___x_2818_;
goto v___jp_2767_;
}
else
{
lean_object* v_pos_2819_; lean_object* v_err_2820_; lean_object* v_array_2821_; lean_object* v_idx_2822_; 
v_pos_2819_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_pos_2819_);
v_err_2820_ = lean_ctor_get(v___x_2813_, 1);
lean_inc(v_err_2820_);
lean_dec_ref_known(v___x_2813_, 2);
v_array_2821_ = lean_ctor_get(v_pos_2819_, 0);
lean_inc_ref(v_array_2821_);
v_idx_2822_ = lean_ctor_get(v_pos_2819_, 1);
lean_inc(v_idx_2822_);
v_pos_2793_ = v_pos_2819_;
v_array_2794_ = v_array_2821_;
v_idx_2795_ = v_idx_2822_;
v_err_2796_ = v_err_2820_;
goto v___jp_2792_;
}
}
}
}
}
v___jp_2748_:
{
lean_object* v___x_2752_; lean_object* v___x_2754_; 
v___x_2752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2752_, 0, v_res_2711_);
lean_ctor_set(v___x_2752_, 1, v_fst_2743_);
lean_ctor_set(v___x_2752_, 2, v_snd_2744_);
lean_ctor_set(v___x_2752_, 3, v___y_2749_);
lean_ctor_set(v___x_2752_, 4, v_res_2751_);
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 1, v___x_2752_);
lean_ctor_set(v___x_2741_, 0, v_pos_2750_);
v___x_2754_ = v___x_2741_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_pos_2750_);
lean_ctor_set(v_reuseFailAlloc_2755_, 1, v___x_2752_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
v___jp_2756_:
{
lean_object* v_idx_2761_; uint8_t v___x_2762_; 
v_idx_2761_ = lean_ctor_get(v_pos_2759_, 1);
v___x_2762_ = lean_nat_dec_eq(v_idx_2757_, v_idx_2761_);
lean_dec(v_idx_2757_);
if (v___x_2762_ == 0)
{
lean_object* v___x_2764_; 
lean_dec(v___y_2758_);
lean_dec(v_snd_2744_);
lean_dec(v_fst_2743_);
lean_del_object(v___x_2741_);
lean_dec(v_res_2711_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set_tag(v___x_2713_, 1);
lean_ctor_set(v___x_2713_, 1, v_err_2760_);
lean_ctor_set(v___x_2713_, 0, v_pos_2759_);
v___x_2764_ = v___x_2713_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_pos_2759_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v_err_2760_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
else
{
lean_object* v___x_2766_; 
lean_dec(v_err_2760_);
lean_del_object(v___x_2713_);
v___x_2766_ = lean_box(0);
v___y_2749_ = v___y_2758_;
v_pos_2750_ = v_pos_2759_;
v_res_2751_ = v___x_2766_;
goto v___jp_2748_;
}
}
v___jp_2767_:
{
lean_object* v___x_2772_; uint8_t v___x_2773_; 
v___x_2772_ = lean_byte_array_size(v_array_2769_);
v___x_2773_ = lean_nat_dec_lt(v_idx_2770_, v___x_2772_);
if (v___x_2773_ == 0)
{
lean_object* v___x_2774_; 
lean_dec_ref(v_array_2769_);
lean_del_object(v___x_2746_);
lean_dec_ref(v_config_2707_);
v___x_2774_ = lean_box(0);
v_idx_2757_ = v_idx_2770_;
v___y_2758_ = v_res_2771_;
v_pos_2759_ = v_pos_2768_;
v_err_2760_ = v___x_2774_;
goto v___jp_2756_;
}
else
{
uint8_t v___x_2775_; uint8_t v_got_2776_; uint8_t v___x_2777_; 
v___x_2775_ = 35;
v_got_2776_ = lean_byte_array_fget(v_array_2769_, v_idx_2770_);
v___x_2777_ = lean_uint8_dec_eq(v_got_2776_, v___x_2775_);
if (v___x_2777_ == 0)
{
lean_object* v___x_2778_; 
lean_dec_ref(v_array_2769_);
lean_del_object(v___x_2746_);
lean_dec_ref(v_config_2707_);
v___x_2778_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v_idx_2757_ = v_idx_2770_;
v___y_2758_ = v_res_2771_;
v_pos_2759_ = v_pos_2768_;
v_err_2760_ = v___x_2778_;
goto v___jp_2756_;
}
else
{
lean_object* v___x_2779_; lean_object* v___x_2781_; 
lean_dec_ref(v_pos_2768_);
v___x_2779_ = lean_nat_add(v_idx_2770_, v___x_2733_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 1, v___x_2779_);
lean_ctor_set(v___x_2746_, 0, v_array_2769_);
v___x_2781_ = v___x_2746_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_array_2769_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v___x_2779_);
v___x_2781_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v___x_2782_; 
v___x_2782_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2707_, v___x_2781_);
lean_dec_ref(v_config_2707_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_pos_2783_; lean_object* v_res_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
lean_dec(v_idx_2770_);
lean_del_object(v___x_2713_);
v_pos_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_pos_2783_);
v_res_2784_ = lean_ctor_get(v___x_2782_, 1);
lean_inc(v_res_2784_);
lean_dec_ref_known(v___x_2782_, 2);
v___x_2785_ = l_Std_Http_URI_EncodedString_decodeLossy___redArg(v_res_2784_);
lean_dec(v_res_2784_);
v___x_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
v___y_2749_ = v_res_2771_;
v_pos_2750_ = v_pos_2783_;
v_res_2751_ = v___x_2786_;
goto v___jp_2748_;
}
else
{
lean_object* v_pos_2787_; lean_object* v_err_2788_; 
v_pos_2787_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_pos_2787_);
v_err_2788_ = lean_ctor_get(v___x_2782_, 1);
lean_inc(v_err_2788_);
lean_dec_ref_known(v___x_2782_, 2);
v_idx_2757_ = v_idx_2770_;
v___y_2758_ = v_res_2771_;
v_pos_2759_ = v_pos_2787_;
v_err_2760_ = v_err_2788_;
goto v___jp_2756_;
}
}
}
}
}
v___jp_2792_:
{
uint8_t v___x_2797_; 
v___x_2797_ = lean_nat_dec_eq(v_idx_2791_, v_idx_2795_);
lean_dec(v_idx_2791_);
if (v___x_2797_ == 0)
{
lean_object* v___x_2798_; 
lean_dec(v_idx_2795_);
lean_dec_ref(v_array_2794_);
lean_del_object(v___x_2746_);
lean_dec(v_snd_2744_);
lean_dec(v_fst_2743_);
lean_del_object(v___x_2741_);
lean_del_object(v___x_2713_);
lean_dec(v_res_2711_);
lean_dec_ref(v_config_2707_);
v___x_2798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2798_, 0, v_pos_2793_);
lean_ctor_set(v___x_2798_, 1, v_err_2796_);
return v___x_2798_;
}
else
{
lean_object* v___x_2799_; 
lean_dec(v_err_2796_);
v___x_2799_ = lean_box(0);
v_pos_2768_ = v_pos_2793_;
v_array_2769_ = v_array_2794_;
v_idx_2770_ = v_idx_2795_;
v_res_2771_ = v___x_2799_;
goto v___jp_2767_;
}
}
}
}
}
else
{
lean_object* v_pos_2829_; lean_object* v_err_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
lean_del_object(v___x_2713_);
lean_dec(v_res_2711_);
lean_dec_ref(v_config_2707_);
v_pos_2829_ = lean_ctor_get(v___x_2737_, 0);
v_err_2830_ = lean_ctor_get(v___x_2737_, 1);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2832_ = v___x_2737_;
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_err_2830_);
lean_inc(v_pos_2829_);
lean_dec(v___x_2737_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_pos_2829_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v_err_2830_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
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
lean_object* v_pos_2843_; lean_object* v_err_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2851_; 
lean_dec_ref(v_config_2707_);
v_pos_2843_ = lean_ctor_get(v___x_2709_, 0);
v_err_2844_ = lean_ctor_get(v___x_2709_, 1);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2846_ = v___x_2709_;
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_err_2844_);
lean_inc(v_pos_2843_);
lean_dec(v___x_2709_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2849_; 
if (v_isShared_2847_ == 0)
{
v___x_2849_ = v___x_2846_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_pos_2843_);
lean_ctor_set(v_reuseFailAlloc_2850_, 1, v_err_2844_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(lean_object* v_a_2855_){
_start:
{
lean_object* v_array_2856_; lean_object* v_idx_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; 
v_array_2856_ = lean_ctor_get(v_a_2855_, 0);
v_idx_2857_ = lean_ctor_get(v_a_2855_, 1);
v___x_2858_ = lean_byte_array_size(v_array_2856_);
v___x_2859_ = lean_nat_dec_lt(v_idx_2857_, v___x_2858_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = lean_box(0);
v___x_2861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2861_, 0, v_a_2855_);
lean_ctor_set(v___x_2861_, 1, v___x_2860_);
return v___x_2861_;
}
else
{
uint8_t v___x_2862_; uint8_t v_got_2863_; uint8_t v___x_2864_; 
v___x_2862_ = 42;
v_got_2863_ = lean_byte_array_fget(v_array_2856_, v_idx_2857_);
v___x_2864_ = lean_uint8_dec_eq(v_got_2863_, v___x_2862_);
if (v___x_2864_ == 0)
{
lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2865_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1));
v___x_2866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2866_, 0, v_a_2855_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
return v___x_2866_;
}
else
{
lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2877_; 
lean_inc(v_idx_2857_);
lean_inc_ref(v_array_2856_);
v_isSharedCheck_2877_ = !lean_is_exclusive(v_a_2855_);
if (v_isSharedCheck_2877_ == 0)
{
lean_object* v_unused_2878_; lean_object* v_unused_2879_; 
v_unused_2878_ = lean_ctor_get(v_a_2855_, 1);
lean_dec(v_unused_2878_);
v_unused_2879_ = lean_ctor_get(v_a_2855_, 0);
lean_dec(v_unused_2879_);
v___x_2868_ = v_a_2855_;
v_isShared_2869_ = v_isSharedCheck_2877_;
goto v_resetjp_2867_;
}
else
{
lean_dec(v_a_2855_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2877_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2873_; 
v___x_2870_ = lean_unsigned_to_nat(1u);
v___x_2871_ = lean_nat_add(v_idx_2857_, v___x_2870_);
lean_dec(v_idx_2857_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 1, v___x_2871_);
v___x_2873_ = v___x_2868_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_array_2856_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v___x_2871_);
v___x_2873_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2874_ = lean_box(3);
v___x_2875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2873_);
lean_ctor_set(v___x_2875_, 1, v___x_2874_);
return v___x_2875_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(lean_object* v_config_2883_, lean_object* v_a_2884_){
_start:
{
lean_object* v_array_2888_; lean_object* v_idx_2889_; lean_object* v___x_2890_; uint8_t v___x_2891_; 
v_array_2888_ = lean_ctor_get(v_a_2884_, 0);
v_idx_2889_ = lean_ctor_get(v_a_2884_, 1);
v___x_2890_ = lean_byte_array_size(v_array_2888_);
v___x_2891_ = lean_nat_dec_lt(v_idx_2889_, v___x_2890_);
if (v___x_2891_ == 0)
{
lean_dec_ref(v_config_2883_);
goto v___jp_2885_;
}
else
{
uint8_t v___x_2892_; uint8_t v___x_2893_; uint8_t v___x_2894_; 
v___x_2892_ = lean_byte_array_fget(v_array_2888_, v_idx_2889_);
v___x_2893_ = 47;
v___x_2894_ = lean_uint8_dec_eq(v___x_2892_, v___x_2893_);
if (v___x_2894_ == 0)
{
lean_dec_ref(v_config_2883_);
goto v___jp_2885_;
}
else
{
lean_object* v___x_2895_; 
lean_inc_ref(v_a_2884_);
lean_inc_ref(v_config_2883_);
v___x_2895_ = l_Std_Http_URI_Parser_parsePath(v_config_2883_, v___x_2894_, v___x_2894_, v_a_2884_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_pos_2896_; lean_object* v_res_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2942_; 
v_pos_2896_ = lean_ctor_get(v___x_2895_, 0);
v_res_2897_ = lean_ctor_get(v___x_2895_, 1);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2899_ = v___x_2895_;
v_isShared_2900_ = v_isSharedCheck_2942_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_res_2897_);
lean_inc(v_pos_2896_);
lean_dec(v___x_2895_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2942_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v_pos_2902_; lean_object* v_res_2903_; lean_object* v_array_2908_; lean_object* v_idx_2909_; lean_object* v_pos_2911_; lean_object* v_idx_2912_; lean_object* v_err_2913_; lean_object* v___x_2917_; uint8_t v___x_2918_; 
v_array_2908_ = lean_ctor_get(v_pos_2896_, 0);
v_idx_2909_ = lean_ctor_get(v_pos_2896_, 1);
lean_inc(v_idx_2909_);
v___x_2917_ = lean_byte_array_size(v_array_2908_);
v___x_2918_ = lean_nat_dec_lt(v_idx_2909_, v___x_2917_);
if (v___x_2918_ == 0)
{
lean_object* v___x_2919_; 
lean_dec_ref(v_config_2883_);
v___x_2919_ = lean_box(0);
lean_inc(v_idx_2909_);
v_pos_2911_ = v_pos_2896_;
v_idx_2912_ = v_idx_2909_;
v_err_2913_ = v___x_2919_;
goto v___jp_2910_;
}
else
{
uint8_t v___x_2920_; uint8_t v_got_2921_; uint8_t v___x_2922_; 
v___x_2920_ = 63;
v_got_2921_ = lean_byte_array_fget(v_array_2908_, v_idx_2909_);
v___x_2922_ = lean_uint8_dec_eq(v_got_2921_, v___x_2920_);
if (v___x_2922_ == 0)
{
lean_object* v___x_2923_; 
lean_dec_ref(v_config_2883_);
v___x_2923_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__3));
lean_inc(v_idx_2909_);
v_pos_2911_ = v_pos_2896_;
v_idx_2912_ = v_idx_2909_;
v_err_2913_ = v___x_2923_;
goto v___jp_2910_;
}
else
{
lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2939_; 
lean_inc_ref(v_array_2908_);
v_isSharedCheck_2939_ = !lean_is_exclusive(v_pos_2896_);
if (v_isSharedCheck_2939_ == 0)
{
lean_object* v_unused_2940_; lean_object* v_unused_2941_; 
v_unused_2940_ = lean_ctor_get(v_pos_2896_, 1);
lean_dec(v_unused_2940_);
v_unused_2941_ = lean_ctor_get(v_pos_2896_, 0);
lean_dec(v_unused_2941_);
v___x_2925_ = v_pos_2896_;
v_isShared_2926_ = v_isSharedCheck_2939_;
goto v_resetjp_2924_;
}
else
{
lean_dec(v_pos_2896_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2939_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2930_; 
v___x_2927_ = lean_unsigned_to_nat(1u);
v___x_2928_ = lean_nat_add(v_idx_2909_, v___x_2927_);
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 1, v___x_2928_);
v___x_2930_ = v___x_2925_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_array_2908_);
lean_ctor_set(v_reuseFailAlloc_2938_, 1, v___x_2928_);
v___x_2930_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
lean_object* v___x_2931_; 
v___x_2931_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2883_, v___x_2930_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v_pos_2932_; lean_object* v_res_2933_; lean_object* v___x_2934_; 
lean_dec(v_idx_2909_);
lean_dec_ref(v_a_2884_);
v_pos_2932_ = lean_ctor_get(v___x_2931_, 0);
lean_inc(v_pos_2932_);
v_res_2933_ = lean_ctor_get(v___x_2931_, 1);
lean_inc(v_res_2933_);
lean_dec_ref_known(v___x_2931_, 2);
v___x_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2934_, 0, v_res_2933_);
v_pos_2902_ = v_pos_2932_;
v_res_2903_ = v___x_2934_;
goto v___jp_2901_;
}
else
{
lean_object* v_pos_2935_; lean_object* v_err_2936_; lean_object* v_idx_2937_; 
v_pos_2935_ = lean_ctor_get(v___x_2931_, 0);
lean_inc(v_pos_2935_);
v_err_2936_ = lean_ctor_get(v___x_2931_, 1);
lean_inc(v_err_2936_);
lean_dec_ref_known(v___x_2931_, 2);
v_idx_2937_ = lean_ctor_get(v_pos_2935_, 1);
lean_inc(v_idx_2937_);
v_pos_2911_ = v_pos_2935_;
v_idx_2912_ = v_idx_2937_;
v_err_2913_ = v_err_2936_;
goto v___jp_2910_;
}
}
}
}
}
v___jp_2901_:
{
lean_object* v___x_2904_; lean_object* v___x_2906_; 
v___x_2904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2904_, 0, v_res_2897_);
lean_ctor_set(v___x_2904_, 1, v_res_2903_);
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 1, v___x_2904_);
lean_ctor_set(v___x_2899_, 0, v_pos_2902_);
v___x_2906_ = v___x_2899_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_pos_2902_);
lean_ctor_set(v_reuseFailAlloc_2907_, 1, v___x_2904_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
v___jp_2910_:
{
uint8_t v___x_2914_; 
v___x_2914_ = lean_nat_dec_eq(v_idx_2909_, v_idx_2912_);
lean_dec(v_idx_2912_);
lean_dec(v_idx_2909_);
if (v___x_2914_ == 0)
{
lean_object* v___x_2915_; 
lean_dec_ref(v_pos_2911_);
lean_del_object(v___x_2899_);
lean_dec(v_res_2897_);
v___x_2915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2915_, 0, v_a_2884_);
lean_ctor_set(v___x_2915_, 1, v_err_2913_);
return v___x_2915_;
}
else
{
lean_object* v___x_2916_; 
lean_dec(v_err_2913_);
lean_dec_ref(v_a_2884_);
v___x_2916_ = lean_box(0);
v_pos_2902_ = v_pos_2911_;
v_res_2903_ = v___x_2916_;
goto v___jp_2901_;
}
}
}
}
else
{
lean_object* v_err_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
lean_dec_ref(v_config_2883_);
v_err_2943_ = lean_ctor_get(v___x_2895_, 1);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2950_ == 0)
{
lean_object* v_unused_2951_; 
v_unused_2951_ = lean_ctor_get(v___x_2895_, 0);
lean_dec(v_unused_2951_);
v___x_2945_ = v___x_2895_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_err_2943_);
lean_dec(v___x_2895_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 0, v_a_2884_);
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2884_);
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
v___jp_2885_:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1));
v___x_2887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2887_, 0, v_a_2884_);
lean_ctor_set(v___x_2887_, 1, v___x_2886_);
return v___x_2887_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_requireHttpHost(lean_object* v_scheme_2957_, lean_object* v_authority_2958_, lean_object* v_a_2959_){
_start:
{
lean_object* v___x_2966_; uint8_t v___x_2967_; 
v___x_2966_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_requireHttpHost___closed__2));
v___x_2967_ = lean_string_dec_eq(v_scheme_2957_, v___x_2966_);
if (v___x_2967_ == 0)
{
lean_object* v___x_2968_; uint8_t v___x_2969_; 
v___x_2968_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_requireHttpHost___closed__3));
v___x_2969_ = lean_string_dec_eq(v_scheme_2957_, v___x_2968_);
if (v___x_2969_ == 0)
{
goto v___jp_2960_;
}
else
{
goto v___jp_2963_;
}
}
else
{
goto v___jp_2963_;
}
v___jp_2960_:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2961_ = lean_box(0);
v___x_2962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2962_, 0, v_a_2959_);
lean_ctor_set(v___x_2962_, 1, v___x_2961_);
return v___x_2962_;
}
v___jp_2963_:
{
if (lean_obj_tag(v_authority_2958_) == 0)
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2964_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_requireHttpHost___closed__1));
v___x_2965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2965_, 0, v_a_2959_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
return v___x_2965_;
}
else
{
goto v___jp_2960_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_requireHttpHost___boxed(lean_object* v_scheme_2970_, lean_object* v_authority_2971_, lean_object* v_a_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_requireHttpHost(v_scheme_2970_, v_authority_2971_, v_a_2972_);
lean_dec(v_authority_2971_);
lean_dec_ref(v_scheme_2970_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(lean_object* v_config_2974_, lean_object* v_scheme_2975_, lean_object* v_a_2976_){
_start:
{
lean_object* v_array_2977_; lean_object* v_idx_2978_; lean_object* v___x_2979_; uint8_t v___x_2980_; 
v_array_2977_ = lean_ctor_get(v_a_2976_, 0);
v_idx_2978_ = lean_ctor_get(v_a_2976_, 1);
v___x_2979_ = lean_byte_array_size(v_array_2977_);
v___x_2980_ = lean_nat_dec_lt(v_idx_2978_, v___x_2979_);
if (v___x_2980_ == 0)
{
lean_object* v___x_2981_; lean_object* v___x_2982_; 
lean_dec_ref(v_scheme_2975_);
lean_dec_ref(v_config_2974_);
v___x_2981_ = lean_box(0);
v___x_2982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2982_, 0, v_a_2976_);
lean_ctor_set(v___x_2982_, 1, v___x_2981_);
return v___x_2982_;
}
else
{
uint8_t v___x_2983_; uint8_t v_got_2984_; uint8_t v___x_2985_; 
v___x_2983_ = 58;
v_got_2984_ = lean_byte_array_fget(v_array_2977_, v_idx_2978_);
v___x_2985_ = lean_uint8_dec_eq(v_got_2984_, v___x_2983_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
lean_dec_ref(v_scheme_2975_);
lean_dec_ref(v_config_2974_);
v___x_2986_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
v___x_2987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2987_, 0, v_a_2976_);
lean_ctor_set(v___x_2987_, 1, v___x_2986_);
return v___x_2987_;
}
else
{
lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_3074_; 
lean_inc(v_idx_2978_);
lean_inc_ref(v_array_2977_);
v_isSharedCheck_3074_ = !lean_is_exclusive(v_a_2976_);
if (v_isSharedCheck_3074_ == 0)
{
lean_object* v_unused_3075_; lean_object* v_unused_3076_; 
v_unused_3075_ = lean_ctor_get(v_a_2976_, 1);
lean_dec(v_unused_3075_);
v_unused_3076_ = lean_ctor_get(v_a_2976_, 0);
lean_dec(v_unused_3076_);
v___x_2989_ = v_a_2976_;
v_isShared_2990_ = v_isSharedCheck_3074_;
goto v_resetjp_2988_;
}
else
{
lean_dec(v_a_2976_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_3074_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2994_; 
v___x_2991_ = lean_unsigned_to_nat(1u);
v___x_2992_ = lean_nat_add(v_idx_2978_, v___x_2991_);
lean_dec(v_idx_2978_);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 1, v___x_2992_);
v___x_2994_ = v___x_2989_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_array_2977_);
lean_ctor_set(v_reuseFailAlloc_3073_, 1, v___x_2992_);
v___x_2994_ = v_reuseFailAlloc_3073_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
lean_object* v___x_2995_; 
lean_inc_ref(v_config_2974_);
v___x_2995_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2974_, v___x_2994_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_res_2996_; lean_object* v_pos_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3063_; 
v_res_2996_ = lean_ctor_get(v___x_2995_, 1);
v_pos_2997_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_2999_ = v___x_2995_;
v_isShared_3000_ = v_isSharedCheck_3063_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_res_2996_);
lean_inc(v_pos_2997_);
lean_dec(v___x_2995_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3063_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v_fst_3001_; lean_object* v_snd_3002_; lean_object* v_pos_3004_; lean_object* v_res_3005_; lean_object* v_array_3028_; lean_object* v_idx_3029_; lean_object* v_pos_3031_; lean_object* v_idx_3032_; lean_object* v_err_3033_; lean_object* v___x_3039_; uint8_t v___x_3040_; 
v_fst_3001_ = lean_ctor_get(v_res_2996_, 0);
lean_inc(v_fst_3001_);
v_snd_3002_ = lean_ctor_get(v_res_2996_, 1);
lean_inc(v_snd_3002_);
lean_dec(v_res_2996_);
v_array_3028_ = lean_ctor_get(v_pos_2997_, 0);
v_idx_3029_ = lean_ctor_get(v_pos_2997_, 1);
lean_inc(v_idx_3029_);
v___x_3039_ = lean_byte_array_size(v_array_3028_);
v___x_3040_ = lean_nat_dec_lt(v_idx_3029_, v___x_3039_);
if (v___x_3040_ == 0)
{
lean_object* v___x_3041_; 
lean_dec_ref(v_config_2974_);
v___x_3041_ = lean_box(0);
lean_inc(v_idx_3029_);
v_pos_3031_ = v_pos_2997_;
v_idx_3032_ = v_idx_3029_;
v_err_3033_ = v___x_3041_;
goto v___jp_3030_;
}
else
{
uint8_t v___x_3042_; uint8_t v_got_3043_; uint8_t v___x_3044_; 
v___x_3042_ = 63;
v_got_3043_ = lean_byte_array_fget(v_array_3028_, v_idx_3029_);
v___x_3044_ = lean_uint8_dec_eq(v_got_3043_, v___x_3042_);
if (v___x_3044_ == 0)
{
lean_object* v___x_3045_; 
lean_dec_ref(v_config_2974_);
v___x_3045_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__3));
lean_inc(v_idx_3029_);
v_pos_3031_ = v_pos_2997_;
v_idx_3032_ = v_idx_3029_;
v_err_3033_ = v___x_3045_;
goto v___jp_3030_;
}
else
{
lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3060_; 
lean_inc_ref(v_array_3028_);
v_isSharedCheck_3060_ = !lean_is_exclusive(v_pos_2997_);
if (v_isSharedCheck_3060_ == 0)
{
lean_object* v_unused_3061_; lean_object* v_unused_3062_; 
v_unused_3061_ = lean_ctor_get(v_pos_2997_, 1);
lean_dec(v_unused_3061_);
v_unused_3062_ = lean_ctor_get(v_pos_2997_, 0);
lean_dec(v_unused_3062_);
v___x_3047_ = v_pos_2997_;
v_isShared_3048_ = v_isSharedCheck_3060_;
goto v_resetjp_3046_;
}
else
{
lean_dec(v_pos_2997_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3060_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3049_; lean_object* v___x_3051_; 
v___x_3049_ = lean_nat_add(v_idx_3029_, v___x_2991_);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 1, v___x_3049_);
v___x_3051_ = v___x_3047_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_array_3028_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v___x_3049_);
v___x_3051_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
lean_object* v___x_3052_; 
v___x_3052_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2974_, v___x_3051_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_pos_3053_; lean_object* v_res_3054_; lean_object* v___x_3055_; 
lean_dec(v_idx_3029_);
lean_del_object(v___x_2999_);
v_pos_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_pos_3053_);
v_res_3054_ = lean_ctor_get(v___x_3052_, 1);
lean_inc(v_res_3054_);
lean_dec_ref_known(v___x_3052_, 2);
v___x_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3055_, 0, v_res_3054_);
v_pos_3004_ = v_pos_3053_;
v_res_3005_ = v___x_3055_;
goto v___jp_3003_;
}
else
{
lean_object* v_pos_3056_; lean_object* v_err_3057_; lean_object* v_idx_3058_; 
v_pos_3056_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_pos_3056_);
v_err_3057_ = lean_ctor_get(v___x_3052_, 1);
lean_inc(v_err_3057_);
lean_dec_ref_known(v___x_3052_, 2);
v_idx_3058_ = lean_ctor_get(v_pos_3056_, 1);
lean_inc(v_idx_3058_);
v_pos_3031_ = v_pos_3056_;
v_idx_3032_ = v_idx_3058_;
v_err_3033_ = v_err_3057_;
goto v___jp_3030_;
}
}
}
}
}
v___jp_3003_:
{
lean_object* v___x_3006_; 
v___x_3006_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_requireHttpHost(v_scheme_2975_, v_fst_3001_, v_pos_3004_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_pos_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3017_; 
v_pos_3007_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3017_ == 0)
{
lean_object* v_unused_3018_; 
v_unused_3018_ = lean_ctor_get(v___x_3006_, 1);
lean_dec(v_unused_3018_);
v___x_3009_ = v___x_3006_;
v_isShared_3010_ = v_isSharedCheck_3017_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_pos_3007_);
lean_dec(v___x_3006_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3017_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3015_; 
v___x_3011_ = lean_box(0);
v___x_3012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3012_, 0, v_scheme_2975_);
lean_ctor_set(v___x_3012_, 1, v_fst_3001_);
lean_ctor_set(v___x_3012_, 2, v_snd_3002_);
lean_ctor_set(v___x_3012_, 3, v_res_3005_);
lean_ctor_set(v___x_3012_, 4, v___x_3011_);
v___x_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3012_);
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 1, v___x_3013_);
v___x_3015_ = v___x_3009_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_pos_3007_);
lean_ctor_set(v_reuseFailAlloc_3016_, 1, v___x_3013_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
else
{
lean_object* v_pos_3019_; lean_object* v_err_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3027_; 
lean_dec(v_res_3005_);
lean_dec(v_snd_3002_);
lean_dec(v_fst_3001_);
lean_dec_ref(v_scheme_2975_);
v_pos_3019_ = lean_ctor_get(v___x_3006_, 0);
v_err_3020_ = lean_ctor_get(v___x_3006_, 1);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3022_ = v___x_3006_;
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_err_3020_);
lean_inc(v_pos_3019_);
lean_dec(v___x_3006_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3025_; 
if (v_isShared_3023_ == 0)
{
v___x_3025_ = v___x_3022_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_pos_3019_);
lean_ctor_set(v_reuseFailAlloc_3026_, 1, v_err_3020_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
}
v___jp_3030_:
{
uint8_t v___x_3034_; 
v___x_3034_ = lean_nat_dec_eq(v_idx_3029_, v_idx_3032_);
lean_dec(v_idx_3032_);
lean_dec(v_idx_3029_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3036_; 
lean_dec(v_snd_3002_);
lean_dec(v_fst_3001_);
lean_dec_ref(v_scheme_2975_);
if (v_isShared_3000_ == 0)
{
lean_ctor_set_tag(v___x_2999_, 1);
lean_ctor_set(v___x_2999_, 1, v_err_3033_);
lean_ctor_set(v___x_2999_, 0, v_pos_3031_);
v___x_3036_ = v___x_2999_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_pos_3031_);
lean_ctor_set(v_reuseFailAlloc_3037_, 1, v_err_3033_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
else
{
lean_object* v___x_3038_; 
lean_dec(v_err_3033_);
lean_del_object(v___x_2999_);
v___x_3038_ = lean_box(0);
v_pos_3004_ = v_pos_3031_;
v_res_3005_ = v___x_3038_;
goto v___jp_3003_;
}
}
}
}
else
{
lean_object* v_pos_3064_; lean_object* v_err_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3072_; 
lean_dec_ref(v_scheme_2975_);
lean_dec_ref(v_config_2974_);
v_pos_3064_ = lean_ctor_get(v___x_2995_, 0);
v_err_3065_ = lean_ctor_get(v___x_2995_, 1);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3067_ = v___x_2995_;
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_err_3065_);
lean_inc(v_pos_3064_);
lean_dec(v___x_2995_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3070_; 
if (v_isShared_3068_ == 0)
{
v___x_3070_ = v___x_3067_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_pos_3064_);
lean_ctor_set(v_reuseFailAlloc_3071_, 1, v_err_3065_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(lean_object* v_config_3083_, lean_object* v_a_3084_){
_start:
{
lean_object* v___x_3088_; 
lean_inc_ref(v_a_3084_);
v___x_3088_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3083_, v_a_3084_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v_pos_3089_; lean_object* v_res_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3204_; 
v_pos_3089_ = lean_ctor_get(v___x_3088_, 0);
v_res_3090_ = lean_ctor_get(v___x_3088_, 1);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3092_ = v___x_3088_;
v_isShared_3093_ = v_isSharedCheck_3204_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_res_3090_);
lean_inc(v_pos_3089_);
lean_dec(v___x_3088_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3204_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v_pos_3097_; lean_object* v_res_3098_; lean_object* v___y_3122_; lean_object* v_idx_3123_; lean_object* v___y_3124_; lean_object* v_pos_3125_; lean_object* v_idx_3126_; lean_object* v_err_3127_; lean_object* v___x_3198_; uint8_t v___x_3199_; 
v___x_3198_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_requireHttpHost___closed__2));
v___x_3199_ = lean_string_dec_eq(v_res_3090_, v___x_3198_);
if (v___x_3199_ == 0)
{
lean_object* v___x_3200_; uint8_t v___x_3201_; 
v___x_3200_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_requireHttpHost___closed__3));
v___x_3201_ = lean_string_dec_eq(v_res_3090_, v___x_3200_);
if (v___x_3201_ == 0)
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
lean_del_object(v___x_3092_);
lean_dec(v_res_3090_);
lean_dec(v_pos_3089_);
lean_dec_ref(v_config_3083_);
v___x_3202_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3));
v___x_3203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3203_, 0, v_a_3084_);
lean_ctor_set(v___x_3203_, 1, v___x_3202_);
return v___x_3203_;
}
else
{
goto v___jp_3133_;
}
}
else
{
goto v___jp_3133_;
}
v___jp_3094_:
{
lean_object* v___x_3099_; 
v___x_3099_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_requireHttpHost(v_res_3090_, v___y_3096_, v_pos_3097_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_object* v_pos_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3110_; 
lean_dec_ref(v_a_3084_);
v_pos_3100_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3110_ == 0)
{
lean_object* v_unused_3111_; 
v_unused_3111_ = lean_ctor_get(v___x_3099_, 1);
lean_dec(v_unused_3111_);
v___x_3102_ = v___x_3099_;
v_isShared_3103_ = v_isSharedCheck_3110_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_pos_3100_);
lean_dec(v___x_3099_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3110_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3108_; 
v___x_3104_ = lean_box(0);
v___x_3105_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3105_, 0, v_res_3090_);
lean_ctor_set(v___x_3105_, 1, v___y_3096_);
lean_ctor_set(v___x_3105_, 2, v___y_3095_);
lean_ctor_set(v___x_3105_, 3, v_res_3098_);
lean_ctor_set(v___x_3105_, 4, v___x_3104_);
v___x_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3105_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 1, v___x_3106_);
v___x_3108_ = v___x_3102_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_pos_3100_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v___x_3106_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
else
{
lean_object* v_err_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
lean_dec(v_res_3098_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v_res_3090_);
v_err_3112_ = lean_ctor_get(v___x_3099_, 1);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3119_ == 0)
{
lean_object* v_unused_3120_; 
v_unused_3120_ = lean_ctor_get(v___x_3099_, 0);
lean_dec(v_unused_3120_);
v___x_3114_ = v___x_3099_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_err_3112_);
lean_dec(v___x_3099_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 0, v_a_3084_);
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3084_);
lean_ctor_set(v_reuseFailAlloc_3118_, 1, v_err_3112_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
v___jp_3121_:
{
uint8_t v___x_3128_; 
v___x_3128_ = lean_nat_dec_eq(v_idx_3123_, v_idx_3126_);
lean_dec(v_idx_3126_);
lean_dec(v_idx_3123_);
if (v___x_3128_ == 0)
{
lean_object* v___x_3130_; 
lean_dec_ref(v_pos_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3122_);
lean_dec(v_res_3090_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set_tag(v___x_3092_, 1);
lean_ctor_set(v___x_3092_, 1, v_err_3127_);
lean_ctor_set(v___x_3092_, 0, v_a_3084_);
v___x_3130_ = v___x_3092_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_3084_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_err_3127_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
else
{
lean_object* v___x_3132_; 
lean_dec(v_err_3127_);
lean_del_object(v___x_3092_);
v___x_3132_ = lean_box(0);
v___y_3095_ = v___y_3122_;
v___y_3096_ = v___y_3124_;
v_pos_3097_ = v_pos_3125_;
v_res_3098_ = v___x_3132_;
goto v___jp_3094_;
}
}
v___jp_3133_:
{
lean_object* v_array_3134_; lean_object* v_idx_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3197_; 
v_array_3134_ = lean_ctor_get(v_pos_3089_, 0);
v_idx_3135_ = lean_ctor_get(v_pos_3089_, 1);
v_isSharedCheck_3197_ = !lean_is_exclusive(v_pos_3089_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3137_ = v_pos_3089_;
v_isShared_3138_ = v_isSharedCheck_3197_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_idx_3135_);
lean_inc(v_array_3134_);
lean_dec(v_pos_3089_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3197_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3139_; uint8_t v___x_3140_; 
v___x_3139_ = lean_byte_array_size(v_array_3134_);
v___x_3140_ = lean_nat_dec_lt(v_idx_3135_, v___x_3139_);
if (v___x_3140_ == 0)
{
lean_object* v___x_3141_; lean_object* v___x_3142_; 
lean_del_object(v___x_3137_);
lean_dec(v_idx_3135_);
lean_dec_ref(v_array_3134_);
lean_del_object(v___x_3092_);
lean_dec(v_res_3090_);
lean_dec_ref(v_config_3083_);
v___x_3141_ = lean_box(0);
v___x_3142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3142_, 0, v_a_3084_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
return v___x_3142_;
}
else
{
uint8_t v___x_3143_; uint8_t v_got_3144_; uint8_t v___x_3145_; 
v___x_3143_ = 58;
v_got_3144_ = lean_byte_array_fget(v_array_3134_, v_idx_3135_);
v___x_3145_ = lean_uint8_dec_eq(v_got_3144_, v___x_3143_);
if (v___x_3145_ == 0)
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
lean_del_object(v___x_3137_);
lean_dec(v_idx_3135_);
lean_dec_ref(v_array_3134_);
lean_del_object(v___x_3092_);
lean_dec(v_res_3090_);
lean_dec_ref(v_config_3083_);
v___x_3146_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
v___x_3147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3147_, 0, v_a_3084_);
lean_ctor_set(v___x_3147_, 1, v___x_3146_);
return v___x_3147_;
}
else
{
lean_object* v___x_3148_; lean_object* v___x_3149_; uint8_t v___x_3150_; 
v___x_3148_ = lean_unsigned_to_nat(1u);
v___x_3149_ = lean_nat_add(v_idx_3135_, v___x_3148_);
lean_dec(v_idx_3135_);
v___x_3150_ = lean_nat_dec_lt(v___x_3149_, v___x_3139_);
if (v___x_3150_ == 0)
{
lean_dec(v___x_3149_);
lean_del_object(v___x_3137_);
lean_dec_ref(v_array_3134_);
lean_del_object(v___x_3092_);
lean_dec(v_res_3090_);
lean_dec_ref(v_config_3083_);
goto v___jp_3085_;
}
else
{
uint8_t v___x_3151_; uint8_t v___x_3152_; uint8_t v___x_3153_; 
v___x_3151_ = lean_byte_array_fget(v_array_3134_, v___x_3149_);
v___x_3152_ = 47;
v___x_3153_ = lean_uint8_dec_eq(v___x_3151_, v___x_3152_);
if (v___x_3153_ == 0)
{
lean_dec(v___x_3149_);
lean_del_object(v___x_3137_);
lean_dec_ref(v_array_3134_);
lean_del_object(v___x_3092_);
lean_dec(v_res_3090_);
lean_dec_ref(v_config_3083_);
goto v___jp_3085_;
}
else
{
lean_object* v___x_3155_; 
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 1, v___x_3149_);
v___x_3155_ = v___x_3137_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_array_3134_);
lean_ctor_set(v_reuseFailAlloc_3196_, 1, v___x_3149_);
v___x_3155_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
lean_object* v___x_3156_; 
lean_inc_ref(v_config_3083_);
v___x_3156_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_3083_, v___x_3155_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_object* v_res_3157_; lean_object* v_pos_3158_; lean_object* v_fst_3159_; lean_object* v_snd_3160_; lean_object* v_array_3161_; lean_object* v_idx_3162_; lean_object* v___x_3163_; uint8_t v___x_3164_; 
v_res_3157_ = lean_ctor_get(v___x_3156_, 1);
lean_inc(v_res_3157_);
v_pos_3158_ = lean_ctor_get(v___x_3156_, 0);
lean_inc(v_pos_3158_);
lean_dec_ref_known(v___x_3156_, 2);
v_fst_3159_ = lean_ctor_get(v_res_3157_, 0);
lean_inc(v_fst_3159_);
v_snd_3160_ = lean_ctor_get(v_res_3157_, 1);
lean_inc(v_snd_3160_);
lean_dec(v_res_3157_);
v_array_3161_ = lean_ctor_get(v_pos_3158_, 0);
v_idx_3162_ = lean_ctor_get(v_pos_3158_, 1);
lean_inc(v_idx_3162_);
v___x_3163_ = lean_byte_array_size(v_array_3161_);
v___x_3164_ = lean_nat_dec_lt(v_idx_3162_, v___x_3163_);
if (v___x_3164_ == 0)
{
lean_object* v___x_3165_; 
lean_dec_ref(v_config_3083_);
v___x_3165_ = lean_box(0);
lean_inc(v_idx_3162_);
v___y_3122_ = v_snd_3160_;
v_idx_3123_ = v_idx_3162_;
v___y_3124_ = v_fst_3159_;
v_pos_3125_ = v_pos_3158_;
v_idx_3126_ = v_idx_3162_;
v_err_3127_ = v___x_3165_;
goto v___jp_3121_;
}
else
{
uint8_t v___x_3166_; uint8_t v_got_3167_; uint8_t v___x_3168_; 
v___x_3166_ = 63;
v_got_3167_ = lean_byte_array_fget(v_array_3161_, v_idx_3162_);
v___x_3168_ = lean_uint8_dec_eq(v_got_3167_, v___x_3166_);
if (v___x_3168_ == 0)
{
lean_object* v___x_3169_; 
lean_dec_ref(v_config_3083_);
v___x_3169_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__3));
lean_inc(v_idx_3162_);
v___y_3122_ = v_snd_3160_;
v_idx_3123_ = v_idx_3162_;
v___y_3124_ = v_fst_3159_;
v_pos_3125_ = v_pos_3158_;
v_idx_3126_ = v_idx_3162_;
v_err_3127_ = v___x_3169_;
goto v___jp_3121_;
}
else
{
lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3184_; 
lean_inc_ref(v_array_3161_);
v_isSharedCheck_3184_ = !lean_is_exclusive(v_pos_3158_);
if (v_isSharedCheck_3184_ == 0)
{
lean_object* v_unused_3185_; lean_object* v_unused_3186_; 
v_unused_3185_ = lean_ctor_get(v_pos_3158_, 1);
lean_dec(v_unused_3185_);
v_unused_3186_ = lean_ctor_get(v_pos_3158_, 0);
lean_dec(v_unused_3186_);
v___x_3171_ = v_pos_3158_;
v_isShared_3172_ = v_isSharedCheck_3184_;
goto v_resetjp_3170_;
}
else
{
lean_dec(v_pos_3158_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3184_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3173_; lean_object* v___x_3175_; 
v___x_3173_ = lean_nat_add(v_idx_3162_, v___x_3148_);
if (v_isShared_3172_ == 0)
{
lean_ctor_set(v___x_3171_, 1, v___x_3173_);
v___x_3175_ = v___x_3171_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_array_3161_);
lean_ctor_set(v_reuseFailAlloc_3183_, 1, v___x_3173_);
v___x_3175_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
lean_object* v___x_3176_; 
v___x_3176_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3083_, v___x_3175_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v_pos_3177_; lean_object* v_res_3178_; lean_object* v___x_3179_; 
lean_dec(v_idx_3162_);
lean_del_object(v___x_3092_);
v_pos_3177_ = lean_ctor_get(v___x_3176_, 0);
lean_inc(v_pos_3177_);
v_res_3178_ = lean_ctor_get(v___x_3176_, 1);
lean_inc(v_res_3178_);
lean_dec_ref_known(v___x_3176_, 2);
v___x_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3179_, 0, v_res_3178_);
v___y_3095_ = v_snd_3160_;
v___y_3096_ = v_fst_3159_;
v_pos_3097_ = v_pos_3177_;
v_res_3098_ = v___x_3179_;
goto v___jp_3094_;
}
else
{
lean_object* v_pos_3180_; lean_object* v_err_3181_; lean_object* v_idx_3182_; 
v_pos_3180_ = lean_ctor_get(v___x_3176_, 0);
lean_inc(v_pos_3180_);
v_err_3181_ = lean_ctor_get(v___x_3176_, 1);
lean_inc(v_err_3181_);
lean_dec_ref_known(v___x_3176_, 2);
v_idx_3182_ = lean_ctor_get(v_pos_3180_, 1);
lean_inc(v_idx_3182_);
v___y_3122_ = v_snd_3160_;
v_idx_3123_ = v_idx_3162_;
v___y_3124_ = v_fst_3159_;
v_pos_3125_ = v_pos_3180_;
v_idx_3126_ = v_idx_3182_;
v_err_3127_ = v_err_3181_;
goto v___jp_3121_;
}
}
}
}
}
}
else
{
lean_object* v_err_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
lean_del_object(v___x_3092_);
lean_dec(v_res_3090_);
lean_dec_ref(v_config_3083_);
v_err_3187_ = lean_ctor_get(v___x_3156_, 1);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3194_ == 0)
{
lean_object* v_unused_3195_; 
v_unused_3195_ = lean_ctor_get(v___x_3156_, 0);
lean_dec(v_unused_3195_);
v___x_3189_ = v___x_3156_;
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_err_3187_);
lean_dec(v___x_3156_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 0, v_a_3084_);
v___x_3192_ = v___x_3189_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3084_);
lean_ctor_set(v_reuseFailAlloc_3193_, 1, v_err_3187_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
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
lean_object* v_err_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
lean_dec_ref(v_config_3083_);
v_err_3205_ = lean_ctor_get(v___x_3088_, 1);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3212_ == 0)
{
lean_object* v_unused_3213_; 
v_unused_3213_ = lean_ctor_get(v___x_3088_, 0);
lean_dec(v_unused_3213_);
v___x_3207_ = v___x_3088_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_err_3205_);
lean_dec(v___x_3088_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 0, v_a_3084_);
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3084_);
lean_ctor_set(v_reuseFailAlloc_3211_, 1, v_err_3205_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
v___jp_3085_:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3086_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1));
v___x_3087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3087_, 0, v_a_3084_);
lean_ctor_set(v___x_3087_, 1, v___x_3086_);
return v___x_3087_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(lean_object* v_config_3214_, lean_object* v_a_3215_){
_start:
{
lean_object* v___x_3216_; 
lean_inc_ref(v_a_3215_);
v___x_3216_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3214_, v_a_3215_);
if (lean_obj_tag(v___x_3216_) == 0)
{
lean_object* v_pos_3217_; lean_object* v_res_3218_; lean_object* v___x_3219_; 
v_pos_3217_ = lean_ctor_get(v___x_3216_, 0);
lean_inc(v_pos_3217_);
v_res_3218_ = lean_ctor_get(v___x_3216_, 1);
lean_inc(v_res_3218_);
lean_dec_ref_known(v___x_3216_, 2);
v___x_3219_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(v_config_3214_, v_res_3218_, v_pos_3217_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_dec_ref(v_a_3215_);
return v___x_3219_;
}
else
{
lean_object* v_err_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3227_; 
v_err_3220_ = lean_ctor_get(v___x_3219_, 1);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3227_ == 0)
{
lean_object* v_unused_3228_; 
v_unused_3228_ = lean_ctor_get(v___x_3219_, 0);
lean_dec(v_unused_3228_);
v___x_3222_ = v___x_3219_;
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_err_3220_);
lean_dec(v___x_3219_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3225_; 
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 0, v_a_3215_);
v___x_3225_ = v___x_3222_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_a_3215_);
lean_ctor_set(v_reuseFailAlloc_3226_, 1, v_err_3220_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
}
else
{
lean_object* v_err_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3236_; 
lean_dec_ref(v_config_3214_);
v_err_3229_ = lean_ctor_get(v___x_3216_, 1);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3236_ == 0)
{
lean_object* v_unused_3237_; 
v_unused_3237_ = lean_ctor_get(v___x_3216_, 0);
lean_dec(v_unused_3237_);
v___x_3231_ = v___x_3216_;
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_err_3229_);
lean_dec(v___x_3216_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3234_; 
if (v_isShared_3232_ == 0)
{
lean_ctor_set(v___x_3231_, 0, v_a_3215_);
v___x_3234_ = v___x_3231_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_a_3215_);
lean_ctor_set(v_reuseFailAlloc_3235_, 1, v_err_3229_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(lean_object* v_config_3238_, lean_object* v_a_3239_){
_start:
{
lean_object* v___x_3240_; 
lean_inc_ref(v_a_3239_);
v___x_3240_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_3238_, v_a_3239_);
if (lean_obj_tag(v___x_3240_) == 0)
{
lean_object* v_pos_3241_; lean_object* v_res_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3294_; 
v_pos_3241_ = lean_ctor_get(v___x_3240_, 0);
v_res_3242_ = lean_ctor_get(v___x_3240_, 1);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3244_ = v___x_3240_;
v_isShared_3245_ = v_isSharedCheck_3294_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_res_3242_);
lean_inc(v_pos_3241_);
lean_dec(v___x_3240_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3294_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v_array_3246_; lean_object* v_idx_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3293_; 
v_array_3246_ = lean_ctor_get(v_pos_3241_, 0);
v_idx_3247_ = lean_ctor_get(v_pos_3241_, 1);
v_isSharedCheck_3293_ = !lean_is_exclusive(v_pos_3241_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3249_ = v_pos_3241_;
v_isShared_3250_ = v_isSharedCheck_3293_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_idx_3247_);
lean_inc(v_array_3246_);
lean_dec(v_pos_3241_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3293_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3251_; uint8_t v___x_3252_; 
v___x_3251_ = lean_byte_array_size(v_array_3246_);
v___x_3252_ = lean_nat_dec_lt(v_idx_3247_, v___x_3251_);
if (v___x_3252_ == 0)
{
lean_object* v___x_3253_; lean_object* v___x_3255_; 
lean_del_object(v___x_3249_);
lean_dec(v_idx_3247_);
lean_dec_ref(v_array_3246_);
lean_dec(v_res_3242_);
v___x_3253_ = lean_box(0);
if (v_isShared_3245_ == 0)
{
lean_ctor_set_tag(v___x_3244_, 1);
lean_ctor_set(v___x_3244_, 1, v___x_3253_);
lean_ctor_set(v___x_3244_, 0, v_a_3239_);
v___x_3255_ = v___x_3244_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_a_3239_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v___x_3253_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
else
{
uint8_t v___x_3257_; uint8_t v_got_3258_; uint8_t v___x_3259_; 
v___x_3257_ = 58;
v_got_3258_ = lean_byte_array_fget(v_array_3246_, v_idx_3247_);
v___x_3259_ = lean_uint8_dec_eq(v_got_3258_, v___x_3257_);
if (v___x_3259_ == 0)
{
lean_object* v___x_3260_; lean_object* v___x_3262_; 
lean_del_object(v___x_3249_);
lean_dec(v_idx_3247_);
lean_dec_ref(v_array_3246_);
lean_dec(v_res_3242_);
v___x_3260_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
if (v_isShared_3245_ == 0)
{
lean_ctor_set_tag(v___x_3244_, 1);
lean_ctor_set(v___x_3244_, 1, v___x_3260_);
lean_ctor_set(v___x_3244_, 0, v_a_3239_);
v___x_3262_ = v___x_3244_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_a_3239_);
lean_ctor_set(v_reuseFailAlloc_3263_, 1, v___x_3260_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
else
{
lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3267_; 
lean_del_object(v___x_3244_);
v___x_3264_ = lean_unsigned_to_nat(1u);
v___x_3265_ = lean_nat_add(v_idx_3247_, v___x_3264_);
lean_dec(v_idx_3247_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 1, v___x_3265_);
v___x_3267_ = v___x_3249_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_array_3246_);
lean_ctor_set(v_reuseFailAlloc_3292_, 1, v___x_3265_);
v___x_3267_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
lean_object* v___x_3268_; 
v___x_3268_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_3267_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_pos_3269_; lean_object* v_res_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3282_; 
lean_dec_ref(v_a_3239_);
v_pos_3269_ = lean_ctor_get(v___x_3268_, 0);
v_res_3270_ = lean_ctor_get(v___x_3268_, 1);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3272_ = v___x_3268_;
v_isShared_3273_ = v_isSharedCheck_3282_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_res_3270_);
lean_inc(v_pos_3269_);
lean_dec(v___x_3268_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3282_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; uint16_t v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3280_; 
v___x_3274_ = lean_box(0);
v___x_3275_ = lean_alloc_ctor(2, 0, 2);
v___x_3276_ = lean_unbox(v_res_3270_);
lean_dec(v_res_3270_);
lean_ctor_set_uint16(v___x_3275_, 0, v___x_3276_);
v___x_3277_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3274_);
lean_ctor_set(v___x_3277_, 1, v_res_3242_);
lean_ctor_set(v___x_3277_, 2, v___x_3275_);
v___x_3278_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3277_);
if (v_isShared_3273_ == 0)
{
lean_ctor_set(v___x_3272_, 1, v___x_3278_);
v___x_3280_ = v___x_3272_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_pos_3269_);
lean_ctor_set(v_reuseFailAlloc_3281_, 1, v___x_3278_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
}
else
{
lean_object* v_err_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3290_; 
lean_dec(v_res_3242_);
v_err_3283_ = lean_ctor_get(v___x_3268_, 1);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3290_ == 0)
{
lean_object* v_unused_3291_; 
v_unused_3291_ = lean_ctor_get(v___x_3268_, 0);
lean_dec(v_unused_3291_);
v___x_3285_ = v___x_3268_;
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_err_3283_);
lean_dec(v___x_3268_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3288_; 
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 0, v_a_3239_);
v___x_3288_ = v___x_3285_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_a_3239_);
lean_ctor_set(v_reuseFailAlloc_3289_, 1, v_err_3283_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
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
lean_object* v_err_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3302_; 
v_err_3295_ = lean_ctor_get(v___x_3240_, 1);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3302_ == 0)
{
lean_object* v_unused_3303_; 
v_unused_3303_ = lean_ctor_get(v___x_3240_, 0);
lean_dec(v_unused_3303_);
v___x_3297_ = v___x_3240_;
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_err_3295_);
lean_dec(v___x_3240_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3300_; 
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 0, v_a_3239_);
v___x_3300_ = v___x_3297_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3239_);
lean_ctor_set(v_reuseFailAlloc_3301_, 1, v_err_3295_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object* v_config_3304_, lean_object* v_a_3305_){
_start:
{
lean_object* v___x_3306_; 
lean_inc_ref(v_a_3305_);
v___x_3306_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(v_a_3305_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_dec_ref(v_a_3305_);
lean_dec_ref(v_config_3304_);
return v___x_3306_;
}
else
{
lean_object* v_pos_3307_; lean_object* v_idx_3308_; lean_object* v_idx_3309_; uint8_t v___x_3310_; 
v_pos_3307_ = lean_ctor_get(v___x_3306_, 0);
v_idx_3308_ = lean_ctor_get(v_a_3305_, 1);
lean_inc(v_idx_3308_);
lean_dec_ref(v_a_3305_);
v_idx_3309_ = lean_ctor_get(v_pos_3307_, 1);
v___x_3310_ = lean_nat_dec_eq(v_idx_3308_, v_idx_3309_);
lean_dec(v_idx_3308_);
if (v___x_3310_ == 0)
{
lean_dec_ref(v_config_3304_);
return v___x_3306_;
}
else
{
lean_object* v___x_3311_; 
lean_inc(v_idx_3309_);
lean_inc(v_pos_3307_);
lean_dec_ref_known(v___x_3306_, 2);
lean_inc_ref(v_config_3304_);
v___x_3311_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(v_config_3304_, v_pos_3307_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_dec(v_idx_3309_);
lean_dec_ref(v_config_3304_);
return v___x_3311_;
}
else
{
lean_object* v_pos_3312_; lean_object* v_idx_3313_; uint8_t v___x_3314_; 
v_pos_3312_ = lean_ctor_get(v___x_3311_, 0);
v_idx_3313_ = lean_ctor_get(v_pos_3312_, 1);
v___x_3314_ = lean_nat_dec_eq(v_idx_3309_, v_idx_3313_);
lean_dec(v_idx_3309_);
if (v___x_3314_ == 0)
{
lean_dec_ref(v_config_3304_);
return v___x_3311_;
}
else
{
lean_object* v___x_3315_; 
lean_inc(v_idx_3313_);
lean_inc(v_pos_3312_);
lean_dec_ref_known(v___x_3311_, 2);
lean_inc_ref(v_config_3304_);
v___x_3315_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(v_config_3304_, v_pos_3312_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_dec(v_idx_3313_);
lean_dec_ref(v_config_3304_);
return v___x_3315_;
}
else
{
lean_object* v_pos_3316_; lean_object* v_idx_3317_; uint8_t v___x_3318_; 
v_pos_3316_ = lean_ctor_get(v___x_3315_, 0);
v_idx_3317_ = lean_ctor_get(v_pos_3316_, 1);
v___x_3318_ = lean_nat_dec_eq(v_idx_3313_, v_idx_3317_);
lean_dec(v_idx_3313_);
if (v___x_3318_ == 0)
{
lean_dec_ref(v_config_3304_);
return v___x_3315_;
}
else
{
lean_object* v___x_3319_; 
lean_inc(v_idx_3317_);
lean_inc(v_pos_3316_);
lean_dec_ref_known(v___x_3315_, 2);
lean_inc_ref(v_config_3304_);
v___x_3319_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3304_, v_pos_3316_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_dec(v_idx_3317_);
lean_dec_ref(v_config_3304_);
return v___x_3319_;
}
else
{
lean_object* v_pos_3320_; lean_object* v_idx_3321_; uint8_t v___x_3322_; 
v_pos_3320_ = lean_ctor_get(v___x_3319_, 0);
v_idx_3321_ = lean_ctor_get(v_pos_3320_, 1);
v___x_3322_ = lean_nat_dec_eq(v_idx_3317_, v_idx_3321_);
lean_dec(v_idx_3317_);
if (v___x_3322_ == 0)
{
lean_dec_ref(v_config_3304_);
return v___x_3319_;
}
else
{
lean_object* v___x_3323_; 
lean_inc(v_pos_3320_);
lean_dec_ref_known(v___x_3319_, 2);
v___x_3323_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(v_config_3304_, v_pos_3320_);
return v___x_3323_;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(lean_object* v_config_3324_, lean_object* v_a_3325_){
_start:
{
lean_object* v___x_3326_; 
v___x_3326_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_3324_, v_a_3325_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_pos_3327_; lean_object* v_res_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3336_; 
v_pos_3327_ = lean_ctor_get(v___x_3326_, 0);
v_res_3328_ = lean_ctor_get(v___x_3326_, 1);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3330_ = v___x_3326_;
v_isShared_3331_ = v_isSharedCheck_3336_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_res_3328_);
lean_inc(v_pos_3327_);
lean_dec(v___x_3326_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3336_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3332_; lean_object* v___x_3334_; 
v___x_3332_ = l_Std_Http_URI_EncodedString_decodeLossy___redArg(v_res_3328_);
lean_dec(v_res_3328_);
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 1, v___x_3332_);
v___x_3334_ = v___x_3330_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_pos_3327_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v___x_3332_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
else
{
lean_object* v_pos_3337_; lean_object* v_err_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3345_; 
v_pos_3337_ = lean_ctor_get(v___x_3326_, 0);
v_err_3338_ = lean_ctor_get(v___x_3326_, 1);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3340_ = v___x_3326_;
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_err_3338_);
lean_inc(v_pos_3337_);
lean_dec(v___x_3326_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3343_; 
if (v_isShared_3341_ == 0)
{
v___x_3343_ = v___x_3340_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_pos_3337_);
lean_ctor_set(v_reuseFailAlloc_3344_, 1, v_err_3338_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___boxed(lean_object* v_config_3346_, lean_object* v_a_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3346_, v_a_3347_);
lean_dec_ref(v_config_3346_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_uri(lean_object* v_config_3349_, lean_object* v_scheme_3350_, lean_object* v_a_3351_){
_start:
{
lean_object* v___x_3352_; 
lean_inc_ref(v_config_3349_);
v___x_3352_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_3349_, v_a_3351_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v_res_3353_; lean_object* v_pos_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3443_; 
v_res_3353_ = lean_ctor_get(v___x_3352_, 1);
v_pos_3354_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3356_ = v___x_3352_;
v_isShared_3357_ = v_isSharedCheck_3443_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_res_3353_);
lean_inc(v_pos_3354_);
lean_dec(v___x_3352_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3443_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v_fst_3358_; lean_object* v_snd_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3442_; 
v_fst_3358_ = lean_ctor_get(v_res_3353_, 0);
v_snd_3359_ = lean_ctor_get(v_res_3353_, 1);
v_isSharedCheck_3442_ = !lean_is_exclusive(v_res_3353_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3361_ = v_res_3353_;
v_isShared_3362_ = v_isSharedCheck_3442_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_snd_3359_);
lean_inc(v_fst_3358_);
lean_dec(v_res_3353_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3442_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___y_3364_; lean_object* v_pos_3365_; lean_object* v_res_3366_; lean_object* v___y_3373_; lean_object* v_idx_3374_; lean_object* v_pos_3375_; lean_object* v_err_3376_; lean_object* v_pos_3384_; lean_object* v_array_3385_; lean_object* v_idx_3386_; lean_object* v_res_3387_; lean_object* v_array_3404_; lean_object* v_idx_3405_; lean_object* v_pos_3407_; lean_object* v_array_3408_; lean_object* v_idx_3409_; lean_object* v_err_3410_; lean_object* v___x_3414_; uint8_t v___x_3415_; 
v_array_3404_ = lean_ctor_get(v_pos_3354_, 0);
lean_inc_ref(v_array_3404_);
v_idx_3405_ = lean_ctor_get(v_pos_3354_, 1);
lean_inc(v_idx_3405_);
v___x_3414_ = lean_byte_array_size(v_array_3404_);
v___x_3415_ = lean_nat_dec_lt(v_idx_3405_, v___x_3414_);
if (v___x_3415_ == 0)
{
lean_object* v___x_3416_; 
v___x_3416_ = lean_box(0);
lean_inc(v_idx_3405_);
v_pos_3407_ = v_pos_3354_;
v_array_3408_ = v_array_3404_;
v_idx_3409_ = v_idx_3405_;
v_err_3410_ = v___x_3416_;
goto v___jp_3406_;
}
else
{
uint8_t v___x_3417_; uint8_t v_got_3418_; uint8_t v___x_3419_; 
v___x_3417_ = 63;
v_got_3418_ = lean_byte_array_fget(v_array_3404_, v_idx_3405_);
v___x_3419_ = lean_uint8_dec_eq(v_got_3418_, v___x_3417_);
if (v___x_3419_ == 0)
{
lean_object* v___x_3420_; 
v___x_3420_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__3));
lean_inc(v_idx_3405_);
v_pos_3407_ = v_pos_3354_;
v_array_3408_ = v_array_3404_;
v_idx_3409_ = v_idx_3405_;
v_err_3410_ = v___x_3420_;
goto v___jp_3406_;
}
else
{
lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3439_; 
v_isSharedCheck_3439_ = !lean_is_exclusive(v_pos_3354_);
if (v_isSharedCheck_3439_ == 0)
{
lean_object* v_unused_3440_; lean_object* v_unused_3441_; 
v_unused_3440_ = lean_ctor_get(v_pos_3354_, 1);
lean_dec(v_unused_3440_);
v_unused_3441_ = lean_ctor_get(v_pos_3354_, 0);
lean_dec(v_unused_3441_);
v___x_3422_ = v_pos_3354_;
v_isShared_3423_ = v_isSharedCheck_3439_;
goto v_resetjp_3421_;
}
else
{
lean_dec(v_pos_3354_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3439_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3427_; 
v___x_3424_ = lean_unsigned_to_nat(1u);
v___x_3425_ = lean_nat_add(v_idx_3405_, v___x_3424_);
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 1, v___x_3425_);
v___x_3427_ = v___x_3422_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_array_3404_);
lean_ctor_set(v_reuseFailAlloc_3438_, 1, v___x_3425_);
v___x_3427_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
lean_object* v___x_3428_; 
lean_inc_ref(v_config_3349_);
v___x_3428_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3349_, v___x_3427_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_pos_3429_; lean_object* v_res_3430_; lean_object* v_array_3431_; lean_object* v_idx_3432_; lean_object* v___x_3433_; 
lean_dec(v_idx_3405_);
v_pos_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_pos_3429_);
v_res_3430_ = lean_ctor_get(v___x_3428_, 1);
lean_inc(v_res_3430_);
lean_dec_ref_known(v___x_3428_, 2);
v_array_3431_ = lean_ctor_get(v_pos_3429_, 0);
lean_inc_ref(v_array_3431_);
v_idx_3432_ = lean_ctor_get(v_pos_3429_, 1);
lean_inc(v_idx_3432_);
v___x_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3433_, 0, v_res_3430_);
v_pos_3384_ = v_pos_3429_;
v_array_3385_ = v_array_3431_;
v_idx_3386_ = v_idx_3432_;
v_res_3387_ = v___x_3433_;
goto v___jp_3383_;
}
else
{
lean_object* v_pos_3434_; lean_object* v_err_3435_; lean_object* v_array_3436_; lean_object* v_idx_3437_; 
v_pos_3434_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_pos_3434_);
v_err_3435_ = lean_ctor_get(v___x_3428_, 1);
lean_inc(v_err_3435_);
lean_dec_ref_known(v___x_3428_, 2);
v_array_3436_ = lean_ctor_get(v_pos_3434_, 0);
lean_inc_ref(v_array_3436_);
v_idx_3437_ = lean_ctor_get(v_pos_3434_, 1);
lean_inc(v_idx_3437_);
v_pos_3407_ = v_pos_3434_;
v_array_3408_ = v_array_3436_;
v_idx_3409_ = v_idx_3437_;
v_err_3410_ = v_err_3435_;
goto v___jp_3406_;
}
}
}
}
}
v___jp_3363_:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3370_; 
v___x_3367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3367_, 0, v_scheme_3350_);
lean_ctor_set(v___x_3367_, 1, v_fst_3358_);
lean_ctor_set(v___x_3367_, 2, v_snd_3359_);
lean_ctor_set(v___x_3367_, 3, v___y_3364_);
lean_ctor_set(v___x_3367_, 4, v_res_3366_);
v___x_3368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3367_);
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 1, v___x_3368_);
lean_ctor_set(v___x_3356_, 0, v_pos_3365_);
v___x_3370_ = v___x_3356_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_pos_3365_);
lean_ctor_set(v_reuseFailAlloc_3371_, 1, v___x_3368_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
v___jp_3372_:
{
lean_object* v_idx_3377_; uint8_t v___x_3378_; 
v_idx_3377_ = lean_ctor_get(v_pos_3375_, 1);
v___x_3378_ = lean_nat_dec_eq(v_idx_3374_, v_idx_3377_);
lean_dec(v_idx_3374_);
if (v___x_3378_ == 0)
{
lean_object* v___x_3380_; 
lean_dec(v___y_3373_);
lean_dec(v_snd_3359_);
lean_dec(v_fst_3358_);
lean_del_object(v___x_3356_);
lean_dec_ref(v_scheme_3350_);
if (v_isShared_3362_ == 0)
{
lean_ctor_set_tag(v___x_3361_, 1);
lean_ctor_set(v___x_3361_, 1, v_err_3376_);
lean_ctor_set(v___x_3361_, 0, v_pos_3375_);
v___x_3380_ = v___x_3361_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_pos_3375_);
lean_ctor_set(v_reuseFailAlloc_3381_, 1, v_err_3376_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
else
{
lean_object* v___x_3382_; 
lean_dec(v_err_3376_);
lean_del_object(v___x_3361_);
v___x_3382_ = lean_box(0);
v___y_3364_ = v___y_3373_;
v_pos_3365_ = v_pos_3375_;
v_res_3366_ = v___x_3382_;
goto v___jp_3363_;
}
}
v___jp_3383_:
{
lean_object* v___x_3388_; uint8_t v___x_3389_; 
v___x_3388_ = lean_byte_array_size(v_array_3385_);
v___x_3389_ = lean_nat_dec_lt(v_idx_3386_, v___x_3388_);
if (v___x_3389_ == 0)
{
lean_object* v___x_3390_; 
lean_dec_ref(v_array_3385_);
lean_dec_ref(v_config_3349_);
v___x_3390_ = lean_box(0);
v___y_3373_ = v_res_3387_;
v_idx_3374_ = v_idx_3386_;
v_pos_3375_ = v_pos_3384_;
v_err_3376_ = v___x_3390_;
goto v___jp_3372_;
}
else
{
uint8_t v___x_3391_; uint8_t v_got_3392_; uint8_t v___x_3393_; 
v___x_3391_ = 35;
v_got_3392_ = lean_byte_array_fget(v_array_3385_, v_idx_3386_);
v___x_3393_ = lean_uint8_dec_eq(v_got_3392_, v___x_3391_);
if (v___x_3393_ == 0)
{
lean_object* v___x_3394_; 
lean_dec_ref(v_array_3385_);
lean_dec_ref(v_config_3349_);
v___x_3394_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v___y_3373_ = v_res_3387_;
v_idx_3374_ = v_idx_3386_;
v_pos_3375_ = v_pos_3384_;
v_err_3376_ = v___x_3394_;
goto v___jp_3372_;
}
else
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
lean_dec_ref(v_pos_3384_);
v___x_3395_ = lean_unsigned_to_nat(1u);
v___x_3396_ = lean_nat_add(v_idx_3386_, v___x_3395_);
v___x_3397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3397_, 0, v_array_3385_);
lean_ctor_set(v___x_3397_, 1, v___x_3396_);
v___x_3398_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3349_, v___x_3397_);
lean_dec_ref(v_config_3349_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_pos_3399_; lean_object* v_res_3400_; lean_object* v___x_3401_; 
lean_dec(v_idx_3386_);
lean_del_object(v___x_3361_);
v_pos_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_pos_3399_);
v_res_3400_ = lean_ctor_get(v___x_3398_, 1);
lean_inc(v_res_3400_);
lean_dec_ref_known(v___x_3398_, 2);
v___x_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3401_, 0, v_res_3400_);
v___y_3364_ = v_res_3387_;
v_pos_3365_ = v_pos_3399_;
v_res_3366_ = v___x_3401_;
goto v___jp_3363_;
}
else
{
lean_object* v_pos_3402_; lean_object* v_err_3403_; 
v_pos_3402_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_pos_3402_);
v_err_3403_ = lean_ctor_get(v___x_3398_, 1);
lean_inc(v_err_3403_);
lean_dec_ref_known(v___x_3398_, 2);
v___y_3373_ = v_res_3387_;
v_idx_3374_ = v_idx_3386_;
v_pos_3375_ = v_pos_3402_;
v_err_3376_ = v_err_3403_;
goto v___jp_3372_;
}
}
}
}
v___jp_3406_:
{
uint8_t v___x_3411_; 
v___x_3411_ = lean_nat_dec_eq(v_idx_3405_, v_idx_3409_);
lean_dec(v_idx_3405_);
if (v___x_3411_ == 0)
{
lean_object* v___x_3412_; 
lean_dec(v_idx_3409_);
lean_dec_ref(v_array_3408_);
lean_del_object(v___x_3361_);
lean_dec(v_snd_3359_);
lean_dec(v_fst_3358_);
lean_del_object(v___x_3356_);
lean_dec_ref(v_scheme_3350_);
lean_dec_ref(v_config_3349_);
v___x_3412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3412_, 0, v_pos_3407_);
lean_ctor_set(v___x_3412_, 1, v_err_3410_);
return v___x_3412_;
}
else
{
lean_object* v___x_3413_; 
lean_dec(v_err_3410_);
v___x_3413_ = lean_box(0);
v_pos_3384_ = v_pos_3407_;
v_array_3385_ = v_array_3408_;
v_idx_3386_ = v_idx_3409_;
v_res_3387_ = v___x_3413_;
goto v___jp_3383_;
}
}
}
}
}
else
{
lean_object* v_pos_3444_; lean_object* v_err_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3452_; 
lean_dec_ref(v_scheme_3350_);
lean_dec_ref(v_config_3349_);
v_pos_3444_ = lean_ctor_get(v___x_3352_, 0);
v_err_3445_ = lean_ctor_get(v___x_3352_, 1);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3447_ = v___x_3352_;
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_err_3445_);
lean_inc(v_pos_3444_);
lean_dec(v___x_3352_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_pos_3444_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v_err_3445_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withAuthority(lean_object* v_config_3453_, lean_object* v_a_3454_){
_start:
{
lean_object* v___x_3455_; 
lean_inc_ref(v_config_3453_);
v___x_3455_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_3453_, v_a_3454_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_pos_3456_; lean_object* v_res_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3557_; 
v_pos_3456_ = lean_ctor_get(v___x_3455_, 0);
v_res_3457_ = lean_ctor_get(v___x_3455_, 1);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3459_ = v___x_3455_;
v_isShared_3460_ = v_isSharedCheck_3557_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_res_3457_);
lean_inc(v_pos_3456_);
lean_dec(v___x_3455_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3557_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
uint8_t v___x_3461_; lean_object* v___x_3462_; 
v___x_3461_ = 1;
lean_inc_ref(v_config_3453_);
v___x_3462_ = l_Std_Http_URI_Parser_parsePath(v_config_3453_, v___x_3461_, v___x_3461_, v_pos_3456_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v_pos_3463_; lean_object* v_res_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3547_; 
v_pos_3463_ = lean_ctor_get(v___x_3462_, 0);
v_res_3464_ = lean_ctor_get(v___x_3462_, 1);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3466_ = v___x_3462_;
v_isShared_3467_ = v_isSharedCheck_3547_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_res_3464_);
lean_inc(v_pos_3463_);
lean_dec(v___x_3462_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3547_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___y_3469_; lean_object* v_pos_3470_; lean_object* v_res_3471_; lean_object* v___y_3478_; lean_object* v_idx_3479_; lean_object* v_pos_3480_; lean_object* v_err_3481_; lean_object* v_pos_3489_; lean_object* v_array_3490_; lean_object* v_idx_3491_; lean_object* v_res_3492_; lean_object* v_array_3509_; lean_object* v_idx_3510_; lean_object* v_pos_3512_; lean_object* v_array_3513_; lean_object* v_idx_3514_; lean_object* v_err_3515_; lean_object* v___x_3519_; uint8_t v___x_3520_; 
v_array_3509_ = lean_ctor_get(v_pos_3463_, 0);
lean_inc_ref(v_array_3509_);
v_idx_3510_ = lean_ctor_get(v_pos_3463_, 1);
lean_inc(v_idx_3510_);
v___x_3519_ = lean_byte_array_size(v_array_3509_);
v___x_3520_ = lean_nat_dec_lt(v_idx_3510_, v___x_3519_);
if (v___x_3520_ == 0)
{
lean_object* v___x_3521_; 
v___x_3521_ = lean_box(0);
lean_inc(v_idx_3510_);
v_pos_3512_ = v_pos_3463_;
v_array_3513_ = v_array_3509_;
v_idx_3514_ = v_idx_3510_;
v_err_3515_ = v___x_3521_;
goto v___jp_3511_;
}
else
{
uint8_t v___x_3522_; uint8_t v_got_3523_; uint8_t v___x_3524_; 
v___x_3522_ = 63;
v_got_3523_ = lean_byte_array_fget(v_array_3509_, v_idx_3510_);
v___x_3524_ = lean_uint8_dec_eq(v_got_3523_, v___x_3522_);
if (v___x_3524_ == 0)
{
lean_object* v___x_3525_; 
v___x_3525_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__3));
lean_inc(v_idx_3510_);
v_pos_3512_ = v_pos_3463_;
v_array_3513_ = v_array_3509_;
v_idx_3514_ = v_idx_3510_;
v_err_3515_ = v___x_3525_;
goto v___jp_3511_;
}
else
{
lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3544_; 
v_isSharedCheck_3544_ = !lean_is_exclusive(v_pos_3463_);
if (v_isSharedCheck_3544_ == 0)
{
lean_object* v_unused_3545_; lean_object* v_unused_3546_; 
v_unused_3545_ = lean_ctor_get(v_pos_3463_, 1);
lean_dec(v_unused_3545_);
v_unused_3546_ = lean_ctor_get(v_pos_3463_, 0);
lean_dec(v_unused_3546_);
v___x_3527_ = v_pos_3463_;
v_isShared_3528_ = v_isSharedCheck_3544_;
goto v_resetjp_3526_;
}
else
{
lean_dec(v_pos_3463_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3544_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3532_; 
v___x_3529_ = lean_unsigned_to_nat(1u);
v___x_3530_ = lean_nat_add(v_idx_3510_, v___x_3529_);
if (v_isShared_3528_ == 0)
{
lean_ctor_set(v___x_3527_, 1, v___x_3530_);
v___x_3532_ = v___x_3527_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_array_3509_);
lean_ctor_set(v_reuseFailAlloc_3543_, 1, v___x_3530_);
v___x_3532_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
lean_object* v___x_3533_; 
lean_inc_ref(v_config_3453_);
v___x_3533_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3453_, v___x_3532_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v_pos_3534_; lean_object* v_res_3535_; lean_object* v_array_3536_; lean_object* v_idx_3537_; lean_object* v___x_3538_; 
lean_dec(v_idx_3510_);
v_pos_3534_ = lean_ctor_get(v___x_3533_, 0);
lean_inc(v_pos_3534_);
v_res_3535_ = lean_ctor_get(v___x_3533_, 1);
lean_inc(v_res_3535_);
lean_dec_ref_known(v___x_3533_, 2);
v_array_3536_ = lean_ctor_get(v_pos_3534_, 0);
lean_inc_ref(v_array_3536_);
v_idx_3537_ = lean_ctor_get(v_pos_3534_, 1);
lean_inc(v_idx_3537_);
v___x_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3538_, 0, v_res_3535_);
v_pos_3489_ = v_pos_3534_;
v_array_3490_ = v_array_3536_;
v_idx_3491_ = v_idx_3537_;
v_res_3492_ = v___x_3538_;
goto v___jp_3488_;
}
else
{
lean_object* v_pos_3539_; lean_object* v_err_3540_; lean_object* v_array_3541_; lean_object* v_idx_3542_; 
v_pos_3539_ = lean_ctor_get(v___x_3533_, 0);
lean_inc(v_pos_3539_);
v_err_3540_ = lean_ctor_get(v___x_3533_, 1);
lean_inc(v_err_3540_);
lean_dec_ref_known(v___x_3533_, 2);
v_array_3541_ = lean_ctor_get(v_pos_3539_, 0);
lean_inc_ref(v_array_3541_);
v_idx_3542_ = lean_ctor_get(v_pos_3539_, 1);
lean_inc(v_idx_3542_);
v_pos_3512_ = v_pos_3539_;
v_array_3513_ = v_array_3541_;
v_idx_3514_ = v_idx_3542_;
v_err_3515_ = v_err_3540_;
goto v___jp_3511_;
}
}
}
}
}
v___jp_3468_:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3475_; 
v___x_3472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3472_, 0, v_res_3457_);
v___x_3473_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3472_);
lean_ctor_set(v___x_3473_, 1, v_res_3464_);
lean_ctor_set(v___x_3473_, 2, v___y_3469_);
lean_ctor_set(v___x_3473_, 3, v_res_3471_);
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 1, v___x_3473_);
lean_ctor_set(v___x_3466_, 0, v_pos_3470_);
v___x_3475_ = v___x_3466_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_pos_3470_);
lean_ctor_set(v_reuseFailAlloc_3476_, 1, v___x_3473_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
v___jp_3477_:
{
lean_object* v_idx_3482_; uint8_t v___x_3483_; 
v_idx_3482_ = lean_ctor_get(v_pos_3480_, 1);
v___x_3483_ = lean_nat_dec_eq(v_idx_3479_, v_idx_3482_);
lean_dec(v_idx_3479_);
if (v___x_3483_ == 0)
{
lean_object* v___x_3485_; 
lean_dec(v___y_3478_);
lean_del_object(v___x_3466_);
lean_dec(v_res_3464_);
lean_dec(v_res_3457_);
if (v_isShared_3460_ == 0)
{
lean_ctor_set_tag(v___x_3459_, 1);
lean_ctor_set(v___x_3459_, 1, v_err_3481_);
lean_ctor_set(v___x_3459_, 0, v_pos_3480_);
v___x_3485_ = v___x_3459_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_pos_3480_);
lean_ctor_set(v_reuseFailAlloc_3486_, 1, v_err_3481_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
else
{
lean_object* v___x_3487_; 
lean_dec(v_err_3481_);
lean_del_object(v___x_3459_);
v___x_3487_ = lean_box(0);
v___y_3469_ = v___y_3478_;
v_pos_3470_ = v_pos_3480_;
v_res_3471_ = v___x_3487_;
goto v___jp_3468_;
}
}
v___jp_3488_:
{
lean_object* v___x_3493_; uint8_t v___x_3494_; 
v___x_3493_ = lean_byte_array_size(v_array_3490_);
v___x_3494_ = lean_nat_dec_lt(v_idx_3491_, v___x_3493_);
if (v___x_3494_ == 0)
{
lean_object* v___x_3495_; 
lean_dec_ref(v_array_3490_);
lean_dec_ref(v_config_3453_);
v___x_3495_ = lean_box(0);
v___y_3478_ = v_res_3492_;
v_idx_3479_ = v_idx_3491_;
v_pos_3480_ = v_pos_3489_;
v_err_3481_ = v___x_3495_;
goto v___jp_3477_;
}
else
{
uint8_t v___x_3496_; uint8_t v_got_3497_; uint8_t v___x_3498_; 
v___x_3496_ = 35;
v_got_3497_ = lean_byte_array_fget(v_array_3490_, v_idx_3491_);
v___x_3498_ = lean_uint8_dec_eq(v_got_3497_, v___x_3496_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3499_; 
lean_dec_ref(v_array_3490_);
lean_dec_ref(v_config_3453_);
v___x_3499_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v___y_3478_ = v_res_3492_;
v_idx_3479_ = v_idx_3491_;
v_pos_3480_ = v_pos_3489_;
v_err_3481_ = v___x_3499_;
goto v___jp_3477_;
}
else
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
lean_dec_ref(v_pos_3489_);
v___x_3500_ = lean_unsigned_to_nat(1u);
v___x_3501_ = lean_nat_add(v_idx_3491_, v___x_3500_);
v___x_3502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3502_, 0, v_array_3490_);
lean_ctor_set(v___x_3502_, 1, v___x_3501_);
v___x_3503_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3453_, v___x_3502_);
lean_dec_ref(v_config_3453_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_pos_3504_; lean_object* v_res_3505_; lean_object* v___x_3506_; 
lean_dec(v_idx_3491_);
lean_del_object(v___x_3459_);
v_pos_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_pos_3504_);
v_res_3505_ = lean_ctor_get(v___x_3503_, 1);
lean_inc(v_res_3505_);
lean_dec_ref_known(v___x_3503_, 2);
v___x_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3506_, 0, v_res_3505_);
v___y_3469_ = v_res_3492_;
v_pos_3470_ = v_pos_3504_;
v_res_3471_ = v___x_3506_;
goto v___jp_3468_;
}
else
{
lean_object* v_pos_3507_; lean_object* v_err_3508_; 
v_pos_3507_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_pos_3507_);
v_err_3508_ = lean_ctor_get(v___x_3503_, 1);
lean_inc(v_err_3508_);
lean_dec_ref_known(v___x_3503_, 2);
v___y_3478_ = v_res_3492_;
v_idx_3479_ = v_idx_3491_;
v_pos_3480_ = v_pos_3507_;
v_err_3481_ = v_err_3508_;
goto v___jp_3477_;
}
}
}
}
v___jp_3511_:
{
uint8_t v___x_3516_; 
v___x_3516_ = lean_nat_dec_eq(v_idx_3510_, v_idx_3514_);
lean_dec(v_idx_3510_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; 
lean_dec(v_idx_3514_);
lean_dec_ref(v_array_3513_);
lean_del_object(v___x_3466_);
lean_dec(v_res_3464_);
lean_del_object(v___x_3459_);
lean_dec(v_res_3457_);
lean_dec_ref(v_config_3453_);
v___x_3517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3517_, 0, v_pos_3512_);
lean_ctor_set(v___x_3517_, 1, v_err_3515_);
return v___x_3517_;
}
else
{
lean_object* v___x_3518_; 
lean_dec(v_err_3515_);
v___x_3518_ = lean_box(0);
v_pos_3489_ = v_pos_3512_;
v_array_3490_ = v_array_3513_;
v_idx_3491_ = v_idx_3514_;
v_res_3492_ = v___x_3518_;
goto v___jp_3488_;
}
}
}
}
else
{
lean_object* v_pos_3548_; lean_object* v_err_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3556_; 
lean_del_object(v___x_3459_);
lean_dec(v_res_3457_);
lean_dec_ref(v_config_3453_);
v_pos_3548_ = lean_ctor_get(v___x_3462_, 0);
v_err_3549_ = lean_ctor_get(v___x_3462_, 1);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3551_ = v___x_3462_;
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_err_3549_);
lean_inc(v_pos_3548_);
lean_dec(v___x_3462_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3554_; 
if (v_isShared_3552_ == 0)
{
v___x_3554_ = v___x_3551_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_pos_3548_);
lean_ctor_set(v_reuseFailAlloc_3555_, 1, v_err_3549_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
}
}
}
else
{
lean_object* v_pos_3558_; lean_object* v_err_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
lean_dec_ref(v_config_3453_);
v_pos_3558_ = lean_ctor_get(v___x_3455_, 0);
v_err_3559_ = lean_ctor_get(v___x_3455_, 1);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3455_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_err_3559_);
lean_inc(v_pos_3558_);
lean_dec(v___x_3455_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
if (v_isShared_3562_ == 0)
{
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_pos_3558_);
lean_ctor_set(v_reuseFailAlloc_3565_, 1, v_err_3559_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath_spec__0(lean_object* v_a_3567_, lean_object* v_i_3568_){
_start:
{
lean_object* v___x_3569_; uint8_t v___x_3570_; 
v___x_3569_ = lean_byte_array_size(v_a_3567_);
v___x_3570_ = lean_nat_dec_lt(v_i_3568_, v___x_3569_);
if (v___x_3570_ == 0)
{
lean_object* v___x_3571_; 
lean_dec(v_i_3568_);
v___x_3571_ = lean_box(0);
return v___x_3571_;
}
else
{
uint8_t v___x_3572_; uint8_t v___x_3573_; uint8_t v___x_3574_; 
v___x_3572_ = lean_byte_array_fget(v_a_3567_, v_i_3568_);
v___x_3573_ = 58;
v___x_3574_ = lean_uint8_dec_eq(v___x_3572_, v___x_3573_);
if (v___x_3574_ == 0)
{
lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3575_ = lean_unsigned_to_nat(1u);
v___x_3576_ = lean_nat_add(v_i_3568_, v___x_3575_);
lean_dec(v_i_3568_);
v_i_3568_ = v___x_3576_;
goto _start;
}
else
{
lean_object* v___x_3578_; 
v___x_3578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3578_, 0, v_i_3568_);
return v___x_3578_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath_spec__0___boxed(lean_object* v_a_3579_, lean_object* v_i_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath_spec__0(v_a_3579_, v_i_3580_);
lean_dec_ref(v_a_3579_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath(lean_object* v_config_3585_, lean_object* v_a_3586_){
_start:
{
uint8_t v___x_3587_; uint8_t v___x_3588_; lean_object* v___x_3589_; 
v___x_3587_ = 0;
v___x_3588_ = 1;
lean_inc_ref(v_config_3585_);
v___x_3589_ = l_Std_Http_URI_Parser_parsePath(v_config_3585_, v___x_3587_, v___x_3588_, v_a_3586_);
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_object* v_pos_3590_; lean_object* v_res_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3680_; 
v_pos_3590_ = lean_ctor_get(v___x_3589_, 0);
v_res_3591_ = lean_ctor_get(v___x_3589_, 1);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3593_ = v___x_3589_;
v_isShared_3594_ = v_isSharedCheck_3680_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_res_3591_);
lean_inc(v_pos_3590_);
lean_dec(v___x_3589_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3680_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___y_3596_; lean_object* v_pos_3597_; lean_object* v_res_3598_; lean_object* v___y_3605_; lean_object* v_idx_3606_; lean_object* v_pos_3607_; lean_object* v_err_3608_; lean_object* v_pos_3614_; lean_object* v_array_3615_; lean_object* v_idx_3616_; lean_object* v_res_3617_; lean_object* v_pos_3635_; lean_object* v_err_3636_; uint8_t v_absolute_3671_; 
v_absolute_3671_ = lean_ctor_get_uint8(v_res_3591_, sizeof(void*)*1);
if (v_absolute_3671_ == 0)
{
lean_object* v_segments_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; uint8_t v___x_3675_; 
v_segments_3672_ = lean_ctor_get(v_res_3591_, 0);
v___x_3673_ = lean_unsigned_to_nat(0u);
v___x_3674_ = lean_array_get_size(v_segments_3672_);
v___x_3675_ = lean_nat_dec_lt(v___x_3673_, v___x_3674_);
if (v___x_3675_ == 0)
{
goto v___jp_3650_;
}
else
{
lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3676_ = lean_array_fget_borrowed(v_segments_3672_, v___x_3673_);
v___x_3677_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath_spec__0(v___x_3676_, v___x_3673_);
if (lean_obj_tag(v___x_3677_) == 0)
{
goto v___jp_3650_;
}
else
{
lean_object* v___x_3678_; lean_object* v___x_3679_; 
lean_dec_ref_known(v___x_3677_, 1);
lean_del_object(v___x_3593_);
lean_dec(v_res_3591_);
lean_dec_ref(v_config_3585_);
v___x_3678_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath___closed__1));
v___x_3679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3679_, 0, v_pos_3590_);
lean_ctor_set(v___x_3679_, 1, v___x_3678_);
return v___x_3679_;
}
}
}
else
{
goto v___jp_3650_;
}
v___jp_3595_:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3602_; 
v___x_3599_ = lean_box(0);
v___x_3600_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3599_);
lean_ctor_set(v___x_3600_, 1, v_res_3591_);
lean_ctor_set(v___x_3600_, 2, v___y_3596_);
lean_ctor_set(v___x_3600_, 3, v_res_3598_);
if (v_isShared_3594_ == 0)
{
lean_ctor_set(v___x_3593_, 1, v___x_3600_);
lean_ctor_set(v___x_3593_, 0, v_pos_3597_);
v___x_3602_ = v___x_3593_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_pos_3597_);
lean_ctor_set(v_reuseFailAlloc_3603_, 1, v___x_3600_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
v___jp_3604_:
{
lean_object* v_idx_3609_; uint8_t v___x_3610_; 
v_idx_3609_ = lean_ctor_get(v_pos_3607_, 1);
v___x_3610_ = lean_nat_dec_eq(v_idx_3606_, v_idx_3609_);
lean_dec(v_idx_3606_);
if (v___x_3610_ == 0)
{
lean_object* v___x_3611_; 
lean_dec(v___y_3605_);
lean_del_object(v___x_3593_);
lean_dec(v_res_3591_);
v___x_3611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3611_, 0, v_pos_3607_);
lean_ctor_set(v___x_3611_, 1, v_err_3608_);
return v___x_3611_;
}
else
{
lean_object* v___x_3612_; 
lean_dec(v_err_3608_);
v___x_3612_ = lean_box(0);
v___y_3596_ = v___y_3605_;
v_pos_3597_ = v_pos_3607_;
v_res_3598_ = v___x_3612_;
goto v___jp_3595_;
}
}
v___jp_3613_:
{
lean_object* v___x_3618_; uint8_t v___x_3619_; 
v___x_3618_ = lean_byte_array_size(v_array_3615_);
v___x_3619_ = lean_nat_dec_lt(v_idx_3616_, v___x_3618_);
if (v___x_3619_ == 0)
{
lean_object* v___x_3620_; 
lean_dec_ref(v_array_3615_);
lean_dec_ref(v_config_3585_);
v___x_3620_ = lean_box(0);
v___y_3605_ = v_res_3617_;
v_idx_3606_ = v_idx_3616_;
v_pos_3607_ = v_pos_3614_;
v_err_3608_ = v___x_3620_;
goto v___jp_3604_;
}
else
{
uint8_t v___x_3621_; uint8_t v_got_3622_; uint8_t v___x_3623_; 
v___x_3621_ = 35;
v_got_3622_ = lean_byte_array_fget(v_array_3615_, v_idx_3616_);
v___x_3623_ = lean_uint8_dec_eq(v_got_3622_, v___x_3621_);
if (v___x_3623_ == 0)
{
lean_object* v___x_3624_; 
lean_dec_ref(v_array_3615_);
lean_dec_ref(v_config_3585_);
v___x_3624_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__1));
v___y_3605_ = v_res_3617_;
v_idx_3606_ = v_idx_3616_;
v_pos_3607_ = v_pos_3614_;
v_err_3608_ = v___x_3624_;
goto v___jp_3604_;
}
else
{
lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
lean_dec_ref(v_pos_3614_);
v___x_3625_ = lean_unsigned_to_nat(1u);
v___x_3626_ = lean_nat_add(v_idx_3616_, v___x_3625_);
v___x_3627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3627_, 0, v_array_3615_);
lean_ctor_set(v___x_3627_, 1, v___x_3626_);
v___x_3628_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3585_, v___x_3627_);
lean_dec_ref(v_config_3585_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v_pos_3629_; lean_object* v_res_3630_; lean_object* v___x_3631_; 
lean_dec(v_idx_3616_);
v_pos_3629_ = lean_ctor_get(v___x_3628_, 0);
lean_inc(v_pos_3629_);
v_res_3630_ = lean_ctor_get(v___x_3628_, 1);
lean_inc(v_res_3630_);
lean_dec_ref_known(v___x_3628_, 2);
v___x_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3631_, 0, v_res_3630_);
v___y_3596_ = v_res_3617_;
v_pos_3597_ = v_pos_3629_;
v_res_3598_ = v___x_3631_;
goto v___jp_3595_;
}
else
{
lean_object* v_pos_3632_; lean_object* v_err_3633_; 
v_pos_3632_ = lean_ctor_get(v___x_3628_, 0);
lean_inc(v_pos_3632_);
v_err_3633_ = lean_ctor_get(v___x_3628_, 1);
lean_inc(v_err_3633_);
lean_dec_ref_known(v___x_3628_, 2);
v___y_3605_ = v_res_3617_;
v_idx_3606_ = v_idx_3616_;
v_pos_3607_ = v_pos_3632_;
v_err_3608_ = v_err_3633_;
goto v___jp_3604_;
}
}
}
}
v___jp_3634_:
{
lean_object* v_idx_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3648_; 
v_idx_3637_ = lean_ctor_get(v_pos_3590_, 1);
v_isSharedCheck_3648_ = !lean_is_exclusive(v_pos_3590_);
if (v_isSharedCheck_3648_ == 0)
{
lean_object* v_unused_3649_; 
v_unused_3649_ = lean_ctor_get(v_pos_3590_, 0);
lean_dec(v_unused_3649_);
v___x_3639_ = v_pos_3590_;
v_isShared_3640_ = v_isSharedCheck_3648_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_idx_3637_);
lean_dec(v_pos_3590_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3648_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v_array_3641_; lean_object* v_idx_3642_; uint8_t v___x_3643_; 
v_array_3641_ = lean_ctor_get(v_pos_3635_, 0);
v_idx_3642_ = lean_ctor_get(v_pos_3635_, 1);
v___x_3643_ = lean_nat_dec_eq(v_idx_3637_, v_idx_3642_);
lean_dec(v_idx_3637_);
if (v___x_3643_ == 0)
{
lean_object* v___x_3645_; 
lean_del_object(v___x_3593_);
lean_dec(v_res_3591_);
lean_dec_ref(v_config_3585_);
if (v_isShared_3640_ == 0)
{
lean_ctor_set_tag(v___x_3639_, 1);
lean_ctor_set(v___x_3639_, 1, v_err_3636_);
lean_ctor_set(v___x_3639_, 0, v_pos_3635_);
v___x_3645_ = v___x_3639_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_pos_3635_);
lean_ctor_set(v_reuseFailAlloc_3646_, 1, v_err_3636_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
else
{
lean_object* v___x_3647_; 
lean_inc(v_idx_3642_);
lean_inc_ref(v_array_3641_);
lean_del_object(v___x_3639_);
lean_dec(v_err_3636_);
v___x_3647_ = lean_box(0);
v_pos_3614_ = v_pos_3635_;
v_array_3615_ = v_array_3641_;
v_idx_3616_ = v_idx_3642_;
v_res_3617_ = v___x_3647_;
goto v___jp_3613_;
}
}
}
v___jp_3650_:
{
lean_object* v_array_3651_; lean_object* v_idx_3652_; lean_object* v___x_3653_; uint8_t v___x_3654_; 
v_array_3651_ = lean_ctor_get(v_pos_3590_, 0);
v_idx_3652_ = lean_ctor_get(v_pos_3590_, 1);
v___x_3653_ = lean_byte_array_size(v_array_3651_);
v___x_3654_ = lean_nat_dec_lt(v_idx_3652_, v___x_3653_);
if (v___x_3654_ == 0)
{
lean_object* v___x_3655_; 
v___x_3655_ = lean_box(0);
lean_inc(v_pos_3590_);
v_pos_3635_ = v_pos_3590_;
v_err_3636_ = v___x_3655_;
goto v___jp_3634_;
}
else
{
uint8_t v___x_3656_; uint8_t v_got_3657_; uint8_t v___x_3658_; 
v___x_3656_ = 63;
v_got_3657_ = lean_byte_array_fget(v_array_3651_, v_idx_3652_);
v___x_3658_ = lean_uint8_dec_eq(v_got_3657_, v___x_3656_);
if (v___x_3658_ == 0)
{
lean_object* v___x_3659_; 
v___x_3659_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__3));
lean_inc(v_pos_3590_);
v_pos_3635_ = v_pos_3590_;
v_err_3636_ = v___x_3659_;
goto v___jp_3634_;
}
else
{
lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3660_ = lean_unsigned_to_nat(1u);
v___x_3661_ = lean_nat_add(v_idx_3652_, v___x_3660_);
lean_inc_ref(v_array_3651_);
v___x_3662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3662_, 0, v_array_3651_);
lean_ctor_set(v___x_3662_, 1, v___x_3661_);
lean_inc_ref(v_config_3585_);
v___x_3663_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3585_, v___x_3662_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_pos_3664_; lean_object* v_res_3665_; lean_object* v_array_3666_; lean_object* v_idx_3667_; lean_object* v___x_3668_; 
lean_dec(v_pos_3590_);
v_pos_3664_ = lean_ctor_get(v___x_3663_, 0);
lean_inc(v_pos_3664_);
v_res_3665_ = lean_ctor_get(v___x_3663_, 1);
lean_inc(v_res_3665_);
lean_dec_ref_known(v___x_3663_, 2);
v_array_3666_ = lean_ctor_get(v_pos_3664_, 0);
lean_inc_ref(v_array_3666_);
v_idx_3667_ = lean_ctor_get(v_pos_3664_, 1);
lean_inc(v_idx_3667_);
v___x_3668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3668_, 0, v_res_3665_);
v_pos_3614_ = v_pos_3664_;
v_array_3615_ = v_array_3666_;
v_idx_3616_ = v_idx_3667_;
v_res_3617_ = v___x_3668_;
goto v___jp_3613_;
}
else
{
lean_object* v_pos_3669_; lean_object* v_err_3670_; 
v_pos_3669_ = lean_ctor_get(v___x_3663_, 0);
lean_inc(v_pos_3669_);
v_err_3670_ = lean_ctor_get(v___x_3663_, 1);
lean_inc(v_err_3670_);
lean_dec_ref_known(v___x_3663_, 2);
v_pos_3635_ = v_pos_3669_;
v_err_3636_ = v_err_3670_;
goto v___jp_3634_;
}
}
}
}
}
}
else
{
lean_object* v_pos_3681_; lean_object* v_err_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
lean_dec_ref(v_config_3585_);
v_pos_3681_ = lean_ctor_get(v___x_3589_, 0);
v_err_3682_ = lean_ctor_get(v___x_3589_, 1);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3684_ = v___x_3589_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_err_3682_);
lean_inc(v_pos_3681_);
lean_dec(v___x_3589_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_pos_3681_);
lean_ctor_set(v_reuseFailAlloc_3688_, 1, v_err_3682_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURIReference(lean_object* v_config_3690_, lean_object* v_a_3691_){
_start:
{
lean_object* v_err_3693_; lean_object* v___x_3740_; 
lean_inc_ref(v_a_3691_);
v___x_3740_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3690_, v_a_3691_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v_pos_3741_; lean_object* v_res_3742_; lean_object* v_array_3743_; lean_object* v_idx_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3761_; 
v_pos_3741_ = lean_ctor_get(v___x_3740_, 0);
lean_inc(v_pos_3741_);
v_res_3742_ = lean_ctor_get(v___x_3740_, 1);
lean_inc(v_res_3742_);
lean_dec_ref_known(v___x_3740_, 2);
v_array_3743_ = lean_ctor_get(v_pos_3741_, 0);
v_idx_3744_ = lean_ctor_get(v_pos_3741_, 1);
v_isSharedCheck_3761_ = !lean_is_exclusive(v_pos_3741_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3746_ = v_pos_3741_;
v_isShared_3747_ = v_isSharedCheck_3761_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_idx_3744_);
lean_inc(v_array_3743_);
lean_dec(v_pos_3741_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3761_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v___x_3748_; uint8_t v___x_3749_; 
v___x_3748_ = lean_byte_array_size(v_array_3743_);
v___x_3749_ = lean_nat_dec_lt(v_idx_3744_, v___x_3748_);
if (v___x_3749_ == 0)
{
lean_object* v___x_3750_; 
lean_del_object(v___x_3746_);
lean_dec(v_idx_3744_);
lean_dec_ref(v_array_3743_);
lean_dec(v_res_3742_);
v___x_3750_ = lean_box(0);
v_err_3693_ = v___x_3750_;
goto v___jp_3692_;
}
else
{
uint8_t v___x_3751_; uint8_t v_got_3752_; uint8_t v___x_3753_; 
v___x_3751_ = 58;
v_got_3752_ = lean_byte_array_fget(v_array_3743_, v_idx_3744_);
v___x_3753_ = lean_uint8_dec_eq(v_got_3752_, v___x_3751_);
if (v___x_3753_ == 0)
{
lean_object* v___x_3754_; 
lean_del_object(v___x_3746_);
lean_dec(v_idx_3744_);
lean_dec_ref(v_array_3743_);
lean_dec(v_res_3742_);
v___x_3754_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3));
v_err_3693_ = v___x_3754_;
goto v___jp_3692_;
}
else
{
lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3758_; 
lean_dec_ref(v_a_3691_);
v___x_3755_ = lean_unsigned_to_nat(1u);
v___x_3756_ = lean_nat_add(v_idx_3744_, v___x_3755_);
lean_dec(v_idx_3744_);
if (v_isShared_3747_ == 0)
{
lean_ctor_set(v___x_3746_, 1, v___x_3756_);
v___x_3758_ = v___x_3746_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_array_3743_);
lean_ctor_set(v_reuseFailAlloc_3760_, 1, v___x_3756_);
v___x_3758_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
lean_object* v___x_3759_; 
v___x_3759_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_uri(v_config_3690_, v_res_3742_, v___x_3758_);
return v___x_3759_;
}
}
}
}
}
else
{
lean_object* v_err_3762_; 
v_err_3762_ = lean_ctor_get(v___x_3740_, 1);
lean_inc(v_err_3762_);
lean_dec_ref_known(v___x_3740_, 2);
v_err_3693_ = v_err_3762_;
goto v___jp_3692_;
}
v___jp_3692_:
{
lean_object* v_idx_3694_; uint8_t v___x_3695_; 
v_idx_3694_ = lean_ctor_get(v_a_3691_, 1);
v___x_3695_ = lean_nat_dec_eq(v_idx_3694_, v_idx_3694_);
if (v___x_3695_ == 0)
{
lean_object* v___x_3696_; 
lean_dec_ref(v_config_3690_);
v___x_3696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3696_, 0, v_a_3691_);
lean_ctor_set(v___x_3696_, 1, v_err_3693_);
return v___x_3696_;
}
else
{
lean_object* v_utf8_3697_; lean_object* v___x_3698_; 
lean_dec(v_err_3693_);
v_utf8_3697_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1);
lean_inc_ref(v_a_3691_);
v___x_3698_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_3697_, v_a_3691_);
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v_pos_3699_; lean_object* v___x_3700_; 
lean_dec_ref(v_a_3691_);
v_pos_3699_ = lean_ctor_get(v___x_3698_, 0);
lean_inc(v_pos_3699_);
lean_dec_ref_known(v___x_3698_, 2);
v___x_3700_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withAuthority(v_config_3690_, v_pos_3699_);
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_object* v_pos_3701_; lean_object* v_res_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3710_; 
v_pos_3701_ = lean_ctor_get(v___x_3700_, 0);
v_res_3702_ = lean_ctor_get(v___x_3700_, 1);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3704_ = v___x_3700_;
v_isShared_3705_ = v_isSharedCheck_3710_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_res_3702_);
lean_inc(v_pos_3701_);
lean_dec(v___x_3700_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3710_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3706_; lean_object* v___x_3708_; 
v___x_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3706_, 0, v_res_3702_);
if (v_isShared_3705_ == 0)
{
lean_ctor_set(v___x_3704_, 1, v___x_3706_);
v___x_3708_ = v___x_3704_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_pos_3701_);
lean_ctor_set(v_reuseFailAlloc_3709_, 1, v___x_3706_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
else
{
lean_object* v_pos_3711_; lean_object* v_err_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3719_; 
v_pos_3711_ = lean_ctor_get(v___x_3700_, 0);
v_err_3712_ = lean_ctor_get(v___x_3700_, 1);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3714_ = v___x_3700_;
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_err_3712_);
lean_inc(v_pos_3711_);
lean_dec(v___x_3700_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_pos_3711_);
lean_ctor_set(v_reuseFailAlloc_3718_, 1, v_err_3712_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
else
{
lean_object* v___x_3720_; 
lean_dec_ref_known(v___x_3698_, 2);
v___x_3720_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath(v_config_3690_, v_a_3691_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_pos_3721_; lean_object* v_res_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3730_; 
v_pos_3721_ = lean_ctor_get(v___x_3720_, 0);
v_res_3722_ = lean_ctor_get(v___x_3720_, 1);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3724_ = v___x_3720_;
v_isShared_3725_ = v_isSharedCheck_3730_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_res_3722_);
lean_inc(v_pos_3721_);
lean_dec(v___x_3720_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3730_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3726_; lean_object* v___x_3728_; 
v___x_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3726_, 0, v_res_3722_);
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 1, v___x_3726_);
v___x_3728_ = v___x_3724_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_pos_3721_);
lean_ctor_set(v_reuseFailAlloc_3729_, 1, v___x_3726_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
else
{
lean_object* v_pos_3731_; lean_object* v_err_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
v_pos_3731_ = lean_ctor_get(v___x_3720_, 0);
v_err_3732_ = lean_ctor_get(v___x_3720_, 1);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3720_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_err_3732_);
lean_inc(v_pos_3731_);
lean_dec(v___x_3720_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_pos_3731_);
lean_ctor_set(v_reuseFailAlloc_3738_, 1, v_err_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader(lean_object* v_config_3769_, lean_object* v_a_3770_){
_start:
{
lean_object* v___x_3771_; 
v___x_3771_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_3769_, v_a_3770_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v_pos_3772_; lean_object* v_res_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3842_; 
v_pos_3772_ = lean_ctor_get(v___x_3771_, 0);
v_res_3773_ = lean_ctor_get(v___x_3771_, 1);
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3775_ = v___x_3771_;
v_isShared_3776_ = v_isSharedCheck_3842_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_res_3773_);
lean_inc(v_pos_3772_);
lean_dec(v___x_3771_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3842_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v_port_3778_; lean_object* v___y_3779_; lean_object* v_pos_3793_; lean_object* v_pos_3796_; lean_object* v_array_3797_; lean_object* v_idx_3798_; lean_object* v_array_3804_; lean_object* v_idx_3805_; lean_object* v___x_3806_; uint8_t v___x_3807_; 
v_array_3804_ = lean_ctor_get(v_pos_3772_, 0);
v_idx_3805_ = lean_ctor_get(v_pos_3772_, 1);
v___x_3806_ = lean_byte_array_size(v_array_3804_);
v___x_3807_ = lean_nat_dec_lt(v_idx_3805_, v___x_3806_);
if (v___x_3807_ == 0)
{
v_pos_3793_ = v_pos_3772_;
goto v___jp_3792_;
}
else
{
uint8_t v___x_3808_; uint8_t v___x_3809_; uint8_t v___x_3810_; 
v___x_3808_ = lean_byte_array_fget(v_array_3804_, v_idx_3805_);
v___x_3809_ = 58;
v___x_3810_ = lean_uint8_dec_eq(v___x_3808_, v___x_3809_);
if (v___x_3810_ == 0)
{
v_pos_3793_ = v_pos_3772_;
goto v___jp_3792_;
}
else
{
lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3839_; 
lean_inc(v_idx_3805_);
lean_inc_ref(v_array_3804_);
v_isSharedCheck_3839_ = !lean_is_exclusive(v_pos_3772_);
if (v_isSharedCheck_3839_ == 0)
{
lean_object* v_unused_3840_; lean_object* v_unused_3841_; 
v_unused_3840_ = lean_ctor_get(v_pos_3772_, 1);
lean_dec(v_unused_3840_);
v_unused_3841_ = lean_ctor_get(v_pos_3772_, 0);
lean_dec(v_unused_3841_);
v___x_3812_ = v_pos_3772_;
v_isShared_3813_ = v_isSharedCheck_3839_;
goto v_resetjp_3811_;
}
else
{
lean_dec(v_pos_3772_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3839_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3817_; 
v___x_3814_ = lean_unsigned_to_nat(1u);
v___x_3815_ = lean_nat_add(v_idx_3805_, v___x_3814_);
lean_dec(v_idx_3805_);
lean_inc(v___x_3815_);
lean_inc_ref(v_array_3804_);
if (v_isShared_3813_ == 0)
{
lean_ctor_set(v___x_3812_, 1, v___x_3815_);
v___x_3817_ = v___x_3812_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_array_3804_);
lean_ctor_set(v_reuseFailAlloc_3838_, 1, v___x_3815_);
v___x_3817_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
uint8_t v___x_3818_; 
v___x_3818_ = lean_nat_dec_lt(v___x_3815_, v___x_3806_);
if (v___x_3818_ == 0)
{
v_pos_3796_ = v___x_3817_;
v_array_3797_ = v_array_3804_;
v_idx_3798_ = v___x_3815_;
goto v___jp_3795_;
}
else
{
uint8_t v___x_3819_; uint8_t v___x_3820_; uint8_t v___x_3821_; 
v___x_3819_ = lean_byte_array_fget(v_array_3804_, v___x_3815_);
v___x_3820_ = 48;
v___x_3821_ = lean_uint8_dec_le(v___x_3820_, v___x_3819_);
if (v___x_3821_ == 0)
{
v_pos_3796_ = v___x_3817_;
v_array_3797_ = v_array_3804_;
v_idx_3798_ = v___x_3815_;
goto v___jp_3795_;
}
else
{
uint8_t v___x_3822_; uint8_t v___x_3823_; 
v___x_3822_ = 57;
v___x_3823_ = lean_uint8_dec_le(v___x_3819_, v___x_3822_);
if (v___x_3823_ == 0)
{
v_pos_3796_ = v___x_3817_;
v_array_3797_ = v_array_3804_;
v_idx_3798_ = v___x_3815_;
goto v___jp_3795_;
}
else
{
lean_object* v___x_3824_; 
lean_dec(v___x_3815_);
lean_dec_ref(v_array_3804_);
v___x_3824_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_3817_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_pos_3825_; lean_object* v_res_3826_; lean_object* v___x_3827_; uint16_t v___x_3828_; 
v_pos_3825_ = lean_ctor_get(v___x_3824_, 0);
lean_inc(v_pos_3825_);
v_res_3826_ = lean_ctor_get(v___x_3824_, 1);
lean_inc(v_res_3826_);
lean_dec_ref_known(v___x_3824_, 2);
v___x_3827_ = lean_alloc_ctor(2, 0, 2);
v___x_3828_ = lean_unbox(v_res_3826_);
lean_dec(v_res_3826_);
lean_ctor_set_uint16(v___x_3827_, 0, v___x_3828_);
v_port_3778_ = v___x_3827_;
v___y_3779_ = v_pos_3825_;
goto v___jp_3777_;
}
else
{
lean_object* v_pos_3829_; lean_object* v_err_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3837_; 
lean_del_object(v___x_3775_);
lean_dec(v_res_3773_);
v_pos_3829_ = lean_ctor_get(v___x_3824_, 0);
v_err_3830_ = lean_ctor_get(v___x_3824_, 1);
v_isSharedCheck_3837_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3832_ = v___x_3824_;
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_err_3830_);
lean_inc(v_pos_3829_);
lean_dec(v___x_3824_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___x_3835_; 
if (v_isShared_3833_ == 0)
{
v___x_3835_ = v___x_3832_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_pos_3829_);
lean_ctor_set(v_reuseFailAlloc_3836_, 1, v_err_3830_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
return v___x_3835_;
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
v___jp_3777_:
{
lean_object* v_array_3780_; lean_object* v_idx_3781_; lean_object* v___x_3782_; uint8_t v___x_3783_; 
v_array_3780_ = lean_ctor_get(v___y_3779_, 0);
v_idx_3781_ = lean_ctor_get(v___y_3779_, 1);
v___x_3782_ = lean_byte_array_size(v_array_3780_);
v___x_3783_ = lean_nat_dec_lt(v_idx_3781_, v___x_3782_);
if (v___x_3783_ == 0)
{
lean_object* v___x_3784_; lean_object* v___x_3786_; 
v___x_3784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3784_, 0, v_res_3773_);
lean_ctor_set(v___x_3784_, 1, v_port_3778_);
if (v_isShared_3776_ == 0)
{
lean_ctor_set(v___x_3775_, 1, v___x_3784_);
lean_ctor_set(v___x_3775_, 0, v___y_3779_);
v___x_3786_ = v___x_3775_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v___y_3779_);
lean_ctor_set(v_reuseFailAlloc_3787_, 1, v___x_3784_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
else
{
lean_object* v___x_3788_; lean_object* v___x_3790_; 
lean_dec(v_port_3778_);
lean_dec(v_res_3773_);
v___x_3788_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__1));
if (v_isShared_3776_ == 0)
{
lean_ctor_set_tag(v___x_3775_, 1);
lean_ctor_set(v___x_3775_, 1, v___x_3788_);
lean_ctor_set(v___x_3775_, 0, v___y_3779_);
v___x_3790_ = v___x_3775_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v___y_3779_);
lean_ctor_set(v_reuseFailAlloc_3791_, 1, v___x_3788_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
}
v___jp_3792_:
{
lean_object* v___x_3794_; 
v___x_3794_ = lean_box(0);
v_port_3778_ = v___x_3794_;
v___y_3779_ = v_pos_3793_;
goto v___jp_3777_;
}
v___jp_3795_:
{
lean_object* v___x_3799_; uint8_t v___x_3800_; 
v___x_3799_ = lean_byte_array_size(v_array_3797_);
lean_dec_ref(v_array_3797_);
v___x_3800_ = lean_nat_dec_lt(v_idx_3798_, v___x_3799_);
lean_dec(v_idx_3798_);
if (v___x_3800_ == 0)
{
lean_object* v___x_3801_; 
v___x_3801_ = lean_box(1);
v_port_3778_ = v___x_3801_;
v___y_3779_ = v_pos_3796_;
goto v___jp_3777_;
}
else
{
lean_object* v___x_3802_; lean_object* v___x_3803_; 
lean_del_object(v___x_3775_);
lean_dec(v_res_3773_);
v___x_3802_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__3));
v___x_3803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3803_, 0, v_pos_3796_);
lean_ctor_set(v___x_3803_, 1, v___x_3802_);
return v___x_3803_;
}
}
}
}
else
{
lean_object* v_pos_3843_; lean_object* v_err_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3851_; 
v_pos_3843_ = lean_ctor_get(v___x_3771_, 0);
v_err_3844_ = lean_ctor_get(v___x_3771_, 1);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3846_ = v___x_3771_;
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_err_3844_);
lean_inc(v_pos_3843_);
lean_dec(v___x_3771_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3849_; 
if (v_isShared_3847_ == 0)
{
v___x_3849_ = v___x_3846_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_pos_3843_);
lean_ctor_set(v_reuseFailAlloc_3850_, 1, v_err_3844_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
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
