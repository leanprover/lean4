// Lean compiler output
// Module: Std.Internal.Http.Data.URI.Parser
// Imports: import Init.While public import Init.Data.String.Basic public import Std.Internal.Parsec public import Std.Internal.Parsec.ByteArray public import Std.Internal.Http.Data.URI.Basic public import Std.Internal.Http.Data.URI.Config import Init.Data.String.Search
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
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
lean_object* l_Std_Http_URI_EncodedString_empty(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo_findEnd(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ByteArray_toByteSlice(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_ByteSlice_toByteArray(lean_object*);
lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(lean_object*);
lean_object* l_ByteSlice_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
extern lean_object* l_Std_Http_URI_Query_empty;
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f(lean_object*);
lean_object* l_Std_Http_URI_Query_insertEncoded(lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo1_findEnd(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t l_Std_Http_Internal_instDecidableIsLowerCase(lean_object*);
lean_object* lean_string_data(lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
lean_object* l_List_head_x3f___redArg(lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Http_URI_isValidDomainLabel(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_uv_pton_v4(lean_object*);
lean_object* lean_uv_pton_v6(lean_object*);
lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(lean_object*);
lean_object* l_Std_Http_URI_EncodedFragment_decode(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_tryOpt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_tryOpt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_peekIs(lean_object*, lean_object*);
static const lean_string_object l_panic___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_panic___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1___closed__0 = (const lean_object*)&l_panic___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(lean_object*);
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3;
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1(uint32_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___boxed(lean_object*);
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4;
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "invalid scheme"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__1_value;
static const lean_closure_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__2_value;
static const lean_closure_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__3 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__3_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Init.Data.String.Basic"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__4 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__4_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "String.fromUTF8!"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid UTF-8 string"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6_value;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7;
static const lean_closure_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__8 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__8_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected at least one char"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__9 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__9_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__9_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "scheme length limit is 0 (no scheme allowed)"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__11 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__11_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__11_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__12 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__12_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__0_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "port number too large: "};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__1_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "invalid port number: "};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(lean_object*);
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13;
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1(uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "invalid percent encoding in user info"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1_value;
static const lean_closure_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1;
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "invalid IPv6 address: "};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__0_value;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "expected: '"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2_value;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6_value;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__0_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "invalid IPv4 address: "};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "invalid domain name: "};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "invalid host"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2_value;
static const lean_closure_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "invalid port number"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__1_value;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__1(uint8_t);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__1___boxed(lean_object*);
static const lean_closure_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__0_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__1;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "too many path segments (limit: "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__2_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__3 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__3_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "path too long (limit: "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__4 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__4_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " bytes)"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__5 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__5_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "invalid percent encoding in path segment"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__6 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__6_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__6_value)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__7 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__7_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid query string"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__1_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__1_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "too many query parameters (limit: "};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "invalid percent encoding in fragment"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "//"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0_value;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_URI_Parser_parseURI___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_Parser_parseURI___closed__0;
static lean_once_cell_t l_Std_Http_URI_Parser_parseURI___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_Parser_parseURI___closed__1;
static lean_once_cell_t l_Std_Http_URI_Parser_parseURI___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_Parser_parseURI___closed__2;
static lean_once_cell_t l_Std_Http_URI_Parser_parseURI___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_Parser_parseURI___closed__3;
static lean_once_cell_t l_Std_Http_URI_Parser_parseURI___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_Parser_parseURI___closed__4;
static const lean_string_object l_Std_Http_URI_Parser_parseURI___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "invalid fragment parse encoding"};
static const lean_object* l_Std_Http_URI_Parser_parseURI___closed__5 = (const lean_object*)&l_Std_Http_URI_Parser_parseURI___closed__5_value;
static const lean_ctor_object l_Std_Http_URI_Parser_parseURI___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_URI_Parser_parseURI___closed__5_value)}};
static const lean_object* l_Std_Http_URI_Parser_parseURI___closed__6 = (const lean_object*)&l_Std_Http_URI_Parser_parseURI___closed__6_value;
static lean_once_cell_t l_Std_Http_URI_Parser_parseURI___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_Parser_parseURI___closed__7;
static lean_once_cell_t l_Std_Http_URI_Parser_parseURI___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_Parser_parseURI___closed__8;
static lean_once_cell_t l_Std_Http_URI_Parser_parseURI___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_Parser_parseURI___closed__9;
static lean_once_cell_t l_Std_Http_URI_Parser_parseURI___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_Parser_parseURI___closed__10;
static lean_once_cell_t l_Std_Http_URI_Parser_parseURI___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_Parser_parseURI___closed__11;
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURI(lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(lean_object*);
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "not origin"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "not http absolute uri with path"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "not http absolute uri"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "http"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__4 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__4_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "https"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_URI_Parser_parseHostHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "invalid host header port"};
static const lean_object* l_Std_Http_URI_Parser_parseHostHeader___closed__0 = (const lean_object*)&l_Std_Http_URI_Parser_parseHostHeader___closed__0_value;
static const lean_ctor_object l_Std_Http_URI_Parser_parseHostHeader___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_URI_Parser_parseHostHeader___closed__0_value)}};
static const lean_object* l_Std_Http_URI_Parser_parseHostHeader___closed__1 = (const lean_object*)&l_Std_Http_URI_Parser_parseHostHeader___closed__1_value;
static const lean_string_object l_Std_Http_URI_Parser_parseHostHeader___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "invalid host header"};
static const lean_object* l_Std_Http_URI_Parser_parseHostHeader___closed__2 = (const lean_object*)&l_Std_Http_URI_Parser_parseHostHeader___closed__2_value;
static const lean_ctor_object l_Std_Http_URI_Parser_parseHostHeader___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_URI_Parser_parseHostHeader___closed__2_value)}};
static const lean_object* l_Std_Http_URI_Parser_parseHostHeader___closed__3 = (const lean_object*)&l_Std_Http_URI_Parser_parseHostHeader___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_tryOpt___redArg(lean_object* v_p_1_, lean_object* v_a_2_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_tryOpt(lean_object* v_00_u03b1_29_, lean_object* v_p_30_, lean_object* v_a_31_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_peekIs(lean_object* v_p_58_, lean_object* v_a_59_){
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(lean_object* v_msg_75_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = ((lean_object*)(l_panic___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1___closed__0));
v___x_77_ = lean_panic_fn_borrowed(v___x_76_, v_msg_75_);
return v___x_77_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0(void){
_start:
{
uint32_t v___x_78_; uint8_t v___x_79_; 
v___x_78_ = 97;
v___x_79_ = lean_uint32_to_uint8(v___x_78_);
return v___x_79_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1(void){
_start:
{
uint32_t v___x_80_; uint8_t v___x_81_; 
v___x_80_ = 122;
v___x_81_ = lean_uint32_to_uint8(v___x_80_);
return v___x_81_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2(void){
_start:
{
uint32_t v___x_82_; uint8_t v___x_83_; 
v___x_82_ = 65;
v___x_83_ = lean_uint32_to_uint8(v___x_82_);
return v___x_83_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3(void){
_start:
{
uint32_t v___x_84_; uint8_t v___x_85_; 
v___x_84_ = 90;
v___x_85_ = lean_uint32_to_uint8(v___x_84_);
return v___x_85_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0(uint8_t v___y_86_){
_start:
{
uint8_t v___y_88_; uint8_t v___x_93_; uint8_t v___x_94_; 
v___x_93_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_94_ = lean_uint8_dec_le(v___x_93_, v___y_86_);
if (v___x_94_ == 0)
{
v___y_88_ = v___x_94_;
goto v___jp_87_;
}
else
{
uint8_t v___x_95_; uint8_t v___x_96_; 
v___x_95_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_96_ = lean_uint8_dec_le(v___y_86_, v___x_95_);
v___y_88_ = v___x_96_;
goto v___jp_87_;
}
v___jp_87_:
{
if (v___y_88_ == 0)
{
uint8_t v___x_89_; uint8_t v___x_90_; 
v___x_89_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_90_ = lean_uint8_dec_le(v___x_89_, v___y_86_);
if (v___x_90_ == 0)
{
return v___x_90_;
}
else
{
uint8_t v___x_91_; uint8_t v___x_92_; 
v___x_91_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_92_ = lean_uint8_dec_le(v___y_86_, v___x_91_);
return v___x_92_;
}
}
else
{
return v___y_88_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___boxed(lean_object* v___y_97_){
_start:
{
uint8_t v___y_2635__boxed_98_; uint8_t v_res_99_; lean_object* v_r_100_; 
v___y_2635__boxed_98_ = lean_unbox(v___y_97_);
v_res_99_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0(v___y_2635__boxed_98_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1(uint32_t v___y_101_){
_start:
{
uint8_t v___y_103_; lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; uint8_t v___y_119_; 
v___x_115_ = lean_uint32_to_nat(v___y_101_);
v___x_116_ = lean_unsigned_to_nat(128u);
v___x_117_ = lean_nat_dec_lt(v___x_115_, v___x_116_);
lean_dec(v___x_115_);
if (v___x_117_ == 0)
{
v___y_103_ = v___x_117_;
goto v___jp_102_;
}
else
{
uint32_t v___x_124_; uint8_t v___x_125_; 
v___x_124_ = 48;
v___x_125_ = lean_uint32_dec_le(v___x_124_, v___y_101_);
if (v___x_125_ == 0)
{
v___y_119_ = v___x_125_;
goto v___jp_118_;
}
else
{
uint32_t v___x_126_; uint8_t v___x_127_; 
v___x_126_ = 57;
v___x_127_ = lean_uint32_dec_le(v___y_101_, v___x_126_);
v___y_119_ = v___x_127_;
goto v___jp_118_;
}
}
v___jp_102_:
{
if (v___y_103_ == 0)
{
uint32_t v___x_104_; uint8_t v___x_105_; 
v___x_104_ = 43;
v___x_105_ = lean_uint32_dec_eq(v___y_101_, v___x_104_);
if (v___x_105_ == 0)
{
uint32_t v___x_106_; uint8_t v___x_107_; 
v___x_106_ = 45;
v___x_107_ = lean_uint32_dec_eq(v___y_101_, v___x_106_);
if (v___x_107_ == 0)
{
uint32_t v___x_108_; uint8_t v___x_109_; 
v___x_108_ = 46;
v___x_109_ = lean_uint32_dec_eq(v___y_101_, v___x_108_);
if (v___x_109_ == 0)
{
return v___y_103_;
}
else
{
return v___x_109_;
}
}
else
{
return v___x_107_;
}
}
else
{
return v___x_105_;
}
}
else
{
return v___y_103_;
}
}
v___jp_110_:
{
uint32_t v___x_111_; uint8_t v___x_112_; 
v___x_111_ = 97;
v___x_112_ = lean_uint32_dec_le(v___x_111_, v___y_101_);
if (v___x_112_ == 0)
{
v___y_103_ = v___x_112_;
goto v___jp_102_;
}
else
{
uint32_t v___x_113_; uint8_t v___x_114_; 
v___x_113_ = 122;
v___x_114_ = lean_uint32_dec_le(v___y_101_, v___x_113_);
v___y_103_ = v___x_114_;
goto v___jp_102_;
}
}
v___jp_118_:
{
if (v___y_119_ == 0)
{
uint32_t v___x_120_; uint8_t v___x_121_; 
v___x_120_ = 65;
v___x_121_ = lean_uint32_dec_le(v___x_120_, v___y_101_);
if (v___x_121_ == 0)
{
goto v___jp_110_;
}
else
{
uint32_t v___x_122_; uint8_t v___x_123_; 
v___x_122_ = 90;
v___x_123_ = lean_uint32_dec_le(v___y_101_, v___x_122_);
if (v___x_123_ == 0)
{
goto v___jp_110_;
}
else
{
v___y_103_ = v___x_117_;
goto v___jp_102_;
}
}
}
else
{
return v___y_119_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___boxed(lean_object* v___y_128_){
_start:
{
uint32_t v___y_2666__boxed_129_; uint8_t v_res_130_; lean_object* v_r_131_; 
v___y_2666__boxed_129_ = lean_unbox_uint32(v___y_128_);
lean_dec(v___y_128_);
v_res_130_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1(v___y_2666__boxed_129_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0(void){
_start:
{
uint32_t v___x_132_; uint8_t v___x_133_; 
v___x_132_ = 43;
v___x_133_ = lean_uint32_to_uint8(v___x_132_);
return v___x_133_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1(void){
_start:
{
uint32_t v___x_134_; uint8_t v___x_135_; 
v___x_134_ = 45;
v___x_135_ = lean_uint32_to_uint8(v___x_134_);
return v___x_135_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2(void){
_start:
{
uint32_t v___x_136_; uint8_t v___x_137_; 
v___x_136_ = 46;
v___x_137_ = lean_uint32_to_uint8(v___x_136_);
return v___x_137_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3(void){
_start:
{
uint32_t v___x_138_; uint8_t v___x_139_; 
v___x_138_ = 48;
v___x_139_ = lean_uint32_to_uint8(v___x_138_);
return v___x_139_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4(void){
_start:
{
uint32_t v___x_140_; uint8_t v___x_141_; 
v___x_140_ = 57;
v___x_141_ = lean_uint32_to_uint8(v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2(uint8_t v_c_142_){
_start:
{
uint8_t v___y_144_; uint8_t v___y_152_; uint8_t v___y_158_; uint8_t v___x_163_; uint8_t v___x_164_; 
v___x_163_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3);
v___x_164_ = lean_uint8_dec_le(v___x_163_, v_c_142_);
if (v___x_164_ == 0)
{
v___y_158_ = v___x_164_;
goto v___jp_157_;
}
else
{
uint8_t v___x_165_; uint8_t v___x_166_; 
v___x_165_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4);
v___x_166_ = lean_uint8_dec_le(v_c_142_, v___x_165_);
v___y_158_ = v___x_166_;
goto v___jp_157_;
}
v___jp_143_:
{
if (v___y_144_ == 0)
{
uint8_t v___x_145_; uint8_t v___x_146_; 
v___x_145_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0);
v___x_146_ = lean_uint8_dec_eq(v_c_142_, v___x_145_);
if (v___x_146_ == 0)
{
uint8_t v___x_147_; uint8_t v___x_148_; 
v___x_147_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1);
v___x_148_ = lean_uint8_dec_eq(v_c_142_, v___x_147_);
if (v___x_148_ == 0)
{
uint8_t v___x_149_; uint8_t v___x_150_; 
v___x_149_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2);
v___x_150_ = lean_uint8_dec_eq(v_c_142_, v___x_149_);
if (v___x_150_ == 0)
{
return v___y_144_;
}
else
{
return v___x_150_;
}
}
else
{
return v___x_148_;
}
}
else
{
return v___x_146_;
}
}
else
{
return v___y_144_;
}
}
v___jp_151_:
{
if (v___y_152_ == 0)
{
uint8_t v___x_153_; uint8_t v___x_154_; 
v___x_153_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_154_ = lean_uint8_dec_le(v___x_153_, v_c_142_);
if (v___x_154_ == 0)
{
v___y_144_ = v___x_154_;
goto v___jp_143_;
}
else
{
uint8_t v___x_155_; uint8_t v___x_156_; 
v___x_155_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_156_ = lean_uint8_dec_le(v_c_142_, v___x_155_);
v___y_144_ = v___x_156_;
goto v___jp_143_;
}
}
else
{
return v___y_152_;
}
}
v___jp_157_:
{
if (v___y_158_ == 0)
{
uint8_t v___x_159_; uint8_t v___x_160_; 
v___x_159_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_160_ = lean_uint8_dec_le(v___x_159_, v_c_142_);
if (v___x_160_ == 0)
{
v___y_152_ = v___x_160_;
goto v___jp_151_;
}
else
{
uint8_t v___x_161_; uint8_t v___x_162_; 
v___x_161_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_162_ = lean_uint8_dec_le(v_c_142_, v___x_161_);
v___y_152_ = v___x_162_;
goto v___jp_151_;
}
}
else
{
return v___y_158_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___boxed(lean_object* v_c_167_){
_start:
{
uint8_t v_c_boxed_168_; uint8_t v_res_169_; lean_object* v_r_170_; 
v_c_boxed_168_ = lean_unbox(v_c_167_);
v_res_169_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2(v_c_boxed_168_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(lean_object* v_s_171_, lean_object* v_p_172_){
_start:
{
uint32_t v___y_174_; lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = lean_string_utf8_byte_size(v_s_171_);
v___x_180_ = lean_nat_dec_eq(v_p_172_, v___x_179_);
if (v___x_180_ == 0)
{
uint32_t v___x_181_; uint32_t v___x_182_; uint8_t v___x_183_; 
v___x_181_ = lean_string_utf8_get_fast(v_s_171_, v_p_172_);
v___x_182_ = 65;
v___x_183_ = lean_uint32_dec_le(v___x_182_, v___x_181_);
if (v___x_183_ == 0)
{
v___y_174_ = v___x_181_;
goto v___jp_173_;
}
else
{
uint32_t v___x_184_; uint8_t v___x_185_; 
v___x_184_ = 90;
v___x_185_ = lean_uint32_dec_le(v___x_181_, v___x_184_);
if (v___x_185_ == 0)
{
v___y_174_ = v___x_181_;
goto v___jp_173_;
}
else
{
uint32_t v___x_186_; uint32_t v___x_187_; 
v___x_186_ = 32;
v___x_187_ = lean_uint32_add(v___x_181_, v___x_186_);
v___y_174_ = v___x_187_;
goto v___jp_173_;
}
}
}
else
{
lean_dec(v_p_172_);
return v_s_171_;
}
v___jp_173_:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
lean_inc(v_p_172_);
v___x_175_ = lean_string_utf8_set(v_s_171_, v_p_172_, v___y_174_);
v___x_176_ = l_Char_utf8Size(v___y_174_);
v___x_177_ = lean_nat_add(v_p_172_, v___x_176_);
lean_dec(v___x_176_);
lean_dec(v_p_172_);
v_s_171_ = v___x_175_;
v_p_172_ = v___x_177_;
goto _start;
}
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_196_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6));
v___x_197_ = lean_unsigned_to_nat(46u);
v___x_198_ = lean_unsigned_to_nat(193u);
v___x_199_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5));
v___x_200_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__4));
v___x_201_ = l_mkPanicMessageWithDecl(v___x_200_, v___x_199_, v___x_198_, v___x_197_, v___x_196_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(lean_object* v_config_209_, lean_object* v_a_210_){
_start:
{
lean_object* v___y_212_; lean_object* v___y_216_; lean_object* v___y_217_; uint8_t v_val_218_; uint32_t v___y_221_; lean_object* v___y_222_; lean_object* v___y_223_; lean_object* v_maxSchemeLength_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v_maxSchemeLength_228_ = lean_ctor_get(v_config_209_, 0);
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = lean_nat_dec_eq(v_maxSchemeLength_228_, v___x_229_);
if (v___x_230_ == 0)
{
lean_object* v___f_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v_fst_234_; lean_object* v_snd_235_; uint8_t v___x_236_; 
v___f_231_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__2));
v___x_232_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_a_210_);
v___x_233_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo1_findEnd(v___f_231_, v___x_232_, v___x_229_, v_a_210_);
v_fst_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_fst_234_);
v_snd_235_ = lean_ctor_get(v___x_233_, 1);
lean_inc(v_snd_235_);
lean_dec_ref(v___x_233_);
v___x_236_ = lean_nat_dec_eq(v_fst_234_, v___x_229_);
if (v___x_236_ == 0)
{
lean_object* v_array_237_; lean_object* v_idx_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_311_; 
v_array_237_ = lean_ctor_get(v_a_210_, 0);
v_idx_238_ = lean_ctor_get(v_a_210_, 1);
v_isSharedCheck_311_ = !lean_is_exclusive(v_a_210_);
if (v_isSharedCheck_311_ == 0)
{
v___x_240_ = v_a_210_;
v_isShared_241_ = v_isSharedCheck_311_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_idx_238_);
lean_inc(v_array_237_);
lean_dec(v_a_210_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_311_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___f_242_; lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v_lower_264_; lean_object* v_upper_265_; lean_object* v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; lean_object* v___f_284_; lean_object* v___y_286_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___y_302_; uint8_t v___x_310_; 
v___f_242_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__3));
v___f_284_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__8));
v___x_299_ = lean_nat_add(v_idx_238_, v_fst_234_);
lean_dec(v_fst_234_);
v___x_300_ = lean_byte_array_size(v_array_237_);
v___x_310_ = lean_nat_dec_le(v_idx_238_, v___x_229_);
if (v___x_310_ == 0)
{
v___y_302_ = v_idx_238_;
goto v___jp_301_;
}
else
{
lean_dec(v_idx_238_);
v___y_302_ = v___x_229_;
goto v___jp_301_;
}
v___jp_243_:
{
lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_246_ = l_String_mapAux___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(v___y_245_, v___x_229_);
lean_inc_ref(v___x_246_);
v___x_247_ = l_Std_Http_Internal_instDecidableIsLowerCase(v___x_246_);
if (v___x_247_ == 0)
{
lean_dec_ref(v___x_246_);
v___y_212_ = v___y_244_;
goto v___jp_211_;
}
else
{
lean_object* v___x_248_; uint8_t v___x_249_; 
lean_inc_ref(v___x_246_);
v___x_248_ = lean_string_data(v___x_246_);
lean_inc(v___x_248_);
v___x_249_ = l_List_all___redArg(v___x_248_, v___f_242_);
if (v___x_249_ == 0)
{
lean_dec(v___x_248_);
lean_dec_ref(v___x_246_);
v___y_212_ = v___y_244_;
goto v___jp_211_;
}
else
{
lean_object* v___x_250_; 
v___x_250_ = l_List_head_x3f___redArg(v___x_248_);
lean_dec(v___x_248_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_dec_ref(v___x_246_);
v___y_212_ = v___y_244_;
goto v___jp_211_;
}
else
{
lean_object* v_val_251_; uint32_t v___x_252_; uint32_t v___x_253_; uint8_t v___x_254_; 
v_val_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_val_251_);
lean_dec_ref(v___x_250_);
v___x_252_ = 65;
v___x_253_ = lean_unbox_uint32(v_val_251_);
v___x_254_ = lean_uint32_dec_le(v___x_252_, v___x_253_);
if (v___x_254_ == 0)
{
uint32_t v___x_255_; 
v___x_255_ = lean_unbox_uint32(v_val_251_);
lean_dec(v_val_251_);
v___y_221_ = v___x_255_;
v___y_222_ = v___y_244_;
v___y_223_ = v___x_246_;
goto v___jp_220_;
}
else
{
uint32_t v___x_256_; uint32_t v___x_257_; uint8_t v___x_258_; 
v___x_256_ = 90;
v___x_257_ = lean_unbox_uint32(v_val_251_);
v___x_258_ = lean_uint32_dec_le(v___x_257_, v___x_256_);
if (v___x_258_ == 0)
{
uint32_t v___x_259_; 
v___x_259_ = lean_unbox_uint32(v_val_251_);
lean_dec(v_val_251_);
v___y_221_ = v___x_259_;
v___y_222_ = v___y_244_;
v___y_223_ = v___x_246_;
goto v___jp_220_;
}
else
{
lean_dec(v_val_251_);
v___y_216_ = v___y_244_;
v___y_217_ = v___x_246_;
v_val_218_ = v___x_249_;
goto v___jp_215_;
}
}
}
}
}
}
v___jp_260_:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_266_ = l_ByteArray_toByteSlice(v___y_263_, v_lower_264_, v_upper_265_);
v___x_267_ = l_ByteSlice_toByteArray(v___y_262_);
v___x_268_ = l_ByteSlice_toByteArray(v___x_266_);
v___x_269_ = lean_byte_array_size(v___x_267_);
v___x_270_ = lean_byte_array_size(v___x_268_);
v___x_271_ = lean_byte_array_copy_slice(v___x_268_, v___x_229_, v___x_267_, v___x_269_, v___x_270_, v___x_236_);
lean_dec_ref(v___x_268_);
v___x_272_ = lean_string_validate_utf8(v___x_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; 
lean_dec_ref(v___x_271_);
v___x_273_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_274_ = l_panic___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(v___x_273_);
v___y_244_ = v___y_261_;
v___y_245_ = v___x_274_;
goto v___jp_243_;
}
else
{
lean_object* v___x_275_; 
v___x_275_ = lean_string_from_utf8_unchecked(v___x_271_);
v___y_244_ = v___y_261_;
v___y_245_ = v___x_275_;
goto v___jp_243_;
}
}
v___jp_276_:
{
uint8_t v___x_283_; 
v___x_283_ = lean_nat_dec_le(v___y_281_, v___y_280_);
if (v___x_283_ == 0)
{
lean_dec(v___y_281_);
v___y_261_ = v___y_279_;
v___y_262_ = v___y_278_;
v___y_263_ = v___y_277_;
v_lower_264_ = v___y_282_;
v_upper_265_ = v___y_280_;
goto v___jp_260_;
}
else
{
lean_dec(v___y_280_);
v___y_261_ = v___y_279_;
v___y_262_ = v___y_278_;
v___y_263_ = v___y_277_;
v_lower_264_ = v___y_282_;
v_upper_265_ = v___y_281_;
goto v___jp_260_;
}
}
v___jp_285_:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v_fst_289_; lean_object* v_snd_290_; lean_object* v_lower_291_; lean_object* v_upper_292_; lean_object* v_array_293_; lean_object* v_idx_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_287_ = lean_nat_sub(v_maxSchemeLength_228_, v___x_232_);
lean_inc(v_snd_235_);
v___x_288_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo_findEnd(v___f_284_, v___x_287_, v___x_229_, v_snd_235_);
lean_dec(v___x_287_);
v_fst_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_fst_289_);
v_snd_290_ = lean_ctor_get(v___x_288_, 1);
lean_inc(v_snd_290_);
lean_dec_ref(v___x_288_);
v_lower_291_ = lean_ctor_get(v___y_286_, 0);
lean_inc(v_lower_291_);
v_upper_292_ = lean_ctor_get(v___y_286_, 1);
lean_inc(v_upper_292_);
lean_dec_ref(v___y_286_);
v_array_293_ = lean_ctor_get(v_snd_235_, 0);
lean_inc_ref(v_array_293_);
v_idx_294_ = lean_ctor_get(v_snd_235_, 1);
lean_inc(v_idx_294_);
lean_dec(v_snd_235_);
v___x_295_ = l_ByteArray_toByteSlice(v_array_237_, v_lower_291_, v_upper_292_);
v___x_296_ = lean_nat_add(v_idx_294_, v_fst_289_);
lean_dec(v_fst_289_);
v___x_297_ = lean_byte_array_size(v_array_293_);
v___x_298_ = lean_nat_dec_le(v_idx_294_, v___x_229_);
if (v___x_298_ == 0)
{
v___y_277_ = v_array_293_;
v___y_278_ = v___x_295_;
v___y_279_ = v_snd_290_;
v___y_280_ = v___x_297_;
v___y_281_ = v___x_296_;
v___y_282_ = v_idx_294_;
goto v___jp_276_;
}
else
{
lean_dec(v_idx_294_);
v___y_277_ = v_array_293_;
v___y_278_ = v___x_295_;
v___y_279_ = v_snd_290_;
v___y_280_ = v___x_297_;
v___y_281_ = v___x_296_;
v___y_282_ = v___x_229_;
goto v___jp_276_;
}
}
v___jp_301_:
{
uint8_t v___x_303_; 
v___x_303_ = lean_nat_dec_le(v___x_299_, v___x_300_);
if (v___x_303_ == 0)
{
lean_object* v___x_305_; 
lean_dec(v___x_299_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 1, v___x_300_);
lean_ctor_set(v___x_240_, 0, v___y_302_);
v___x_305_ = v___x_240_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___y_302_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v___x_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
v___y_286_ = v___x_305_;
goto v___jp_285_;
}
}
else
{
lean_object* v___x_308_; 
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 1, v___x_299_);
lean_ctor_set(v___x_240_, 0, v___y_302_);
v___x_308_ = v___x_240_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___y_302_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v___x_299_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
v___y_286_ = v___x_308_;
goto v___jp_285_;
}
}
}
}
}
else
{
lean_object* v_array_312_; lean_object* v_idx_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_327_; 
lean_dec(v_fst_234_);
v_array_312_ = lean_ctor_get(v_snd_235_, 0);
v_idx_313_ = lean_ctor_get(v_snd_235_, 1);
v_isSharedCheck_327_ = !lean_is_exclusive(v_snd_235_);
if (v_isSharedCheck_327_ == 0)
{
v___x_315_ = v_snd_235_;
v_isShared_316_ = v_isSharedCheck_327_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_idx_313_);
lean_inc(v_array_312_);
lean_dec(v_snd_235_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_327_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_317_ = lean_byte_array_size(v_array_312_);
lean_dec_ref(v_array_312_);
v___x_318_ = lean_nat_dec_le(v___x_317_, v_idx_313_);
lean_dec(v_idx_313_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_321_; 
v___x_319_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10));
if (v_isShared_316_ == 0)
{
lean_ctor_set_tag(v___x_315_, 1);
lean_ctor_set(v___x_315_, 1, v___x_319_);
lean_ctor_set(v___x_315_, 0, v_a_210_);
v___x_321_ = v___x_315_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_210_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
else
{
lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_323_ = lean_box(0);
if (v_isShared_316_ == 0)
{
lean_ctor_set_tag(v___x_315_, 1);
lean_ctor_set(v___x_315_, 1, v___x_323_);
lean_ctor_set(v___x_315_, 0, v_a_210_);
v___x_325_ = v___x_315_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_210_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__12));
v___x_329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_329_, 0, v_a_210_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
return v___x_329_;
}
v___jp_211_:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__1));
v___x_214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_214_, 0, v___y_212_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
return v___x_214_;
}
v___jp_215_:
{
if (v_val_218_ == 0)
{
lean_dec_ref(v___y_217_);
v___y_212_ = v___y_216_;
goto v___jp_211_;
}
else
{
lean_object* v___x_219_; 
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v___y_216_);
lean_ctor_set(v___x_219_, 1, v___y_217_);
return v___x_219_;
}
}
v___jp_220_:
{
uint32_t v___x_224_; uint8_t v___x_225_; 
v___x_224_ = 97;
v___x_225_ = lean_uint32_dec_le(v___x_224_, v___y_221_);
if (v___x_225_ == 0)
{
v___y_216_ = v___y_222_;
v___y_217_ = v___y_223_;
v_val_218_ = v___x_225_;
goto v___jp_215_;
}
else
{
uint32_t v___x_226_; uint8_t v___x_227_; 
v___x_226_ = 122;
v___x_227_ = lean_uint32_dec_le(v___y_221_, v___x_226_);
v___y_216_ = v___y_222_;
v___y_217_ = v___y_223_;
v_val_218_ = v___x_227_;
goto v___jp_215_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___boxed(lean_object* v_config_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_330_, v_a_331_);
lean_dec_ref(v_config_330_);
return v_res_332_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0(uint8_t v___y_333_){
_start:
{
uint8_t v___x_334_; uint8_t v___x_335_; 
v___x_334_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3);
v___x_335_ = lean_uint8_dec_le(v___x_334_, v___y_333_);
if (v___x_335_ == 0)
{
return v___x_335_;
}
else
{
uint8_t v___x_336_; uint8_t v___x_337_; 
v___x_336_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4);
v___x_337_ = lean_uint8_dec_le(v___y_333_, v___x_336_);
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0___boxed(lean_object* v___y_338_){
_start:
{
uint8_t v___y_600__boxed_339_; uint8_t v_res_340_; lean_object* v_r_341_; 
v___y_600__boxed_339_ = lean_unbox(v___y_338_);
v_res_340_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0(v___y_600__boxed_339_);
v_r_341_ = lean_box(v_res_340_);
return v_r_341_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(lean_object* v_a_345_){
_start:
{
lean_object* v___f_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v_fst_350_; lean_object* v_snd_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_421_; 
v___f_346_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__0));
v___x_347_ = lean_unsigned_to_nat(5u);
v___x_348_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_345_);
v___x_349_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo1_findEnd(v___f_346_, v___x_347_, v___x_348_, v_a_345_);
v_fst_350_ = lean_ctor_get(v___x_349_, 0);
v_snd_351_ = lean_ctor_get(v___x_349_, 1);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_421_ == 0)
{
v___x_353_ = v___x_349_;
v_isShared_354_ = v_isSharedCheck_421_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_snd_351_);
lean_inc(v_fst_350_);
lean_dec(v___x_349_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_421_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___y_356_; uint8_t v___x_387_; 
v___x_387_ = lean_nat_dec_eq(v_fst_350_, v___x_348_);
if (v___x_387_ == 0)
{
lean_object* v_array_388_; lean_object* v_idx_389_; lean_object* v_lower_391_; lean_object* v_upper_392_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___y_402_; uint8_t v___x_404_; 
v_array_388_ = lean_ctor_get(v_a_345_, 0);
lean_inc_ref(v_array_388_);
v_idx_389_ = lean_ctor_get(v_a_345_, 1);
lean_inc(v_idx_389_);
lean_dec_ref(v_a_345_);
v___x_399_ = lean_nat_add(v_idx_389_, v_fst_350_);
lean_dec(v_fst_350_);
v___x_400_ = lean_byte_array_size(v_array_388_);
v___x_404_ = lean_nat_dec_le(v_idx_389_, v___x_348_);
if (v___x_404_ == 0)
{
v___y_402_ = v_idx_389_;
goto v___jp_401_;
}
else
{
lean_dec(v_idx_389_);
v___y_402_ = v___x_348_;
goto v___jp_401_;
}
v___jp_390_:
{
lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_393_ = l_ByteArray_toByteSlice(v_array_388_, v_lower_391_, v_upper_392_);
v___x_394_ = l_ByteSlice_toByteArray(v___x_393_);
v___x_395_ = lean_string_validate_utf8(v___x_394_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; 
lean_dec_ref(v___x_394_);
v___x_396_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_397_ = l_panic___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(v___x_396_);
v___y_356_ = v___x_397_;
goto v___jp_355_;
}
else
{
lean_object* v___x_398_; 
v___x_398_ = lean_string_from_utf8_unchecked(v___x_394_);
v___y_356_ = v___x_398_;
goto v___jp_355_;
}
}
v___jp_401_:
{
uint8_t v___x_403_; 
v___x_403_ = lean_nat_dec_le(v___x_399_, v___x_400_);
if (v___x_403_ == 0)
{
lean_dec(v___x_399_);
v_lower_391_ = v___y_402_;
v_upper_392_ = v___x_400_;
goto v___jp_390_;
}
else
{
v_lower_391_ = v___y_402_;
v_upper_392_ = v___x_399_;
goto v___jp_390_;
}
}
}
else
{
lean_object* v_array_405_; lean_object* v_idx_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_420_; 
lean_del_object(v___x_353_);
lean_dec(v_fst_350_);
v_array_405_ = lean_ctor_get(v_snd_351_, 0);
v_idx_406_ = lean_ctor_get(v_snd_351_, 1);
v_isSharedCheck_420_ = !lean_is_exclusive(v_snd_351_);
if (v_isSharedCheck_420_ == 0)
{
v___x_408_ = v_snd_351_;
v_isShared_409_ = v_isSharedCheck_420_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_idx_406_);
lean_inc(v_array_405_);
lean_dec(v_snd_351_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_420_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = lean_byte_array_size(v_array_405_);
lean_dec_ref(v_array_405_);
v___x_411_ = lean_nat_dec_le(v___x_410_, v_idx_406_);
lean_dec(v_idx_406_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_412_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10));
if (v_isShared_409_ == 0)
{
lean_ctor_set_tag(v___x_408_, 1);
lean_ctor_set(v___x_408_, 1, v___x_412_);
lean_ctor_set(v___x_408_, 0, v_a_345_);
v___x_414_ = v___x_408_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_345_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v___x_412_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
else
{
lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_416_ = lean_box(0);
if (v_isShared_409_ == 0)
{
lean_ctor_set_tag(v___x_408_, 1);
lean_ctor_set(v___x_408_, 1, v___x_416_);
lean_ctor_set(v___x_408_, 0, v_a_345_);
v___x_418_ = v___x_408_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_345_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
v___jp_355_:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = lean_string_utf8_byte_size(v___y_356_);
lean_inc_ref(v___y_356_);
v___x_358_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_358_, 0, v___y_356_);
lean_ctor_set(v___x_358_, 1, v___x_348_);
lean_ctor_set(v___x_358_, 2, v___x_357_);
v___x_359_ = l_String_Slice_toNat_x3f(v___x_358_);
lean_dec_ref(v___x_358_);
if (lean_obj_tag(v___x_359_) == 1)
{
lean_object* v_val_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_380_; 
lean_dec_ref(v___y_356_);
v_val_360_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_380_ == 0)
{
v___x_362_ = v___x_359_;
v_isShared_363_ = v_isSharedCheck_380_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_val_360_);
lean_dec(v___x_359_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_380_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_364_ = lean_unsigned_to_nat(65535u);
v___x_365_ = lean_nat_dec_lt(v___x_364_, v_val_360_);
if (v___x_365_ == 0)
{
uint16_t v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
lean_del_object(v___x_362_);
v___x_366_ = lean_uint16_of_nat(v_val_360_);
lean_dec(v_val_360_);
v___x_367_ = lean_box(v___x_366_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v___x_367_);
lean_ctor_set(v___x_353_, 0, v_snd_351_);
v___x_369_ = v___x_353_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_snd_351_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v___x_367_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
else
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_371_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__1));
v___x_372_ = l_Nat_reprFast(v_val_360_);
v___x_373_ = lean_string_append(v___x_371_, v___x_372_);
lean_dec_ref(v___x_372_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v___x_373_);
v___x_375_ = v___x_362_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_373_);
v___x_375_ = v_reuseFailAlloc_379_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_377_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set_tag(v___x_353_, 1);
lean_ctor_set(v___x_353_, 1, v___x_375_);
lean_ctor_set(v___x_353_, 0, v_snd_351_);
v___x_377_ = v___x_353_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_snd_351_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v___x_375_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_385_; 
lean_dec(v___x_359_);
v___x_381_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__2));
v___x_382_ = lean_string_append(v___x_381_, v___y_356_);
lean_dec_ref(v___y_356_);
v___x_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
if (v_isShared_354_ == 0)
{
lean_ctor_set_tag(v___x_353_, 1);
lean_ctor_set(v___x_353_, 1, v___x_383_);
lean_ctor_set(v___x_353_, 0, v_snd_351_);
v___x_385_ = v___x_353_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_snd_351_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0(void){
_start:
{
uint32_t v___x_422_; uint8_t v___x_423_; 
v___x_422_ = 58;
v___x_423_ = lean_uint32_to_uint8(v___x_422_);
return v___x_423_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1(void){
_start:
{
uint32_t v___x_424_; uint8_t v___x_425_; 
v___x_424_ = 37;
v___x_425_ = lean_uint32_to_uint8(v___x_424_);
return v___x_425_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2(void){
_start:
{
uint32_t v___x_426_; uint8_t v___x_427_; 
v___x_426_ = 38;
v___x_427_ = lean_uint32_to_uint8(v___x_426_);
return v___x_427_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3(void){
_start:
{
uint32_t v___x_428_; uint8_t v___x_429_; 
v___x_428_ = 39;
v___x_429_ = lean_uint32_to_uint8(v___x_428_);
return v___x_429_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4(void){
_start:
{
uint32_t v___x_430_; uint8_t v___x_431_; 
v___x_430_ = 40;
v___x_431_ = lean_uint32_to_uint8(v___x_430_);
return v___x_431_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5(void){
_start:
{
uint32_t v___x_432_; uint8_t v___x_433_; 
v___x_432_ = 41;
v___x_433_ = lean_uint32_to_uint8(v___x_432_);
return v___x_433_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6(void){
_start:
{
uint32_t v___x_434_; uint8_t v___x_435_; 
v___x_434_ = 42;
v___x_435_ = lean_uint32_to_uint8(v___x_434_);
return v___x_435_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7(void){
_start:
{
uint32_t v___x_436_; uint8_t v___x_437_; 
v___x_436_ = 44;
v___x_437_ = lean_uint32_to_uint8(v___x_436_);
return v___x_437_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8(void){
_start:
{
uint32_t v___x_438_; uint8_t v___x_439_; 
v___x_438_ = 59;
v___x_439_ = lean_uint32_to_uint8(v___x_438_);
return v___x_439_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9(void){
_start:
{
uint32_t v___x_440_; uint8_t v___x_441_; 
v___x_440_ = 61;
v___x_441_ = lean_uint32_to_uint8(v___x_440_);
return v___x_441_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10(void){
_start:
{
uint32_t v___x_442_; uint8_t v___x_443_; 
v___x_442_ = 33;
v___x_443_ = lean_uint32_to_uint8(v___x_442_);
return v___x_443_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11(void){
_start:
{
uint32_t v___x_444_; uint8_t v___x_445_; 
v___x_444_ = 36;
v___x_445_ = lean_uint32_to_uint8(v___x_444_);
return v___x_445_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12(void){
_start:
{
uint32_t v___x_446_; uint8_t v___x_447_; 
v___x_446_ = 95;
v___x_447_ = lean_uint32_to_uint8(v___x_446_);
return v___x_447_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13(void){
_start:
{
uint32_t v___x_448_; uint8_t v___x_449_; 
v___x_448_ = 126;
v___x_449_ = lean_uint32_to_uint8(v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0(uint8_t v_x_450_){
_start:
{
uint8_t v___y_452_; uint8_t v___y_458_; uint8_t v___y_478_; uint8_t v___y_484_; uint8_t v___y_490_; uint8_t v___y_496_; uint8_t v___y_502_; uint8_t v___x_507_; uint8_t v___x_508_; 
v___x_507_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_508_ = lean_uint8_dec_eq(v_x_450_, v___x_507_);
if (v___x_508_ == 0)
{
uint8_t v___x_509_; uint8_t v___x_510_; 
v___x_509_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3);
v___x_510_ = lean_uint8_dec_le(v___x_509_, v_x_450_);
if (v___x_510_ == 0)
{
v___y_502_ = v___x_510_;
goto v___jp_501_;
}
else
{
uint8_t v___x_511_; uint8_t v___x_512_; 
v___x_511_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4);
v___x_512_ = lean_uint8_dec_le(v_x_450_, v___x_511_);
v___y_502_ = v___x_512_;
goto v___jp_501_;
}
}
else
{
uint8_t v___x_513_; 
v___x_513_ = 0;
return v___x_513_;
}
v___jp_451_:
{
if (v___y_452_ == 0)
{
uint8_t v___x_453_; uint8_t v___x_454_; 
v___x_453_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_454_ = lean_uint8_dec_eq(v_x_450_, v___x_453_);
if (v___x_454_ == 0)
{
uint8_t v___x_455_; uint8_t v___x_456_; 
v___x_455_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_456_ = lean_uint8_dec_eq(v_x_450_, v___x_455_);
if (v___x_456_ == 0)
{
return v___x_454_;
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
return v___y_452_;
}
}
v___jp_457_:
{
if (v___y_458_ == 0)
{
uint8_t v___x_459_; uint8_t v___x_460_; 
v___x_459_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_460_ = lean_uint8_dec_eq(v_x_450_, v___x_459_);
if (v___x_460_ == 0)
{
uint8_t v___x_461_; uint8_t v___x_462_; 
v___x_461_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_462_ = lean_uint8_dec_eq(v_x_450_, v___x_461_);
if (v___x_462_ == 0)
{
uint8_t v___x_463_; uint8_t v___x_464_; 
v___x_463_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_464_ = lean_uint8_dec_eq(v_x_450_, v___x_463_);
if (v___x_464_ == 0)
{
uint8_t v___x_465_; uint8_t v___x_466_; 
v___x_465_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_466_ = lean_uint8_dec_eq(v_x_450_, v___x_465_);
if (v___x_466_ == 0)
{
uint8_t v___x_467_; uint8_t v___x_468_; 
v___x_467_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_468_ = lean_uint8_dec_eq(v_x_450_, v___x_467_);
if (v___x_468_ == 0)
{
uint8_t v___x_469_; uint8_t v___x_470_; 
v___x_469_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0);
v___x_470_ = lean_uint8_dec_eq(v_x_450_, v___x_469_);
if (v___x_470_ == 0)
{
uint8_t v___x_471_; uint8_t v___x_472_; 
v___x_471_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_472_ = lean_uint8_dec_eq(v_x_450_, v___x_471_);
if (v___x_472_ == 0)
{
uint8_t v___x_473_; uint8_t v___x_474_; 
v___x_473_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_474_ = lean_uint8_dec_eq(v_x_450_, v___x_473_);
if (v___x_474_ == 0)
{
uint8_t v___x_475_; uint8_t v___x_476_; 
v___x_475_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_476_ = lean_uint8_dec_eq(v_x_450_, v___x_475_);
v___y_452_ = v___x_476_;
goto v___jp_451_;
}
else
{
v___y_452_ = v___x_474_;
goto v___jp_451_;
}
}
else
{
v___y_452_ = v___x_472_;
goto v___jp_451_;
}
}
else
{
v___y_452_ = v___x_470_;
goto v___jp_451_;
}
}
else
{
v___y_452_ = v___x_468_;
goto v___jp_451_;
}
}
else
{
v___y_452_ = v___x_466_;
goto v___jp_451_;
}
}
else
{
v___y_452_ = v___x_464_;
goto v___jp_451_;
}
}
else
{
v___y_452_ = v___x_462_;
goto v___jp_451_;
}
}
else
{
v___y_452_ = v___x_460_;
goto v___jp_451_;
}
}
else
{
return v___y_458_;
}
}
v___jp_477_:
{
if (v___y_478_ == 0)
{
uint8_t v___x_479_; uint8_t v___x_480_; 
v___x_479_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_480_ = lean_uint8_dec_eq(v_x_450_, v___x_479_);
if (v___x_480_ == 0)
{
uint8_t v___x_481_; uint8_t v___x_482_; 
v___x_481_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_482_ = lean_uint8_dec_eq(v_x_450_, v___x_481_);
v___y_458_ = v___x_482_;
goto v___jp_457_;
}
else
{
v___y_458_ = v___x_480_;
goto v___jp_457_;
}
}
else
{
return v___y_478_;
}
}
v___jp_483_:
{
if (v___y_484_ == 0)
{
uint8_t v___x_485_; uint8_t v___x_486_; 
v___x_485_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_486_ = lean_uint8_dec_eq(v_x_450_, v___x_485_);
if (v___x_486_ == 0)
{
uint8_t v___x_487_; uint8_t v___x_488_; 
v___x_487_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_488_ = lean_uint8_dec_eq(v_x_450_, v___x_487_);
v___y_478_ = v___x_488_;
goto v___jp_477_;
}
else
{
v___y_478_ = v___x_486_;
goto v___jp_477_;
}
}
else
{
return v___y_484_;
}
}
v___jp_489_:
{
if (v___y_490_ == 0)
{
uint8_t v___x_491_; uint8_t v___x_492_; 
v___x_491_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1);
v___x_492_ = lean_uint8_dec_eq(v_x_450_, v___x_491_);
if (v___x_492_ == 0)
{
uint8_t v___x_493_; uint8_t v___x_494_; 
v___x_493_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2);
v___x_494_ = lean_uint8_dec_eq(v_x_450_, v___x_493_);
v___y_484_ = v___x_494_;
goto v___jp_483_;
}
else
{
v___y_484_ = v___x_492_;
goto v___jp_483_;
}
}
else
{
return v___y_490_;
}
}
v___jp_495_:
{
if (v___y_496_ == 0)
{
uint8_t v___x_497_; uint8_t v___x_498_; 
v___x_497_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_498_ = lean_uint8_dec_le(v___x_497_, v_x_450_);
if (v___x_498_ == 0)
{
v___y_490_ = v___x_498_;
goto v___jp_489_;
}
else
{
uint8_t v___x_499_; uint8_t v___x_500_; 
v___x_499_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_500_ = lean_uint8_dec_le(v_x_450_, v___x_499_);
v___y_490_ = v___x_500_;
goto v___jp_489_;
}
}
else
{
return v___y_496_;
}
}
v___jp_501_:
{
if (v___y_502_ == 0)
{
uint8_t v___x_503_; uint8_t v___x_504_; 
v___x_503_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_504_ = lean_uint8_dec_le(v___x_503_, v_x_450_);
if (v___x_504_ == 0)
{
v___y_496_ = v___x_504_;
goto v___jp_495_;
}
else
{
uint8_t v___x_505_; uint8_t v___x_506_; 
v___x_505_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_506_ = lean_uint8_dec_le(v_x_450_, v___x_505_);
v___y_496_ = v___x_506_;
goto v___jp_495_;
}
}
else
{
return v___y_502_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___boxed(lean_object* v_x_514_){
_start:
{
uint8_t v_x_boxed_515_; uint8_t v_res_516_; lean_object* v_r_517_; 
v_x_boxed_515_ = lean_unbox(v_x_514_);
v_res_516_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0(v_x_boxed_515_);
v_r_517_ = lean_box(v_res_516_);
return v_r_517_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1(uint8_t v___x_518_, uint8_t v___x_519_, uint8_t v_x_520_){
_start:
{
uint8_t v___y_522_; uint8_t v___y_527_; uint8_t v___y_547_; uint8_t v___y_553_; uint8_t v___y_559_; uint8_t v___y_565_; uint8_t v___y_571_; uint8_t v___x_576_; uint8_t v___x_577_; 
v___x_576_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3);
v___x_577_ = lean_uint8_dec_le(v___x_576_, v_x_520_);
if (v___x_577_ == 0)
{
v___y_571_ = v___x_577_;
goto v___jp_570_;
}
else
{
uint8_t v___x_578_; uint8_t v___x_579_; 
v___x_578_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4);
v___x_579_ = lean_uint8_dec_le(v_x_520_, v___x_578_);
v___y_571_ = v___x_579_;
goto v___jp_570_;
}
v___jp_521_:
{
if (v___y_522_ == 0)
{
uint8_t v___x_523_; 
v___x_523_ = lean_uint8_dec_eq(v_x_520_, v___x_518_);
if (v___x_523_ == 0)
{
uint8_t v___x_524_; uint8_t v___x_525_; 
v___x_524_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_525_ = lean_uint8_dec_eq(v_x_520_, v___x_524_);
if (v___x_525_ == 0)
{
return v___x_523_;
}
else
{
return v___x_519_;
}
}
else
{
return v___x_523_;
}
}
else
{
return v___y_522_;
}
}
v___jp_526_:
{
if (v___y_527_ == 0)
{
uint8_t v___x_528_; uint8_t v___x_529_; 
v___x_528_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_529_ = lean_uint8_dec_eq(v_x_520_, v___x_528_);
if (v___x_529_ == 0)
{
uint8_t v___x_530_; uint8_t v___x_531_; 
v___x_530_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_531_ = lean_uint8_dec_eq(v_x_520_, v___x_530_);
if (v___x_531_ == 0)
{
uint8_t v___x_532_; uint8_t v___x_533_; 
v___x_532_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_533_ = lean_uint8_dec_eq(v_x_520_, v___x_532_);
if (v___x_533_ == 0)
{
uint8_t v___x_534_; uint8_t v___x_535_; 
v___x_534_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_535_ = lean_uint8_dec_eq(v_x_520_, v___x_534_);
if (v___x_535_ == 0)
{
uint8_t v___x_536_; uint8_t v___x_537_; 
v___x_536_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_537_ = lean_uint8_dec_eq(v_x_520_, v___x_536_);
if (v___x_537_ == 0)
{
uint8_t v___x_538_; uint8_t v___x_539_; 
v___x_538_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0);
v___x_539_ = lean_uint8_dec_eq(v_x_520_, v___x_538_);
if (v___x_539_ == 0)
{
uint8_t v___x_540_; uint8_t v___x_541_; 
v___x_540_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_541_ = lean_uint8_dec_eq(v_x_520_, v___x_540_);
if (v___x_541_ == 0)
{
uint8_t v___x_542_; uint8_t v___x_543_; 
v___x_542_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_543_ = lean_uint8_dec_eq(v_x_520_, v___x_542_);
if (v___x_543_ == 0)
{
uint8_t v___x_544_; uint8_t v___x_545_; 
v___x_544_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_545_ = lean_uint8_dec_eq(v_x_520_, v___x_544_);
v___y_522_ = v___x_545_;
goto v___jp_521_;
}
else
{
v___y_522_ = v___x_543_;
goto v___jp_521_;
}
}
else
{
v___y_522_ = v___x_541_;
goto v___jp_521_;
}
}
else
{
v___y_522_ = v___x_539_;
goto v___jp_521_;
}
}
else
{
v___y_522_ = v___x_537_;
goto v___jp_521_;
}
}
else
{
v___y_522_ = v___x_535_;
goto v___jp_521_;
}
}
else
{
v___y_522_ = v___x_533_;
goto v___jp_521_;
}
}
else
{
v___y_522_ = v___x_531_;
goto v___jp_521_;
}
}
else
{
v___y_522_ = v___x_529_;
goto v___jp_521_;
}
}
else
{
return v___y_527_;
}
}
v___jp_546_:
{
if (v___y_547_ == 0)
{
uint8_t v___x_548_; uint8_t v___x_549_; 
v___x_548_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_549_ = lean_uint8_dec_eq(v_x_520_, v___x_548_);
if (v___x_549_ == 0)
{
uint8_t v___x_550_; uint8_t v___x_551_; 
v___x_550_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_551_ = lean_uint8_dec_eq(v_x_520_, v___x_550_);
v___y_527_ = v___x_551_;
goto v___jp_526_;
}
else
{
v___y_527_ = v___x_549_;
goto v___jp_526_;
}
}
else
{
return v___y_547_;
}
}
v___jp_552_:
{
if (v___y_553_ == 0)
{
uint8_t v___x_554_; uint8_t v___x_555_; 
v___x_554_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_555_ = lean_uint8_dec_eq(v_x_520_, v___x_554_);
if (v___x_555_ == 0)
{
uint8_t v___x_556_; uint8_t v___x_557_; 
v___x_556_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_557_ = lean_uint8_dec_eq(v_x_520_, v___x_556_);
v___y_547_ = v___x_557_;
goto v___jp_546_;
}
else
{
v___y_547_ = v___x_555_;
goto v___jp_546_;
}
}
else
{
return v___y_553_;
}
}
v___jp_558_:
{
if (v___y_559_ == 0)
{
uint8_t v___x_560_; uint8_t v___x_561_; 
v___x_560_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1);
v___x_561_ = lean_uint8_dec_eq(v_x_520_, v___x_560_);
if (v___x_561_ == 0)
{
uint8_t v___x_562_; uint8_t v___x_563_; 
v___x_562_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2);
v___x_563_ = lean_uint8_dec_eq(v_x_520_, v___x_562_);
v___y_553_ = v___x_563_;
goto v___jp_552_;
}
else
{
v___y_553_ = v___x_561_;
goto v___jp_552_;
}
}
else
{
return v___y_559_;
}
}
v___jp_564_:
{
if (v___y_565_ == 0)
{
uint8_t v___x_566_; uint8_t v___x_567_; 
v___x_566_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_567_ = lean_uint8_dec_le(v___x_566_, v_x_520_);
if (v___x_567_ == 0)
{
v___y_559_ = v___x_567_;
goto v___jp_558_;
}
else
{
uint8_t v___x_568_; uint8_t v___x_569_; 
v___x_568_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_569_ = lean_uint8_dec_le(v_x_520_, v___x_568_);
v___y_559_ = v___x_569_;
goto v___jp_558_;
}
}
else
{
return v___y_565_;
}
}
v___jp_570_:
{
if (v___y_571_ == 0)
{
uint8_t v___x_572_; uint8_t v___x_573_; 
v___x_572_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_573_ = lean_uint8_dec_le(v___x_572_, v_x_520_);
if (v___x_573_ == 0)
{
v___y_565_ = v___x_573_;
goto v___jp_564_;
}
else
{
uint8_t v___x_574_; uint8_t v___x_575_; 
v___x_574_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_575_ = lean_uint8_dec_le(v_x_520_, v___x_574_);
v___y_565_ = v___x_575_;
goto v___jp_564_;
}
}
else
{
return v___y_571_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1___boxed(lean_object* v___x_580_, lean_object* v___x_581_, lean_object* v_x_582_){
_start:
{
uint8_t v___x_4635__boxed_583_; uint8_t v___x_4636__boxed_584_; uint8_t v_x_boxed_585_; uint8_t v_res_586_; lean_object* v_r_587_; 
v___x_4635__boxed_583_ = lean_unbox(v___x_580_);
v___x_4636__boxed_584_ = lean_unbox(v___x_581_);
v_x_boxed_585_ = lean_unbox(v_x_582_);
v_res_586_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1(v___x_4635__boxed_583_, v___x_4636__boxed_584_, v_x_boxed_585_);
v_r_587_ = lean_box(v_res_586_);
return v_r_587_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(lean_object* v_config_592_, lean_object* v_a_593_){
_start:
{
lean_object* v___y_595_; lean_object* v_userPassEncoded_596_; lean_object* v___y_597_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v_lower_604_; lean_object* v_upper_605_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_620_; lean_object* v_pos_621_; lean_object* v_maxUserInfoLength_623_; lean_object* v___f_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v_fst_627_; lean_object* v_snd_628_; lean_object* v_array_629_; lean_object* v_idx_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_681_; 
v_maxUserInfoLength_623_ = lean_ctor_get(v_config_592_, 2);
v___f_624_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__2));
v___x_625_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_593_);
v___x_626_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo_findEnd(v___f_624_, v_maxUserInfoLength_623_, v___x_625_, v_a_593_);
v_fst_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_fst_627_);
v_snd_628_ = lean_ctor_get(v___x_626_, 1);
lean_inc(v_snd_628_);
lean_dec_ref(v___x_626_);
v_array_629_ = lean_ctor_get(v_a_593_, 0);
v_idx_630_ = lean_ctor_get(v_a_593_, 1);
v_isSharedCheck_681_ = !lean_is_exclusive(v_a_593_);
if (v_isSharedCheck_681_ == 0)
{
v___x_632_ = v_a_593_;
v_isShared_633_ = v_isSharedCheck_681_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_idx_630_);
lean_inc(v_array_629_);
lean_dec(v_a_593_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_681_;
goto v_resetjp_631_;
}
v___jp_594_:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v___y_595_);
lean_ctor_set(v___x_598_, 1, v_userPassEncoded_596_);
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v___y_597_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
return v___x_599_;
}
v___jp_600_:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_606_ = l_ByteArray_toByteSlice(v___y_601_, v_lower_604_, v_upper_605_);
v___x_607_ = l_ByteSlice_toByteArray(v___x_606_);
v___x_608_ = l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(v___x_607_);
if (lean_obj_tag(v___x_608_) == 1)
{
v___y_595_ = v___y_603_;
v_userPassEncoded_596_ = v___x_608_;
v___y_597_ = v___y_602_;
goto v___jp_594_;
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; 
lean_dec(v___x_608_);
lean_dec_ref(v___y_603_);
v___x_609_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1));
v___x_610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_610_, 0, v___y_602_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
return v___x_610_;
}
}
v___jp_611_:
{
uint8_t v___x_618_; 
v___x_618_ = lean_nat_dec_le(v___y_615_, v___y_613_);
if (v___x_618_ == 0)
{
lean_dec(v___y_615_);
v___y_601_ = v___y_612_;
v___y_602_ = v___y_614_;
v___y_603_ = v___y_616_;
v_lower_604_ = v___y_617_;
v_upper_605_ = v___y_613_;
goto v___jp_600_;
}
else
{
lean_dec(v___y_613_);
v___y_601_ = v___y_612_;
v___y_602_ = v___y_614_;
v___y_603_ = v___y_616_;
v_lower_604_ = v___y_617_;
v_upper_605_ = v___y_615_;
goto v___jp_600_;
}
}
v___jp_619_:
{
lean_object* v___x_622_; 
v___x_622_ = lean_box(0);
v___y_595_ = v___y_620_;
v_userPassEncoded_596_ = v___x_622_;
v___y_597_ = v_pos_621_;
goto v___jp_594_;
}
v_resetjp_631_:
{
lean_object* v_lower_635_; lean_object* v_upper_636_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___y_678_; uint8_t v___x_680_; 
v___x_675_ = lean_nat_add(v_idx_630_, v_fst_627_);
lean_dec(v_fst_627_);
v___x_676_ = lean_byte_array_size(v_array_629_);
v___x_680_ = lean_nat_dec_le(v_idx_630_, v___x_625_);
if (v___x_680_ == 0)
{
v___y_678_ = v_idx_630_;
goto v___jp_677_;
}
else
{
lean_dec(v_idx_630_);
v___y_678_ = v___x_625_;
goto v___jp_677_;
}
v___jp_634_:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = l_ByteArray_toByteSlice(v_array_629_, v_lower_635_, v_upper_636_);
v___x_638_ = l_ByteSlice_toByteArray(v___x_637_);
v___x_639_ = l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(v___x_638_);
if (lean_obj_tag(v___x_639_) == 1)
{
lean_object* v_val_640_; lean_object* v_array_641_; lean_object* v_idx_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v_val_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_val_640_);
lean_dec_ref(v___x_639_);
v_array_641_ = lean_ctor_get(v_snd_628_, 0);
v_idx_642_ = lean_ctor_get(v_snd_628_, 1);
v___x_643_ = lean_byte_array_size(v_array_641_);
v___x_644_ = lean_nat_dec_lt(v_idx_642_, v___x_643_);
if (v___x_644_ == 0)
{
lean_del_object(v___x_632_);
v___y_620_ = v_val_640_;
v_pos_621_ = v_snd_628_;
goto v___jp_619_;
}
else
{
uint8_t v___x_645_; uint8_t v___x_646_; uint8_t v___x_647_; 
v___x_645_ = lean_byte_array_fget(v_array_641_, v_idx_642_);
v___x_646_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_647_ = lean_uint8_dec_eq(v___x_645_, v___x_646_);
if (v___x_647_ == 0)
{
lean_del_object(v___x_632_);
v___y_620_ = v_val_640_;
v_pos_621_ = v_snd_628_;
goto v___jp_619_;
}
else
{
if (v___x_647_ == 0)
{
lean_del_object(v___x_632_);
v___y_620_ = v_val_640_;
v_pos_621_ = v_snd_628_;
goto v___jp_619_;
}
else
{
if (v___x_644_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_650_; 
lean_dec(v_val_640_);
v___x_648_ = lean_box(0);
if (v_isShared_633_ == 0)
{
lean_ctor_set_tag(v___x_632_, 1);
lean_ctor_set(v___x_632_, 1, v___x_648_);
lean_ctor_set(v___x_632_, 0, v_snd_628_);
v___x_650_ = v___x_632_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_snd_628_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v___x_648_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
else
{
lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_668_; 
lean_inc(v_idx_642_);
lean_inc_ref(v_array_641_);
lean_del_object(v___x_632_);
v_isSharedCheck_668_ = !lean_is_exclusive(v_snd_628_);
if (v_isSharedCheck_668_ == 0)
{
lean_object* v_unused_669_; lean_object* v_unused_670_; 
v_unused_669_ = lean_ctor_get(v_snd_628_, 1);
lean_dec(v_unused_669_);
v_unused_670_ = lean_ctor_get(v_snd_628_, 0);
lean_dec(v_unused_670_);
v___x_653_ = v_snd_628_;
v_isShared_654_ = v_isSharedCheck_668_;
goto v_resetjp_652_;
}
else
{
lean_dec(v_snd_628_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_668_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___f_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_655_ = lean_box(v___x_646_);
v___x_656_ = lean_box(v___x_644_);
v___f_657_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1___boxed), 3, 2);
lean_closure_set(v___f_657_, 0, v___x_655_);
lean_closure_set(v___f_657_, 1, v___x_656_);
v___x_658_ = lean_unsigned_to_nat(1u);
v___x_659_ = lean_nat_add(v_idx_642_, v___x_658_);
lean_dec(v_idx_642_);
lean_inc(v___x_659_);
lean_inc_ref(v_array_641_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 1, v___x_659_);
v___x_661_ = v___x_653_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_array_641_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v___x_659_);
v___x_661_ = v_reuseFailAlloc_667_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_662_; lean_object* v_fst_663_; lean_object* v_snd_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_662_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo_findEnd(v___f_657_, v_maxUserInfoLength_623_, v___x_625_, v___x_661_);
v_fst_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_fst_663_);
v_snd_664_ = lean_ctor_get(v___x_662_, 1);
lean_inc(v_snd_664_);
lean_dec_ref(v___x_662_);
v___x_665_ = lean_nat_add(v___x_659_, v_fst_663_);
lean_dec(v_fst_663_);
v___x_666_ = lean_nat_dec_le(v___x_659_, v___x_625_);
if (v___x_666_ == 0)
{
v___y_612_ = v_array_641_;
v___y_613_ = v___x_643_;
v___y_614_ = v_snd_664_;
v___y_615_ = v___x_665_;
v___y_616_ = v_val_640_;
v___y_617_ = v___x_659_;
goto v___jp_611_;
}
else
{
lean_dec(v___x_659_);
v___y_612_ = v_array_641_;
v___y_613_ = v___x_643_;
v___y_614_ = v_snd_664_;
v___y_615_ = v___x_665_;
v___y_616_ = v_val_640_;
v___y_617_ = v___x_625_;
goto v___jp_611_;
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
lean_object* v___x_671_; lean_object* v___x_673_; 
lean_dec(v___x_639_);
v___x_671_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1));
if (v_isShared_633_ == 0)
{
lean_ctor_set_tag(v___x_632_, 1);
lean_ctor_set(v___x_632_, 1, v___x_671_);
lean_ctor_set(v___x_632_, 0, v_snd_628_);
v___x_673_ = v___x_632_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_snd_628_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v___x_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
v___jp_677_:
{
uint8_t v___x_679_; 
v___x_679_ = lean_nat_dec_le(v___x_675_, v___x_676_);
if (v___x_679_ == 0)
{
lean_dec(v___x_675_);
v_lower_635_ = v___y_678_;
v_upper_636_ = v___x_676_;
goto v___jp_634_;
}
else
{
v_lower_635_ = v___y_678_;
v_upper_636_ = v___x_675_;
goto v___jp_634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___boxed(lean_object* v_config_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(v_config_682_, v_a_683_);
lean_dec_ref(v_config_682_);
return v_res_684_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0(void){
_start:
{
uint32_t v___x_685_; uint8_t v___x_686_; 
v___x_685_ = 70;
v___x_686_ = lean_uint32_to_uint8(v___x_685_);
return v___x_686_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1(void){
_start:
{
uint32_t v___x_687_; uint8_t v___x_688_; 
v___x_687_ = 102;
v___x_688_ = lean_uint32_to_uint8(v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(uint8_t v___x_689_, uint8_t v_x_690_){
_start:
{
uint8_t v___y_692_; uint8_t v___y_698_; uint8_t v___x_703_; uint8_t v___x_704_; 
v___x_703_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_704_ = lean_uint8_dec_eq(v_x_690_, v___x_703_);
if (v___x_704_ == 0)
{
uint8_t v___x_705_; uint8_t v___x_706_; 
v___x_705_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2);
v___x_706_ = lean_uint8_dec_eq(v_x_690_, v___x_705_);
if (v___x_706_ == 0)
{
uint8_t v___x_707_; uint8_t v___x_708_; 
v___x_707_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3);
v___x_708_ = lean_uint8_dec_le(v___x_707_, v_x_690_);
if (v___x_708_ == 0)
{
v___y_698_ = v___x_708_;
goto v___jp_697_;
}
else
{
uint8_t v___x_709_; uint8_t v___x_710_; 
v___x_709_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4);
v___x_710_ = lean_uint8_dec_le(v_x_690_, v___x_709_);
v___y_698_ = v___x_710_;
goto v___jp_697_;
}
}
else
{
return v___x_689_;
}
}
else
{
return v___x_689_;
}
v___jp_691_:
{
if (v___y_692_ == 0)
{
uint8_t v___x_693_; uint8_t v___x_694_; 
v___x_693_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_694_ = lean_uint8_dec_le(v___x_693_, v_x_690_);
if (v___x_694_ == 0)
{
if (v___x_694_ == 0)
{
return v___x_694_;
}
else
{
return v___x_689_;
}
}
else
{
uint8_t v___x_695_; uint8_t v___x_696_; 
v___x_695_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0);
v___x_696_ = lean_uint8_dec_le(v_x_690_, v___x_695_);
if (v___x_696_ == 0)
{
return v___x_696_;
}
else
{
return v___x_689_;
}
}
}
else
{
return v___x_689_;
}
}
v___jp_697_:
{
if (v___y_698_ == 0)
{
uint8_t v___x_699_; uint8_t v___x_700_; 
v___x_699_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_700_ = lean_uint8_dec_le(v___x_699_, v_x_690_);
if (v___x_700_ == 0)
{
v___y_692_ = v___x_700_;
goto v___jp_691_;
}
else
{
uint8_t v___x_701_; uint8_t v___x_702_; 
v___x_701_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1);
v___x_702_ = lean_uint8_dec_le(v_x_690_, v___x_701_);
v___y_692_ = v___x_702_;
goto v___jp_691_;
}
}
else
{
return v___x_689_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___boxed(lean_object* v___x_711_, lean_object* v_x_712_){
_start:
{
uint8_t v___x_1506__boxed_713_; uint8_t v_x_boxed_714_; uint8_t v_res_715_; lean_object* v_r_716_; 
v___x_1506__boxed_713_ = lean_unbox(v___x_711_);
v_x_boxed_714_ = lean_unbox(v_x_712_);
v_res_715_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(v___x_1506__boxed_713_, v_x_boxed_714_);
v_r_716_ = lean_box(v_res_715_);
return v_r_716_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1(void){
_start:
{
uint32_t v___x_718_; uint8_t v___x_719_; 
v___x_718_ = 91;
v___x_719_ = lean_uint32_to_uint8(v___x_718_);
return v___x_719_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3(void){
_start:
{
uint8_t v___x_721_; lean_object* v___x_722_; 
v___x_721_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1);
v___x_722_ = lean_uint8_to_nat(v___x_721_);
return v___x_722_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3);
v___x_724_ = l_Nat_reprFast(v___x_723_);
return v___x_724_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_725_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4);
v___x_726_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_727_ = lean_string_append(v___x_726_, v___x_725_);
return v___x_727_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_729_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_730_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5);
v___x_731_ = lean_string_append(v___x_730_, v___x_729_);
return v___x_731_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7);
v___x_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
return v___x_733_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9(void){
_start:
{
uint32_t v___x_734_; uint8_t v___x_735_; 
v___x_734_ = 93;
v___x_735_ = lean_uint32_to_uint8(v___x_734_);
return v___x_735_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10(void){
_start:
{
uint8_t v___x_736_; lean_object* v___x_737_; 
v___x_736_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9);
v___x_737_ = lean_uint8_to_nat(v___x_736_);
return v___x_737_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10);
v___x_739_ = l_Nat_reprFast(v___x_738_);
return v___x_739_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_740_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11);
v___x_741_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_742_ = lean_string_append(v___x_741_, v___x_740_);
return v___x_742_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_743_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_744_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12);
v___x_745_ = lean_string_append(v___x_744_, v___x_743_);
return v___x_745_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13);
v___x_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(lean_object* v_a_748_){
_start:
{
lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v_array_759_; lean_object* v_idx_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v_array_759_ = lean_ctor_get(v_a_748_, 0);
v_idx_760_ = lean_ctor_get(v_a_748_, 1);
v___x_761_ = lean_byte_array_size(v_array_759_);
v___x_762_ = lean_nat_dec_lt(v_idx_760_, v___x_761_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = lean_box(0);
v___x_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_764_, 0, v_a_748_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
return v___x_764_;
}
else
{
uint8_t v___x_765_; uint8_t v_c_766_; uint8_t v___x_767_; 
v___x_765_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1);
v_c_766_ = lean_byte_array_fget(v_array_759_, v_idx_760_);
v___x_767_ = lean_uint8_dec_eq(v_c_766_, v___x_765_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8);
v___x_769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_769_, 0, v_a_748_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
return v___x_769_;
}
else
{
lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_840_; 
lean_inc(v_idx_760_);
lean_inc_ref(v_array_759_);
v_isSharedCheck_840_ = !lean_is_exclusive(v_a_748_);
if (v_isSharedCheck_840_ == 0)
{
lean_object* v_unused_841_; lean_object* v_unused_842_; 
v_unused_841_ = lean_ctor_get(v_a_748_, 1);
lean_dec(v_unused_841_);
v_unused_842_ = lean_ctor_get(v_a_748_, 0);
lean_dec(v_unused_842_);
v___x_771_ = v_a_748_;
v_isShared_772_ = v_isSharedCheck_840_;
goto v_resetjp_770_;
}
else
{
lean_dec(v_a_748_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_840_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; lean_object* v___f_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v_it_x27_778_; 
v___x_773_ = lean_box(v___x_762_);
v___f_774_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___boxed), 2, 1);
lean_closure_set(v___f_774_, 0, v___x_773_);
v___x_775_ = lean_unsigned_to_nat(1u);
v___x_776_ = lean_nat_add(v_idx_760_, v___x_775_);
lean_dec(v_idx_760_);
lean_inc(v___x_776_);
lean_inc_ref(v_array_759_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 1, v___x_776_);
v_it_x27_778_ = v___x_771_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_array_759_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v___x_776_);
v_it_x27_778_ = v_reuseFailAlloc_839_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v_fst_782_; lean_object* v_snd_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_838_; 
v___x_779_ = lean_unsigned_to_nat(256u);
v___x_780_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_x27_778_);
v___x_781_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo1_findEnd(v___f_774_, v___x_779_, v___x_780_, v_it_x27_778_);
v_fst_782_ = lean_ctor_get(v___x_781_, 0);
v_snd_783_ = lean_ctor_get(v___x_781_, 1);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_838_ == 0)
{
v___x_785_ = v___x_781_;
v_isShared_786_ = v_isSharedCheck_838_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_snd_783_);
lean_inc(v_fst_782_);
lean_dec(v___x_781_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_838_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___y_788_; uint8_t v___x_822_; 
v___x_822_ = lean_nat_dec_eq(v_fst_782_, v___x_780_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; lean_object* v___y_825_; uint8_t v___x_829_; 
lean_dec_ref(v_it_x27_778_);
v___x_823_ = lean_nat_add(v___x_776_, v_fst_782_);
lean_dec(v_fst_782_);
v___x_829_ = lean_nat_dec_le(v___x_776_, v___x_780_);
if (v___x_829_ == 0)
{
v___y_825_ = v___x_776_;
goto v___jp_824_;
}
else
{
lean_dec(v___x_776_);
v___y_825_ = v___x_780_;
goto v___jp_824_;
}
v___jp_824_:
{
uint8_t v___x_826_; 
v___x_826_ = lean_nat_dec_le(v___x_823_, v___x_761_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; 
lean_dec(v___x_823_);
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v___y_825_);
lean_ctor_set(v___x_827_, 1, v___x_761_);
v___y_788_ = v___x_827_;
goto v___jp_787_;
}
else
{
lean_object* v___x_828_; 
v___x_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_828_, 0, v___y_825_);
lean_ctor_set(v___x_828_, 1, v___x_823_);
v___y_788_ = v___x_828_;
goto v___jp_787_;
}
}
}
else
{
lean_object* v_array_830_; lean_object* v_idx_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
lean_del_object(v___x_785_);
lean_dec(v_fst_782_);
lean_dec(v___x_776_);
lean_dec_ref(v_array_759_);
v_array_830_ = lean_ctor_get(v_snd_783_, 0);
lean_inc_ref(v_array_830_);
v_idx_831_ = lean_ctor_get(v_snd_783_, 1);
lean_inc(v_idx_831_);
lean_dec(v_snd_783_);
v___x_832_ = lean_byte_array_size(v_array_830_);
lean_dec_ref(v_array_830_);
v___x_833_ = lean_nat_dec_le(v___x_832_, v_idx_831_);
lean_dec(v_idx_831_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10));
v___x_835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_835_, 0, v_it_x27_778_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
return v___x_835_;
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = lean_box(0);
v___x_837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_837_, 0, v_it_x27_778_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
return v___x_837_;
}
}
v___jp_787_:
{
lean_object* v_array_789_; lean_object* v_idx_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
v_array_789_ = lean_ctor_get(v_snd_783_, 0);
v_idx_790_ = lean_ctor_get(v_snd_783_, 1);
v___x_791_ = lean_byte_array_size(v_array_789_);
v___x_792_ = lean_nat_dec_lt(v_idx_790_, v___x_791_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; lean_object* v___x_795_; 
lean_dec_ref(v___y_788_);
lean_dec_ref(v_array_759_);
v___x_793_ = lean_box(0);
if (v_isShared_786_ == 0)
{
lean_ctor_set_tag(v___x_785_, 1);
lean_ctor_set(v___x_785_, 1, v___x_793_);
lean_ctor_set(v___x_785_, 0, v_snd_783_);
v___x_795_ = v___x_785_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_snd_783_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
else
{
uint8_t v___x_797_; uint8_t v_c_798_; uint8_t v___x_799_; 
v___x_797_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9);
v_c_798_ = lean_byte_array_fget(v_array_789_, v_idx_790_);
v___x_799_ = lean_uint8_dec_eq(v_c_798_, v___x_797_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; lean_object* v___x_802_; 
lean_dec_ref(v___y_788_);
lean_dec_ref(v_array_759_);
v___x_800_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14);
if (v_isShared_786_ == 0)
{
lean_ctor_set_tag(v___x_785_, 1);
lean_ctor_set(v___x_785_, 1, v___x_800_);
lean_ctor_set(v___x_785_, 0, v_snd_783_);
v___x_802_ = v___x_785_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_snd_783_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v___x_800_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
else
{
lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_819_; 
lean_inc(v_idx_790_);
lean_inc_ref(v_array_789_);
lean_del_object(v___x_785_);
v_isSharedCheck_819_ = !lean_is_exclusive(v_snd_783_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; lean_object* v_unused_821_; 
v_unused_820_ = lean_ctor_get(v_snd_783_, 1);
lean_dec(v_unused_820_);
v_unused_821_ = lean_ctor_get(v_snd_783_, 0);
lean_dec(v_unused_821_);
v___x_805_ = v_snd_783_;
v_isShared_806_ = v_isSharedCheck_819_;
goto v_resetjp_804_;
}
else
{
lean_dec(v_snd_783_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_819_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v_lower_807_; lean_object* v_upper_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v_it_x27_812_; 
v_lower_807_ = lean_ctor_get(v___y_788_, 0);
lean_inc(v_lower_807_);
v_upper_808_ = lean_ctor_get(v___y_788_, 1);
lean_inc(v_upper_808_);
lean_dec_ref(v___y_788_);
v___x_809_ = l_ByteArray_toByteSlice(v_array_759_, v_lower_807_, v_upper_808_);
v___x_810_ = lean_nat_add(v_idx_790_, v___x_775_);
lean_dec(v_idx_790_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 1, v___x_810_);
v_it_x27_812_ = v___x_805_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_array_789_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v___x_810_);
v_it_x27_812_ = v_reuseFailAlloc_818_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_813_ = l_ByteSlice_toByteArray(v___x_809_);
v___x_814_ = lean_string_validate_utf8(v___x_813_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; lean_object* v___x_816_; 
lean_dec_ref(v___x_813_);
v___x_815_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_816_ = l_panic___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(v___x_815_);
v___y_750_ = v_it_x27_812_;
v___y_751_ = v___x_816_;
goto v___jp_749_;
}
else
{
lean_object* v___x_817_; 
v___x_817_ = lean_string_from_utf8_unchecked(v___x_813_);
v___y_750_ = v_it_x27_812_;
v___y_751_ = v___x_817_;
goto v___jp_749_;
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
v___jp_749_:
{
lean_object* v___x_752_; 
v___x_752_ = lean_uv_pton_v6(v___y_751_);
if (lean_obj_tag(v___x_752_) == 1)
{
lean_object* v_val_753_; lean_object* v___x_754_; 
lean_dec_ref(v___y_751_);
v_val_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_val_753_);
lean_dec_ref(v___x_752_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v___y_750_);
lean_ctor_set(v___x_754_, 1, v_val_753_);
return v___x_754_;
}
else
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
lean_dec(v___x_752_);
v___x_755_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__0));
v___x_756_ = lean_string_append(v___x_755_, v___y_751_);
lean_dec_ref(v___y_751_);
v___x_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
v___x_758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_758_, 0, v___y_750_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
return v___x_758_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0(uint8_t v_x_843_){
_start:
{
uint8_t v___x_844_; uint8_t v___x_845_; 
v___x_844_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2);
v___x_845_ = lean_uint8_dec_eq(v_x_843_, v___x_844_);
if (v___x_845_ == 0)
{
uint8_t v___x_846_; uint8_t v___x_847_; 
v___x_846_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3);
v___x_847_ = lean_uint8_dec_le(v___x_846_, v_x_843_);
if (v___x_847_ == 0)
{
return v___x_847_;
}
else
{
uint8_t v___x_848_; uint8_t v___x_849_; 
v___x_848_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4);
v___x_849_ = lean_uint8_dec_le(v_x_843_, v___x_848_);
return v___x_849_;
}
}
else
{
return v___x_845_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0___boxed(lean_object* v_x_850_){
_start:
{
uint8_t v_x_boxed_851_; uint8_t v_res_852_; lean_object* v_r_853_; 
v_x_boxed_851_ = lean_unbox(v_x_850_);
v_res_852_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0(v_x_boxed_851_);
v_r_853_ = lean_box(v_res_852_);
return v_r_853_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(lean_object* v_a_856_){
_start:
{
lean_object* v___f_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v_fst_861_; lean_object* v_snd_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_913_; 
v___f_857_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__0));
v___x_858_ = lean_unsigned_to_nat(256u);
v___x_859_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_856_);
v___x_860_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo1_findEnd(v___f_857_, v___x_858_, v___x_859_, v_a_856_);
v_fst_861_ = lean_ctor_get(v___x_860_, 0);
v_snd_862_ = lean_ctor_get(v___x_860_, 1);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_913_ == 0)
{
v___x_864_ = v___x_860_;
v_isShared_865_ = v_isSharedCheck_913_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_snd_862_);
lean_inc(v_fst_861_);
lean_dec(v___x_860_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_913_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___y_867_; uint8_t v___x_879_; 
v___x_879_ = lean_nat_dec_eq(v_fst_861_, v___x_859_);
if (v___x_879_ == 0)
{
lean_object* v_array_880_; lean_object* v_idx_881_; lean_object* v_lower_883_; lean_object* v_upper_884_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___y_894_; uint8_t v___x_896_; 
v_array_880_ = lean_ctor_get(v_a_856_, 0);
lean_inc_ref(v_array_880_);
v_idx_881_ = lean_ctor_get(v_a_856_, 1);
lean_inc(v_idx_881_);
lean_dec_ref(v_a_856_);
v___x_891_ = lean_nat_add(v_idx_881_, v_fst_861_);
lean_dec(v_fst_861_);
v___x_892_ = lean_byte_array_size(v_array_880_);
v___x_896_ = lean_nat_dec_le(v_idx_881_, v___x_859_);
if (v___x_896_ == 0)
{
v___y_894_ = v_idx_881_;
goto v___jp_893_;
}
else
{
lean_dec(v_idx_881_);
v___y_894_ = v___x_859_;
goto v___jp_893_;
}
v___jp_882_:
{
lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_885_ = l_ByteArray_toByteSlice(v_array_880_, v_lower_883_, v_upper_884_);
v___x_886_ = l_ByteSlice_toByteArray(v___x_885_);
v___x_887_ = lean_string_validate_utf8(v___x_886_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; lean_object* v___x_889_; 
lean_dec_ref(v___x_886_);
v___x_888_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_889_ = l_panic___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(v___x_888_);
v___y_867_ = v___x_889_;
goto v___jp_866_;
}
else
{
lean_object* v___x_890_; 
v___x_890_ = lean_string_from_utf8_unchecked(v___x_886_);
v___y_867_ = v___x_890_;
goto v___jp_866_;
}
}
v___jp_893_:
{
uint8_t v___x_895_; 
v___x_895_ = lean_nat_dec_le(v___x_891_, v___x_892_);
if (v___x_895_ == 0)
{
lean_dec(v___x_891_);
v_lower_883_ = v___y_894_;
v_upper_884_ = v___x_892_;
goto v___jp_882_;
}
else
{
v_lower_883_ = v___y_894_;
v_upper_884_ = v___x_891_;
goto v___jp_882_;
}
}
}
else
{
lean_object* v_array_897_; lean_object* v_idx_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_912_; 
lean_del_object(v___x_864_);
lean_dec(v_fst_861_);
v_array_897_ = lean_ctor_get(v_snd_862_, 0);
v_idx_898_ = lean_ctor_get(v_snd_862_, 1);
v_isSharedCheck_912_ = !lean_is_exclusive(v_snd_862_);
if (v_isSharedCheck_912_ == 0)
{
v___x_900_ = v_snd_862_;
v_isShared_901_ = v_isSharedCheck_912_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_idx_898_);
lean_inc(v_array_897_);
lean_dec(v_snd_862_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_912_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_902_ = lean_byte_array_size(v_array_897_);
lean_dec_ref(v_array_897_);
v___x_903_ = lean_nat_dec_le(v___x_902_, v_idx_898_);
lean_dec(v_idx_898_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_904_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10));
if (v_isShared_901_ == 0)
{
lean_ctor_set_tag(v___x_900_, 1);
lean_ctor_set(v___x_900_, 1, v___x_904_);
lean_ctor_set(v___x_900_, 0, v_a_856_);
v___x_906_ = v___x_900_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_856_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v___x_904_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
else
{
lean_object* v___x_908_; lean_object* v___x_910_; 
v___x_908_ = lean_box(0);
if (v_isShared_901_ == 0)
{
lean_ctor_set_tag(v___x_900_, 1);
lean_ctor_set(v___x_900_, 1, v___x_908_);
lean_ctor_set(v___x_900_, 0, v_a_856_);
v___x_910_ = v___x_900_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_856_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v___x_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
v___jp_866_:
{
lean_object* v___x_868_; 
v___x_868_ = lean_uv_pton_v4(v___y_867_);
if (lean_obj_tag(v___x_868_) == 1)
{
lean_object* v_val_869_; lean_object* v___x_871_; 
lean_dec_ref(v___y_867_);
v_val_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_val_869_);
lean_dec_ref(v___x_868_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 1, v_val_869_);
lean_ctor_set(v___x_864_, 0, v_snd_862_);
v___x_871_ = v___x_864_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_snd_862_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_val_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
else
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
lean_dec(v___x_868_);
v___x_873_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__1));
v___x_874_ = lean_string_append(v___x_873_, v___y_867_);
lean_dec_ref(v___y_867_);
v___x_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
if (v_isShared_865_ == 0)
{
lean_ctor_set_tag(v___x_864_, 1);
lean_ctor_set(v___x_864_, 1, v___x_875_);
lean_ctor_set(v___x_864_, 0, v_snd_862_);
v___x_877_ = v___x_864_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_snd_862_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(lean_object* v_s_916_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0));
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___boxed(lean_object* v_s_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(v_s_918_);
lean_dec_ref(v_s_918_);
return v_res_919_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(uint8_t v_x_920_){
_start:
{
uint8_t v___y_922_; uint8_t v___y_928_; uint8_t v___y_934_; uint8_t v___x_939_; uint8_t v___x_940_; 
v___x_939_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3);
v___x_940_ = lean_uint8_dec_le(v___x_939_, v_x_920_);
if (v___x_940_ == 0)
{
v___y_934_ = v___x_940_;
goto v___jp_933_;
}
else
{
uint8_t v___x_941_; uint8_t v___x_942_; 
v___x_941_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4);
v___x_942_ = lean_uint8_dec_le(v_x_920_, v___x_941_);
v___y_934_ = v___x_942_;
goto v___jp_933_;
}
v___jp_921_:
{
if (v___y_922_ == 0)
{
uint8_t v___x_923_; uint8_t v___x_924_; 
v___x_923_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1);
v___x_924_ = lean_uint8_dec_eq(v_x_920_, v___x_923_);
if (v___x_924_ == 0)
{
uint8_t v___x_925_; uint8_t v___x_926_; 
v___x_925_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2);
v___x_926_ = lean_uint8_dec_eq(v_x_920_, v___x_925_);
if (v___x_926_ == 0)
{
return v___y_922_;
}
else
{
return v___x_926_;
}
}
else
{
return v___x_924_;
}
}
else
{
return v___y_922_;
}
}
v___jp_927_:
{
if (v___y_928_ == 0)
{
uint8_t v___x_929_; uint8_t v___x_930_; 
v___x_929_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_930_ = lean_uint8_dec_le(v___x_929_, v_x_920_);
if (v___x_930_ == 0)
{
v___y_922_ = v___x_930_;
goto v___jp_921_;
}
else
{
uint8_t v___x_931_; uint8_t v___x_932_; 
v___x_931_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_932_ = lean_uint8_dec_le(v_x_920_, v___x_931_);
v___y_922_ = v___x_932_;
goto v___jp_921_;
}
}
else
{
return v___y_928_;
}
}
v___jp_933_:
{
if (v___y_934_ == 0)
{
uint8_t v___x_935_; uint8_t v___x_936_; 
v___x_935_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_936_ = lean_uint8_dec_le(v___x_935_, v_x_920_);
if (v___x_936_ == 0)
{
v___y_928_ = v___x_936_;
goto v___jp_927_;
}
else
{
uint8_t v___x_937_; uint8_t v___x_938_; 
v___x_937_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_938_ = lean_uint8_dec_le(v_x_920_, v___x_937_);
v___y_928_ = v___x_938_;
goto v___jp_927_;
}
}
else
{
return v___y_934_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed(lean_object* v_x_943_){
_start:
{
uint8_t v_x_boxed_944_; uint8_t v_res_945_; lean_object* v_r_946_; 
v_x_boxed_944_ = lean_unbox(v_x_943_);
v_res_945_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(v_x_boxed_944_);
v_r_946_ = lean_box(v_res_945_);
return v_r_946_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(lean_object* v___x_947_, lean_object* v___x_948_, lean_object* v___x_949_, lean_object* v_a_950_, uint8_t v_b_951_){
_start:
{
if (lean_obj_tag(v_a_950_) == 0)
{
lean_object* v_currPos_952_; lean_object* v_searcher_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_987_; 
v_currPos_952_ = lean_ctor_get(v_a_950_, 0);
v_searcher_953_ = lean_ctor_get(v_a_950_, 1);
v_isSharedCheck_987_ = !lean_is_exclusive(v_a_950_);
if (v_isSharedCheck_987_ == 0)
{
v___x_955_ = v_a_950_;
v_isShared_956_ = v_isSharedCheck_987_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_searcher_953_);
lean_inc(v_currPos_952_);
lean_dec(v_a_950_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_987_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v_startInclusive_957_; lean_object* v_endExclusive_958_; uint8_t v___x_959_; lean_object* v_it_961_; lean_object* v_startInclusive_962_; lean_object* v_endExclusive_963_; lean_object* v___x_967_; uint8_t v___x_968_; 
v_startInclusive_957_ = lean_ctor_get(v___x_948_, 1);
v_endExclusive_958_ = lean_ctor_get(v___x_948_, 2);
v___x_959_ = 1;
v___x_967_ = lean_nat_sub(v_endExclusive_958_, v_startInclusive_957_);
v___x_968_ = lean_nat_dec_eq(v_searcher_953_, v___x_967_);
lean_dec(v___x_967_);
if (v___x_968_ == 0)
{
uint32_t v___x_969_; uint32_t v___x_970_; uint8_t v___x_971_; 
v___x_969_ = 46;
v___x_970_ = lean_string_utf8_get_fast(v___x_947_, v_searcher_953_);
v___x_971_ = lean_uint32_dec_eq(v___x_970_, v___x_969_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_972_ = lean_string_utf8_next_fast(v___x_947_, v_searcher_953_);
lean_dec(v_searcher_953_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v___x_972_);
v___x_974_ = v___x_955_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_currPos_952_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v___x_972_);
v___x_974_ = v_reuseFailAlloc_976_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
v_a_950_ = v___x_974_;
goto _start;
}
}
else
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v_slice_980_; lean_object* v_nextIt_982_; 
v___x_977_ = lean_string_utf8_next_fast(v___x_947_, v_searcher_953_);
v___x_978_ = lean_nat_sub(v___x_977_, v_searcher_953_);
v___x_979_ = lean_nat_add(v_searcher_953_, v___x_978_);
lean_dec(v___x_978_);
v_slice_980_ = l_String_Slice_subslice_x21(v___x_948_, v_currPos_952_, v_searcher_953_);
lean_inc(v___x_979_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v___x_979_);
lean_ctor_set(v___x_955_, 0, v___x_979_);
v_nextIt_982_ = v___x_955_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v___x_979_);
v_nextIt_982_ = v_reuseFailAlloc_985_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v_startInclusive_983_; lean_object* v_endExclusive_984_; 
v_startInclusive_983_ = lean_ctor_get(v_slice_980_, 0);
lean_inc(v_startInclusive_983_);
v_endExclusive_984_ = lean_ctor_get(v_slice_980_, 1);
lean_inc(v_endExclusive_984_);
lean_dec_ref(v_slice_980_);
v_it_961_ = v_nextIt_982_;
v_startInclusive_962_ = v_startInclusive_983_;
v_endExclusive_963_ = v_endExclusive_984_;
goto v___jp_960_;
}
}
}
else
{
lean_object* v___x_986_; 
lean_del_object(v___x_955_);
lean_dec(v_searcher_953_);
v___x_986_ = lean_box(1);
lean_inc(v___x_949_);
v_it_961_ = v___x_986_;
v_startInclusive_962_ = v_currPos_952_;
v_endExclusive_963_ = v___x_949_;
goto v___jp_960_;
}
v___jp_960_:
{
lean_object* v___x_964_; uint8_t v___x_965_; 
v___x_964_ = lean_string_utf8_extract(v___x_947_, v_startInclusive_962_, v_endExclusive_963_);
lean_dec(v_endExclusive_963_);
lean_dec(v_startInclusive_962_);
v___x_965_ = l_Std_Http_URI_isValidDomainLabel(v___x_964_);
if (v___x_965_ == 0)
{
lean_dec(v_it_961_);
lean_dec(v___x_949_);
return v___x_965_;
}
else
{
v_a_950_ = v_it_961_;
v_b_951_ = v___x_959_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_949_);
return v_b_951_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg___boxed(lean_object* v___x_988_, lean_object* v___x_989_, lean_object* v___x_990_, lean_object* v_a_991_, lean_object* v_b_992_){
_start:
{
uint8_t v_b_boxed_993_; uint8_t v_res_994_; lean_object* v_r_995_; 
v_b_boxed_993_ = lean_unbox(v_b_992_);
v_res_994_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_988_, v___x_989_, v___x_990_, v_a_991_, v_b_boxed_993_);
lean_dec_ref(v___x_989_);
lean_dec_ref(v___x_988_);
v_r_995_ = lean_box(v_res_994_);
return v_r_995_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(lean_object* v___x_996_, lean_object* v___x_997_, lean_object* v_a_998_, uint8_t v_b_999_){
_start:
{
if (lean_obj_tag(v_a_998_) == 0)
{
lean_object* v_currPos_1000_; lean_object* v_searcher_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1018_; 
v_currPos_1000_ = lean_ctor_get(v_a_998_, 0);
v_searcher_1001_ = lean_ctor_get(v_a_998_, 1);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_a_998_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1003_ = v_a_998_;
v_isShared_1004_ = v_isSharedCheck_1018_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_searcher_1001_);
lean_inc(v_currPos_1000_);
lean_dec(v_a_998_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1018_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v_startInclusive_1005_; lean_object* v_endExclusive_1006_; uint8_t v___x_1007_; lean_object* v___x_1008_; uint8_t v___x_1009_; 
v_startInclusive_1005_ = lean_ctor_get(v___x_997_, 1);
v_endExclusive_1006_ = lean_ctor_get(v___x_997_, 2);
v___x_1007_ = 0;
v___x_1008_ = lean_nat_sub(v_endExclusive_1006_, v_startInclusive_1005_);
v___x_1009_ = lean_nat_dec_eq(v_searcher_1001_, v___x_1008_);
lean_dec(v___x_1008_);
if (v___x_1009_ == 0)
{
uint32_t v___x_1010_; uint32_t v___x_1011_; uint8_t v___x_1012_; 
v___x_1010_ = 46;
v___x_1011_ = lean_string_utf8_get_fast(v___x_996_, v_searcher_1001_);
v___x_1012_ = lean_uint32_dec_eq(v___x_1011_, v___x_1010_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1013_ = lean_string_utf8_next_fast(v___x_996_, v_searcher_1001_);
lean_dec(v_searcher_1001_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 1, v___x_1013_);
v___x_1015_ = v___x_1003_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_currPos_1000_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
v_a_998_ = v___x_1015_;
goto _start;
}
}
else
{
lean_del_object(v___x_1003_);
lean_dec(v_searcher_1001_);
lean_dec(v_currPos_1000_);
return v___x_1007_;
}
}
else
{
lean_del_object(v___x_1003_);
lean_dec(v_searcher_1001_);
lean_dec(v_currPos_1000_);
return v___x_1007_;
}
}
}
else
{
return v_b_999_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg___boxed(lean_object* v___x_1019_, lean_object* v___x_1020_, lean_object* v_a_1021_, lean_object* v_b_1022_){
_start:
{
uint8_t v_b_boxed_1023_; uint8_t v_res_1024_; lean_object* v_r_1025_; 
v_b_boxed_1023_ = lean_unbox(v_b_1022_);
v_res_1024_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_1019_, v___x_1020_, v_a_1021_, v_b_boxed_1023_);
lean_dec_ref(v___x_1020_);
lean_dec_ref(v___x_1019_);
v_r_1025_ = lean_box(v_res_1024_);
return v_r_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(lean_object* v_config_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; uint8_t v___y_1044_; lean_object* v___y_1048_; lean_object* v___y_1049_; uint8_t v___y_1050_; uint8_t v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; uint8_t v___y_1054_; lean_object* v___y_1064_; uint8_t v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v_lower_1068_; lean_object* v_upper_1069_; lean_object* v___y_1082_; lean_object* v___y_1083_; uint8_t v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v_array_1090_; lean_object* v_idx_1091_; lean_object* v___f_1092_; lean_object* v___y_1094_; lean_object* v_pos_1123_; lean_object* v_pos_1147_; lean_object* v_res_1148_; lean_object* v___y_1150_; lean_object* v___y_1151_; uint8_t v___y_1152_; lean_object* v_pos_1154_; lean_object* v_res_1155_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v_array_1090_ = lean_ctor_get(v_a_1032_, 0);
v_idx_1091_ = lean_ctor_get(v_a_1032_, 1);
v___f_1092_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3));
v___x_1163_ = lean_byte_array_size(v_array_1090_);
v___x_1164_ = lean_nat_dec_lt(v_idx_1091_, v___x_1163_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; 
lean_inc(v_idx_1091_);
lean_inc_ref(v_array_1090_);
v___x_1165_ = lean_box(0);
v_pos_1154_ = v_a_1032_;
v_res_1155_ = v___x_1165_;
goto v___jp_1153_;
}
else
{
uint8_t v___x_1166_; uint8_t v___x_1167_; uint8_t v___x_1168_; 
v___x_1166_ = lean_byte_array_fget(v_array_1090_, v_idx_1091_);
v___x_1167_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1);
v___x_1168_ = lean_uint8_dec_eq(v___x_1166_, v___x_1167_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; 
lean_inc(v_idx_1091_);
lean_inc_ref(v_array_1090_);
v___x_1169_ = lean_box(0);
v_pos_1154_ = v_a_1032_;
v_res_1155_ = v___x_1169_;
goto v___jp_1153_;
}
else
{
lean_object* v___x_1170_; 
v___x_1170_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(v_a_1032_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_pos_1171_; lean_object* v_res_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1180_; 
v_pos_1171_ = lean_ctor_get(v___x_1170_, 0);
v_res_1172_ = lean_ctor_get(v___x_1170_, 1);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1174_ = v___x_1170_;
v_isShared_1175_ = v_isSharedCheck_1180_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_res_1172_);
lean_inc(v_pos_1171_);
lean_dec(v___x_1170_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1180_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; lean_object* v___x_1178_; 
v___x_1176_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1176_, 0, v_res_1172_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 1, v___x_1176_);
v___x_1178_ = v___x_1174_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_pos_1171_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
else
{
lean_object* v_pos_1181_; lean_object* v_err_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
v_pos_1181_ = lean_ctor_get(v___x_1170_, 0);
v_err_1182_ = lean_ctor_get(v___x_1170_, 1);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1170_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_err_1182_);
lean_inc(v_pos_1181_);
lean_dec(v___x_1170_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_pos_1181_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_err_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
}
v___jp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1036_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0));
v___x_1037_ = lean_string_append(v___x_1036_, v___y_1035_);
lean_dec_ref(v___y_1035_);
v___x_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
v___x_1039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___y_1034_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
return v___x_1039_;
}
v___jp_1040_:
{
if (v___y_1044_ == 0)
{
lean_dec_ref(v___y_1041_);
v___y_1034_ = v___y_1042_;
v___y_1035_ = v___y_1043_;
goto v___jp_1033_;
}
else
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
lean_dec_ref(v___y_1043_);
v___x_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1045_, 0, v___y_1041_);
v___x_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___y_1042_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
return v___x_1046_;
}
}
v___jp_1047_:
{
if (v___y_1054_ == 0)
{
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
v___y_1034_ = v___y_1052_;
v___y_1035_ = v___y_1053_;
goto v___jp_1033_;
}
else
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1055_ = lean_string_utf8_byte_size(v___y_1048_);
lean_inc(v___y_1049_);
lean_inc_ref(v___y_1048_);
v___x_1056_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1056_, 0, v___y_1048_);
lean_ctor_set(v___x_1056_, 1, v___y_1049_);
lean_ctor_set(v___x_1056_, 2, v___x_1055_);
v___x_1057_ = l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(v___x_1056_);
v___x_1058_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___y_1048_, v___x_1056_, v___x_1055_, v___x_1057_, v___y_1054_);
lean_dec_ref(v___x_1056_);
if (v___x_1058_ == 0)
{
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
v___y_1034_ = v___y_1052_;
v___y_1035_ = v___y_1053_;
goto v___jp_1033_;
}
else
{
lean_object* v___x_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1059_ = lean_string_length(v___y_1048_);
v___x_1060_ = lean_unsigned_to_nat(255u);
v___x_1061_ = lean_nat_dec_le(v___x_1059_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
v___y_1034_ = v___y_1052_;
v___y_1035_ = v___y_1053_;
goto v___jp_1033_;
}
else
{
uint8_t v___x_1062_; 
v___x_1062_ = lean_nat_dec_eq(v___x_1055_, v___y_1049_);
lean_dec(v___y_1049_);
if (v___x_1062_ == 0)
{
v___y_1041_ = v___y_1048_;
v___y_1042_ = v___y_1052_;
v___y_1043_ = v___y_1053_;
v___y_1044_ = v___y_1051_;
goto v___jp_1040_;
}
else
{
v___y_1041_ = v___y_1048_;
v___y_1042_ = v___y_1052_;
v___y_1043_ = v___y_1053_;
v___y_1044_ = v___y_1050_;
goto v___jp_1040_;
}
}
}
}
}
v___jp_1063_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; 
v___x_1070_ = l_ByteArray_toByteSlice(v___y_1067_, v_lower_1068_, v_upper_1069_);
v___x_1071_ = l_ByteSlice_toByteArray(v___x_1070_);
v___x_1072_ = lean_string_validate_utf8(v___x_1071_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
lean_dec_ref(v___x_1071_);
lean_dec(v___y_1064_);
v___x_1073_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2));
v___x_1074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___y_1066_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
return v___x_1074_;
}
else
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1075_ = lean_string_from_utf8_unchecked(v___x_1071_);
lean_inc_n(v___y_1064_, 2);
lean_inc_ref(v___x_1075_);
v___x_1076_ = l_String_mapAux___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(v___x_1075_, v___y_1064_);
v___x_1077_ = lean_string_utf8_byte_size(v___x_1076_);
lean_inc_ref(v___x_1076_);
v___x_1078_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1076_);
lean_ctor_set(v___x_1078_, 1, v___y_1064_);
lean_ctor_set(v___x_1078_, 2, v___x_1077_);
v___x_1079_ = l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(v___x_1078_);
v___x_1080_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_1076_, v___x_1078_, v___x_1079_, v___x_1072_);
lean_dec_ref(v___x_1078_);
if (v___x_1080_ == 0)
{
v___y_1048_ = v___x_1076_;
v___y_1049_ = v___y_1064_;
v___y_1050_ = v___y_1065_;
v___y_1051_ = v___x_1072_;
v___y_1052_ = v___y_1066_;
v___y_1053_ = v___x_1075_;
v___y_1054_ = v___x_1072_;
goto v___jp_1047_;
}
else
{
v___y_1048_ = v___x_1076_;
v___y_1049_ = v___y_1064_;
v___y_1050_ = v___y_1065_;
v___y_1051_ = v___x_1072_;
v___y_1052_ = v___y_1066_;
v___y_1053_ = v___x_1075_;
v___y_1054_ = v___y_1065_;
goto v___jp_1047_;
}
}
}
v___jp_1081_:
{
uint8_t v___x_1089_; 
v___x_1089_ = lean_nat_dec_le(v___y_1086_, v___y_1082_);
if (v___x_1089_ == 0)
{
lean_dec(v___y_1086_);
v___y_1064_ = v___y_1083_;
v___y_1065_ = v___y_1084_;
v___y_1066_ = v___y_1085_;
v___y_1067_ = v___y_1087_;
v_lower_1068_ = v___y_1088_;
v_upper_1069_ = v___y_1082_;
goto v___jp_1063_;
}
else
{
lean_dec(v___y_1082_);
v___y_1064_ = v___y_1083_;
v___y_1065_ = v___y_1084_;
v___y_1066_ = v___y_1085_;
v___y_1067_ = v___y_1087_;
v_lower_1068_ = v___y_1088_;
v_upper_1069_ = v___y_1086_;
goto v___jp_1063_;
}
}
v___jp_1093_:
{
lean_object* v_maxHostLength_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v_fst_1098_; lean_object* v_snd_1099_; uint8_t v___x_1100_; 
v_maxHostLength_1095_ = lean_ctor_get(v_config_1031_, 1);
v___x_1096_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___y_1094_);
v___x_1097_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo1_findEnd(v___f_1092_, v_maxHostLength_1095_, v___x_1096_, v___y_1094_);
v_fst_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_fst_1098_);
v_snd_1099_ = lean_ctor_get(v___x_1097_, 1);
lean_inc(v_snd_1099_);
lean_dec_ref(v___x_1097_);
v___x_1100_ = lean_nat_dec_eq(v_fst_1098_, v___x_1096_);
if (v___x_1100_ == 0)
{
lean_object* v_array_1101_; lean_object* v_idx_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v_array_1101_ = lean_ctor_get(v___y_1094_, 0);
lean_inc_ref(v_array_1101_);
v_idx_1102_ = lean_ctor_get(v___y_1094_, 1);
lean_inc(v_idx_1102_);
lean_dec_ref(v___y_1094_);
v___x_1103_ = lean_nat_add(v_idx_1102_, v_fst_1098_);
lean_dec(v_fst_1098_);
v___x_1104_ = lean_byte_array_size(v_array_1101_);
v___x_1105_ = lean_nat_dec_le(v_idx_1102_, v___x_1096_);
if (v___x_1105_ == 0)
{
v___y_1082_ = v___x_1104_;
v___y_1083_ = v___x_1096_;
v___y_1084_ = v___x_1100_;
v___y_1085_ = v_snd_1099_;
v___y_1086_ = v___x_1103_;
v___y_1087_ = v_array_1101_;
v___y_1088_ = v_idx_1102_;
goto v___jp_1081_;
}
else
{
lean_dec(v_idx_1102_);
v___y_1082_ = v___x_1104_;
v___y_1083_ = v___x_1096_;
v___y_1084_ = v___x_1100_;
v___y_1085_ = v_snd_1099_;
v___y_1086_ = v___x_1103_;
v___y_1087_ = v_array_1101_;
v___y_1088_ = v___x_1096_;
goto v___jp_1081_;
}
}
else
{
lean_object* v_array_1106_; lean_object* v_idx_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1121_; 
lean_dec(v_fst_1098_);
v_array_1106_ = lean_ctor_get(v_snd_1099_, 0);
v_idx_1107_ = lean_ctor_get(v_snd_1099_, 1);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_snd_1099_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1109_ = v_snd_1099_;
v_isShared_1110_ = v_isSharedCheck_1121_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_idx_1107_);
lean_inc(v_array_1106_);
lean_dec(v_snd_1099_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1121_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1111_ = lean_byte_array_size(v_array_1106_);
lean_dec_ref(v_array_1106_);
v___x_1112_ = lean_nat_dec_le(v___x_1111_, v_idx_1107_);
lean_dec(v_idx_1107_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; lean_object* v___x_1115_; 
v___x_1113_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10));
if (v_isShared_1110_ == 0)
{
lean_ctor_set_tag(v___x_1109_, 1);
lean_ctor_set(v___x_1109_, 1, v___x_1113_);
lean_ctor_set(v___x_1109_, 0, v___y_1094_);
v___x_1115_ = v___x_1109_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___y_1094_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
else
{
lean_object* v___x_1117_; lean_object* v___x_1119_; 
v___x_1117_ = lean_box(0);
if (v_isShared_1110_ == 0)
{
lean_ctor_set_tag(v___x_1109_, 1);
lean_ctor_set(v___x_1109_, 1, v___x_1117_);
lean_ctor_set(v___x_1109_, 0, v___y_1094_);
v___x_1119_ = v___x_1109_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___y_1094_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v___x_1117_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
v___jp_1122_:
{
lean_object* v___x_1124_; 
lean_inc_ref(v_pos_1123_);
v___x_1124_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(v_pos_1123_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_pos_1125_; lean_object* v_res_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1134_; 
lean_dec_ref(v_pos_1123_);
v_pos_1125_ = lean_ctor_get(v___x_1124_, 0);
v_res_1126_ = lean_ctor_get(v___x_1124_, 1);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1128_ = v___x_1124_;
v_isShared_1129_ = v_isSharedCheck_1134_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_res_1126_);
lean_inc(v_pos_1125_);
lean_dec(v___x_1124_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1134_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1130_, 0, v_res_1126_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 1, v___x_1130_);
v___x_1132_ = v___x_1128_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_pos_1125_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
else
{
lean_object* v_err_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1144_; 
v_err_1135_ = lean_ctor_get(v___x_1124_, 1);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; 
v_unused_1145_ = lean_ctor_get(v___x_1124_, 0);
lean_dec(v_unused_1145_);
v___x_1137_ = v___x_1124_;
v_isShared_1138_ = v_isSharedCheck_1144_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_err_1135_);
lean_dec(v___x_1124_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1144_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v_idx_1139_; uint8_t v___x_1140_; 
v_idx_1139_ = lean_ctor_get(v_pos_1123_, 1);
v___x_1140_ = lean_nat_dec_eq(v_idx_1139_, v_idx_1139_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1142_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v_pos_1123_);
v___x_1142_ = v___x_1137_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_pos_1123_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_err_1135_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
else
{
lean_del_object(v___x_1137_);
lean_dec(v_err_1135_);
v___y_1094_ = v_pos_1123_;
goto v___jp_1093_;
}
}
}
}
v___jp_1146_:
{
v___y_1094_ = v_pos_1147_;
goto v___jp_1093_;
}
v___jp_1149_:
{
if (v___y_1152_ == 0)
{
v_pos_1147_ = v___y_1151_;
v_res_1148_ = v___y_1150_;
goto v___jp_1146_;
}
else
{
v_pos_1123_ = v___y_1151_;
goto v___jp_1122_;
}
}
v___jp_1153_:
{
lean_object* v___x_1156_; uint8_t v___x_1157_; 
v___x_1156_ = lean_byte_array_size(v_array_1090_);
v___x_1157_ = lean_nat_dec_lt(v_idx_1091_, v___x_1156_);
if (v___x_1157_ == 0)
{
lean_dec(v_idx_1091_);
lean_dec_ref(v_array_1090_);
v_pos_1147_ = v_pos_1154_;
v_res_1148_ = v_res_1155_;
goto v___jp_1146_;
}
else
{
uint8_t v___x_1158_; uint8_t v___x_1159_; uint8_t v___x_1160_; 
v___x_1158_ = lean_byte_array_fget(v_array_1090_, v_idx_1091_);
lean_dec(v_idx_1091_);
lean_dec_ref(v_array_1090_);
v___x_1159_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3);
v___x_1160_ = lean_uint8_dec_le(v___x_1159_, v___x_1158_);
if (v___x_1160_ == 0)
{
v___y_1150_ = v_res_1155_;
v___y_1151_ = v_pos_1154_;
v___y_1152_ = v___x_1160_;
goto v___jp_1149_;
}
else
{
uint8_t v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4);
v___x_1162_ = lean_uint8_dec_le(v___x_1158_, v___x_1161_);
v___y_1150_ = v_res_1155_;
v___y_1151_ = v_pos_1154_;
v___y_1152_ = v___x_1162_;
goto v___jp_1149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___boxed(lean_object* v_config_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_1190_, v_a_1191_);
lean_dec_ref(v_config_1190_);
return v_res_1192_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(lean_object* v___x_1193_, lean_object* v___x_1194_, lean_object* v___x_1195_, lean_object* v_inst_1196_, lean_object* v_R_1197_, lean_object* v_a_1198_, uint8_t v_b_1199_, lean_object* v_c_1200_){
_start:
{
uint8_t v___x_1201_; 
v___x_1201_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_1193_, v___x_1194_, v___x_1195_, v_a_1198_, v_b_1199_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___boxed(lean_object* v___x_1202_, lean_object* v___x_1203_, lean_object* v___x_1204_, lean_object* v_inst_1205_, lean_object* v_R_1206_, lean_object* v_a_1207_, lean_object* v_b_1208_, lean_object* v_c_1209_){
_start:
{
uint8_t v_b_boxed_1210_; uint8_t v_res_1211_; lean_object* v_r_1212_; 
v_b_boxed_1210_ = lean_unbox(v_b_1208_);
v_res_1211_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(v___x_1202_, v___x_1203_, v___x_1204_, v_inst_1205_, v_R_1206_, v_a_1207_, v_b_boxed_1210_, v_c_1209_);
lean_dec_ref(v___x_1203_);
lean_dec_ref(v___x_1202_);
v_r_1212_ = lean_box(v_res_1211_);
return v_r_1212_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(lean_object* v___x_1213_, lean_object* v___x_1214_, lean_object* v___x_1215_, lean_object* v_inst_1216_, lean_object* v_R_1217_, lean_object* v_a_1218_, uint8_t v_b_1219_, lean_object* v_c_1220_){
_start:
{
uint8_t v___x_1221_; 
v___x_1221_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_1213_, v___x_1214_, v_a_1218_, v_b_1219_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___boxed(lean_object* v___x_1222_, lean_object* v___x_1223_, lean_object* v___x_1224_, lean_object* v_inst_1225_, lean_object* v_R_1226_, lean_object* v_a_1227_, lean_object* v_b_1228_, lean_object* v_c_1229_){
_start:
{
uint8_t v_b_boxed_1230_; uint8_t v_res_1231_; lean_object* v_r_1232_; 
v_b_boxed_1230_ = lean_unbox(v_b_1228_);
v_res_1231_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(v___x_1222_, v___x_1223_, v___x_1224_, v_inst_1225_, v_R_1226_, v_a_1227_, v_b_boxed_1230_, v_c_1229_);
lean_dec(v___x_1224_);
lean_dec_ref(v___x_1223_);
lean_dec_ref(v___x_1222_);
v_r_1232_ = lean_box(v_res_1231_);
return v_r_1232_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2(void){
_start:
{
uint32_t v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = 47;
v___x_1237_ = lean_uint32_to_uint8(v___x_1236_);
return v___x_1237_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3(void){
_start:
{
uint32_t v___x_1238_; uint8_t v___x_1239_; 
v___x_1238_ = 63;
v___x_1239_ = lean_uint32_to_uint8(v___x_1238_);
return v___x_1239_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4(void){
_start:
{
uint32_t v___x_1240_; uint8_t v___x_1241_; 
v___x_1240_ = 35;
v___x_1241_ = lean_uint32_to_uint8(v___x_1240_);
return v___x_1241_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5(void){
_start:
{
uint8_t v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_1243_ = lean_uint8_to_nat(v___x_1242_);
return v___x_1243_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6(void){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5);
v___x_1245_ = l_Nat_reprFast(v___x_1244_);
return v___x_1245_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7(void){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1246_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6);
v___x_1247_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_1248_ = lean_string_append(v___x_1247_, v___x_1246_);
return v___x_1248_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8(void){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1249_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_1250_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7);
v___x_1251_ = lean_string_append(v___x_1250_, v___x_1249_);
return v___x_1251_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8);
v___x_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
return v___x_1253_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10(void){
_start:
{
uint32_t v___x_1254_; uint8_t v___x_1255_; 
v___x_1254_ = 64;
v___x_1255_ = lean_uint32_to_uint8(v___x_1254_);
return v___x_1255_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11(void){
_start:
{
uint8_t v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_1257_ = lean_uint8_to_nat(v___x_1256_);
return v___x_1257_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12(void){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11);
v___x_1259_ = l_Nat_reprFast(v___x_1258_);
return v___x_1259_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13(void){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1260_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12);
v___x_1261_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_1262_ = lean_string_append(v___x_1261_, v___x_1260_);
return v___x_1262_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_1264_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13);
v___x_1265_ = lean_string_append(v___x_1264_, v___x_1263_);
return v___x_1265_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14);
v___x_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(lean_object* v_config_1268_, lean_object* v_a_1269_){
_start:
{
lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v_port_1273_; lean_object* v___y_1274_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v_pos_1280_; lean_object* v___y_1283_; lean_object* v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; uint8_t v___y_1295_; lean_object* v___y_1297_; uint8_t v___y_1298_; lean_object* v___y_1299_; lean_object* v___y_1300_; uint8_t v___y_1301_; lean_object* v___y_1302_; uint8_t v___y_1303_; lean_object* v___y_1315_; lean_object* v___y_1316_; uint8_t v___y_1317_; lean_object* v___y_1318_; uint8_t v___y_1319_; uint8_t v___y_1320_; lean_object* v___y_1330_; uint8_t v___y_1331_; uint8_t v___y_1332_; lean_object* v___y_1333_; lean_object* v_pos_1334_; lean_object* v___y_1337_; lean_object* v___y_1338_; uint8_t v___y_1339_; lean_object* v___y_1340_; uint8_t v___y_1341_; lean_object* v___y_1342_; uint8_t v___y_1343_; lean_object* v_pos_1359_; lean_object* v_res_1360_; lean_object* v_pos_1412_; lean_object* v_res_1413_; lean_object* v_err_1416_; lean_object* v___x_1421_; 
lean_inc_ref(v_a_1269_);
v___x_1421_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(v_config_1268_, v_a_1269_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_pos_1422_; lean_object* v_res_1423_; lean_object* v_array_1424_; lean_object* v_idx_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1441_; 
v_pos_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_pos_1422_);
v_res_1423_ = lean_ctor_get(v___x_1421_, 1);
lean_inc(v_res_1423_);
lean_dec_ref(v___x_1421_);
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
uint8_t v___x_1432_; uint8_t v_c_1433_; uint8_t v___x_1434_; 
v___x_1432_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v_c_1433_ = lean_byte_array_fget(v_array_1424_, v_idx_1425_);
v___x_1434_ = lean_uint8_dec_eq(v_c_1433_, v___x_1432_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; 
lean_del_object(v___x_1427_);
lean_dec(v_idx_1425_);
lean_dec_ref(v_array_1424_);
lean_dec(v_res_1423_);
v___x_1435_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15);
v_err_1416_ = v___x_1435_;
goto v___jp_1415_;
}
else
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v_it_x27_1439_; 
lean_dec_ref(v_a_1269_);
v___x_1436_ = lean_unsigned_to_nat(1u);
v___x_1437_ = lean_nat_add(v_idx_1425_, v___x_1436_);
lean_dec(v_idx_1425_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 1, v___x_1437_);
v_it_x27_1439_ = v___x_1427_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_array_1424_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v___x_1437_);
v_it_x27_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
v_pos_1412_ = v_it_x27_1439_;
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
lean_dec_ref(v_a_1269_);
v_pos_1442_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_pos_1442_);
v_res_1443_ = lean_ctor_get(v___x_1421_, 1);
lean_inc(v_res_1443_);
lean_dec_ref(v___x_1421_);
v_pos_1412_ = v_pos_1442_;
v_res_1413_ = v_res_1443_;
goto v___jp_1411_;
}
else
{
lean_object* v_err_1444_; 
v_err_1444_ = lean_ctor_get(v___x_1421_, 1);
lean_inc(v_err_1444_);
lean_dec_ref(v___x_1421_);
v_err_1416_ = v_err_1444_;
goto v___jp_1415_;
}
}
v___jp_1270_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1275_, 0, v___y_1272_);
lean_ctor_set(v___x_1275_, 1, v___y_1271_);
lean_ctor_set(v___x_1275_, 2, v_port_1273_);
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___y_1274_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
return v___x_1276_;
}
v___jp_1277_:
{
lean_object* v___x_1281_; 
v___x_1281_ = lean_box(0);
v___y_1271_ = v___y_1278_;
v___y_1272_ = v___y_1279_;
v_port_1273_ = v___x_1281_;
v___y_1274_ = v_pos_1280_;
goto v___jp_1270_;
}
v___jp_1282_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__1));
v___x_1285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___y_1283_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
return v___x_1285_;
}
v___jp_1286_:
{
lean_object* v___x_1290_; 
v___x_1290_ = lean_box(1);
v___y_1271_ = v___y_1287_;
v___y_1272_ = v___y_1289_;
v_port_1273_ = v___x_1290_;
v___y_1274_ = v___y_1288_;
goto v___jp_1270_;
}
v___jp_1291_:
{
if (v___y_1295_ == 0)
{
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1292_);
v___y_1283_ = v___y_1293_;
goto v___jp_1282_;
}
else
{
v___y_1287_ = v___y_1292_;
v___y_1288_ = v___y_1293_;
v___y_1289_ = v___y_1294_;
goto v___jp_1286_;
}
}
v___jp_1296_:
{
if (v___y_1303_ == 0)
{
if (lean_obj_tag(v___y_1300_) == 0)
{
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1297_);
v___y_1283_ = v___y_1299_;
goto v___jp_1282_;
}
else
{
lean_object* v_val_1304_; uint8_t v___x_1305_; uint8_t v___x_1306_; uint8_t v___x_1307_; 
v_val_1304_ = lean_ctor_get(v___y_1300_, 0);
lean_inc(v_val_1304_);
lean_dec_ref(v___y_1300_);
v___x_1305_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_1306_ = lean_unbox(v_val_1304_);
v___x_1307_ = lean_uint8_dec_eq(v___x_1306_, v___x_1305_);
if (v___x_1307_ == 0)
{
uint8_t v___x_1308_; uint8_t v___x_1309_; uint8_t v___x_1310_; 
v___x_1308_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v___x_1309_ = lean_unbox(v_val_1304_);
v___x_1310_ = lean_uint8_dec_eq(v___x_1309_, v___x_1308_);
if (v___x_1310_ == 0)
{
uint8_t v___x_1311_; uint8_t v___x_1312_; uint8_t v___x_1313_; 
v___x_1311_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v___x_1312_ = lean_unbox(v_val_1304_);
lean_dec(v_val_1304_);
v___x_1313_ = lean_uint8_dec_eq(v___x_1312_, v___x_1311_);
if (v___x_1313_ == 0)
{
v___y_1292_ = v___y_1297_;
v___y_1293_ = v___y_1299_;
v___y_1294_ = v___y_1302_;
v___y_1295_ = v___x_1313_;
goto v___jp_1291_;
}
else
{
v___y_1292_ = v___y_1297_;
v___y_1293_ = v___y_1299_;
v___y_1294_ = v___y_1302_;
v___y_1295_ = v___y_1298_;
goto v___jp_1291_;
}
}
else
{
lean_dec(v_val_1304_);
v___y_1292_ = v___y_1297_;
v___y_1293_ = v___y_1299_;
v___y_1294_ = v___y_1302_;
v___y_1295_ = v___y_1298_;
goto v___jp_1291_;
}
}
else
{
lean_dec(v_val_1304_);
v___y_1292_ = v___y_1297_;
v___y_1293_ = v___y_1299_;
v___y_1294_ = v___y_1302_;
v___y_1295_ = v___y_1301_;
goto v___jp_1291_;
}
}
}
else
{
lean_dec(v___y_1300_);
v___y_1287_ = v___y_1297_;
v___y_1288_ = v___y_1299_;
v___y_1289_ = v___y_1302_;
goto v___jp_1286_;
}
}
v___jp_1314_:
{
lean_object* v_array_1321_; lean_object* v_idx_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; 
v_array_1321_ = lean_ctor_get(v___y_1316_, 0);
v_idx_1322_ = lean_ctor_get(v___y_1316_, 1);
v___x_1323_ = lean_byte_array_size(v_array_1321_);
v___x_1324_ = lean_nat_dec_lt(v_idx_1322_, v___x_1323_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; 
v___x_1325_ = lean_box(0);
v___y_1297_ = v___y_1315_;
v___y_1298_ = v___y_1317_;
v___y_1299_ = v___y_1316_;
v___y_1300_ = v___x_1325_;
v___y_1301_ = v___y_1319_;
v___y_1302_ = v___y_1318_;
v___y_1303_ = v___y_1319_;
goto v___jp_1296_;
}
else
{
uint8_t v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1326_ = lean_byte_array_fget(v_array_1321_, v_idx_1322_);
v___x_1327_ = lean_box(v___x_1326_);
v___x_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
v___y_1297_ = v___y_1315_;
v___y_1298_ = v___y_1317_;
v___y_1299_ = v___y_1316_;
v___y_1300_ = v___x_1328_;
v___y_1301_ = v___y_1319_;
v___y_1302_ = v___y_1318_;
v___y_1303_ = v___y_1320_;
goto v___jp_1296_;
}
}
v___jp_1329_:
{
uint8_t v___x_1335_; 
v___x_1335_ = 0;
v___y_1315_ = v___y_1330_;
v___y_1316_ = v_pos_1334_;
v___y_1317_ = v___y_1331_;
v___y_1318_ = v___y_1333_;
v___y_1319_ = v___y_1332_;
v___y_1320_ = v___x_1335_;
goto v___jp_1314_;
}
v___jp_1336_:
{
lean_dec(v___y_1342_);
if (v___y_1343_ == 0)
{
v___y_1330_ = v___y_1337_;
v___y_1331_ = v___y_1339_;
v___y_1332_ = v___y_1341_;
v___y_1333_ = v___y_1340_;
v_pos_1334_ = v___y_1338_;
goto v___jp_1329_;
}
else
{
if (v___y_1341_ == 0)
{
v___y_1315_ = v___y_1337_;
v___y_1316_ = v___y_1338_;
v___y_1317_ = v___y_1339_;
v___y_1318_ = v___y_1340_;
v___y_1319_ = v___y_1341_;
v___y_1320_ = v___y_1341_;
goto v___jp_1314_;
}
else
{
lean_object* v___x_1344_; 
v___x_1344_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___y_1338_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_pos_1345_; lean_object* v_res_1346_; lean_object* v___x_1347_; uint16_t v___x_1348_; 
v_pos_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_pos_1345_);
v_res_1346_ = lean_ctor_get(v___x_1344_, 1);
lean_inc(v_res_1346_);
lean_dec_ref(v___x_1344_);
v___x_1347_ = lean_alloc_ctor(2, 0, 2);
v___x_1348_ = lean_unbox(v_res_1346_);
lean_dec(v_res_1346_);
lean_ctor_set_uint16(v___x_1347_, 0, v___x_1348_);
v___y_1271_ = v___y_1337_;
v___y_1272_ = v___y_1340_;
v_port_1273_ = v___x_1347_;
v___y_1274_ = v_pos_1345_;
goto v___jp_1270_;
}
else
{
lean_object* v_pos_1349_; lean_object* v_err_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1337_);
v_pos_1349_ = lean_ctor_get(v___x_1344_, 0);
v_err_1350_ = lean_ctor_get(v___x_1344_, 1);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1344_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_err_1350_);
lean_inc(v_pos_1349_);
lean_dec(v___x_1344_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_pos_1349_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_err_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
}
}
v___jp_1358_:
{
lean_object* v___x_1361_; 
v___x_1361_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_1268_, v_pos_1359_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_pos_1362_; lean_object* v_res_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1401_; 
v_pos_1362_ = lean_ctor_get(v___x_1361_, 0);
v_res_1363_ = lean_ctor_get(v___x_1361_, 1);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1365_ = v___x_1361_;
v_isShared_1366_ = v_isSharedCheck_1401_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_res_1363_);
lean_inc(v_pos_1362_);
lean_dec(v___x_1361_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1401_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v_array_1367_; lean_object* v_idx_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v_array_1367_ = lean_ctor_get(v_pos_1362_, 0);
v_idx_1368_ = lean_ctor_get(v_pos_1362_, 1);
v___x_1369_ = lean_byte_array_size(v_array_1367_);
v___x_1370_ = lean_nat_dec_lt(v_idx_1368_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_del_object(v___x_1365_);
v___y_1278_ = v_res_1363_;
v___y_1279_ = v_res_1360_;
v_pos_1280_ = v_pos_1362_;
goto v___jp_1277_;
}
else
{
uint8_t v___x_1371_; uint8_t v___x_1372_; uint8_t v___x_1373_; 
v___x_1371_ = lean_byte_array_fget(v_array_1367_, v_idx_1368_);
v___x_1372_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_1373_ = lean_uint8_dec_eq(v___x_1371_, v___x_1372_);
if (v___x_1373_ == 0)
{
lean_del_object(v___x_1365_);
v___y_1278_ = v_res_1363_;
v___y_1279_ = v_res_1360_;
v_pos_1280_ = v_pos_1362_;
goto v___jp_1277_;
}
else
{
if (v___x_1373_ == 0)
{
lean_del_object(v___x_1365_);
v___y_1278_ = v_res_1363_;
v___y_1279_ = v_res_1360_;
v_pos_1280_ = v_pos_1362_;
goto v___jp_1277_;
}
else
{
if (v___x_1370_ == 0)
{
lean_object* v___x_1374_; lean_object* v___x_1376_; 
lean_dec(v_res_1363_);
lean_dec(v_res_1360_);
v___x_1374_ = lean_box(0);
if (v_isShared_1366_ == 0)
{
lean_ctor_set_tag(v___x_1365_, 1);
lean_ctor_set(v___x_1365_, 1, v___x_1374_);
v___x_1376_ = v___x_1365_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_pos_1362_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
else
{
if (v___x_1373_ == 0)
{
lean_object* v___x_1378_; lean_object* v___x_1380_; 
lean_dec(v_res_1363_);
lean_dec(v_res_1360_);
v___x_1378_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
if (v_isShared_1366_ == 0)
{
lean_ctor_set_tag(v___x_1365_, 1);
lean_ctor_set(v___x_1365_, 1, v___x_1378_);
v___x_1380_ = v___x_1365_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_pos_1362_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
else
{
lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1398_; 
lean_inc(v_idx_1368_);
lean_inc_ref(v_array_1367_);
lean_del_object(v___x_1365_);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_pos_1362_);
if (v_isSharedCheck_1398_ == 0)
{
lean_object* v_unused_1399_; lean_object* v_unused_1400_; 
v_unused_1399_ = lean_ctor_get(v_pos_1362_, 1);
lean_dec(v_unused_1399_);
v_unused_1400_ = lean_ctor_get(v_pos_1362_, 0);
lean_dec(v_unused_1400_);
v___x_1383_ = v_pos_1362_;
v_isShared_1384_ = v_isSharedCheck_1398_;
goto v_resetjp_1382_;
}
else
{
lean_dec(v_pos_1362_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1398_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v_it_x27_1388_; 
v___x_1385_ = lean_unsigned_to_nat(1u);
v___x_1386_ = lean_nat_add(v_idx_1368_, v___x_1385_);
lean_dec(v_idx_1368_);
lean_inc(v___x_1386_);
lean_inc_ref(v_array_1367_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 1, v___x_1386_);
v_it_x27_1388_ = v___x_1383_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_array_1367_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v___x_1386_);
v_it_x27_1388_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
uint8_t v___x_1389_; 
v___x_1389_ = lean_nat_dec_lt(v___x_1386_, v___x_1369_);
if (v___x_1389_ == 0)
{
lean_dec(v___x_1386_);
lean_dec_ref(v_array_1367_);
v___y_1330_ = v_res_1363_;
v___y_1331_ = v___x_1373_;
v___y_1332_ = v___x_1370_;
v___y_1333_ = v_res_1360_;
v_pos_1334_ = v_it_x27_1388_;
goto v___jp_1329_;
}
else
{
uint8_t v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; uint8_t v___x_1393_; uint8_t v___x_1394_; 
v___x_1390_ = lean_byte_array_fget(v_array_1367_, v___x_1386_);
lean_dec(v___x_1386_);
lean_dec_ref(v_array_1367_);
v___x_1391_ = lean_box(v___x_1390_);
v___x_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
v___x_1393_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3);
v___x_1394_ = lean_uint8_dec_le(v___x_1393_, v___x_1390_);
if (v___x_1394_ == 0)
{
v___y_1337_ = v_res_1363_;
v___y_1338_ = v_it_x27_1388_;
v___y_1339_ = v___x_1373_;
v___y_1340_ = v_res_1360_;
v___y_1341_ = v___x_1370_;
v___y_1342_ = v___x_1392_;
v___y_1343_ = v___x_1394_;
goto v___jp_1336_;
}
else
{
uint8_t v___x_1395_; uint8_t v___x_1396_; 
v___x_1395_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4);
v___x_1396_ = lean_uint8_dec_le(v___x_1390_, v___x_1395_);
v___y_1337_ = v_res_1363_;
v___y_1338_ = v_it_x27_1388_;
v___y_1339_ = v___x_1373_;
v___y_1340_ = v_res_1360_;
v___y_1341_ = v___x_1370_;
v___y_1342_ = v___x_1392_;
v___y_1343_ = v___x_1396_;
goto v___jp_1336_;
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
lean_dec(v_res_1360_);
v_pos_1402_ = lean_ctor_get(v___x_1361_, 0);
v_err_1403_ = lean_ctor_get(v___x_1361_, 1);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1361_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_err_1403_);
lean_inc(v_pos_1402_);
lean_dec(v___x_1361_);
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
v_pos_1359_ = v_pos_1412_;
v_res_1360_ = v___x_1414_;
goto v___jp_1358_;
}
v___jp_1415_:
{
lean_object* v_idx_1417_; uint8_t v___x_1418_; 
v_idx_1417_ = lean_ctor_get(v_a_1269_, 1);
v___x_1418_ = lean_nat_dec_eq(v_idx_1417_, v_idx_1417_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1419_, 0, v_a_1269_);
lean_ctor_set(v___x_1419_, 1, v_err_1416_);
return v___x_1419_;
}
else
{
lean_object* v___x_1420_; 
lean_dec(v_err_1416_);
v___x_1420_ = lean_box(0);
v_pos_1359_ = v_a_1269_;
v_res_1360_ = v___x_1420_;
goto v___jp_1358_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___boxed(lean_object* v_config_1445_, lean_object* v_a_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_1445_, v_a_1446_);
lean_dec_ref(v_config_1445_);
return v_res_1447_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(uint8_t v_c_1448_){
_start:
{
uint8_t v___y_1450_; uint8_t v___y_1454_; uint8_t v___y_1460_; uint8_t v___y_1480_; uint8_t v___y_1486_; uint8_t v___y_1492_; uint8_t v___y_1498_; uint8_t v___y_1504_; uint8_t v___x_1509_; uint8_t v___x_1510_; 
v___x_1509_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3);
v___x_1510_ = lean_uint8_dec_le(v___x_1509_, v_c_1448_);
if (v___x_1510_ == 0)
{
v___y_1504_ = v___x_1510_;
goto v___jp_1503_;
}
else
{
uint8_t v___x_1511_; uint8_t v___x_1512_; 
v___x_1511_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4);
v___x_1512_ = lean_uint8_dec_le(v_c_1448_, v___x_1511_);
v___y_1504_ = v___x_1512_;
goto v___jp_1503_;
}
v___jp_1449_:
{
if (v___y_1450_ == 0)
{
uint8_t v___x_1451_; uint8_t v___x_1452_; 
v___x_1451_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_1452_ = lean_uint8_dec_eq(v_c_1448_, v___x_1451_);
if (v___x_1452_ == 0)
{
return v___y_1450_;
}
else
{
return v___x_1452_;
}
}
else
{
return v___y_1450_;
}
}
v___jp_1453_:
{
if (v___y_1454_ == 0)
{
uint8_t v___x_1455_; uint8_t v___x_1456_; 
v___x_1455_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_1456_ = lean_uint8_dec_eq(v_c_1448_, v___x_1455_);
if (v___x_1456_ == 0)
{
uint8_t v___x_1457_; uint8_t v___x_1458_; 
v___x_1457_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_1458_ = lean_uint8_dec_eq(v_c_1448_, v___x_1457_);
v___y_1450_ = v___x_1458_;
goto v___jp_1449_;
}
else
{
v___y_1450_ = v___x_1456_;
goto v___jp_1449_;
}
}
else
{
return v___y_1454_;
}
}
v___jp_1459_:
{
if (v___y_1460_ == 0)
{
uint8_t v___x_1461_; uint8_t v___x_1462_; 
v___x_1461_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_1462_ = lean_uint8_dec_eq(v_c_1448_, v___x_1461_);
if (v___x_1462_ == 0)
{
uint8_t v___x_1463_; uint8_t v___x_1464_; 
v___x_1463_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_1464_ = lean_uint8_dec_eq(v_c_1448_, v___x_1463_);
if (v___x_1464_ == 0)
{
uint8_t v___x_1465_; uint8_t v___x_1466_; 
v___x_1465_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_1466_ = lean_uint8_dec_eq(v_c_1448_, v___x_1465_);
if (v___x_1466_ == 0)
{
uint8_t v___x_1467_; uint8_t v___x_1468_; 
v___x_1467_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_1468_ = lean_uint8_dec_eq(v_c_1448_, v___x_1467_);
if (v___x_1468_ == 0)
{
uint8_t v___x_1469_; uint8_t v___x_1470_; 
v___x_1469_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_1470_ = lean_uint8_dec_eq(v_c_1448_, v___x_1469_);
if (v___x_1470_ == 0)
{
uint8_t v___x_1471_; uint8_t v___x_1472_; 
v___x_1471_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0);
v___x_1472_ = lean_uint8_dec_eq(v_c_1448_, v___x_1471_);
if (v___x_1472_ == 0)
{
uint8_t v___x_1473_; uint8_t v___x_1474_; 
v___x_1473_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_1474_ = lean_uint8_dec_eq(v_c_1448_, v___x_1473_);
if (v___x_1474_ == 0)
{
uint8_t v___x_1475_; uint8_t v___x_1476_; 
v___x_1475_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_1476_ = lean_uint8_dec_eq(v_c_1448_, v___x_1475_);
if (v___x_1476_ == 0)
{
uint8_t v___x_1477_; uint8_t v___x_1478_; 
v___x_1477_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_1478_ = lean_uint8_dec_eq(v_c_1448_, v___x_1477_);
v___y_1454_ = v___x_1478_;
goto v___jp_1453_;
}
else
{
v___y_1454_ = v___x_1476_;
goto v___jp_1453_;
}
}
else
{
v___y_1454_ = v___x_1474_;
goto v___jp_1453_;
}
}
else
{
v___y_1454_ = v___x_1472_;
goto v___jp_1453_;
}
}
else
{
v___y_1454_ = v___x_1470_;
goto v___jp_1453_;
}
}
else
{
v___y_1454_ = v___x_1468_;
goto v___jp_1453_;
}
}
else
{
v___y_1454_ = v___x_1466_;
goto v___jp_1453_;
}
}
else
{
v___y_1454_ = v___x_1464_;
goto v___jp_1453_;
}
}
else
{
v___y_1454_ = v___x_1462_;
goto v___jp_1453_;
}
}
else
{
return v___y_1460_;
}
}
v___jp_1479_:
{
if (v___y_1480_ == 0)
{
uint8_t v___x_1481_; uint8_t v___x_1482_; 
v___x_1481_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_1482_ = lean_uint8_dec_eq(v_c_1448_, v___x_1481_);
if (v___x_1482_ == 0)
{
uint8_t v___x_1483_; uint8_t v___x_1484_; 
v___x_1483_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_1484_ = lean_uint8_dec_eq(v_c_1448_, v___x_1483_);
v___y_1460_ = v___x_1484_;
goto v___jp_1459_;
}
else
{
v___y_1460_ = v___x_1482_;
goto v___jp_1459_;
}
}
else
{
return v___y_1480_;
}
}
v___jp_1485_:
{
if (v___y_1486_ == 0)
{
uint8_t v___x_1487_; uint8_t v___x_1488_; 
v___x_1487_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_1488_ = lean_uint8_dec_eq(v_c_1448_, v___x_1487_);
if (v___x_1488_ == 0)
{
uint8_t v___x_1489_; uint8_t v___x_1490_; 
v___x_1489_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_1490_ = lean_uint8_dec_eq(v_c_1448_, v___x_1489_);
v___y_1480_ = v___x_1490_;
goto v___jp_1479_;
}
else
{
v___y_1480_ = v___x_1488_;
goto v___jp_1479_;
}
}
else
{
return v___y_1486_;
}
}
v___jp_1491_:
{
if (v___y_1492_ == 0)
{
uint8_t v___x_1493_; uint8_t v___x_1494_; 
v___x_1493_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1);
v___x_1494_ = lean_uint8_dec_eq(v_c_1448_, v___x_1493_);
if (v___x_1494_ == 0)
{
uint8_t v___x_1495_; uint8_t v___x_1496_; 
v___x_1495_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2);
v___x_1496_ = lean_uint8_dec_eq(v_c_1448_, v___x_1495_);
v___y_1486_ = v___x_1496_;
goto v___jp_1485_;
}
else
{
v___y_1486_ = v___x_1494_;
goto v___jp_1485_;
}
}
else
{
return v___y_1492_;
}
}
v___jp_1497_:
{
if (v___y_1498_ == 0)
{
uint8_t v___x_1499_; uint8_t v___x_1500_; 
v___x_1499_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_1500_ = lean_uint8_dec_le(v___x_1499_, v_c_1448_);
if (v___x_1500_ == 0)
{
v___y_1492_ = v___x_1500_;
goto v___jp_1491_;
}
else
{
uint8_t v___x_1501_; uint8_t v___x_1502_; 
v___x_1501_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_1502_ = lean_uint8_dec_le(v_c_1448_, v___x_1501_);
v___y_1492_ = v___x_1502_;
goto v___jp_1491_;
}
}
else
{
return v___y_1498_;
}
}
v___jp_1503_:
{
if (v___y_1504_ == 0)
{
uint8_t v___x_1505_; uint8_t v___x_1506_; 
v___x_1505_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_1506_ = lean_uint8_dec_le(v___x_1505_, v_c_1448_);
if (v___x_1506_ == 0)
{
v___y_1498_ = v___x_1506_;
goto v___jp_1497_;
}
else
{
uint8_t v___x_1507_; uint8_t v___x_1508_; 
v___x_1507_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_1508_ = lean_uint8_dec_le(v_c_1448_, v___x_1507_);
v___y_1498_ = v___x_1508_;
goto v___jp_1497_;
}
}
else
{
return v___y_1504_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0___boxed(lean_object* v_c_1513_){
_start:
{
uint8_t v_c_boxed_1514_; uint8_t v_res_1515_; lean_object* v_r_1516_; 
v_c_boxed_1514_ = lean_unbox(v_c_1513_);
v_res_1515_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(v_c_boxed_1514_);
v_r_1516_ = lean_box(v_res_1515_);
return v_r_1516_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(lean_object* v_config_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v_maxSegmentLength_1520_; lean_object* v___f_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v_fst_1524_; lean_object* v_snd_1525_; lean_object* v_array_1526_; lean_object* v_idx_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1544_; 
v_maxSegmentLength_1520_ = lean_ctor_get(v_config_1518_, 3);
v___f_1521_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___closed__0));
v___x_1522_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1519_);
v___x_1523_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo_findEnd(v___f_1521_, v_maxSegmentLength_1520_, v___x_1522_, v_a_1519_);
v_fst_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_fst_1524_);
v_snd_1525_ = lean_ctor_get(v___x_1523_, 1);
lean_inc(v_snd_1525_);
lean_dec_ref(v___x_1523_);
v_array_1526_ = lean_ctor_get(v_a_1519_, 0);
v_idx_1527_ = lean_ctor_get(v_a_1519_, 1);
v_isSharedCheck_1544_ = !lean_is_exclusive(v_a_1519_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1529_ = v_a_1519_;
v_isShared_1530_ = v_isSharedCheck_1544_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_idx_1527_);
lean_inc(v_array_1526_);
lean_dec(v_a_1519_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1544_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v_lower_1532_; lean_object* v_upper_1533_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___y_1541_; uint8_t v___x_1543_; 
v___x_1538_ = lean_nat_add(v_idx_1527_, v_fst_1524_);
lean_dec(v_fst_1524_);
v___x_1539_ = lean_byte_array_size(v_array_1526_);
v___x_1543_ = lean_nat_dec_le(v_idx_1527_, v___x_1522_);
if (v___x_1543_ == 0)
{
v___y_1541_ = v_idx_1527_;
goto v___jp_1540_;
}
else
{
lean_dec(v_idx_1527_);
v___y_1541_ = v___x_1522_;
goto v___jp_1540_;
}
v___jp_1531_:
{
lean_object* v___x_1534_; lean_object* v___x_1536_; 
v___x_1534_ = l_ByteArray_toByteSlice(v_array_1526_, v_lower_1532_, v_upper_1533_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 1, v___x_1534_);
lean_ctor_set(v___x_1529_, 0, v_snd_1525_);
v___x_1536_ = v___x_1529_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_snd_1525_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v___x_1534_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
v___jp_1540_:
{
uint8_t v___x_1542_; 
v___x_1542_ = lean_nat_dec_le(v___x_1538_, v___x_1539_);
if (v___x_1542_ == 0)
{
lean_dec(v___x_1538_);
v_lower_1532_ = v___y_1541_;
v_upper_1533_ = v___x_1539_;
goto v___jp_1531_;
}
else
{
v_lower_1532_ = v___y_1541_;
v_upper_1533_ = v___x_1538_;
goto v___jp_1531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___boxed(lean_object* v_config_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1545_, v_a_1546_);
lean_dec_ref(v_config_1545_);
return v_res_1547_;
}
}
LEAN_EXPORT uint8_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__0(uint8_t v_c_1548_){
_start:
{
uint8_t v___x_1549_; uint8_t v___x_1550_; 
v___x_1549_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v___x_1550_ = lean_uint8_dec_eq(v_c_1548_, v___x_1549_);
if (v___x_1550_ == 0)
{
uint8_t v___x_1551_; uint8_t v___x_1552_; 
v___x_1551_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v___x_1552_ = lean_uint8_dec_eq(v_c_1548_, v___x_1551_);
return v___x_1552_;
}
else
{
return v___x_1550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__0___boxed(lean_object* v_c_1553_){
_start:
{
uint8_t v_c_boxed_1554_; uint8_t v_res_1555_; lean_object* v_r_1556_; 
v_c_boxed_1554_ = lean_unbox(v_c_1553_);
v_res_1555_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__0(v_c_boxed_1554_);
v_r_1556_ = lean_box(v_res_1555_);
return v_r_1556_;
}
}
LEAN_EXPORT uint8_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__1(uint8_t v___y_1557_){
_start:
{
uint8_t v___y_1559_; uint8_t v___y_1565_; uint8_t v___y_1585_; uint8_t v___y_1591_; uint8_t v___y_1597_; uint8_t v___y_1603_; uint8_t v___y_1609_; uint8_t v___x_1614_; uint8_t v___x_1615_; 
v___x_1614_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3);
v___x_1615_ = lean_uint8_dec_le(v___x_1614_, v___y_1557_);
if (v___x_1615_ == 0)
{
v___y_1609_ = v___x_1615_;
goto v___jp_1608_;
}
else
{
uint8_t v___x_1616_; uint8_t v___x_1617_; 
v___x_1616_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4);
v___x_1617_ = lean_uint8_dec_le(v___y_1557_, v___x_1616_);
v___y_1609_ = v___x_1617_;
goto v___jp_1608_;
}
v___jp_1558_:
{
if (v___y_1559_ == 0)
{
uint8_t v___x_1560_; uint8_t v___x_1561_; 
v___x_1560_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_1561_ = lean_uint8_dec_eq(v___y_1557_, v___x_1560_);
if (v___x_1561_ == 0)
{
uint8_t v___x_1562_; uint8_t v___x_1563_; 
v___x_1562_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_1563_ = lean_uint8_dec_eq(v___y_1557_, v___x_1562_);
return v___x_1563_;
}
else
{
return v___x_1561_;
}
}
else
{
return v___y_1559_;
}
}
v___jp_1564_:
{
if (v___y_1565_ == 0)
{
uint8_t v___x_1566_; uint8_t v___x_1567_; 
v___x_1566_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_1567_ = lean_uint8_dec_eq(v___y_1557_, v___x_1566_);
if (v___x_1567_ == 0)
{
uint8_t v___x_1568_; uint8_t v___x_1569_; 
v___x_1568_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_1569_ = lean_uint8_dec_eq(v___y_1557_, v___x_1568_);
if (v___x_1569_ == 0)
{
uint8_t v___x_1570_; uint8_t v___x_1571_; 
v___x_1570_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_1571_ = lean_uint8_dec_eq(v___y_1557_, v___x_1570_);
if (v___x_1571_ == 0)
{
uint8_t v___x_1572_; uint8_t v___x_1573_; 
v___x_1572_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_1573_ = lean_uint8_dec_eq(v___y_1557_, v___x_1572_);
if (v___x_1573_ == 0)
{
uint8_t v___x_1574_; uint8_t v___x_1575_; 
v___x_1574_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_1575_ = lean_uint8_dec_eq(v___y_1557_, v___x_1574_);
if (v___x_1575_ == 0)
{
uint8_t v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0);
v___x_1577_ = lean_uint8_dec_eq(v___y_1557_, v___x_1576_);
if (v___x_1577_ == 0)
{
uint8_t v___x_1578_; uint8_t v___x_1579_; 
v___x_1578_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_1579_ = lean_uint8_dec_eq(v___y_1557_, v___x_1578_);
if (v___x_1579_ == 0)
{
uint8_t v___x_1580_; uint8_t v___x_1581_; 
v___x_1580_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_1581_ = lean_uint8_dec_eq(v___y_1557_, v___x_1580_);
if (v___x_1581_ == 0)
{
uint8_t v___x_1582_; uint8_t v___x_1583_; 
v___x_1582_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_1583_ = lean_uint8_dec_eq(v___y_1557_, v___x_1582_);
v___y_1559_ = v___x_1583_;
goto v___jp_1558_;
}
else
{
v___y_1559_ = v___x_1581_;
goto v___jp_1558_;
}
}
else
{
v___y_1559_ = v___x_1579_;
goto v___jp_1558_;
}
}
else
{
v___y_1559_ = v___x_1577_;
goto v___jp_1558_;
}
}
else
{
v___y_1559_ = v___x_1575_;
goto v___jp_1558_;
}
}
else
{
v___y_1559_ = v___x_1573_;
goto v___jp_1558_;
}
}
else
{
v___y_1559_ = v___x_1571_;
goto v___jp_1558_;
}
}
else
{
v___y_1559_ = v___x_1569_;
goto v___jp_1558_;
}
}
else
{
v___y_1559_ = v___x_1567_;
goto v___jp_1558_;
}
}
else
{
return v___y_1565_;
}
}
v___jp_1584_:
{
if (v___y_1585_ == 0)
{
uint8_t v___x_1586_; uint8_t v___x_1587_; 
v___x_1586_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_1587_ = lean_uint8_dec_eq(v___y_1557_, v___x_1586_);
if (v___x_1587_ == 0)
{
uint8_t v___x_1588_; uint8_t v___x_1589_; 
v___x_1588_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_1589_ = lean_uint8_dec_eq(v___y_1557_, v___x_1588_);
v___y_1565_ = v___x_1589_;
goto v___jp_1564_;
}
else
{
v___y_1565_ = v___x_1587_;
goto v___jp_1564_;
}
}
else
{
return v___y_1585_;
}
}
v___jp_1590_:
{
if (v___y_1591_ == 0)
{
uint8_t v___x_1592_; uint8_t v___x_1593_; 
v___x_1592_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_1593_ = lean_uint8_dec_eq(v___y_1557_, v___x_1592_);
if (v___x_1593_ == 0)
{
uint8_t v___x_1594_; uint8_t v___x_1595_; 
v___x_1594_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_1595_ = lean_uint8_dec_eq(v___y_1557_, v___x_1594_);
v___y_1585_ = v___x_1595_;
goto v___jp_1584_;
}
else
{
v___y_1585_ = v___x_1593_;
goto v___jp_1584_;
}
}
else
{
return v___y_1591_;
}
}
v___jp_1596_:
{
if (v___y_1597_ == 0)
{
uint8_t v___x_1598_; uint8_t v___x_1599_; 
v___x_1598_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1);
v___x_1599_ = lean_uint8_dec_eq(v___y_1557_, v___x_1598_);
if (v___x_1599_ == 0)
{
uint8_t v___x_1600_; uint8_t v___x_1601_; 
v___x_1600_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2);
v___x_1601_ = lean_uint8_dec_eq(v___y_1557_, v___x_1600_);
v___y_1591_ = v___x_1601_;
goto v___jp_1590_;
}
else
{
v___y_1591_ = v___x_1599_;
goto v___jp_1590_;
}
}
else
{
return v___y_1597_;
}
}
v___jp_1602_:
{
if (v___y_1603_ == 0)
{
uint8_t v___x_1604_; uint8_t v___x_1605_; 
v___x_1604_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_1605_ = lean_uint8_dec_le(v___x_1604_, v___y_1557_);
if (v___x_1605_ == 0)
{
v___y_1597_ = v___x_1605_;
goto v___jp_1596_;
}
else
{
uint8_t v___x_1606_; uint8_t v___x_1607_; 
v___x_1606_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_1607_ = lean_uint8_dec_le(v___y_1557_, v___x_1606_);
v___y_1597_ = v___x_1607_;
goto v___jp_1596_;
}
}
else
{
return v___y_1603_;
}
}
v___jp_1608_:
{
if (v___y_1609_ == 0)
{
uint8_t v___x_1610_; uint8_t v___x_1611_; 
v___x_1610_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_1611_ = lean_uint8_dec_le(v___x_1610_, v___y_1557_);
if (v___x_1611_ == 0)
{
v___y_1603_ = v___x_1611_;
goto v___jp_1602_;
}
else
{
uint8_t v___x_1612_; uint8_t v___x_1613_; 
v___x_1612_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_1613_ = lean_uint8_dec_le(v___y_1557_, v___x_1612_);
v___y_1603_ = v___x_1613_;
goto v___jp_1602_;
}
}
else
{
return v___y_1609_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__1___boxed(lean_object* v___y_1618_){
_start:
{
uint8_t v___y_19202__boxed_1619_; uint8_t v_res_1620_; lean_object* v_r_1621_; 
v___y_19202__boxed_1619_ = lean_unbox(v___y_1618_);
v_res_1620_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__1(v___y_19202__boxed_1619_);
v_r_1621_ = lean_box(v_res_1620_);
return v_r_1621_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___f_1623_; lean_object* v___x_1624_; 
v___f_1623_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__0));
v___x_1624_ = l_Std_Http_URI_EncodedString_empty(v___f_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0(lean_object* v_config_1632_, lean_object* v_b_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v_array_1647_; lean_object* v_idx_1648_; lean_object* v_fst_1649_; lean_object* v_snd_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1852_; 
v_array_1647_ = lean_ctor_get(v___y_1634_, 0);
v_idx_1648_ = lean_ctor_get(v___y_1634_, 1);
v_fst_1649_ = lean_ctor_get(v_b_1633_, 0);
v_snd_1650_ = lean_ctor_get(v_b_1633_, 1);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_b_1633_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1652_ = v_b_1633_;
v_isShared_1653_ = v_isSharedCheck_1852_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_snd_1650_);
lean_inc(v_fst_1649_);
lean_dec(v_b_1633_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1852_;
goto v_resetjp_1651_;
}
v___jp_1635_:
{
lean_object* v___x_1639_; 
v___x_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___y_1637_);
lean_ctor_set(v___x_1639_, 1, v___y_1636_);
v_b_1633_ = v___x_1639_;
v___y_1634_ = v___y_1638_;
goto _start;
}
v___jp_1641_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___y_1644_);
lean_ctor_set(v___x_1645_, 1, v___y_1643_);
v___x_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___y_1642_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
return v___x_1646_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; uint8_t v___x_1655_; 
v___x_1654_ = lean_byte_array_size(v_array_1647_);
v___x_1655_ = lean_nat_dec_lt(v_idx_1648_, v___x_1654_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1657_; 
lean_dec_ref(v_config_1632_);
if (v_isShared_1653_ == 0)
{
v___x_1657_ = v___x_1652_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_fst_1649_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v_snd_1650_);
v___x_1657_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___y_1634_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
return v___x_1658_;
}
}
else
{
if (v___x_1655_ == 0)
{
lean_object* v___x_1661_; 
lean_dec_ref(v_config_1632_);
if (v_isShared_1653_ == 0)
{
v___x_1661_ = v___x_1652_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_fst_1649_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v_snd_1650_);
v___x_1661_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_object* v___x_1662_; 
v___x_1662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___y_1634_);
lean_ctor_set(v___x_1662_, 1, v___x_1661_);
return v___x_1662_;
}
}
else
{
uint8_t v___x_1664_; uint8_t v___x_1665_; 
v___x_1664_ = lean_byte_array_fget(v_array_1647_, v_idx_1648_);
v___x_1665_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__0(v___x_1664_);
if (v___x_1665_ == 0)
{
lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; uint8_t v___y_1779_; uint8_t v___y_1783_; uint8_t v___y_1787_; uint8_t v___y_1793_; uint8_t v___y_1813_; uint8_t v___y_1819_; uint8_t v___y_1825_; uint8_t v___y_1831_; uint8_t v___y_1837_; uint8_t v___x_1842_; uint8_t v___x_1843_; 
v___x_1842_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_1843_ = lean_uint8_dec_eq(v___x_1664_, v___x_1842_);
if (v___x_1843_ == 0)
{
uint8_t v___x_1844_; uint8_t v___x_1845_; 
v___x_1844_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3);
v___x_1845_ = lean_uint8_dec_le(v___x_1844_, v___x_1664_);
if (v___x_1845_ == 0)
{
v___y_1837_ = v___x_1845_;
goto v___jp_1836_;
}
else
{
uint8_t v___x_1846_; uint8_t v___x_1847_; 
v___x_1846_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4);
v___x_1847_ = lean_uint8_dec_le(v___x_1664_, v___x_1846_);
v___y_1837_ = v___x_1847_;
goto v___jp_1836_;
}
}
else
{
v___y_1779_ = v___x_1843_;
goto v___jp_1778_;
}
v___jp_1666_:
{
lean_object* v___x_1671_; uint8_t v___x_1672_; 
v___x_1671_ = lean_array_get_size(v___y_1668_);
v___x_1672_ = lean_nat_dec_le(v___y_1669_, v___x_1671_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1676_; 
lean_dec(v___y_1669_);
v___x_1673_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__1, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__1_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__1);
v___x_1674_ = lean_array_push(v___y_1668_, v___x_1673_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 1, v___y_1667_);
lean_ctor_set(v___x_1652_, 0, v___x_1674_);
v___x_1676_ = v___x_1652_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1674_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v___y_1667_);
v___x_1676_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
v_b_1633_ = v___x_1676_;
v___y_1634_ = v___y_1670_;
goto _start;
}
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_del_object(v___x_1652_);
lean_dec_ref(v_config_1632_);
v___x_1679_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__2));
v___x_1680_ = l_Nat_reprFast(v___y_1669_);
v___x_1681_ = lean_string_append(v___x_1679_, v___x_1680_);
lean_dec_ref(v___x_1680_);
v___x_1682_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__3));
v___x_1683_ = lean_string_append(v___x_1681_, v___x_1682_);
v___x_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1683_);
v___x_1685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___y_1670_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
return v___x_1685_;
}
}
v___jp_1686_:
{
lean_object* v_maxPathSegments_1687_; lean_object* v_maxTotalPathLength_1688_; lean_object* v___x_1689_; uint8_t v___x_1690_; 
v_maxPathSegments_1687_ = lean_ctor_get(v_config_1632_, 6);
v_maxTotalPathLength_1688_ = lean_ctor_get(v_config_1632_, 7);
v___x_1689_ = lean_array_get_size(v_fst_1649_);
v___x_1690_ = lean_nat_dec_le(v_maxPathSegments_1687_, v___x_1689_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; 
v___x_1691_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1632_, v___y_1634_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_pos_1692_; lean_object* v_res_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1761_; 
v_pos_1692_ = lean_ctor_get(v___x_1691_, 0);
v_res_1693_ = lean_ctor_get(v___x_1691_, 1);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1695_ = v___x_1691_;
v_isShared_1696_ = v_isSharedCheck_1761_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_res_1693_);
lean_inc(v_pos_1692_);
lean_dec(v___x_1691_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1761_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
lean_inc(v_res_1693_);
v___x_1697_ = l_ByteSlice_toByteArray(v_res_1693_);
v___x_1698_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_1697_);
if (lean_obj_tag(v___x_1698_) == 1)
{
lean_object* v_val_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1756_; 
v_val_1699_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1701_ = v___x_1698_;
v_isShared_1702_ = v_isSharedCheck_1756_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_val_1699_);
lean_dec(v___x_1698_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1756_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; 
v___x_1703_ = l_ByteSlice_size(v_res_1693_);
lean_dec(v_res_1693_);
v___x_1704_ = lean_nat_add(v_snd_1650_, v___x_1703_);
lean_dec(v___x_1703_);
lean_dec(v_snd_1650_);
v___x_1705_ = lean_nat_dec_lt(v_maxTotalPathLength_1688_, v___x_1704_);
if (v___x_1705_ == 0)
{
lean_object* v_array_1706_; lean_object* v_idx_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; uint8_t v___x_1710_; 
v_array_1706_ = lean_ctor_get(v_pos_1692_, 0);
v_idx_1707_ = lean_ctor_get(v_pos_1692_, 1);
v___x_1708_ = lean_array_push(v_fst_1649_, v_val_1699_);
v___x_1709_ = lean_byte_array_size(v_array_1706_);
v___x_1710_ = lean_nat_dec_lt(v_idx_1707_, v___x_1709_);
if (v___x_1710_ == 0)
{
lean_del_object(v___x_1701_);
lean_del_object(v___x_1695_);
lean_del_object(v___x_1652_);
lean_dec_ref(v_config_1632_);
v___y_1642_ = v_pos_1692_;
v___y_1643_ = v___x_1704_;
v___y_1644_ = v___x_1708_;
goto v___jp_1641_;
}
else
{
uint8_t v___x_1711_; uint8_t v___x_1712_; uint8_t v___x_1713_; 
v___x_1711_ = lean_byte_array_fget(v_array_1706_, v_idx_1707_);
v___x_1712_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_1713_ = lean_uint8_dec_eq(v___x_1711_, v___x_1712_);
if (v___x_1713_ == 0)
{
lean_del_object(v___x_1701_);
lean_del_object(v___x_1695_);
lean_del_object(v___x_1652_);
lean_dec_ref(v_config_1632_);
v___y_1642_ = v_pos_1692_;
v___y_1643_ = v___x_1704_;
v___y_1644_ = v___x_1708_;
goto v___jp_1641_;
}
else
{
lean_object* v___x_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; 
v___x_1714_ = lean_unsigned_to_nat(1u);
v___x_1715_ = lean_nat_add(v___x_1704_, v___x_1714_);
lean_dec(v___x_1704_);
v___x_1716_ = lean_nat_dec_lt(v_maxTotalPathLength_1688_, v___x_1715_);
if (v___x_1716_ == 0)
{
lean_del_object(v___x_1701_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1717_; lean_object* v___x_1719_; 
lean_dec(v___x_1715_);
lean_dec_ref(v___x_1708_);
lean_del_object(v___x_1652_);
lean_dec_ref(v_config_1632_);
v___x_1717_ = lean_box(0);
if (v_isShared_1696_ == 0)
{
lean_ctor_set_tag(v___x_1695_, 1);
lean_ctor_set(v___x_1695_, 1, v___x_1717_);
v___x_1719_ = v___x_1695_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_pos_1692_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v___x_1717_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
else
{
lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1731_; 
lean_inc(v_idx_1707_);
lean_inc_ref(v_array_1706_);
lean_del_object(v___x_1695_);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_pos_1692_);
if (v_isSharedCheck_1731_ == 0)
{
lean_object* v_unused_1732_; lean_object* v_unused_1733_; 
v_unused_1732_ = lean_ctor_get(v_pos_1692_, 1);
lean_dec(v_unused_1732_);
v_unused_1733_ = lean_ctor_get(v_pos_1692_, 0);
lean_dec(v_unused_1733_);
v___x_1722_ = v_pos_1692_;
v_isShared_1723_ = v_isSharedCheck_1731_;
goto v_resetjp_1721_;
}
else
{
lean_dec(v_pos_1692_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1731_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1724_; lean_object* v___x_1726_; 
v___x_1724_ = lean_nat_add(v_idx_1707_, v___x_1714_);
lean_dec(v_idx_1707_);
lean_inc(v___x_1724_);
lean_inc_ref(v_array_1706_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 1, v___x_1724_);
v___x_1726_ = v___x_1722_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_array_1706_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v___x_1724_);
v___x_1726_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
uint8_t v___x_1727_; 
v___x_1727_ = lean_nat_dec_lt(v___x_1724_, v___x_1709_);
if (v___x_1727_ == 0)
{
lean_dec(v___x_1724_);
lean_dec_ref(v_array_1706_);
if (v___x_1710_ == 0)
{
lean_del_object(v___x_1652_);
v___y_1636_ = v___x_1715_;
v___y_1637_ = v___x_1708_;
v___y_1638_ = v___x_1726_;
goto v___jp_1635_;
}
else
{
lean_inc(v_maxPathSegments_1687_);
v___y_1667_ = v___x_1715_;
v___y_1668_ = v___x_1708_;
v___y_1669_ = v_maxPathSegments_1687_;
v___y_1670_ = v___x_1726_;
goto v___jp_1666_;
}
}
else
{
uint8_t v___x_1728_; uint8_t v___x_1729_; 
v___x_1728_ = lean_byte_array_fget(v_array_1706_, v___x_1724_);
lean_dec(v___x_1724_);
lean_dec_ref(v_array_1706_);
v___x_1729_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__0(v___x_1728_);
if (v___x_1729_ == 0)
{
lean_del_object(v___x_1652_);
v___y_1636_ = v___x_1715_;
v___y_1637_ = v___x_1708_;
v___y_1638_ = v___x_1726_;
goto v___jp_1635_;
}
else
{
lean_inc(v_maxPathSegments_1687_);
v___y_1667_ = v___x_1715_;
v___y_1668_ = v___x_1708_;
v___y_1669_ = v_maxPathSegments_1687_;
v___y_1670_ = v___x_1726_;
goto v___jp_1666_;
}
}
}
}
}
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1740_; 
lean_inc(v_maxTotalPathLength_1688_);
lean_dec(v___x_1715_);
lean_dec_ref(v___x_1708_);
lean_del_object(v___x_1652_);
lean_dec_ref(v_config_1632_);
v___x_1734_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__4));
v___x_1735_ = l_Nat_reprFast(v_maxTotalPathLength_1688_);
v___x_1736_ = lean_string_append(v___x_1734_, v___x_1735_);
lean_dec_ref(v___x_1735_);
v___x_1737_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__5));
v___x_1738_ = lean_string_append(v___x_1736_, v___x_1737_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v___x_1738_);
v___x_1740_ = v___x_1701_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v___x_1742_; 
if (v_isShared_1696_ == 0)
{
lean_ctor_set_tag(v___x_1695_, 1);
lean_ctor_set(v___x_1695_, 1, v___x_1740_);
v___x_1742_ = v___x_1695_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_pos_1692_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v___x_1740_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
}
}
else
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1751_; 
lean_inc(v_maxTotalPathLength_1688_);
lean_dec(v___x_1704_);
lean_dec(v_val_1699_);
lean_del_object(v___x_1652_);
lean_dec(v_fst_1649_);
lean_dec_ref(v_config_1632_);
v___x_1745_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__4));
v___x_1746_ = l_Nat_reprFast(v_maxTotalPathLength_1688_);
v___x_1747_ = lean_string_append(v___x_1745_, v___x_1746_);
lean_dec_ref(v___x_1746_);
v___x_1748_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__5));
v___x_1749_ = lean_string_append(v___x_1747_, v___x_1748_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v___x_1749_);
v___x_1751_ = v___x_1701_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1749_);
v___x_1751_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
lean_object* v___x_1753_; 
if (v_isShared_1696_ == 0)
{
lean_ctor_set_tag(v___x_1695_, 1);
lean_ctor_set(v___x_1695_, 1, v___x_1751_);
v___x_1753_ = v___x_1695_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_pos_1692_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v___x_1751_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
}
else
{
lean_object* v___x_1757_; lean_object* v___x_1759_; 
lean_dec(v___x_1698_);
lean_dec(v_res_1693_);
lean_del_object(v___x_1652_);
lean_dec(v_snd_1650_);
lean_dec(v_fst_1649_);
lean_dec_ref(v_config_1632_);
v___x_1757_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__7));
if (v_isShared_1696_ == 0)
{
lean_ctor_set_tag(v___x_1695_, 1);
lean_ctor_set(v___x_1695_, 1, v___x_1757_);
v___x_1759_ = v___x_1695_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_pos_1692_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v___x_1757_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
else
{
lean_object* v_pos_1762_; lean_object* v_err_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
lean_del_object(v___x_1652_);
lean_dec(v_snd_1650_);
lean_dec(v_fst_1649_);
lean_dec_ref(v_config_1632_);
v_pos_1762_ = lean_ctor_get(v___x_1691_, 0);
v_err_1763_ = lean_ctor_get(v___x_1691_, 1);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1691_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_err_1763_);
lean_inc(v_pos_1762_);
lean_dec(v___x_1691_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_pos_1762_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_err_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
else
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
lean_inc(v_maxPathSegments_1687_);
lean_del_object(v___x_1652_);
lean_dec(v_snd_1650_);
lean_dec(v_fst_1649_);
lean_dec_ref(v_config_1632_);
v___x_1771_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__2));
v___x_1772_ = l_Nat_reprFast(v_maxPathSegments_1687_);
v___x_1773_ = lean_string_append(v___x_1771_, v___x_1772_);
lean_dec_ref(v___x_1772_);
v___x_1774_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__3));
v___x_1775_ = lean_string_append(v___x_1773_, v___x_1774_);
v___x_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
v___x_1777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___y_1634_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
return v___x_1777_;
}
}
v___jp_1778_:
{
if (v___y_1779_ == 0)
{
if (v___x_1655_ == 0)
{
goto v___jp_1686_;
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
lean_del_object(v___x_1652_);
lean_dec_ref(v_config_1632_);
v___x_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1780_, 0, v_fst_1649_);
lean_ctor_set(v___x_1780_, 1, v_snd_1650_);
v___x_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___y_1634_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
return v___x_1781_;
}
}
else
{
goto v___jp_1686_;
}
}
v___jp_1782_:
{
if (v___y_1783_ == 0)
{
uint8_t v___x_1784_; uint8_t v___x_1785_; 
v___x_1784_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_1785_ = lean_uint8_dec_eq(v___x_1664_, v___x_1784_);
if (v___x_1785_ == 0)
{
v___y_1779_ = v___x_1785_;
goto v___jp_1778_;
}
else
{
v___y_1779_ = v___x_1655_;
goto v___jp_1778_;
}
}
else
{
v___y_1779_ = v___x_1655_;
goto v___jp_1778_;
}
}
v___jp_1786_:
{
if (v___y_1787_ == 0)
{
uint8_t v___x_1788_; uint8_t v___x_1789_; 
v___x_1788_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_1789_ = lean_uint8_dec_eq(v___x_1664_, v___x_1788_);
if (v___x_1789_ == 0)
{
uint8_t v___x_1790_; uint8_t v___x_1791_; 
v___x_1790_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_1791_ = lean_uint8_dec_eq(v___x_1664_, v___x_1790_);
v___y_1783_ = v___x_1791_;
goto v___jp_1782_;
}
else
{
v___y_1783_ = v___x_1789_;
goto v___jp_1782_;
}
}
else
{
v___y_1779_ = v___x_1655_;
goto v___jp_1778_;
}
}
v___jp_1792_:
{
if (v___y_1793_ == 0)
{
uint8_t v___x_1794_; uint8_t v___x_1795_; 
v___x_1794_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_1795_ = lean_uint8_dec_eq(v___x_1664_, v___x_1794_);
if (v___x_1795_ == 0)
{
uint8_t v___x_1796_; uint8_t v___x_1797_; 
v___x_1796_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_1797_ = lean_uint8_dec_eq(v___x_1664_, v___x_1796_);
if (v___x_1797_ == 0)
{
uint8_t v___x_1798_; uint8_t v___x_1799_; 
v___x_1798_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_1799_ = lean_uint8_dec_eq(v___x_1664_, v___x_1798_);
if (v___x_1799_ == 0)
{
uint8_t v___x_1800_; uint8_t v___x_1801_; 
v___x_1800_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_1801_ = lean_uint8_dec_eq(v___x_1664_, v___x_1800_);
if (v___x_1801_ == 0)
{
uint8_t v___x_1802_; uint8_t v___x_1803_; 
v___x_1802_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_1803_ = lean_uint8_dec_eq(v___x_1664_, v___x_1802_);
if (v___x_1803_ == 0)
{
uint8_t v___x_1804_; uint8_t v___x_1805_; 
v___x_1804_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0);
v___x_1805_ = lean_uint8_dec_eq(v___x_1664_, v___x_1804_);
if (v___x_1805_ == 0)
{
uint8_t v___x_1806_; uint8_t v___x_1807_; 
v___x_1806_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_1807_ = lean_uint8_dec_eq(v___x_1664_, v___x_1806_);
if (v___x_1807_ == 0)
{
uint8_t v___x_1808_; uint8_t v___x_1809_; 
v___x_1808_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_1809_ = lean_uint8_dec_eq(v___x_1664_, v___x_1808_);
if (v___x_1809_ == 0)
{
uint8_t v___x_1810_; uint8_t v___x_1811_; 
v___x_1810_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_1811_ = lean_uint8_dec_eq(v___x_1664_, v___x_1810_);
v___y_1787_ = v___x_1811_;
goto v___jp_1786_;
}
else
{
v___y_1787_ = v___x_1809_;
goto v___jp_1786_;
}
}
else
{
v___y_1787_ = v___x_1807_;
goto v___jp_1786_;
}
}
else
{
v___y_1787_ = v___x_1805_;
goto v___jp_1786_;
}
}
else
{
v___y_1787_ = v___x_1803_;
goto v___jp_1786_;
}
}
else
{
v___y_1787_ = v___x_1801_;
goto v___jp_1786_;
}
}
else
{
v___y_1787_ = v___x_1799_;
goto v___jp_1786_;
}
}
else
{
v___y_1787_ = v___x_1797_;
goto v___jp_1786_;
}
}
else
{
v___y_1787_ = v___x_1795_;
goto v___jp_1786_;
}
}
else
{
v___y_1779_ = v___x_1655_;
goto v___jp_1778_;
}
}
v___jp_1812_:
{
if (v___y_1813_ == 0)
{
uint8_t v___x_1814_; uint8_t v___x_1815_; 
v___x_1814_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_1815_ = lean_uint8_dec_eq(v___x_1664_, v___x_1814_);
if (v___x_1815_ == 0)
{
uint8_t v___x_1816_; uint8_t v___x_1817_; 
v___x_1816_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_1817_ = lean_uint8_dec_eq(v___x_1664_, v___x_1816_);
v___y_1793_ = v___x_1817_;
goto v___jp_1792_;
}
else
{
v___y_1793_ = v___x_1815_;
goto v___jp_1792_;
}
}
else
{
v___y_1779_ = v___x_1655_;
goto v___jp_1778_;
}
}
v___jp_1818_:
{
if (v___y_1819_ == 0)
{
uint8_t v___x_1820_; uint8_t v___x_1821_; 
v___x_1820_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_1821_ = lean_uint8_dec_eq(v___x_1664_, v___x_1820_);
if (v___x_1821_ == 0)
{
uint8_t v___x_1822_; uint8_t v___x_1823_; 
v___x_1822_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_1823_ = lean_uint8_dec_eq(v___x_1664_, v___x_1822_);
v___y_1813_ = v___x_1823_;
goto v___jp_1812_;
}
else
{
v___y_1813_ = v___x_1821_;
goto v___jp_1812_;
}
}
else
{
v___y_1779_ = v___x_1655_;
goto v___jp_1778_;
}
}
v___jp_1824_:
{
if (v___y_1825_ == 0)
{
uint8_t v___x_1826_; uint8_t v___x_1827_; 
v___x_1826_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1);
v___x_1827_ = lean_uint8_dec_eq(v___x_1664_, v___x_1826_);
if (v___x_1827_ == 0)
{
uint8_t v___x_1828_; uint8_t v___x_1829_; 
v___x_1828_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2);
v___x_1829_ = lean_uint8_dec_eq(v___x_1664_, v___x_1828_);
v___y_1819_ = v___x_1829_;
goto v___jp_1818_;
}
else
{
v___y_1819_ = v___x_1827_;
goto v___jp_1818_;
}
}
else
{
v___y_1779_ = v___x_1655_;
goto v___jp_1778_;
}
}
v___jp_1830_:
{
if (v___y_1831_ == 0)
{
uint8_t v___x_1832_; uint8_t v___x_1833_; 
v___x_1832_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_1833_ = lean_uint8_dec_le(v___x_1832_, v___x_1664_);
if (v___x_1833_ == 0)
{
v___y_1825_ = v___x_1833_;
goto v___jp_1824_;
}
else
{
uint8_t v___x_1834_; uint8_t v___x_1835_; 
v___x_1834_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_1835_ = lean_uint8_dec_le(v___x_1664_, v___x_1834_);
v___y_1825_ = v___x_1835_;
goto v___jp_1824_;
}
}
else
{
v___y_1779_ = v___x_1655_;
goto v___jp_1778_;
}
}
v___jp_1836_:
{
if (v___y_1837_ == 0)
{
uint8_t v___x_1838_; uint8_t v___x_1839_; 
v___x_1838_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_1839_ = lean_uint8_dec_le(v___x_1838_, v___x_1664_);
if (v___x_1839_ == 0)
{
v___y_1831_ = v___x_1839_;
goto v___jp_1830_;
}
else
{
uint8_t v___x_1840_; uint8_t v___x_1841_; 
v___x_1840_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_1841_ = lean_uint8_dec_le(v___x_1664_, v___x_1840_);
v___y_1831_ = v___x_1841_;
goto v___jp_1830_;
}
}
else
{
v___y_1779_ = v___x_1655_;
goto v___jp_1778_;
}
}
}
else
{
lean_object* v___x_1849_; 
lean_dec_ref(v_config_1632_);
if (v_isShared_1653_ == 0)
{
v___x_1849_ = v___x_1652_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_fst_1649_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_snd_1650_);
v___x_1849_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1850_; 
v___x_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___y_1634_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
return v___x_1850_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0(lean_object* v_config_1853_, lean_object* v_b_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v_array_1868_; lean_object* v_idx_1869_; lean_object* v_fst_1870_; lean_object* v_snd_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_2073_; 
v_array_1868_ = lean_ctor_get(v___y_1855_, 0);
v_idx_1869_ = lean_ctor_get(v___y_1855_, 1);
v_fst_1870_ = lean_ctor_get(v_b_1854_, 0);
v_snd_1871_ = lean_ctor_get(v_b_1854_, 1);
v_isSharedCheck_2073_ = !lean_is_exclusive(v_b_1854_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_1873_ = v_b_1854_;
v_isShared_1874_ = v_isSharedCheck_2073_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_snd_1871_);
lean_inc(v_fst_1870_);
lean_dec(v_b_1854_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_2073_;
goto v_resetjp_1872_;
}
v___jp_1856_:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___y_1857_);
lean_ctor_set(v___x_1860_, 1, v___y_1859_);
v___x_1861_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0(v_config_1853_, v___x_1860_, v___y_1858_);
return v___x_1861_;
}
v___jp_1862_:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___y_1863_);
lean_ctor_set(v___x_1866_, 1, v___y_1864_);
v___x_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___y_1865_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
return v___x_1867_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; uint8_t v___x_1876_; 
v___x_1875_ = lean_byte_array_size(v_array_1868_);
v___x_1876_ = lean_nat_dec_lt(v_idx_1869_, v___x_1875_);
if (v___x_1876_ == 0)
{
lean_object* v___x_1878_; 
lean_dec_ref(v_config_1853_);
if (v_isShared_1874_ == 0)
{
v___x_1878_ = v___x_1873_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_fst_1870_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_snd_1871_);
v___x_1878_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1879_; 
v___x_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___y_1855_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
return v___x_1879_;
}
}
else
{
if (v___x_1876_ == 0)
{
lean_object* v___x_1882_; 
lean_dec_ref(v_config_1853_);
if (v_isShared_1874_ == 0)
{
v___x_1882_ = v___x_1873_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_fst_1870_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_snd_1871_);
v___x_1882_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
lean_object* v___x_1883_; 
v___x_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___y_1855_);
lean_ctor_set(v___x_1883_, 1, v___x_1882_);
return v___x_1883_;
}
}
else
{
uint8_t v___x_1885_; uint8_t v___x_1886_; 
v___x_1885_ = lean_byte_array_fget(v_array_1868_, v_idx_1869_);
v___x_1886_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__0(v___x_1885_);
if (v___x_1886_ == 0)
{
lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; uint8_t v___y_2000_; uint8_t v___y_2004_; uint8_t v___y_2008_; uint8_t v___y_2014_; uint8_t v___y_2034_; uint8_t v___y_2040_; uint8_t v___y_2046_; uint8_t v___y_2052_; uint8_t v___y_2058_; uint8_t v___x_2063_; uint8_t v___x_2064_; 
v___x_2063_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2064_ = lean_uint8_dec_eq(v___x_1885_, v___x_2063_);
if (v___x_2064_ == 0)
{
uint8_t v___x_2065_; uint8_t v___x_2066_; 
v___x_2065_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3);
v___x_2066_ = lean_uint8_dec_le(v___x_2065_, v___x_1885_);
if (v___x_2066_ == 0)
{
v___y_2058_ = v___x_2066_;
goto v___jp_2057_;
}
else
{
uint8_t v___x_2067_; uint8_t v___x_2068_; 
v___x_2067_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4);
v___x_2068_ = lean_uint8_dec_le(v___x_1885_, v___x_2067_);
v___y_2058_ = v___x_2068_;
goto v___jp_2057_;
}
}
else
{
v___y_2000_ = v___x_2064_;
goto v___jp_1999_;
}
v___jp_1887_:
{
lean_object* v___x_1892_; uint8_t v___x_1893_; 
v___x_1892_ = lean_array_get_size(v___y_1888_);
v___x_1893_ = lean_nat_dec_le(v___y_1889_, v___x_1892_);
if (v___x_1893_ == 0)
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1897_; 
lean_dec(v___y_1889_);
v___x_1894_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__1, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__1_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__1);
v___x_1895_ = lean_array_push(v___y_1888_, v___x_1894_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 1, v___y_1891_);
lean_ctor_set(v___x_1873_, 0, v___x_1895_);
v___x_1897_ = v___x_1873_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1895_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v___y_1891_);
v___x_1897_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
lean_object* v___x_1898_; 
v___x_1898_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0(v_config_1853_, v___x_1897_, v___y_1890_);
return v___x_1898_;
}
}
else
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1888_);
lean_del_object(v___x_1873_);
lean_dec_ref(v_config_1853_);
v___x_1900_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__2));
v___x_1901_ = l_Nat_reprFast(v___y_1889_);
v___x_1902_ = lean_string_append(v___x_1900_, v___x_1901_);
lean_dec_ref(v___x_1901_);
v___x_1903_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__3));
v___x_1904_ = lean_string_append(v___x_1902_, v___x_1903_);
v___x_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
v___x_1906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___y_1890_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
return v___x_1906_;
}
}
v___jp_1907_:
{
lean_object* v_maxPathSegments_1908_; lean_object* v_maxTotalPathLength_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; 
v_maxPathSegments_1908_ = lean_ctor_get(v_config_1853_, 6);
v_maxTotalPathLength_1909_ = lean_ctor_get(v_config_1853_, 7);
v___x_1910_ = lean_array_get_size(v_fst_1870_);
v___x_1911_ = lean_nat_dec_le(v_maxPathSegments_1908_, v___x_1910_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1912_; 
v___x_1912_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1853_, v___y_1855_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_pos_1913_; lean_object* v_res_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1982_; 
v_pos_1913_ = lean_ctor_get(v___x_1912_, 0);
v_res_1914_ = lean_ctor_get(v___x_1912_, 1);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1916_ = v___x_1912_;
v_isShared_1917_ = v_isSharedCheck_1982_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_res_1914_);
lean_inc(v_pos_1913_);
lean_dec(v___x_1912_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1982_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
lean_inc(v_res_1914_);
v___x_1918_ = l_ByteSlice_toByteArray(v_res_1914_);
v___x_1919_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_1918_);
if (lean_obj_tag(v___x_1919_) == 1)
{
lean_object* v_val_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1977_; 
v_val_1920_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1922_ = v___x_1919_;
v_isShared_1923_ = v_isSharedCheck_1977_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_val_1920_);
lean_dec(v___x_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1977_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; uint8_t v___x_1926_; 
v___x_1924_ = l_ByteSlice_size(v_res_1914_);
lean_dec(v_res_1914_);
v___x_1925_ = lean_nat_add(v_snd_1871_, v___x_1924_);
lean_dec(v___x_1924_);
lean_dec(v_snd_1871_);
v___x_1926_ = lean_nat_dec_lt(v_maxTotalPathLength_1909_, v___x_1925_);
if (v___x_1926_ == 0)
{
lean_object* v_array_1927_; lean_object* v_idx_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; 
v_array_1927_ = lean_ctor_get(v_pos_1913_, 0);
v_idx_1928_ = lean_ctor_get(v_pos_1913_, 1);
v___x_1929_ = lean_array_push(v_fst_1870_, v_val_1920_);
v___x_1930_ = lean_byte_array_size(v_array_1927_);
v___x_1931_ = lean_nat_dec_lt(v_idx_1928_, v___x_1930_);
if (v___x_1931_ == 0)
{
lean_del_object(v___x_1922_);
lean_del_object(v___x_1916_);
lean_del_object(v___x_1873_);
lean_dec_ref(v_config_1853_);
v___y_1863_ = v___x_1929_;
v___y_1864_ = v___x_1925_;
v___y_1865_ = v_pos_1913_;
goto v___jp_1862_;
}
else
{
uint8_t v___x_1932_; uint8_t v___x_1933_; uint8_t v___x_1934_; 
v___x_1932_ = lean_byte_array_fget(v_array_1927_, v_idx_1928_);
v___x_1933_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_1934_ = lean_uint8_dec_eq(v___x_1932_, v___x_1933_);
if (v___x_1934_ == 0)
{
lean_del_object(v___x_1922_);
lean_del_object(v___x_1916_);
lean_del_object(v___x_1873_);
lean_dec_ref(v_config_1853_);
v___y_1863_ = v___x_1929_;
v___y_1864_ = v___x_1925_;
v___y_1865_ = v_pos_1913_;
goto v___jp_1862_;
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; 
v___x_1935_ = lean_unsigned_to_nat(1u);
v___x_1936_ = lean_nat_add(v___x_1925_, v___x_1935_);
lean_dec(v___x_1925_);
v___x_1937_ = lean_nat_dec_lt(v_maxTotalPathLength_1909_, v___x_1936_);
if (v___x_1937_ == 0)
{
lean_del_object(v___x_1922_);
if (v___x_1931_ == 0)
{
lean_object* v___x_1938_; lean_object* v___x_1940_; 
lean_dec(v___x_1936_);
lean_dec_ref(v___x_1929_);
lean_del_object(v___x_1873_);
lean_dec_ref(v_config_1853_);
v___x_1938_ = lean_box(0);
if (v_isShared_1917_ == 0)
{
lean_ctor_set_tag(v___x_1916_, 1);
lean_ctor_set(v___x_1916_, 1, v___x_1938_);
v___x_1940_ = v___x_1916_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_pos_1913_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v___x_1938_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
else
{
lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1952_; 
lean_inc(v_idx_1928_);
lean_inc_ref(v_array_1927_);
lean_del_object(v___x_1916_);
v_isSharedCheck_1952_ = !lean_is_exclusive(v_pos_1913_);
if (v_isSharedCheck_1952_ == 0)
{
lean_object* v_unused_1953_; lean_object* v_unused_1954_; 
v_unused_1953_ = lean_ctor_get(v_pos_1913_, 1);
lean_dec(v_unused_1953_);
v_unused_1954_ = lean_ctor_get(v_pos_1913_, 0);
lean_dec(v_unused_1954_);
v___x_1943_ = v_pos_1913_;
v_isShared_1944_ = v_isSharedCheck_1952_;
goto v_resetjp_1942_;
}
else
{
lean_dec(v_pos_1913_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1952_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1945_; lean_object* v___x_1947_; 
v___x_1945_ = lean_nat_add(v_idx_1928_, v___x_1935_);
lean_dec(v_idx_1928_);
lean_inc(v___x_1945_);
lean_inc_ref(v_array_1927_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 1, v___x_1945_);
v___x_1947_ = v___x_1943_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_array_1927_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v___x_1945_);
v___x_1947_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
uint8_t v___x_1948_; 
v___x_1948_ = lean_nat_dec_lt(v___x_1945_, v___x_1930_);
if (v___x_1948_ == 0)
{
lean_dec(v___x_1945_);
lean_dec_ref(v_array_1927_);
if (v___x_1931_ == 0)
{
lean_del_object(v___x_1873_);
v___y_1857_ = v___x_1929_;
v___y_1858_ = v___x_1947_;
v___y_1859_ = v___x_1936_;
goto v___jp_1856_;
}
else
{
lean_inc(v_maxPathSegments_1908_);
v___y_1888_ = v___x_1929_;
v___y_1889_ = v_maxPathSegments_1908_;
v___y_1890_ = v___x_1947_;
v___y_1891_ = v___x_1936_;
goto v___jp_1887_;
}
}
else
{
uint8_t v___x_1949_; uint8_t v___x_1950_; 
v___x_1949_ = lean_byte_array_fget(v_array_1927_, v___x_1945_);
lean_dec(v___x_1945_);
lean_dec_ref(v_array_1927_);
v___x_1950_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__0(v___x_1949_);
if (v___x_1950_ == 0)
{
lean_del_object(v___x_1873_);
v___y_1857_ = v___x_1929_;
v___y_1858_ = v___x_1947_;
v___y_1859_ = v___x_1936_;
goto v___jp_1856_;
}
else
{
lean_inc(v_maxPathSegments_1908_);
v___y_1888_ = v___x_1929_;
v___y_1889_ = v_maxPathSegments_1908_;
v___y_1890_ = v___x_1947_;
v___y_1891_ = v___x_1936_;
goto v___jp_1887_;
}
}
}
}
}
}
else
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1961_; 
lean_inc(v_maxTotalPathLength_1909_);
lean_dec(v___x_1936_);
lean_dec_ref(v___x_1929_);
lean_del_object(v___x_1873_);
lean_dec_ref(v_config_1853_);
v___x_1955_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__4));
v___x_1956_ = l_Nat_reprFast(v_maxTotalPathLength_1909_);
v___x_1957_ = lean_string_append(v___x_1955_, v___x_1956_);
lean_dec_ref(v___x_1956_);
v___x_1958_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__5));
v___x_1959_ = lean_string_append(v___x_1957_, v___x_1958_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v___x_1959_);
v___x_1961_ = v___x_1922_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1959_);
v___x_1961_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
lean_object* v___x_1963_; 
if (v_isShared_1917_ == 0)
{
lean_ctor_set_tag(v___x_1916_, 1);
lean_ctor_set(v___x_1916_, 1, v___x_1961_);
v___x_1963_ = v___x_1916_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_pos_1913_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
}
}
else
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1972_; 
lean_inc(v_maxTotalPathLength_1909_);
lean_dec(v___x_1925_);
lean_dec(v_val_1920_);
lean_del_object(v___x_1873_);
lean_dec(v_fst_1870_);
lean_dec_ref(v_config_1853_);
v___x_1966_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__4));
v___x_1967_ = l_Nat_reprFast(v_maxTotalPathLength_1909_);
v___x_1968_ = lean_string_append(v___x_1966_, v___x_1967_);
lean_dec_ref(v___x_1967_);
v___x_1969_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__5));
v___x_1970_ = lean_string_append(v___x_1968_, v___x_1969_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v___x_1970_);
v___x_1972_ = v___x_1922_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
lean_object* v___x_1974_; 
if (v_isShared_1917_ == 0)
{
lean_ctor_set_tag(v___x_1916_, 1);
lean_ctor_set(v___x_1916_, 1, v___x_1972_);
v___x_1974_ = v___x_1916_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_pos_1913_);
lean_ctor_set(v_reuseFailAlloc_1975_, 1, v___x_1972_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
}
else
{
lean_object* v___x_1978_; lean_object* v___x_1980_; 
lean_dec(v___x_1919_);
lean_dec(v_res_1914_);
lean_del_object(v___x_1873_);
lean_dec(v_snd_1871_);
lean_dec(v_fst_1870_);
lean_dec_ref(v_config_1853_);
v___x_1978_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__7));
if (v_isShared_1917_ == 0)
{
lean_ctor_set_tag(v___x_1916_, 1);
lean_ctor_set(v___x_1916_, 1, v___x_1978_);
v___x_1980_ = v___x_1916_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_pos_1913_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v___x_1978_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
else
{
lean_object* v_pos_1983_; lean_object* v_err_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_del_object(v___x_1873_);
lean_dec(v_snd_1871_);
lean_dec(v_fst_1870_);
lean_dec_ref(v_config_1853_);
v_pos_1983_ = lean_ctor_get(v___x_1912_, 0);
v_err_1984_ = lean_ctor_get(v___x_1912_, 1);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1912_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_err_1984_);
lean_inc(v_pos_1983_);
lean_dec(v___x_1912_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_pos_1983_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_err_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
else
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
lean_inc(v_maxPathSegments_1908_);
lean_del_object(v___x_1873_);
lean_dec(v_snd_1871_);
lean_dec(v_fst_1870_);
lean_dec_ref(v_config_1853_);
v___x_1992_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__2));
v___x_1993_ = l_Nat_reprFast(v_maxPathSegments_1908_);
v___x_1994_ = lean_string_append(v___x_1992_, v___x_1993_);
lean_dec_ref(v___x_1993_);
v___x_1995_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__3));
v___x_1996_ = lean_string_append(v___x_1994_, v___x_1995_);
v___x_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
v___x_1998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___y_1855_);
lean_ctor_set(v___x_1998_, 1, v___x_1997_);
return v___x_1998_;
}
}
v___jp_1999_:
{
if (v___y_2000_ == 0)
{
if (v___x_1876_ == 0)
{
goto v___jp_1907_;
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
lean_del_object(v___x_1873_);
lean_dec_ref(v_config_1853_);
v___x_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2001_, 0, v_fst_1870_);
lean_ctor_set(v___x_2001_, 1, v_snd_1871_);
v___x_2002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___y_1855_);
lean_ctor_set(v___x_2002_, 1, v___x_2001_);
return v___x_2002_;
}
}
else
{
goto v___jp_1907_;
}
}
v___jp_2003_:
{
if (v___y_2004_ == 0)
{
uint8_t v___x_2005_; uint8_t v___x_2006_; 
v___x_2005_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_2006_ = lean_uint8_dec_eq(v___x_1885_, v___x_2005_);
if (v___x_2006_ == 0)
{
v___y_2000_ = v___x_2006_;
goto v___jp_1999_;
}
else
{
v___y_2000_ = v___x_1876_;
goto v___jp_1999_;
}
}
else
{
v___y_2000_ = v___x_1876_;
goto v___jp_1999_;
}
}
v___jp_2007_:
{
if (v___y_2008_ == 0)
{
uint8_t v___x_2009_; uint8_t v___x_2010_; 
v___x_2009_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_2010_ = lean_uint8_dec_eq(v___x_1885_, v___x_2009_);
if (v___x_2010_ == 0)
{
uint8_t v___x_2011_; uint8_t v___x_2012_; 
v___x_2011_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_2012_ = lean_uint8_dec_eq(v___x_1885_, v___x_2011_);
v___y_2004_ = v___x_2012_;
goto v___jp_2003_;
}
else
{
v___y_2004_ = v___x_2010_;
goto v___jp_2003_;
}
}
else
{
v___y_2000_ = v___x_1876_;
goto v___jp_1999_;
}
}
v___jp_2013_:
{
if (v___y_2014_ == 0)
{
uint8_t v___x_2015_; uint8_t v___x_2016_; 
v___x_2015_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_2016_ = lean_uint8_dec_eq(v___x_1885_, v___x_2015_);
if (v___x_2016_ == 0)
{
uint8_t v___x_2017_; uint8_t v___x_2018_; 
v___x_2017_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_2018_ = lean_uint8_dec_eq(v___x_1885_, v___x_2017_);
if (v___x_2018_ == 0)
{
uint8_t v___x_2019_; uint8_t v___x_2020_; 
v___x_2019_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_2020_ = lean_uint8_dec_eq(v___x_1885_, v___x_2019_);
if (v___x_2020_ == 0)
{
uint8_t v___x_2021_; uint8_t v___x_2022_; 
v___x_2021_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_2022_ = lean_uint8_dec_eq(v___x_1885_, v___x_2021_);
if (v___x_2022_ == 0)
{
uint8_t v___x_2023_; uint8_t v___x_2024_; 
v___x_2023_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_2024_ = lean_uint8_dec_eq(v___x_1885_, v___x_2023_);
if (v___x_2024_ == 0)
{
uint8_t v___x_2025_; uint8_t v___x_2026_; 
v___x_2025_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0);
v___x_2026_ = lean_uint8_dec_eq(v___x_1885_, v___x_2025_);
if (v___x_2026_ == 0)
{
uint8_t v___x_2027_; uint8_t v___x_2028_; 
v___x_2027_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_2028_ = lean_uint8_dec_eq(v___x_1885_, v___x_2027_);
if (v___x_2028_ == 0)
{
uint8_t v___x_2029_; uint8_t v___x_2030_; 
v___x_2029_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_2030_ = lean_uint8_dec_eq(v___x_1885_, v___x_2029_);
if (v___x_2030_ == 0)
{
uint8_t v___x_2031_; uint8_t v___x_2032_; 
v___x_2031_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_2032_ = lean_uint8_dec_eq(v___x_1885_, v___x_2031_);
v___y_2008_ = v___x_2032_;
goto v___jp_2007_;
}
else
{
v___y_2008_ = v___x_2030_;
goto v___jp_2007_;
}
}
else
{
v___y_2008_ = v___x_2028_;
goto v___jp_2007_;
}
}
else
{
v___y_2008_ = v___x_2026_;
goto v___jp_2007_;
}
}
else
{
v___y_2008_ = v___x_2024_;
goto v___jp_2007_;
}
}
else
{
v___y_2008_ = v___x_2022_;
goto v___jp_2007_;
}
}
else
{
v___y_2008_ = v___x_2020_;
goto v___jp_2007_;
}
}
else
{
v___y_2008_ = v___x_2018_;
goto v___jp_2007_;
}
}
else
{
v___y_2008_ = v___x_2016_;
goto v___jp_2007_;
}
}
else
{
v___y_2000_ = v___x_1876_;
goto v___jp_1999_;
}
}
v___jp_2033_:
{
if (v___y_2034_ == 0)
{
uint8_t v___x_2035_; uint8_t v___x_2036_; 
v___x_2035_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_2036_ = lean_uint8_dec_eq(v___x_1885_, v___x_2035_);
if (v___x_2036_ == 0)
{
uint8_t v___x_2037_; uint8_t v___x_2038_; 
v___x_2037_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_2038_ = lean_uint8_dec_eq(v___x_1885_, v___x_2037_);
v___y_2014_ = v___x_2038_;
goto v___jp_2013_;
}
else
{
v___y_2014_ = v___x_2036_;
goto v___jp_2013_;
}
}
else
{
v___y_2000_ = v___x_1876_;
goto v___jp_1999_;
}
}
v___jp_2039_:
{
if (v___y_2040_ == 0)
{
uint8_t v___x_2041_; uint8_t v___x_2042_; 
v___x_2041_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_2042_ = lean_uint8_dec_eq(v___x_1885_, v___x_2041_);
if (v___x_2042_ == 0)
{
uint8_t v___x_2043_; uint8_t v___x_2044_; 
v___x_2043_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_2044_ = lean_uint8_dec_eq(v___x_1885_, v___x_2043_);
v___y_2034_ = v___x_2044_;
goto v___jp_2033_;
}
else
{
v___y_2034_ = v___x_2042_;
goto v___jp_2033_;
}
}
else
{
v___y_2000_ = v___x_1876_;
goto v___jp_1999_;
}
}
v___jp_2045_:
{
if (v___y_2046_ == 0)
{
uint8_t v___x_2047_; uint8_t v___x_2048_; 
v___x_2047_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1);
v___x_2048_ = lean_uint8_dec_eq(v___x_1885_, v___x_2047_);
if (v___x_2048_ == 0)
{
uint8_t v___x_2049_; uint8_t v___x_2050_; 
v___x_2049_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2);
v___x_2050_ = lean_uint8_dec_eq(v___x_1885_, v___x_2049_);
v___y_2040_ = v___x_2050_;
goto v___jp_2039_;
}
else
{
v___y_2040_ = v___x_2048_;
goto v___jp_2039_;
}
}
else
{
v___y_2000_ = v___x_1876_;
goto v___jp_1999_;
}
}
v___jp_2051_:
{
if (v___y_2052_ == 0)
{
uint8_t v___x_2053_; uint8_t v___x_2054_; 
v___x_2053_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_2054_ = lean_uint8_dec_le(v___x_2053_, v___x_1885_);
if (v___x_2054_ == 0)
{
v___y_2046_ = v___x_2054_;
goto v___jp_2045_;
}
else
{
uint8_t v___x_2055_; uint8_t v___x_2056_; 
v___x_2055_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_2056_ = lean_uint8_dec_le(v___x_1885_, v___x_2055_);
v___y_2046_ = v___x_2056_;
goto v___jp_2045_;
}
}
else
{
v___y_2000_ = v___x_1876_;
goto v___jp_1999_;
}
}
v___jp_2057_:
{
if (v___y_2058_ == 0)
{
uint8_t v___x_2059_; uint8_t v___x_2060_; 
v___x_2059_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_2060_ = lean_uint8_dec_le(v___x_2059_, v___x_1885_);
if (v___x_2060_ == 0)
{
v___y_2052_ = v___x_2060_;
goto v___jp_2051_;
}
else
{
uint8_t v___x_2061_; uint8_t v___x_2062_; 
v___x_2061_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_2062_ = lean_uint8_dec_le(v___x_1885_, v___x_2061_);
v___y_2052_ = v___x_2062_;
goto v___jp_2051_;
}
}
else
{
v___y_2000_ = v___x_1876_;
goto v___jp_1999_;
}
}
}
else
{
lean_object* v___x_2070_; 
lean_dec_ref(v_config_1853_);
if (v_isShared_1874_ == 0)
{
v___x_2070_ = v___x_1873_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_fst_1870_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v_snd_1871_);
v___x_2070_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
lean_object* v___x_2071_; 
v___x_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___y_1855_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
return v___x_2071_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath(lean_object* v_config_2085_, uint8_t v_forceAbsolute_2086_, uint8_t v_allowEmpty_2087_, lean_object* v_a_2088_){
_start:
{
lean_object* v___y_2090_; lean_object* v___y_2094_; lean_object* v_array_2097_; lean_object* v_idx_2098_; uint8_t v_isAbsolute_2099_; lean_object* v___x_2100_; lean_object* v_segments_2101_; uint8_t v_isAbsolute_2103_; lean_object* v_totalLength_2104_; lean_object* v___y_2105_; lean_object* v___y_2129_; uint8_t v___y_2133_; lean_object* v_pos_2134_; uint8_t v_res_2135_; uint8_t v___y_2137_; lean_object* v_pos_2138_; uint8_t v___y_2144_; lean_object* v___y_2145_; uint8_t v___y_2167_; lean_object* v_pos_2168_; uint8_t v_res_2169_; lean_object* v_pos_2171_; lean_object* v_array_2172_; lean_object* v_idx_2173_; uint8_t v_res_2174_; uint8_t v___y_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; 
v_array_2097_ = lean_ctor_get(v_a_2088_, 0);
lean_inc_ref(v_array_2097_);
v_idx_2098_ = lean_ctor_get(v_a_2088_, 1);
lean_inc(v_idx_2098_);
v_isAbsolute_2099_ = 0;
v___x_2100_ = lean_unsigned_to_nat(0u);
v_segments_2101_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__4));
v___x_2180_ = lean_byte_array_size(v_array_2097_);
v___x_2181_ = lean_nat_dec_lt(v_idx_2098_, v___x_2180_);
if (v___x_2181_ == 0)
{
v_pos_2171_ = v_a_2088_;
v_array_2172_ = v_array_2097_;
v_idx_2173_ = v_idx_2098_;
v_res_2174_ = v_isAbsolute_2099_;
goto v___jp_2170_;
}
else
{
uint8_t v___x_2182_; uint8_t v___y_2184_; uint8_t v___y_2190_; uint8_t v___y_2196_; uint8_t v___y_2216_; uint8_t v___y_2222_; uint8_t v___y_2228_; uint8_t v___y_2234_; uint8_t v___y_2240_; uint8_t v___x_2245_; uint8_t v___x_2246_; 
v___x_2182_ = lean_byte_array_fget(v_array_2097_, v_idx_2098_);
v___x_2245_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3);
v___x_2246_ = lean_uint8_dec_le(v___x_2245_, v___x_2182_);
if (v___x_2246_ == 0)
{
v___y_2240_ = v___x_2246_;
goto v___jp_2239_;
}
else
{
uint8_t v___x_2247_; uint8_t v___x_2248_; 
v___x_2247_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4);
v___x_2248_ = lean_uint8_dec_le(v___x_2182_, v___x_2247_);
v___y_2240_ = v___x_2248_;
goto v___jp_2239_;
}
v___jp_2183_:
{
if (v___y_2184_ == 0)
{
uint8_t v___x_2185_; uint8_t v___x_2186_; 
v___x_2185_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_2186_ = lean_uint8_dec_eq(v___x_2182_, v___x_2185_);
if (v___x_2186_ == 0)
{
uint8_t v___x_2187_; uint8_t v___x_2188_; 
v___x_2187_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2188_ = lean_uint8_dec_eq(v___x_2182_, v___x_2187_);
v___y_2179_ = v___x_2188_;
goto v___jp_2178_;
}
else
{
v___y_2179_ = v___x_2186_;
goto v___jp_2178_;
}
}
else
{
v___y_2179_ = v___x_2181_;
goto v___jp_2178_;
}
}
v___jp_2189_:
{
if (v___y_2190_ == 0)
{
uint8_t v___x_2191_; uint8_t v___x_2192_; 
v___x_2191_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_2192_ = lean_uint8_dec_eq(v___x_2182_, v___x_2191_);
if (v___x_2192_ == 0)
{
uint8_t v___x_2193_; uint8_t v___x_2194_; 
v___x_2193_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_2194_ = lean_uint8_dec_eq(v___x_2182_, v___x_2193_);
v___y_2184_ = v___x_2194_;
goto v___jp_2183_;
}
else
{
v___y_2184_ = v___x_2192_;
goto v___jp_2183_;
}
}
else
{
v___y_2179_ = v___x_2181_;
goto v___jp_2178_;
}
}
v___jp_2195_:
{
if (v___y_2196_ == 0)
{
uint8_t v___x_2197_; uint8_t v___x_2198_; 
v___x_2197_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_2198_ = lean_uint8_dec_eq(v___x_2182_, v___x_2197_);
if (v___x_2198_ == 0)
{
uint8_t v___x_2199_; uint8_t v___x_2200_; 
v___x_2199_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_2200_ = lean_uint8_dec_eq(v___x_2182_, v___x_2199_);
if (v___x_2200_ == 0)
{
uint8_t v___x_2201_; uint8_t v___x_2202_; 
v___x_2201_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_2202_ = lean_uint8_dec_eq(v___x_2182_, v___x_2201_);
if (v___x_2202_ == 0)
{
uint8_t v___x_2203_; uint8_t v___x_2204_; 
v___x_2203_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_2204_ = lean_uint8_dec_eq(v___x_2182_, v___x_2203_);
if (v___x_2204_ == 0)
{
uint8_t v___x_2205_; uint8_t v___x_2206_; 
v___x_2205_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_2206_ = lean_uint8_dec_eq(v___x_2182_, v___x_2205_);
if (v___x_2206_ == 0)
{
uint8_t v___x_2207_; uint8_t v___x_2208_; 
v___x_2207_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0);
v___x_2208_ = lean_uint8_dec_eq(v___x_2182_, v___x_2207_);
if (v___x_2208_ == 0)
{
uint8_t v___x_2209_; uint8_t v___x_2210_; 
v___x_2209_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_2210_ = lean_uint8_dec_eq(v___x_2182_, v___x_2209_);
if (v___x_2210_ == 0)
{
uint8_t v___x_2211_; uint8_t v___x_2212_; 
v___x_2211_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_2212_ = lean_uint8_dec_eq(v___x_2182_, v___x_2211_);
if (v___x_2212_ == 0)
{
uint8_t v___x_2213_; uint8_t v___x_2214_; 
v___x_2213_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_2214_ = lean_uint8_dec_eq(v___x_2182_, v___x_2213_);
v___y_2190_ = v___x_2214_;
goto v___jp_2189_;
}
else
{
v___y_2190_ = v___x_2212_;
goto v___jp_2189_;
}
}
else
{
v___y_2190_ = v___x_2210_;
goto v___jp_2189_;
}
}
else
{
v___y_2190_ = v___x_2208_;
goto v___jp_2189_;
}
}
else
{
v___y_2190_ = v___x_2206_;
goto v___jp_2189_;
}
}
else
{
v___y_2190_ = v___x_2204_;
goto v___jp_2189_;
}
}
else
{
v___y_2190_ = v___x_2202_;
goto v___jp_2189_;
}
}
else
{
v___y_2190_ = v___x_2200_;
goto v___jp_2189_;
}
}
else
{
v___y_2190_ = v___x_2198_;
goto v___jp_2189_;
}
}
else
{
v___y_2179_ = v___x_2181_;
goto v___jp_2178_;
}
}
v___jp_2215_:
{
if (v___y_2216_ == 0)
{
uint8_t v___x_2217_; uint8_t v___x_2218_; 
v___x_2217_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_2218_ = lean_uint8_dec_eq(v___x_2182_, v___x_2217_);
if (v___x_2218_ == 0)
{
uint8_t v___x_2219_; uint8_t v___x_2220_; 
v___x_2219_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_2220_ = lean_uint8_dec_eq(v___x_2182_, v___x_2219_);
v___y_2196_ = v___x_2220_;
goto v___jp_2195_;
}
else
{
v___y_2196_ = v___x_2218_;
goto v___jp_2195_;
}
}
else
{
v___y_2179_ = v___x_2181_;
goto v___jp_2178_;
}
}
v___jp_2221_:
{
if (v___y_2222_ == 0)
{
uint8_t v___x_2223_; uint8_t v___x_2224_; 
v___x_2223_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_2224_ = lean_uint8_dec_eq(v___x_2182_, v___x_2223_);
if (v___x_2224_ == 0)
{
uint8_t v___x_2225_; uint8_t v___x_2226_; 
v___x_2225_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_2226_ = lean_uint8_dec_eq(v___x_2182_, v___x_2225_);
v___y_2216_ = v___x_2226_;
goto v___jp_2215_;
}
else
{
v___y_2216_ = v___x_2224_;
goto v___jp_2215_;
}
}
else
{
v___y_2179_ = v___x_2181_;
goto v___jp_2178_;
}
}
v___jp_2227_:
{
if (v___y_2228_ == 0)
{
uint8_t v___x_2229_; uint8_t v___x_2230_; 
v___x_2229_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1);
v___x_2230_ = lean_uint8_dec_eq(v___x_2182_, v___x_2229_);
if (v___x_2230_ == 0)
{
uint8_t v___x_2231_; uint8_t v___x_2232_; 
v___x_2231_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2);
v___x_2232_ = lean_uint8_dec_eq(v___x_2182_, v___x_2231_);
v___y_2222_ = v___x_2232_;
goto v___jp_2221_;
}
else
{
v___y_2222_ = v___x_2230_;
goto v___jp_2221_;
}
}
else
{
v___y_2179_ = v___x_2181_;
goto v___jp_2178_;
}
}
v___jp_2233_:
{
if (v___y_2234_ == 0)
{
uint8_t v___x_2235_; uint8_t v___x_2236_; 
v___x_2235_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_2236_ = lean_uint8_dec_le(v___x_2235_, v___x_2182_);
if (v___x_2236_ == 0)
{
v___y_2228_ = v___x_2236_;
goto v___jp_2227_;
}
else
{
uint8_t v___x_2237_; uint8_t v___x_2238_; 
v___x_2237_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_2238_ = lean_uint8_dec_le(v___x_2182_, v___x_2237_);
v___y_2228_ = v___x_2238_;
goto v___jp_2227_;
}
}
else
{
v___y_2179_ = v___x_2181_;
goto v___jp_2178_;
}
}
v___jp_2239_:
{
if (v___y_2240_ == 0)
{
uint8_t v___x_2241_; uint8_t v___x_2242_; 
v___x_2241_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_2242_ = lean_uint8_dec_le(v___x_2241_, v___x_2182_);
if (v___x_2242_ == 0)
{
v___y_2234_ = v___x_2242_;
goto v___jp_2233_;
}
else
{
uint8_t v___x_2243_; uint8_t v___x_2244_; 
v___x_2243_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_2244_ = lean_uint8_dec_le(v___x_2182_, v___x_2243_);
v___y_2234_ = v___x_2244_;
goto v___jp_2233_;
}
}
else
{
v___y_2179_ = v___x_2181_;
goto v___jp_2178_;
}
}
}
v___jp_2089_:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__1));
v___x_2092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___y_2090_);
lean_ctor_set(v___x_2092_, 1, v___x_2091_);
return v___x_2092_;
}
v___jp_2093_:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2095_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__3));
v___x_2096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___y_2094_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
return v___x_2096_;
}
v___jp_2102_:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2106_, 0, v_segments_2101_);
lean_ctor_set(v___x_2106_, 1, v_totalLength_2104_);
v___x_2107_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0(v_config_2085_, v___x_2106_, v___y_2105_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_res_2108_; lean_object* v_pos_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2118_; 
v_res_2108_ = lean_ctor_get(v___x_2107_, 1);
v_pos_2109_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2111_ = v___x_2107_;
v_isShared_2112_ = v_isSharedCheck_2118_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_res_2108_);
lean_inc(v_pos_2109_);
lean_dec(v___x_2107_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2118_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v_fst_2113_; lean_object* v___x_2114_; lean_object* v___x_2116_; 
v_fst_2113_ = lean_ctor_get(v_res_2108_, 0);
lean_inc(v_fst_2113_);
lean_dec(v_res_2108_);
v___x_2114_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2114_, 0, v_fst_2113_);
lean_ctor_set_uint8(v___x_2114_, sizeof(void*)*1, v_isAbsolute_2103_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 1, v___x_2114_);
v___x_2116_ = v___x_2111_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_pos_2109_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v___x_2114_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
else
{
lean_object* v_pos_2119_; lean_object* v_err_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
v_pos_2119_ = lean_ctor_get(v___x_2107_, 0);
v_err_2120_ = lean_ctor_get(v___x_2107_, 1);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2107_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_err_2120_);
lean_inc(v_pos_2119_);
lean_dec(v___x_2107_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_pos_2119_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v_err_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
v___jp_2128_:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__5));
v___x_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___y_2129_);
lean_ctor_set(v___x_2131_, 1, v___x_2130_);
return v___x_2131_;
}
v___jp_2132_:
{
if (v_allowEmpty_2087_ == 0)
{
v___y_2090_ = v_pos_2134_;
goto v___jp_2089_;
}
else
{
if (v_res_2135_ == 0)
{
if (v___y_2133_ == 0)
{
v___y_2129_ = v_pos_2134_;
goto v___jp_2128_;
}
else
{
v___y_2090_ = v_pos_2134_;
goto v___jp_2089_;
}
}
else
{
v___y_2129_ = v_pos_2134_;
goto v___jp_2128_;
}
}
}
v___jp_2136_:
{
if (v_forceAbsolute_2086_ == 0)
{
v_isAbsolute_2103_ = v_isAbsolute_2099_;
v_totalLength_2104_ = v___x_2100_;
v___y_2105_ = v_pos_2138_;
goto v___jp_2102_;
}
else
{
lean_object* v_array_2139_; lean_object* v_idx_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
lean_dec_ref(v_config_2085_);
v_array_2139_ = lean_ctor_get(v_pos_2138_, 0);
v_idx_2140_ = lean_ctor_get(v_pos_2138_, 1);
v___x_2141_ = lean_byte_array_size(v_array_2139_);
v___x_2142_ = lean_nat_dec_lt(v_idx_2140_, v___x_2141_);
if (v___x_2142_ == 0)
{
v___y_2133_ = v___y_2137_;
v_pos_2134_ = v_pos_2138_;
v_res_2135_ = v_forceAbsolute_2086_;
goto v___jp_2132_;
}
else
{
v___y_2133_ = v___y_2137_;
v_pos_2134_ = v_pos_2138_;
v_res_2135_ = v_isAbsolute_2099_;
goto v___jp_2132_;
}
}
}
v___jp_2143_:
{
lean_object* v_array_2146_; lean_object* v_idx_2147_; lean_object* v___x_2148_; uint8_t v___x_2149_; 
v_array_2146_ = lean_ctor_get(v___y_2145_, 0);
v_idx_2147_ = lean_ctor_get(v___y_2145_, 1);
v___x_2148_ = lean_byte_array_size(v_array_2146_);
v___x_2149_ = lean_nat_dec_lt(v_idx_2147_, v___x_2148_);
if (v___x_2149_ == 0)
{
v___y_2137_ = v___y_2144_;
v_pos_2138_ = v___y_2145_;
goto v___jp_2136_;
}
else
{
uint8_t v___x_2150_; uint8_t v___x_2151_; uint8_t v___x_2152_; 
v___x_2150_ = lean_byte_array_fget(v_array_2146_, v_idx_2147_);
v___x_2151_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2152_ = lean_uint8_dec_eq(v___x_2150_, v___x_2151_);
if (v___x_2152_ == 0)
{
v___y_2137_ = v___y_2144_;
v_pos_2138_ = v___y_2145_;
goto v___jp_2136_;
}
else
{
if (v___x_2149_ == 0)
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
lean_dec_ref(v_config_2085_);
v___x_2153_ = lean_box(0);
v___x_2154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___y_2145_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
return v___x_2154_;
}
else
{
lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2163_; 
lean_inc(v_idx_2147_);
lean_inc_ref(v_array_2146_);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___y_2145_);
if (v_isSharedCheck_2163_ == 0)
{
lean_object* v_unused_2164_; lean_object* v_unused_2165_; 
v_unused_2164_ = lean_ctor_get(v___y_2145_, 1);
lean_dec(v_unused_2164_);
v_unused_2165_ = lean_ctor_get(v___y_2145_, 0);
lean_dec(v_unused_2165_);
v___x_2156_ = v___y_2145_;
v_isShared_2157_ = v_isSharedCheck_2163_;
goto v_resetjp_2155_;
}
else
{
lean_dec(v___y_2145_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2163_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2161_; 
v___x_2158_ = lean_unsigned_to_nat(1u);
v___x_2159_ = lean_nat_add(v_idx_2147_, v___x_2158_);
lean_dec(v_idx_2147_);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 1, v___x_2159_);
v___x_2161_ = v___x_2156_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_array_2146_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
v_isAbsolute_2103_ = v___x_2149_;
v_totalLength_2104_ = v___x_2158_;
v___y_2105_ = v___x_2161_;
goto v___jp_2102_;
}
}
}
}
}
}
v___jp_2166_:
{
if (v_allowEmpty_2087_ == 0)
{
if (v_res_2169_ == 0)
{
if (v___y_2167_ == 0)
{
lean_dec_ref(v_config_2085_);
v___y_2094_ = v_pos_2168_;
goto v___jp_2093_;
}
else
{
v___y_2144_ = v___y_2167_;
v___y_2145_ = v_pos_2168_;
goto v___jp_2143_;
}
}
else
{
lean_dec_ref(v_config_2085_);
v___y_2094_ = v_pos_2168_;
goto v___jp_2093_;
}
}
else
{
v___y_2144_ = v___y_2167_;
v___y_2145_ = v_pos_2168_;
goto v___jp_2143_;
}
}
v___jp_2170_:
{
lean_object* v___x_2175_; uint8_t v___x_2176_; 
v___x_2175_ = lean_byte_array_size(v_array_2172_);
lean_dec_ref(v_array_2172_);
v___x_2176_ = lean_nat_dec_lt(v_idx_2173_, v___x_2175_);
lean_dec(v_idx_2173_);
if (v___x_2176_ == 0)
{
uint8_t v___x_2177_; 
v___x_2177_ = 1;
v___y_2167_ = v_res_2174_;
v_pos_2168_ = v_pos_2171_;
v_res_2169_ = v___x_2177_;
goto v___jp_2166_;
}
else
{
v___y_2167_ = v_res_2174_;
v_pos_2168_ = v_pos_2171_;
v_res_2169_ = v_isAbsolute_2099_;
goto v___jp_2166_;
}
}
v___jp_2178_:
{
if (v___y_2179_ == 0)
{
v_pos_2171_ = v_a_2088_;
v_array_2172_ = v_array_2097_;
v_idx_2173_ = v_idx_2098_;
v_res_2174_ = v_isAbsolute_2099_;
goto v___jp_2170_;
}
else
{
v_pos_2171_ = v_a_2088_;
v_array_2172_ = v_array_2097_;
v_idx_2173_ = v_idx_2098_;
v_res_2174_ = v___y_2179_;
goto v___jp_2170_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath___boxed(lean_object* v_config_2249_, lean_object* v_forceAbsolute_2250_, lean_object* v_allowEmpty_2251_, lean_object* v_a_2252_){
_start:
{
uint8_t v_forceAbsolute_boxed_2253_; uint8_t v_allowEmpty_boxed_2254_; lean_object* v_res_2255_; 
v_forceAbsolute_boxed_2253_ = lean_unbox(v_forceAbsolute_2250_);
v_allowEmpty_boxed_2254_ = lean_unbox(v_allowEmpty_2251_);
v_res_2255_ = l_Std_Http_URI_Parser_parsePath(v_config_2249_, v_forceAbsolute_boxed_2253_, v_allowEmpty_boxed_2254_, v_a_2252_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(lean_object* v_s_2256_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0));
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___boxed(lean_object* v_s_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(v_s_2258_);
lean_dec_ref(v_s_2258_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(lean_object* v_s_2260_){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0));
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___boxed(lean_object* v_s_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(v_s_2262_);
lean_dec_ref(v_s_2262_);
return v_res_2263_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(uint8_t v_c_2264_){
_start:
{
uint8_t v___y_2266_; uint8_t v___y_2270_; uint8_t v___y_2276_; uint8_t v___y_2282_; uint8_t v___y_2302_; uint8_t v___y_2308_; uint8_t v___y_2314_; uint8_t v___y_2320_; uint8_t v___y_2326_; uint8_t v___x_2331_; uint8_t v___x_2332_; 
v___x_2331_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3);
v___x_2332_ = lean_uint8_dec_le(v___x_2331_, v_c_2264_);
if (v___x_2332_ == 0)
{
v___y_2326_ = v___x_2332_;
goto v___jp_2325_;
}
else
{
uint8_t v___x_2333_; uint8_t v___x_2334_; 
v___x_2333_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4);
v___x_2334_ = lean_uint8_dec_le(v_c_2264_, v___x_2333_);
v___y_2326_ = v___x_2334_;
goto v___jp_2325_;
}
v___jp_2265_:
{
if (v___y_2266_ == 0)
{
uint8_t v___x_2267_; uint8_t v___x_2268_; 
v___x_2267_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_2268_ = lean_uint8_dec_eq(v_c_2264_, v___x_2267_);
if (v___x_2268_ == 0)
{
return v___y_2266_;
}
else
{
return v___x_2268_;
}
}
else
{
return v___y_2266_;
}
}
v___jp_2269_:
{
if (v___y_2270_ == 0)
{
uint8_t v___x_2271_; uint8_t v___x_2272_; 
v___x_2271_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2272_ = lean_uint8_dec_eq(v_c_2264_, v___x_2271_);
if (v___x_2272_ == 0)
{
uint8_t v___x_2273_; uint8_t v___x_2274_; 
v___x_2273_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v___x_2274_ = lean_uint8_dec_eq(v_c_2264_, v___x_2273_);
v___y_2266_ = v___x_2274_;
goto v___jp_2265_;
}
else
{
v___y_2266_ = v___x_2272_;
goto v___jp_2265_;
}
}
else
{
return v___y_2270_;
}
}
v___jp_2275_:
{
if (v___y_2276_ == 0)
{
uint8_t v___x_2277_; uint8_t v___x_2278_; 
v___x_2277_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_2278_ = lean_uint8_dec_eq(v_c_2264_, v___x_2277_);
if (v___x_2278_ == 0)
{
uint8_t v___x_2279_; uint8_t v___x_2280_; 
v___x_2279_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_2280_ = lean_uint8_dec_eq(v_c_2264_, v___x_2279_);
v___y_2270_ = v___x_2280_;
goto v___jp_2269_;
}
else
{
v___y_2270_ = v___x_2278_;
goto v___jp_2269_;
}
}
else
{
return v___y_2276_;
}
}
v___jp_2281_:
{
if (v___y_2282_ == 0)
{
uint8_t v___x_2283_; uint8_t v___x_2284_; 
v___x_2283_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_2284_ = lean_uint8_dec_eq(v_c_2264_, v___x_2283_);
if (v___x_2284_ == 0)
{
uint8_t v___x_2285_; uint8_t v___x_2286_; 
v___x_2285_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_2286_ = lean_uint8_dec_eq(v_c_2264_, v___x_2285_);
if (v___x_2286_ == 0)
{
uint8_t v___x_2287_; uint8_t v___x_2288_; 
v___x_2287_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_2288_ = lean_uint8_dec_eq(v_c_2264_, v___x_2287_);
if (v___x_2288_ == 0)
{
uint8_t v___x_2289_; uint8_t v___x_2290_; 
v___x_2289_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_2290_ = lean_uint8_dec_eq(v_c_2264_, v___x_2289_);
if (v___x_2290_ == 0)
{
uint8_t v___x_2291_; uint8_t v___x_2292_; 
v___x_2291_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_2292_ = lean_uint8_dec_eq(v_c_2264_, v___x_2291_);
if (v___x_2292_ == 0)
{
uint8_t v___x_2293_; uint8_t v___x_2294_; 
v___x_2293_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0);
v___x_2294_ = lean_uint8_dec_eq(v_c_2264_, v___x_2293_);
if (v___x_2294_ == 0)
{
uint8_t v___x_2295_; uint8_t v___x_2296_; 
v___x_2295_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_2296_ = lean_uint8_dec_eq(v_c_2264_, v___x_2295_);
if (v___x_2296_ == 0)
{
uint8_t v___x_2297_; uint8_t v___x_2298_; 
v___x_2297_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_2298_ = lean_uint8_dec_eq(v_c_2264_, v___x_2297_);
if (v___x_2298_ == 0)
{
uint8_t v___x_2299_; uint8_t v___x_2300_; 
v___x_2299_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_2300_ = lean_uint8_dec_eq(v_c_2264_, v___x_2299_);
v___y_2276_ = v___x_2300_;
goto v___jp_2275_;
}
else
{
v___y_2276_ = v___x_2298_;
goto v___jp_2275_;
}
}
else
{
v___y_2276_ = v___x_2296_;
goto v___jp_2275_;
}
}
else
{
v___y_2276_ = v___x_2294_;
goto v___jp_2275_;
}
}
else
{
v___y_2276_ = v___x_2292_;
goto v___jp_2275_;
}
}
else
{
v___y_2276_ = v___x_2290_;
goto v___jp_2275_;
}
}
else
{
v___y_2276_ = v___x_2288_;
goto v___jp_2275_;
}
}
else
{
v___y_2276_ = v___x_2286_;
goto v___jp_2275_;
}
}
else
{
v___y_2276_ = v___x_2284_;
goto v___jp_2275_;
}
}
else
{
return v___y_2282_;
}
}
v___jp_2301_:
{
if (v___y_2302_ == 0)
{
uint8_t v___x_2303_; uint8_t v___x_2304_; 
v___x_2303_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_2304_ = lean_uint8_dec_eq(v_c_2264_, v___x_2303_);
if (v___x_2304_ == 0)
{
uint8_t v___x_2305_; uint8_t v___x_2306_; 
v___x_2305_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_2306_ = lean_uint8_dec_eq(v_c_2264_, v___x_2305_);
v___y_2282_ = v___x_2306_;
goto v___jp_2281_;
}
else
{
v___y_2282_ = v___x_2304_;
goto v___jp_2281_;
}
}
else
{
return v___y_2302_;
}
}
v___jp_2307_:
{
if (v___y_2308_ == 0)
{
uint8_t v___x_2309_; uint8_t v___x_2310_; 
v___x_2309_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_2310_ = lean_uint8_dec_eq(v_c_2264_, v___x_2309_);
if (v___x_2310_ == 0)
{
uint8_t v___x_2311_; uint8_t v___x_2312_; 
v___x_2311_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_2312_ = lean_uint8_dec_eq(v_c_2264_, v___x_2311_);
v___y_2302_ = v___x_2312_;
goto v___jp_2301_;
}
else
{
v___y_2302_ = v___x_2310_;
goto v___jp_2301_;
}
}
else
{
return v___y_2308_;
}
}
v___jp_2313_:
{
if (v___y_2314_ == 0)
{
uint8_t v___x_2315_; uint8_t v___x_2316_; 
v___x_2315_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1);
v___x_2316_ = lean_uint8_dec_eq(v_c_2264_, v___x_2315_);
if (v___x_2316_ == 0)
{
uint8_t v___x_2317_; uint8_t v___x_2318_; 
v___x_2317_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2);
v___x_2318_ = lean_uint8_dec_eq(v_c_2264_, v___x_2317_);
v___y_2308_ = v___x_2318_;
goto v___jp_2307_;
}
else
{
v___y_2308_ = v___x_2316_;
goto v___jp_2307_;
}
}
else
{
return v___y_2314_;
}
}
v___jp_2319_:
{
if (v___y_2320_ == 0)
{
uint8_t v___x_2321_; uint8_t v___x_2322_; 
v___x_2321_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_2322_ = lean_uint8_dec_le(v___x_2321_, v_c_2264_);
if (v___x_2322_ == 0)
{
v___y_2314_ = v___x_2322_;
goto v___jp_2313_;
}
else
{
uint8_t v___x_2323_; uint8_t v___x_2324_; 
v___x_2323_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_2324_ = lean_uint8_dec_le(v_c_2264_, v___x_2323_);
v___y_2314_ = v___x_2324_;
goto v___jp_2313_;
}
}
else
{
return v___y_2320_;
}
}
v___jp_2325_:
{
if (v___y_2326_ == 0)
{
uint8_t v___x_2327_; uint8_t v___x_2328_; 
v___x_2327_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_2328_ = lean_uint8_dec_le(v___x_2327_, v_c_2264_);
if (v___x_2328_ == 0)
{
v___y_2320_ = v___x_2328_;
goto v___jp_2319_;
}
else
{
uint8_t v___x_2329_; uint8_t v___x_2330_; 
v___x_2329_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_2330_ = lean_uint8_dec_le(v_c_2264_, v___x_2329_);
v___y_2320_ = v___x_2330_;
goto v___jp_2319_;
}
}
else
{
return v___y_2326_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0___boxed(lean_object* v_c_2335_){
_start:
{
uint8_t v_c_boxed_2336_; uint8_t v_res_2337_; lean_object* v_r_2338_; 
v_c_boxed_2336_ = lean_unbox(v_c_2335_);
v_res_2337_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(v_c_boxed_2336_);
v_r_2338_ = lean_box(v_res_2337_);
return v_r_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(lean_object* v_out_2339_, lean_object* v_a_2340_, lean_object* v_b_2341_){
_start:
{
if (lean_obj_tag(v_a_2340_) == 0)
{
lean_object* v_currPos_2342_; lean_object* v_searcher_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2382_; 
v_currPos_2342_ = lean_ctor_get(v_a_2340_, 0);
v_searcher_2343_ = lean_ctor_get(v_a_2340_, 1);
v_isSharedCheck_2382_ = !lean_is_exclusive(v_a_2340_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2345_ = v_a_2340_;
v_isShared_2346_ = v_isSharedCheck_2382_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_searcher_2343_);
lean_inc(v_currPos_2342_);
lean_dec(v_a_2340_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2382_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v_str_2347_; lean_object* v_startInclusive_2348_; lean_object* v_endExclusive_2349_; lean_object* v_it_2351_; lean_object* v_startInclusive_2352_; lean_object* v_endExclusive_2353_; lean_object* v___x_2360_; uint8_t v___x_2361_; 
v_str_2347_ = lean_ctor_get(v_out_2339_, 0);
v_startInclusive_2348_ = lean_ctor_get(v_out_2339_, 1);
v_endExclusive_2349_ = lean_ctor_get(v_out_2339_, 2);
v___x_2360_ = lean_nat_sub(v_endExclusive_2349_, v_startInclusive_2348_);
v___x_2361_ = lean_nat_dec_eq(v_searcher_2343_, v___x_2360_);
if (v___x_2361_ == 0)
{
uint32_t v___x_2362_; lean_object* v___x_2363_; uint32_t v___x_2364_; uint8_t v___x_2365_; 
lean_dec(v___x_2360_);
v___x_2362_ = 61;
v___x_2363_ = lean_nat_add(v_startInclusive_2348_, v_searcher_2343_);
v___x_2364_ = lean_string_utf8_get_fast(v_str_2347_, v___x_2363_);
v___x_2365_ = lean_uint32_dec_eq(v___x_2364_, v___x_2362_);
if (v___x_2365_ == 0)
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; 
lean_dec(v_searcher_2343_);
v___x_2366_ = lean_string_utf8_next_fast(v_str_2347_, v___x_2363_);
lean_dec(v___x_2363_);
v___x_2367_ = lean_nat_sub(v___x_2366_, v_startInclusive_2348_);
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 1, v___x_2367_);
v___x_2369_ = v___x_2345_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_currPos_2342_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
v_a_2340_ = v___x_2369_;
goto _start;
}
}
else
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v_slice_2375_; lean_object* v_nextIt_2377_; 
v___x_2372_ = lean_string_utf8_next_fast(v_str_2347_, v___x_2363_);
v___x_2373_ = lean_nat_sub(v___x_2372_, v___x_2363_);
lean_dec(v___x_2363_);
v___x_2374_ = lean_nat_add(v_searcher_2343_, v___x_2373_);
lean_dec(v___x_2373_);
v_slice_2375_ = l_String_Slice_subslice_x21(v_out_2339_, v_currPos_2342_, v_searcher_2343_);
lean_inc(v___x_2374_);
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 1, v___x_2374_);
lean_ctor_set(v___x_2345_, 0, v___x_2374_);
v_nextIt_2377_ = v___x_2345_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2374_);
lean_ctor_set(v_reuseFailAlloc_2380_, 1, v___x_2374_);
v_nextIt_2377_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
lean_object* v_startInclusive_2378_; lean_object* v_endExclusive_2379_; 
v_startInclusive_2378_ = lean_ctor_get(v_slice_2375_, 0);
lean_inc(v_startInclusive_2378_);
v_endExclusive_2379_ = lean_ctor_get(v_slice_2375_, 1);
lean_inc(v_endExclusive_2379_);
lean_dec_ref(v_slice_2375_);
v_it_2351_ = v_nextIt_2377_;
v_startInclusive_2352_ = v_startInclusive_2378_;
v_endExclusive_2353_ = v_endExclusive_2379_;
goto v___jp_2350_;
}
}
}
else
{
lean_object* v___x_2381_; 
lean_del_object(v___x_2345_);
lean_dec(v_searcher_2343_);
v___x_2381_ = lean_box(1);
v_it_2351_ = v___x_2381_;
v_startInclusive_2352_ = v_currPos_2342_;
v_endExclusive_2353_ = v___x_2360_;
goto v___jp_2350_;
}
v___jp_2350_:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2354_ = lean_nat_add(v_startInclusive_2348_, v_startInclusive_2352_);
lean_dec(v_startInclusive_2352_);
v___x_2355_ = lean_nat_add(v_startInclusive_2348_, v_endExclusive_2353_);
lean_dec(v_endExclusive_2353_);
lean_inc_ref(v_str_2347_);
v___x_2356_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2356_, 0, v_str_2347_);
lean_ctor_set(v___x_2356_, 1, v___x_2354_);
lean_ctor_set(v___x_2356_, 2, v___x_2355_);
v___x_2357_ = l_String_Slice_toString(v___x_2356_);
lean_dec_ref(v___x_2356_);
v___x_2358_ = lean_array_push(v_b_2341_, v___x_2357_);
v_a_2340_ = v_it_2351_;
v_b_2341_ = v___x_2358_;
goto _start;
}
}
}
else
{
return v_b_2341_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg___boxed(lean_object* v_out_2383_, lean_object* v_a_2384_, lean_object* v_b_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_2383_, v_a_2384_, v_b_2385_);
lean_dec_ref(v_out_2383_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(lean_object* v___x_2390_, lean_object* v___x_2391_, lean_object* v___x_2392_, lean_object* v_a_2393_, lean_object* v_b_2394_){
_start:
{
lean_object* v_it_2396_; lean_object* v_startInclusive_2397_; lean_object* v_endExclusive_2398_; 
if (lean_obj_tag(v_a_2393_) == 0)
{
lean_object* v_currPos_2423_; lean_object* v_searcher_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2453_; 
v_currPos_2423_ = lean_ctor_get(v_a_2393_, 0);
v_searcher_2424_ = lean_ctor_get(v_a_2393_, 1);
v_isSharedCheck_2453_ = !lean_is_exclusive(v_a_2393_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2426_ = v_a_2393_;
v_isShared_2427_ = v_isSharedCheck_2453_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_searcher_2424_);
lean_inc(v_currPos_2423_);
lean_dec(v_a_2393_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2453_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v_str_2428_; lean_object* v_startInclusive_2429_; lean_object* v_endExclusive_2430_; lean_object* v___x_2431_; uint8_t v___x_2432_; 
v_str_2428_ = lean_ctor_get(v___x_2391_, 0);
v_startInclusive_2429_ = lean_ctor_get(v___x_2391_, 1);
v_endExclusive_2430_ = lean_ctor_get(v___x_2391_, 2);
v___x_2431_ = lean_nat_sub(v_endExclusive_2430_, v_startInclusive_2429_);
v___x_2432_ = lean_nat_dec_eq(v_searcher_2424_, v___x_2431_);
lean_dec(v___x_2431_);
if (v___x_2432_ == 0)
{
uint32_t v___x_2433_; lean_object* v___x_2434_; uint32_t v___x_2435_; uint8_t v___x_2436_; 
v___x_2433_ = 38;
v___x_2434_ = lean_nat_add(v_startInclusive_2429_, v_searcher_2424_);
v___x_2435_ = lean_string_utf8_get_fast(v_str_2428_, v___x_2434_);
v___x_2436_ = lean_uint32_dec_eq(v___x_2435_, v___x_2433_);
if (v___x_2436_ == 0)
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2440_; 
lean_dec(v_searcher_2424_);
v___x_2437_ = lean_string_utf8_next_fast(v_str_2428_, v___x_2434_);
lean_dec(v___x_2434_);
v___x_2438_ = lean_nat_sub(v___x_2437_, v_startInclusive_2429_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 1, v___x_2438_);
v___x_2440_ = v___x_2426_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_currPos_2423_);
lean_ctor_set(v_reuseFailAlloc_2442_, 1, v___x_2438_);
v___x_2440_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
v_a_2393_ = v___x_2440_;
goto _start;
}
}
else
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v_slice_2446_; lean_object* v_nextIt_2448_; 
v___x_2443_ = lean_string_utf8_next_fast(v_str_2428_, v___x_2434_);
v___x_2444_ = lean_nat_sub(v___x_2443_, v___x_2434_);
lean_dec(v___x_2434_);
v___x_2445_ = lean_nat_add(v_searcher_2424_, v___x_2444_);
lean_dec(v___x_2444_);
v_slice_2446_ = l_String_Slice_subslice_x21(v___x_2391_, v_currPos_2423_, v_searcher_2424_);
lean_inc(v___x_2445_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 1, v___x_2445_);
lean_ctor_set(v___x_2426_, 0, v___x_2445_);
v_nextIt_2448_ = v___x_2426_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2445_);
lean_ctor_set(v_reuseFailAlloc_2451_, 1, v___x_2445_);
v_nextIt_2448_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v_startInclusive_2449_; lean_object* v_endExclusive_2450_; 
v_startInclusive_2449_ = lean_ctor_get(v_slice_2446_, 0);
lean_inc(v_startInclusive_2449_);
v_endExclusive_2450_ = lean_ctor_get(v_slice_2446_, 1);
lean_inc(v_endExclusive_2450_);
lean_dec_ref(v_slice_2446_);
v_it_2396_ = v_nextIt_2448_;
v_startInclusive_2397_ = v_startInclusive_2449_;
v_endExclusive_2398_ = v_endExclusive_2450_;
goto v___jp_2395_;
}
}
}
else
{
lean_object* v___x_2452_; 
lean_del_object(v___x_2426_);
lean_dec(v_searcher_2424_);
v___x_2452_ = lean_box(1);
lean_inc(v___x_2392_);
v_it_2396_ = v___x_2452_;
v_startInclusive_2397_ = v_currPos_2423_;
v_endExclusive_2398_ = v___x_2392_;
goto v___jp_2395_;
}
}
}
else
{
lean_object* v___x_2454_; 
lean_dec(v___x_2392_);
lean_dec_ref(v___x_2390_);
v___x_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2454_, 0, v_b_2394_);
return v___x_2454_;
}
v___jp_2395_:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
lean_inc_ref(v___x_2390_);
v___x_2399_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2390_);
lean_ctor_set(v___x_2399_, 1, v_startInclusive_2397_);
lean_ctor_set(v___x_2399_, 2, v_endExclusive_2398_);
v___x_2400_ = l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(v___x_2399_);
v___x_2401_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0));
v___x_2402_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_2399_, v___x_2400_, v___x_2401_);
lean_dec_ref(v___x_2399_);
v___x_2403_ = lean_array_to_list(v___x_2402_);
if (lean_obj_tag(v___x_2403_) == 0)
{
v_a_2393_ = v_it_2396_;
goto _start;
}
else
{
lean_object* v_tail_2405_; 
v_tail_2405_ = lean_ctor_get(v___x_2403_, 1);
lean_inc(v_tail_2405_);
if (lean_obj_tag(v_tail_2405_) == 0)
{
lean_object* v_head_2406_; lean_object* v___x_2407_; 
v_head_2406_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_head_2406_);
lean_dec_ref(v___x_2403_);
v___x_2407_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2406_);
lean_dec(v_head_2406_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v___x_2408_; 
lean_dec(v_it_2396_);
lean_dec_ref(v_b_2394_);
lean_dec(v___x_2392_);
lean_dec_ref(v___x_2390_);
v___x_2408_ = lean_box(0);
return v___x_2408_;
}
else
{
lean_object* v_val_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v_val_2409_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_val_2409_);
lean_dec_ref(v___x_2407_);
v___x_2410_ = lean_box(0);
v___x_2411_ = l_Std_Http_URI_Query_insertEncoded(v_b_2394_, v_val_2409_, v___x_2410_);
v_a_2393_ = v_it_2396_;
v_b_2394_ = v___x_2411_;
goto _start;
}
}
else
{
lean_object* v_head_2413_; lean_object* v___x_2414_; 
v_head_2413_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_head_2413_);
lean_dec_ref(v___x_2403_);
v___x_2414_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2413_);
lean_dec(v_head_2413_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v___x_2415_; 
lean_dec(v_tail_2405_);
lean_dec(v_it_2396_);
lean_dec_ref(v_b_2394_);
lean_dec(v___x_2392_);
lean_dec_ref(v___x_2390_);
v___x_2415_ = lean_box(0);
return v___x_2415_;
}
else
{
lean_object* v_val_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v_val_2416_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_val_2416_);
lean_dec_ref(v___x_2414_);
v___x_2417_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1));
v___x_2418_ = l_String_intercalate(v___x_2417_, v_tail_2405_);
v___x_2419_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2418_);
lean_dec_ref(v___x_2418_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v___x_2420_; 
lean_dec(v_val_2416_);
lean_dec(v_it_2396_);
lean_dec_ref(v_b_2394_);
lean_dec(v___x_2392_);
lean_dec_ref(v___x_2390_);
v___x_2420_ = lean_box(0);
return v___x_2420_;
}
else
{
lean_object* v___x_2421_; 
v___x_2421_ = l_Std_Http_URI_Query_insertEncoded(v_b_2394_, v_val_2416_, v___x_2419_);
v_a_2393_ = v_it_2396_;
v_b_2394_ = v___x_2421_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___boxed(lean_object* v___x_2455_, lean_object* v___x_2456_, lean_object* v___x_2457_, lean_object* v_a_2458_, lean_object* v_b_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2455_, v___x_2456_, v___x_2457_, v_a_2458_, v_b_2459_);
lean_dec_ref(v___x_2456_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(lean_object* v___x_2461_, lean_object* v___x_2462_, lean_object* v___x_2463_, lean_object* v_a_2464_, lean_object* v_b_2465_){
_start:
{
lean_object* v_it_2467_; lean_object* v_startInclusive_2468_; lean_object* v_endExclusive_2469_; 
if (lean_obj_tag(v_a_2464_) == 0)
{
lean_object* v_currPos_2494_; lean_object* v_searcher_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2524_; 
v_currPos_2494_ = lean_ctor_get(v_a_2464_, 0);
v_searcher_2495_ = lean_ctor_get(v_a_2464_, 1);
v_isSharedCheck_2524_ = !lean_is_exclusive(v_a_2464_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2497_ = v_a_2464_;
v_isShared_2498_ = v_isSharedCheck_2524_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_searcher_2495_);
lean_inc(v_currPos_2494_);
lean_dec(v_a_2464_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2524_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v_str_2499_; lean_object* v_startInclusive_2500_; lean_object* v_endExclusive_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; 
v_str_2499_ = lean_ctor_get(v___x_2462_, 0);
v_startInclusive_2500_ = lean_ctor_get(v___x_2462_, 1);
v_endExclusive_2501_ = lean_ctor_get(v___x_2462_, 2);
v___x_2502_ = lean_nat_sub(v_endExclusive_2501_, v_startInclusive_2500_);
v___x_2503_ = lean_nat_dec_eq(v_searcher_2495_, v___x_2502_);
lean_dec(v___x_2502_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2504_; uint32_t v___x_2505_; uint32_t v___x_2506_; uint8_t v___x_2507_; 
v___x_2504_ = lean_nat_add(v_startInclusive_2500_, v_searcher_2495_);
v___x_2505_ = lean_string_utf8_get_fast(v_str_2499_, v___x_2504_);
v___x_2506_ = 38;
v___x_2507_ = lean_uint32_dec_eq(v___x_2505_, v___x_2506_);
if (v___x_2507_ == 0)
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2511_; 
lean_dec(v_searcher_2495_);
v___x_2508_ = lean_string_utf8_next_fast(v_str_2499_, v___x_2504_);
lean_dec(v___x_2504_);
v___x_2509_ = lean_nat_sub(v___x_2508_, v_startInclusive_2500_);
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 1, v___x_2509_);
v___x_2511_ = v___x_2497_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_currPos_2494_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v___x_2509_);
v___x_2511_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
lean_object* v___x_2512_; 
v___x_2512_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2461_, v___x_2462_, v___x_2463_, v___x_2511_, v_b_2465_);
return v___x_2512_;
}
}
else
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v_slice_2517_; lean_object* v_nextIt_2519_; 
v___x_2514_ = lean_string_utf8_next_fast(v_str_2499_, v___x_2504_);
v___x_2515_ = lean_nat_sub(v___x_2514_, v___x_2504_);
lean_dec(v___x_2504_);
v___x_2516_ = lean_nat_add(v_searcher_2495_, v___x_2515_);
lean_dec(v___x_2515_);
v_slice_2517_ = l_String_Slice_subslice_x21(v___x_2462_, v_currPos_2494_, v_searcher_2495_);
lean_inc(v___x_2516_);
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 1, v___x_2516_);
lean_ctor_set(v___x_2497_, 0, v___x_2516_);
v_nextIt_2519_ = v___x_2497_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2516_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v___x_2516_);
v_nextIt_2519_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
lean_object* v_startInclusive_2520_; lean_object* v_endExclusive_2521_; 
v_startInclusive_2520_ = lean_ctor_get(v_slice_2517_, 0);
lean_inc(v_startInclusive_2520_);
v_endExclusive_2521_ = lean_ctor_get(v_slice_2517_, 1);
lean_inc(v_endExclusive_2521_);
lean_dec_ref(v_slice_2517_);
v_it_2467_ = v_nextIt_2519_;
v_startInclusive_2468_ = v_startInclusive_2520_;
v_endExclusive_2469_ = v_endExclusive_2521_;
goto v___jp_2466_;
}
}
}
else
{
lean_object* v___x_2523_; 
lean_del_object(v___x_2497_);
lean_dec(v_searcher_2495_);
v___x_2523_ = lean_box(1);
lean_inc(v___x_2463_);
v_it_2467_ = v___x_2523_;
v_startInclusive_2468_ = v_currPos_2494_;
v_endExclusive_2469_ = v___x_2463_;
goto v___jp_2466_;
}
}
}
else
{
lean_object* v___x_2525_; 
lean_dec(v___x_2463_);
lean_dec_ref(v___x_2461_);
v___x_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2525_, 0, v_b_2465_);
return v___x_2525_;
}
v___jp_2466_:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
lean_inc_ref(v___x_2461_);
v___x_2470_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2461_);
lean_ctor_set(v___x_2470_, 1, v_startInclusive_2468_);
lean_ctor_set(v___x_2470_, 2, v_endExclusive_2469_);
v___x_2471_ = l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(v___x_2470_);
v___x_2472_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0));
v___x_2473_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_2470_, v___x_2471_, v___x_2472_);
lean_dec_ref(v___x_2470_);
v___x_2474_ = lean_array_to_list(v___x_2473_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v___x_2475_; 
v___x_2475_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2461_, v___x_2462_, v___x_2463_, v_it_2467_, v_b_2465_);
return v___x_2475_;
}
else
{
lean_object* v_tail_2476_; 
v_tail_2476_ = lean_ctor_get(v___x_2474_, 1);
lean_inc(v_tail_2476_);
if (lean_obj_tag(v_tail_2476_) == 0)
{
lean_object* v_head_2477_; lean_object* v___x_2478_; 
v_head_2477_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_head_2477_);
lean_dec_ref(v___x_2474_);
v___x_2478_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2477_);
lean_dec(v_head_2477_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v___x_2479_; 
lean_dec(v_it_2467_);
lean_dec_ref(v_b_2465_);
lean_dec(v___x_2463_);
lean_dec_ref(v___x_2461_);
v___x_2479_ = lean_box(0);
return v___x_2479_;
}
else
{
lean_object* v_val_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v_val_2480_ = lean_ctor_get(v___x_2478_, 0);
lean_inc(v_val_2480_);
lean_dec_ref(v___x_2478_);
v___x_2481_ = lean_box(0);
v___x_2482_ = l_Std_Http_URI_Query_insertEncoded(v_b_2465_, v_val_2480_, v___x_2481_);
v___x_2483_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2461_, v___x_2462_, v___x_2463_, v_it_2467_, v___x_2482_);
return v___x_2483_;
}
}
else
{
lean_object* v_head_2484_; lean_object* v___x_2485_; 
v_head_2484_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_head_2484_);
lean_dec_ref(v___x_2474_);
v___x_2485_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2484_);
lean_dec(v_head_2484_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v___x_2486_; 
lean_dec(v_tail_2476_);
lean_dec(v_it_2467_);
lean_dec_ref(v_b_2465_);
lean_dec(v___x_2463_);
lean_dec_ref(v___x_2461_);
v___x_2486_ = lean_box(0);
return v___x_2486_;
}
else
{
lean_object* v_val_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v_val_2487_ = lean_ctor_get(v___x_2485_, 0);
lean_inc(v_val_2487_);
lean_dec_ref(v___x_2485_);
v___x_2488_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1));
v___x_2489_ = l_String_intercalate(v___x_2488_, v_tail_2476_);
v___x_2490_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2489_);
lean_dec_ref(v___x_2489_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v___x_2491_; 
lean_dec(v_val_2487_);
lean_dec(v_it_2467_);
lean_dec_ref(v_b_2465_);
lean_dec(v___x_2463_);
lean_dec_ref(v___x_2461_);
v___x_2491_ = lean_box(0);
return v___x_2491_;
}
else
{
lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2492_ = l_Std_Http_URI_Query_insertEncoded(v_b_2465_, v_val_2487_, v___x_2490_);
v___x_2493_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2461_, v___x_2462_, v___x_2463_, v_it_2467_, v___x_2492_);
return v___x_2493_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg___boxed(lean_object* v___x_2526_, lean_object* v___x_2527_, lean_object* v___x_2528_, lean_object* v_a_2529_, lean_object* v_b_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2526_, v___x_2527_, v___x_2528_, v_a_2529_, v_b_2530_);
lean_dec_ref(v___x_2527_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(lean_object* v___x_2532_, lean_object* v___x_2533_, lean_object* v_a_2534_, lean_object* v_b_2535_){
_start:
{
lean_object* v_it_2537_; 
if (lean_obj_tag(v_a_2534_) == 0)
{
lean_object* v_currPos_2541_; lean_object* v_searcher_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2568_; 
v_currPos_2541_ = lean_ctor_get(v_a_2534_, 0);
v_searcher_2542_ = lean_ctor_get(v_a_2534_, 1);
v_isSharedCheck_2568_ = !lean_is_exclusive(v_a_2534_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2544_ = v_a_2534_;
v_isShared_2545_ = v_isSharedCheck_2568_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_searcher_2542_);
lean_inc(v_currPos_2541_);
lean_dec(v_a_2534_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2568_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v_str_2546_; lean_object* v_startInclusive_2547_; lean_object* v_endExclusive_2548_; lean_object* v___x_2549_; uint8_t v___x_2550_; 
v_str_2546_ = lean_ctor_get(v___x_2532_, 0);
v_startInclusive_2547_ = lean_ctor_get(v___x_2532_, 1);
v_endExclusive_2548_ = lean_ctor_get(v___x_2532_, 2);
v___x_2549_ = lean_nat_sub(v_endExclusive_2548_, v_startInclusive_2547_);
v___x_2550_ = lean_nat_dec_eq(v_searcher_2542_, v___x_2549_);
lean_dec(v___x_2549_);
if (v___x_2550_ == 0)
{
uint32_t v___x_2551_; lean_object* v___x_2552_; uint32_t v___x_2553_; uint8_t v___x_2554_; 
v___x_2551_ = 38;
v___x_2552_ = lean_nat_add(v_startInclusive_2547_, v_searcher_2542_);
v___x_2553_ = lean_string_utf8_get_fast(v_str_2546_, v___x_2552_);
v___x_2554_ = lean_uint32_dec_eq(v___x_2553_, v___x_2551_);
if (v___x_2554_ == 0)
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2558_; 
lean_dec(v_searcher_2542_);
v___x_2555_ = lean_string_utf8_next_fast(v_str_2546_, v___x_2552_);
lean_dec(v___x_2552_);
v___x_2556_ = lean_nat_sub(v___x_2555_, v_startInclusive_2547_);
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 1, v___x_2556_);
v___x_2558_ = v___x_2544_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_currPos_2541_);
lean_ctor_set(v_reuseFailAlloc_2560_, 1, v___x_2556_);
v___x_2558_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
v_a_2534_ = v___x_2558_;
goto _start;
}
}
else
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v_nextIt_2565_; 
lean_dec(v_currPos_2541_);
v___x_2561_ = lean_string_utf8_next_fast(v_str_2546_, v___x_2552_);
v___x_2562_ = lean_nat_sub(v___x_2561_, v___x_2552_);
lean_dec(v___x_2552_);
v___x_2563_ = lean_nat_add(v_searcher_2542_, v___x_2562_);
lean_dec(v___x_2562_);
lean_dec(v_searcher_2542_);
lean_inc(v___x_2563_);
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 1, v___x_2563_);
lean_ctor_set(v___x_2544_, 0, v___x_2563_);
v_nextIt_2565_ = v___x_2544_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v___x_2563_);
lean_ctor_set(v_reuseFailAlloc_2566_, 1, v___x_2563_);
v_nextIt_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
v_it_2537_ = v_nextIt_2565_;
goto v___jp_2536_;
}
}
}
else
{
lean_object* v___x_2567_; 
lean_del_object(v___x_2544_);
lean_dec(v_searcher_2542_);
lean_dec(v_currPos_2541_);
v___x_2567_ = lean_box(1);
v_it_2537_ = v___x_2567_;
goto v___jp_2536_;
}
}
}
else
{
return v_b_2535_;
}
v___jp_2536_:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = lean_unsigned_to_nat(1u);
v___x_2539_ = lean_nat_add(v_b_2535_, v___x_2538_);
lean_dec(v_b_2535_);
v_a_2534_ = v_it_2537_;
v_b_2535_ = v___x_2539_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg___boxed(lean_object* v___x_2569_, lean_object* v___x_2570_, lean_object* v_a_2571_, lean_object* v_b_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2569_, v___x_2570_, v_a_2571_, v_b_2572_);
lean_dec(v___x_2570_);
lean_dec_ref(v___x_2569_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(lean_object* v___x_2574_, lean_object* v___x_2575_, lean_object* v___x_2576_, lean_object* v_a_2577_, lean_object* v_b_2578_){
_start:
{
lean_object* v_it_2580_; 
if (lean_obj_tag(v_a_2577_) == 0)
{
lean_object* v_currPos_2584_; lean_object* v_searcher_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2611_; 
v_currPos_2584_ = lean_ctor_get(v_a_2577_, 0);
v_searcher_2585_ = lean_ctor_get(v_a_2577_, 1);
v_isSharedCheck_2611_ = !lean_is_exclusive(v_a_2577_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2587_ = v_a_2577_;
v_isShared_2588_ = v_isSharedCheck_2611_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_searcher_2585_);
lean_inc(v_currPos_2584_);
lean_dec(v_a_2577_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2611_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v_str_2589_; lean_object* v_startInclusive_2590_; lean_object* v_endExclusive_2591_; lean_object* v___x_2592_; uint8_t v___x_2593_; 
v_str_2589_ = lean_ctor_get(v___x_2575_, 0);
v_startInclusive_2590_ = lean_ctor_get(v___x_2575_, 1);
v_endExclusive_2591_ = lean_ctor_get(v___x_2575_, 2);
v___x_2592_ = lean_nat_sub(v_endExclusive_2591_, v_startInclusive_2590_);
v___x_2593_ = lean_nat_dec_eq(v_searcher_2585_, v___x_2592_);
lean_dec(v___x_2592_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2594_; uint32_t v___x_2595_; uint32_t v___x_2596_; uint8_t v___x_2597_; 
v___x_2594_ = lean_nat_add(v_startInclusive_2590_, v_searcher_2585_);
v___x_2595_ = lean_string_utf8_get_fast(v_str_2589_, v___x_2594_);
v___x_2596_ = 38;
v___x_2597_ = lean_uint32_dec_eq(v___x_2595_, v___x_2596_);
if (v___x_2597_ == 0)
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2601_; 
lean_dec(v_searcher_2585_);
v___x_2598_ = lean_string_utf8_next_fast(v_str_2589_, v___x_2594_);
lean_dec(v___x_2594_);
v___x_2599_ = lean_nat_sub(v___x_2598_, v_startInclusive_2590_);
if (v_isShared_2588_ == 0)
{
lean_ctor_set(v___x_2587_, 1, v___x_2599_);
v___x_2601_ = v___x_2587_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_currPos_2584_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v___x_2599_);
v___x_2601_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
lean_object* v___x_2602_; 
v___x_2602_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2575_, v___x_2576_, v___x_2601_, v_b_2578_);
return v___x_2602_;
}
}
else
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v_nextIt_2608_; 
lean_dec(v_currPos_2584_);
v___x_2604_ = lean_string_utf8_next_fast(v_str_2589_, v___x_2594_);
v___x_2605_ = lean_nat_sub(v___x_2604_, v___x_2594_);
lean_dec(v___x_2594_);
v___x_2606_ = lean_nat_add(v_searcher_2585_, v___x_2605_);
lean_dec(v___x_2605_);
lean_dec(v_searcher_2585_);
lean_inc(v___x_2606_);
if (v_isShared_2588_ == 0)
{
lean_ctor_set(v___x_2587_, 1, v___x_2606_);
lean_ctor_set(v___x_2587_, 0, v___x_2606_);
v_nextIt_2608_ = v___x_2587_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2606_);
lean_ctor_set(v_reuseFailAlloc_2609_, 1, v___x_2606_);
v_nextIt_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
v_it_2580_ = v_nextIt_2608_;
goto v___jp_2579_;
}
}
}
else
{
lean_object* v___x_2610_; 
lean_del_object(v___x_2587_);
lean_dec(v_searcher_2585_);
lean_dec(v_currPos_2584_);
v___x_2610_ = lean_box(1);
v_it_2580_ = v___x_2610_;
goto v___jp_2579_;
}
}
}
else
{
return v_b_2578_;
}
v___jp_2579_:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2581_ = lean_unsigned_to_nat(1u);
v___x_2582_ = lean_nat_add(v_b_2578_, v___x_2581_);
lean_dec(v_b_2578_);
v___x_2583_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2575_, v___x_2576_, v_it_2580_, v___x_2582_);
return v___x_2583_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg___boxed(lean_object* v___x_2612_, lean_object* v___x_2613_, lean_object* v___x_2614_, lean_object* v_a_2615_, lean_object* v_b_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2612_, v___x_2613_, v___x_2614_, v_a_2615_, v_b_2616_);
lean_dec(v___x_2614_);
lean_dec_ref(v___x_2613_);
lean_dec_ref(v___x_2612_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(lean_object* v_config_2623_, lean_object* v_a_2624_){
_start:
{
lean_object* v_maxQueryLength_2625_; lean_object* v_maxQueryParams_2626_; lean_object* v___f_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v_fst_2630_; lean_object* v_snd_2631_; lean_object* v_array_2632_; lean_object* v_idx_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2683_; 
v_maxQueryLength_2625_ = lean_ctor_get(v_config_2623_, 4);
lean_inc(v_maxQueryLength_2625_);
v_maxQueryParams_2626_ = lean_ctor_get(v_config_2623_, 8);
lean_inc(v_maxQueryParams_2626_);
lean_dec_ref(v_config_2623_);
v___f_2627_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2628_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2624_);
v___x_2629_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo_findEnd(v___f_2627_, v_maxQueryLength_2625_, v___x_2628_, v_a_2624_);
lean_dec(v_maxQueryLength_2625_);
v_fst_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_fst_2630_);
v_snd_2631_ = lean_ctor_get(v___x_2629_, 1);
lean_inc(v_snd_2631_);
lean_dec_ref(v___x_2629_);
v_array_2632_ = lean_ctor_get(v_a_2624_, 0);
v_idx_2633_ = lean_ctor_get(v_a_2624_, 1);
v_isSharedCheck_2683_ = !lean_is_exclusive(v_a_2624_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2635_ = v_a_2624_;
v_isShared_2636_ = v_isSharedCheck_2683_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_idx_2633_);
lean_inc(v_array_2632_);
lean_dec(v_a_2624_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2683_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v_lower_2638_; lean_object* v_upper_2639_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___y_2680_; uint8_t v___x_2682_; 
v___x_2677_ = lean_nat_add(v_idx_2633_, v_fst_2630_);
lean_dec(v_fst_2630_);
v___x_2678_ = lean_byte_array_size(v_array_2632_);
v___x_2682_ = lean_nat_dec_le(v_idx_2633_, v___x_2628_);
if (v___x_2682_ == 0)
{
v___y_2680_ = v_idx_2633_;
goto v___jp_2679_;
}
else
{
lean_dec(v_idx_2633_);
v___y_2680_ = v___x_2628_;
goto v___jp_2679_;
}
v___jp_2637_:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; 
v___x_2640_ = l_ByteArray_toByteSlice(v_array_2632_, v_lower_2638_, v_upper_2639_);
v___x_2641_ = l_ByteSlice_toByteArray(v___x_2640_);
v___x_2642_ = lean_string_validate_utf8(v___x_2641_);
if (v___x_2642_ == 0)
{
lean_object* v___x_2643_; lean_object* v___x_2645_; 
lean_dec_ref(v___x_2641_);
lean_dec(v_maxQueryParams_2626_);
v___x_2643_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2636_ == 0)
{
lean_ctor_set_tag(v___x_2635_, 1);
lean_ctor_set(v___x_2635_, 1, v___x_2643_);
lean_ctor_set(v___x_2635_, 0, v_snd_2631_);
v___x_2645_ = v___x_2635_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_snd_2631_);
lean_ctor_set(v_reuseFailAlloc_2646_, 1, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
else
{
lean_object* v___x_2647_; lean_object* v___x_2648_; uint8_t v___x_2649_; 
v___x_2647_ = lean_string_from_utf8_unchecked(v___x_2641_);
v___x_2648_ = lean_string_utf8_byte_size(v___x_2647_);
v___x_2649_ = lean_nat_dec_eq(v___x_2648_, v___x_2628_);
if (v___x_2649_ == 0)
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; uint8_t v___x_2653_; 
lean_inc_ref(v___x_2647_);
v___x_2650_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2647_);
lean_ctor_set(v___x_2650_, 1, v___x_2628_);
lean_ctor_set(v___x_2650_, 2, v___x_2648_);
v___x_2651_ = l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(v___x_2650_);
lean_inc(v___x_2651_);
v___x_2652_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2647_, v___x_2650_, v___x_2648_, v___x_2651_, v___x_2628_);
v___x_2653_ = lean_nat_dec_lt(v_maxQueryParams_2626_, v___x_2652_);
lean_dec(v___x_2652_);
if (v___x_2653_ == 0)
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
lean_dec(v_maxQueryParams_2626_);
v___x_2654_ = l_Std_Http_URI_Query_empty;
v___x_2655_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2647_, v___x_2650_, v___x_2648_, v___x_2651_, v___x_2654_);
lean_dec_ref(v___x_2650_);
if (lean_obj_tag(v___x_2655_) == 1)
{
lean_object* v_val_2656_; lean_object* v___x_2658_; 
v_val_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_val_2656_);
lean_dec_ref(v___x_2655_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 1, v_val_2656_);
lean_ctor_set(v___x_2635_, 0, v_snd_2631_);
v___x_2658_ = v___x_2635_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_snd_2631_);
lean_ctor_set(v_reuseFailAlloc_2659_, 1, v_val_2656_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
else
{
lean_object* v___x_2660_; lean_object* v___x_2662_; 
lean_dec(v___x_2655_);
v___x_2660_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2636_ == 0)
{
lean_ctor_set_tag(v___x_2635_, 1);
lean_ctor_set(v___x_2635_, 1, v___x_2660_);
lean_ctor_set(v___x_2635_, 0, v_snd_2631_);
v___x_2662_ = v___x_2635_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_snd_2631_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v___x_2660_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
else
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2671_; 
lean_dec(v___x_2651_);
lean_dec_ref(v___x_2650_);
lean_dec_ref(v___x_2647_);
v___x_2664_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3));
v___x_2665_ = l_Nat_reprFast(v_maxQueryParams_2626_);
v___x_2666_ = lean_string_append(v___x_2664_, v___x_2665_);
lean_dec_ref(v___x_2665_);
v___x_2667_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__3));
v___x_2668_ = lean_string_append(v___x_2666_, v___x_2667_);
v___x_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2668_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set_tag(v___x_2635_, 1);
lean_ctor_set(v___x_2635_, 1, v___x_2669_);
lean_ctor_set(v___x_2635_, 0, v_snd_2631_);
v___x_2671_ = v___x_2635_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_snd_2631_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v___x_2669_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
else
{
lean_object* v___x_2673_; lean_object* v___x_2675_; 
lean_dec_ref(v___x_2647_);
lean_dec(v_maxQueryParams_2626_);
v___x_2673_ = l_Std_Http_URI_Query_empty;
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 1, v___x_2673_);
lean_ctor_set(v___x_2635_, 0, v_snd_2631_);
v___x_2675_ = v___x_2635_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_snd_2631_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v___x_2673_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
v___jp_2679_:
{
uint8_t v___x_2681_; 
v___x_2681_ = lean_nat_dec_le(v___x_2677_, v___x_2678_);
if (v___x_2681_ == 0)
{
lean_dec(v___x_2677_);
v_lower_2638_ = v___y_2680_;
v_upper_2639_ = v___x_2678_;
goto v___jp_2637_;
}
else
{
v_lower_2638_ = v___y_2680_;
v_upper_2639_ = v___x_2677_;
goto v___jp_2637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(lean_object* v___x_2684_, lean_object* v___x_2685_, lean_object* v___x_2686_, lean_object* v_inst_2687_, lean_object* v_R_2688_, lean_object* v_a_2689_, lean_object* v_b_2690_, lean_object* v_c_2691_){
_start:
{
lean_object* v___x_2692_; 
v___x_2692_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2684_, v___x_2685_, v___x_2686_, v_a_2689_, v_b_2690_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___boxed(lean_object* v___x_2693_, lean_object* v___x_2694_, lean_object* v___x_2695_, lean_object* v_inst_2696_, lean_object* v_R_2697_, lean_object* v_a_2698_, lean_object* v_b_2699_, lean_object* v_c_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(v___x_2693_, v___x_2694_, v___x_2695_, v_inst_2696_, v_R_2697_, v_a_2698_, v_b_2699_, v_c_2700_);
lean_dec(v___x_2695_);
lean_dec_ref(v___x_2694_);
lean_dec_ref(v___x_2693_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(lean_object* v_out_2702_, lean_object* v_inst_2703_, lean_object* v_R_2704_, lean_object* v_a_2705_, lean_object* v_b_2706_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_2702_, v_a_2705_, v_b_2706_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___boxed(lean_object* v_out_2708_, lean_object* v_inst_2709_, lean_object* v_R_2710_, lean_object* v_a_2711_, lean_object* v_b_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(v_out_2708_, v_inst_2709_, v_R_2710_, v_a_2711_, v_b_2712_);
lean_dec_ref(v_out_2708_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(lean_object* v___x_2714_, lean_object* v___x_2715_, lean_object* v___x_2716_, lean_object* v_inst_2717_, lean_object* v_R_2718_, lean_object* v_a_2719_, lean_object* v_b_2720_, lean_object* v_c_2721_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2714_, v___x_2715_, v___x_2716_, v_a_2719_, v_b_2720_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___boxed(lean_object* v___x_2723_, lean_object* v___x_2724_, lean_object* v___x_2725_, lean_object* v_inst_2726_, lean_object* v_R_2727_, lean_object* v_a_2728_, lean_object* v_b_2729_, lean_object* v_c_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(v___x_2723_, v___x_2724_, v___x_2725_, v_inst_2726_, v_R_2727_, v_a_2728_, v_b_2729_, v_c_2730_);
lean_dec_ref(v___x_2724_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(lean_object* v___x_2732_, lean_object* v___x_2733_, lean_object* v___x_2734_, lean_object* v_inst_2735_, lean_object* v_R_2736_, lean_object* v_a_2737_, lean_object* v_b_2738_, lean_object* v_c_2739_){
_start:
{
lean_object* v___x_2740_; 
v___x_2740_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2733_, v___x_2734_, v_a_2737_, v_b_2738_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___boxed(lean_object* v___x_2741_, lean_object* v___x_2742_, lean_object* v___x_2743_, lean_object* v_inst_2744_, lean_object* v_R_2745_, lean_object* v_a_2746_, lean_object* v_b_2747_, lean_object* v_c_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(v___x_2741_, v___x_2742_, v___x_2743_, v_inst_2744_, v_R_2745_, v_a_2746_, v_b_2747_, v_c_2748_);
lean_dec(v___x_2743_);
lean_dec_ref(v___x_2742_);
lean_dec_ref(v___x_2741_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(lean_object* v___x_2750_, lean_object* v___x_2751_, lean_object* v___x_2752_, lean_object* v_inst_2753_, lean_object* v_R_2754_, lean_object* v_a_2755_, lean_object* v_b_2756_, lean_object* v_c_2757_){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2750_, v___x_2751_, v___x_2752_, v_a_2755_, v_b_2756_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___boxed(lean_object* v___x_2759_, lean_object* v___x_2760_, lean_object* v___x_2761_, lean_object* v_inst_2762_, lean_object* v_R_2763_, lean_object* v_a_2764_, lean_object* v_b_2765_, lean_object* v_c_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(v___x_2759_, v___x_2760_, v___x_2761_, v_inst_2762_, v_R_2763_, v_a_2764_, v_b_2765_, v_c_2766_);
lean_dec_ref(v___x_2760_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(lean_object* v_config_2771_, lean_object* v_a_2772_){
_start:
{
lean_object* v_maxFragmentLength_2773_; lean_object* v___f_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v_fst_2777_; lean_object* v_snd_2778_; lean_object* v_array_2779_; lean_object* v_idx_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2804_; 
v_maxFragmentLength_2773_ = lean_ctor_get(v_config_2771_, 5);
v___f_2774_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2775_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2772_);
v___x_2776_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo_findEnd(v___f_2774_, v_maxFragmentLength_2773_, v___x_2775_, v_a_2772_);
v_fst_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_fst_2777_);
v_snd_2778_ = lean_ctor_get(v___x_2776_, 1);
lean_inc(v_snd_2778_);
lean_dec_ref(v___x_2776_);
v_array_2779_ = lean_ctor_get(v_a_2772_, 0);
v_idx_2780_ = lean_ctor_get(v_a_2772_, 1);
v_isSharedCheck_2804_ = !lean_is_exclusive(v_a_2772_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2782_ = v_a_2772_;
v_isShared_2783_ = v_isSharedCheck_2804_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_idx_2780_);
lean_inc(v_array_2779_);
lean_dec(v_a_2772_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2804_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v_lower_2785_; lean_object* v_upper_2786_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___y_2801_; uint8_t v___x_2803_; 
v___x_2798_ = lean_nat_add(v_idx_2780_, v_fst_2777_);
lean_dec(v_fst_2777_);
v___x_2799_ = lean_byte_array_size(v_array_2779_);
v___x_2803_ = lean_nat_dec_le(v_idx_2780_, v___x_2775_);
if (v___x_2803_ == 0)
{
v___y_2801_ = v_idx_2780_;
goto v___jp_2800_;
}
else
{
lean_dec(v_idx_2780_);
v___y_2801_ = v___x_2775_;
goto v___jp_2800_;
}
v___jp_2784_:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2787_ = l_ByteArray_toByteSlice(v_array_2779_, v_lower_2785_, v_upper_2786_);
v___x_2788_ = l_ByteSlice_toByteArray(v___x_2787_);
v___x_2789_ = l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(v___x_2788_);
if (lean_obj_tag(v___x_2789_) == 1)
{
lean_object* v_val_2790_; lean_object* v___x_2792_; 
v_val_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_val_2790_);
lean_dec_ref(v___x_2789_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 1, v_val_2790_);
lean_ctor_set(v___x_2782_, 0, v_snd_2778_);
v___x_2792_ = v___x_2782_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_snd_2778_);
lean_ctor_set(v_reuseFailAlloc_2793_, 1, v_val_2790_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
else
{
lean_object* v___x_2794_; lean_object* v___x_2796_; 
lean_dec(v___x_2789_);
v___x_2794_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1));
if (v_isShared_2783_ == 0)
{
lean_ctor_set_tag(v___x_2782_, 1);
lean_ctor_set(v___x_2782_, 1, v___x_2794_);
lean_ctor_set(v___x_2782_, 0, v_snd_2778_);
v___x_2796_ = v___x_2782_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_snd_2778_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v___x_2794_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
v___jp_2800_:
{
uint8_t v___x_2802_; 
v___x_2802_ = lean_nat_dec_le(v___x_2798_, v___x_2799_);
if (v___x_2802_ == 0)
{
lean_dec(v___x_2798_);
v_lower_2785_ = v___y_2801_;
v_upper_2786_ = v___x_2799_;
goto v___jp_2784_;
}
else
{
v_lower_2785_ = v___y_2801_;
v_upper_2786_ = v___x_2798_;
goto v___jp_2784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___boxed(lean_object* v_config_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2805_, v_a_2806_);
lean_dec_ref(v_config_2805_);
return v_res_2807_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1(void){
_start:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0));
v___x_2810_ = lean_string_to_utf8(v___x_2809_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(lean_object* v_config_2811_, lean_object* v_a_2812_){
_start:
{
lean_object* v_pos_2814_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2849_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1);
lean_inc_ref(v_a_2812_);
v___x_2850_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2849_, v_a_2812_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_pos_2851_; 
lean_dec_ref(v_a_2812_);
v_pos_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_pos_2851_);
lean_dec_ref(v___x_2850_);
v_pos_2814_ = v_pos_2851_;
goto v___jp_2813_;
}
else
{
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_pos_2852_; 
lean_dec_ref(v_a_2812_);
v_pos_2852_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_pos_2852_);
lean_dec_ref(v___x_2850_);
v_pos_2814_ = v_pos_2852_;
goto v___jp_2813_;
}
else
{
lean_object* v_err_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2884_; 
v_err_2853_ = lean_ctor_get(v___x_2850_, 1);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2884_ == 0)
{
lean_object* v_unused_2885_; 
v_unused_2885_ = lean_ctor_get(v___x_2850_, 0);
lean_dec(v_unused_2885_);
v___x_2855_ = v___x_2850_;
v_isShared_2856_ = v_isSharedCheck_2884_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_err_2853_);
lean_dec(v___x_2850_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2884_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v_idx_2857_; uint8_t v___x_2858_; 
v_idx_2857_ = lean_ctor_get(v_a_2812_, 1);
v___x_2858_ = lean_nat_dec_eq(v_idx_2857_, v_idx_2857_);
if (v___x_2858_ == 0)
{
lean_object* v___x_2860_; 
lean_dec_ref(v_config_2811_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v_a_2812_);
v___x_2860_ = v___x_2855_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2812_);
lean_ctor_set(v_reuseFailAlloc_2861_, 1, v_err_2853_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
else
{
uint8_t v___x_2862_; lean_object* v___x_2863_; 
lean_del_object(v___x_2855_);
lean_dec(v_err_2853_);
v___x_2862_ = 0;
v___x_2863_ = l_Std_Http_URI_Parser_parsePath(v_config_2811_, v___x_2862_, v___x_2858_, v_a_2812_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_pos_2864_; lean_object* v_res_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2874_; 
v_pos_2864_ = lean_ctor_get(v___x_2863_, 0);
v_res_2865_ = lean_ctor_get(v___x_2863_, 1);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2867_ = v___x_2863_;
v_isShared_2868_ = v_isSharedCheck_2874_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_res_2865_);
lean_inc(v_pos_2864_);
lean_dec(v___x_2863_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2874_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2872_; 
v___x_2869_ = lean_box(0);
v___x_2870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2869_);
lean_ctor_set(v___x_2870_, 1, v_res_2865_);
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 1, v___x_2870_);
v___x_2872_ = v___x_2867_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_pos_2864_);
lean_ctor_set(v_reuseFailAlloc_2873_, 1, v___x_2870_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
else
{
lean_object* v_pos_2875_; lean_object* v_err_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
v_pos_2875_ = lean_ctor_get(v___x_2863_, 0);
v_err_2876_ = lean_ctor_get(v___x_2863_, 1);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2863_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_err_2876_);
lean_inc(v_pos_2875_);
lean_dec(v___x_2863_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_pos_2875_);
lean_ctor_set(v_reuseFailAlloc_2882_, 1, v_err_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
}
}
}
v___jp_2813_:
{
lean_object* v___x_2815_; 
v___x_2815_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_2811_, v_pos_2814_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_pos_2816_; lean_object* v_res_2817_; uint8_t v___x_2818_; lean_object* v___x_2819_; 
v_pos_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_pos_2816_);
v_res_2817_ = lean_ctor_get(v___x_2815_, 1);
lean_inc(v_res_2817_);
lean_dec_ref(v___x_2815_);
v___x_2818_ = 1;
v___x_2819_ = l_Std_Http_URI_Parser_parsePath(v_config_2811_, v___x_2818_, v___x_2818_, v_pos_2816_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_pos_2820_; lean_object* v_res_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2830_; 
v_pos_2820_ = lean_ctor_get(v___x_2819_, 0);
v_res_2821_ = lean_ctor_get(v___x_2819_, 1);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2823_ = v___x_2819_;
v_isShared_2824_ = v_isSharedCheck_2830_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_res_2821_);
lean_inc(v_pos_2820_);
lean_dec(v___x_2819_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2830_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2828_; 
v___x_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2825_, 0, v_res_2817_);
v___x_2826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2825_);
lean_ctor_set(v___x_2826_, 1, v_res_2821_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 1, v___x_2826_);
v___x_2828_ = v___x_2823_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_pos_2820_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v___x_2826_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
else
{
lean_object* v_pos_2831_; lean_object* v_err_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
lean_dec(v_res_2817_);
v_pos_2831_ = lean_ctor_get(v___x_2819_, 0);
v_err_2832_ = lean_ctor_get(v___x_2819_, 1);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2819_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_err_2832_);
lean_inc(v_pos_2831_);
lean_dec(v___x_2819_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_pos_2831_);
lean_ctor_set(v_reuseFailAlloc_2838_, 1, v_err_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
else
{
lean_object* v_pos_2840_; lean_object* v_err_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2848_; 
lean_dec_ref(v_config_2811_);
v_pos_2840_ = lean_ctor_get(v___x_2815_, 0);
v_err_2841_ = lean_ctor_get(v___x_2815_, 1);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2843_ = v___x_2815_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_err_2841_);
lean_inc(v_pos_2840_);
lean_dec(v___x_2815_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_pos_2840_);
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
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__0(void){
_start:
{
uint8_t v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v___x_2887_ = lean_uint8_to_nat(v___x_2886_);
return v___x_2887_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__1(void){
_start:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2888_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__0, &l_Std_Http_URI_Parser_parseURI___closed__0_once, _init_l_Std_Http_URI_Parser_parseURI___closed__0);
v___x_2889_ = l_Nat_reprFast(v___x_2888_);
return v___x_2889_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__2(void){
_start:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2890_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__1, &l_Std_Http_URI_Parser_parseURI___closed__1_once, _init_l_Std_Http_URI_Parser_parseURI___closed__1);
v___x_2891_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_2892_ = lean_string_append(v___x_2891_, v___x_2890_);
return v___x_2892_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__3(void){
_start:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2893_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_2894_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__2, &l_Std_Http_URI_Parser_parseURI___closed__2_once, _init_l_Std_Http_URI_Parser_parseURI___closed__2);
v___x_2895_ = lean_string_append(v___x_2894_, v___x_2893_);
return v___x_2895_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__4(void){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2896_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__3, &l_Std_Http_URI_Parser_parseURI___closed__3_once, _init_l_Std_Http_URI_Parser_parseURI___closed__3);
v___x_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2896_);
return v___x_2897_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__7(void){
_start:
{
uint8_t v___x_2901_; lean_object* v___x_2902_; 
v___x_2901_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v___x_2902_ = lean_uint8_to_nat(v___x_2901_);
return v___x_2902_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__8(void){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2903_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__7, &l_Std_Http_URI_Parser_parseURI___closed__7_once, _init_l_Std_Http_URI_Parser_parseURI___closed__7);
v___x_2904_ = l_Nat_reprFast(v___x_2903_);
return v___x_2904_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__9(void){
_start:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2905_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__8, &l_Std_Http_URI_Parser_parseURI___closed__8_once, _init_l_Std_Http_URI_Parser_parseURI___closed__8);
v___x_2906_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_2907_ = lean_string_append(v___x_2906_, v___x_2905_);
return v___x_2907_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__10(void){
_start:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v___x_2908_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_2909_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__9, &l_Std_Http_URI_Parser_parseURI___closed__9_once, _init_l_Std_Http_URI_Parser_parseURI___closed__9);
v___x_2910_ = lean_string_append(v___x_2909_, v___x_2908_);
return v___x_2910_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__11(void){
_start:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2911_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__10, &l_Std_Http_URI_Parser_parseURI___closed__10_once, _init_l_Std_Http_URI_Parser_parseURI___closed__10);
v___x_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2911_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURI(lean_object* v_config_2913_, lean_object* v_a_2914_){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_2913_, v_a_2914_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_pos_2916_; lean_object* v_res_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_3057_; 
v_pos_2916_ = lean_ctor_get(v___x_2915_, 0);
v_res_2917_ = lean_ctor_get(v___x_2915_, 1);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_2919_ = v___x_2915_;
v_isShared_2920_ = v_isSharedCheck_3057_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_res_2917_);
lean_inc(v_pos_2916_);
lean_dec(v___x_2915_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_3057_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v_array_2921_; lean_object* v_idx_2922_; lean_object* v___x_2923_; uint8_t v___x_2924_; 
v_array_2921_ = lean_ctor_get(v_pos_2916_, 0);
v_idx_2922_ = lean_ctor_get(v_pos_2916_, 1);
v___x_2923_ = lean_byte_array_size(v_array_2921_);
v___x_2924_ = lean_nat_dec_lt(v_idx_2922_, v___x_2923_);
if (v___x_2924_ == 0)
{
lean_object* v___x_2925_; lean_object* v___x_2927_; 
lean_dec(v_res_2917_);
lean_dec_ref(v_config_2913_);
v___x_2925_ = lean_box(0);
if (v_isShared_2920_ == 0)
{
lean_ctor_set_tag(v___x_2919_, 1);
lean_ctor_set(v___x_2919_, 1, v___x_2925_);
v___x_2927_ = v___x_2919_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_pos_2916_);
lean_ctor_set(v_reuseFailAlloc_2928_, 1, v___x_2925_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
else
{
uint8_t v___x_2929_; uint8_t v_c_2930_; uint8_t v___x_2931_; 
v___x_2929_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v_c_2930_ = lean_byte_array_fget(v_array_2921_, v_idx_2922_);
v___x_2931_ = lean_uint8_dec_eq(v_c_2930_, v___x_2929_);
if (v___x_2931_ == 0)
{
lean_object* v___x_2932_; lean_object* v___x_2934_; 
lean_dec(v_res_2917_);
lean_dec_ref(v_config_2913_);
v___x_2932_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
if (v_isShared_2920_ == 0)
{
lean_ctor_set_tag(v___x_2919_, 1);
lean_ctor_set(v___x_2919_, 1, v___x_2932_);
v___x_2934_ = v___x_2919_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_pos_2916_);
lean_ctor_set(v_reuseFailAlloc_2935_, 1, v___x_2932_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
else
{
lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_3054_; 
lean_inc(v_idx_2922_);
lean_inc_ref(v_array_2921_);
v_isSharedCheck_3054_ = !lean_is_exclusive(v_pos_2916_);
if (v_isSharedCheck_3054_ == 0)
{
lean_object* v_unused_3055_; lean_object* v_unused_3056_; 
v_unused_3055_ = lean_ctor_get(v_pos_2916_, 1);
lean_dec(v_unused_3055_);
v_unused_3056_ = lean_ctor_get(v_pos_2916_, 0);
lean_dec(v_unused_3056_);
v___x_2937_ = v_pos_2916_;
v_isShared_2938_ = v_isSharedCheck_3054_;
goto v_resetjp_2936_;
}
else
{
lean_dec(v_pos_2916_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_3054_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v_it_x27_2942_; 
v___x_2939_ = lean_unsigned_to_nat(1u);
v___x_2940_ = lean_nat_add(v_idx_2922_, v___x_2939_);
lean_dec(v_idx_2922_);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 1, v___x_2940_);
v_it_x27_2942_ = v___x_2937_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_array_2921_);
lean_ctor_set(v_reuseFailAlloc_3053_, 1, v___x_2940_);
v_it_x27_2942_ = v_reuseFailAlloc_3053_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
lean_object* v___x_2943_; 
lean_inc_ref(v_config_2913_);
v___x_2943_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2913_, v_it_x27_2942_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_res_2944_; lean_object* v_pos_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_3043_; 
v_res_2944_ = lean_ctor_get(v___x_2943_, 1);
v_pos_2945_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_2947_ = v___x_2943_;
v_isShared_2948_ = v_isSharedCheck_3043_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_res_2944_);
lean_inc(v_pos_2945_);
lean_dec(v___x_2943_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_3043_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v_fst_2949_; lean_object* v_snd_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_3042_; 
v_fst_2949_ = lean_ctor_get(v_res_2944_, 0);
v_snd_2950_ = lean_ctor_get(v_res_2944_, 1);
v_isSharedCheck_3042_ = !lean_is_exclusive(v_res_2944_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_2952_ = v_res_2944_;
v_isShared_2953_ = v_isSharedCheck_3042_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_snd_2950_);
lean_inc(v_fst_2949_);
lean_dec(v_res_2944_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_3042_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___y_2955_; lean_object* v_pos_2956_; lean_object* v_res_2957_; lean_object* v___y_2963_; lean_object* v_idx_2964_; lean_object* v_pos_2965_; lean_object* v_idx_2966_; lean_object* v_err_2967_; lean_object* v___y_2974_; lean_object* v_idx_2975_; lean_object* v_pos_2976_; lean_object* v_err_2977_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v_array_3008_; lean_object* v_idx_3009_; lean_object* v_pos_3011_; lean_object* v_idx_3012_; lean_object* v_err_3013_; lean_object* v___x_3019_; uint8_t v___x_3020_; 
v_array_3008_ = lean_ctor_get(v_pos_2945_, 0);
v_idx_3009_ = lean_ctor_get(v_pos_2945_, 1);
lean_inc(v_idx_3009_);
v___x_3019_ = lean_byte_array_size(v_array_3008_);
v___x_3020_ = lean_nat_dec_lt(v_idx_3009_, v___x_3019_);
if (v___x_3020_ == 0)
{
lean_object* v___x_3021_; 
v___x_3021_ = lean_box(0);
lean_inc(v_idx_3009_);
v_pos_3011_ = v_pos_2945_;
v_idx_3012_ = v_idx_3009_;
v_err_3013_ = v___x_3021_;
goto v___jp_3010_;
}
else
{
uint8_t v___x_3022_; uint8_t v_c_3023_; uint8_t v___x_3024_; 
v___x_3022_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_c_3023_ = lean_byte_array_fget(v_array_3008_, v_idx_3009_);
v___x_3024_ = lean_uint8_dec_eq(v_c_3023_, v___x_3022_);
if (v___x_3024_ == 0)
{
lean_object* v___x_3025_; 
v___x_3025_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3009_);
v_pos_3011_ = v_pos_2945_;
v_idx_3012_ = v_idx_3009_;
v_err_3013_ = v___x_3025_;
goto v___jp_3010_;
}
else
{
lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3039_; 
lean_inc_ref(v_array_3008_);
v_isSharedCheck_3039_ = !lean_is_exclusive(v_pos_2945_);
if (v_isSharedCheck_3039_ == 0)
{
lean_object* v_unused_3040_; lean_object* v_unused_3041_; 
v_unused_3040_ = lean_ctor_get(v_pos_2945_, 1);
lean_dec(v_unused_3040_);
v_unused_3041_ = lean_ctor_get(v_pos_2945_, 0);
lean_dec(v_unused_3041_);
v___x_3027_ = v_pos_2945_;
v_isShared_3028_ = v_isSharedCheck_3039_;
goto v_resetjp_3026_;
}
else
{
lean_dec(v_pos_2945_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3039_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3029_; lean_object* v_it_x27_3031_; 
v___x_3029_ = lean_nat_add(v_idx_3009_, v___x_2939_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 1, v___x_3029_);
v_it_x27_3031_ = v___x_3027_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_array_3008_);
lean_ctor_set(v_reuseFailAlloc_3038_, 1, v___x_3029_);
v_it_x27_3031_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
lean_object* v___x_3032_; 
lean_inc_ref(v_config_2913_);
v___x_3032_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2913_, v_it_x27_3031_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_pos_3033_; lean_object* v_res_3034_; 
lean_dec(v_idx_3009_);
lean_del_object(v___x_2952_);
v_pos_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_pos_3033_);
v_res_3034_ = lean_ctor_get(v___x_3032_, 1);
lean_inc(v_res_3034_);
lean_dec_ref(v___x_3032_);
v___y_2980_ = v_pos_3033_;
v___y_2981_ = v_res_3034_;
goto v___jp_2979_;
}
else
{
lean_object* v_pos_3035_; lean_object* v_err_3036_; lean_object* v_idx_3037_; 
v_pos_3035_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_pos_3035_);
v_err_3036_ = lean_ctor_get(v___x_3032_, 1);
lean_inc(v_err_3036_);
lean_dec_ref(v___x_3032_);
v_idx_3037_ = lean_ctor_get(v_pos_3035_, 1);
lean_inc(v_idx_3037_);
v_pos_3011_ = v_pos_3035_;
v_idx_3012_ = v_idx_3037_;
v_err_3013_ = v_err_3036_;
goto v___jp_3010_;
}
}
}
}
}
v___jp_2954_:
{
lean_object* v___x_2958_; lean_object* v___x_2960_; 
v___x_2958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2958_, 0, v_res_2917_);
lean_ctor_set(v___x_2958_, 1, v_fst_2949_);
lean_ctor_set(v___x_2958_, 2, v_snd_2950_);
lean_ctor_set(v___x_2958_, 3, v___y_2955_);
lean_ctor_set(v___x_2958_, 4, v_res_2957_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 1, v___x_2958_);
lean_ctor_set(v___x_2947_, 0, v_pos_2956_);
v___x_2960_ = v___x_2947_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_pos_2956_);
lean_ctor_set(v_reuseFailAlloc_2961_, 1, v___x_2958_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
v___jp_2962_:
{
uint8_t v___x_2968_; 
v___x_2968_ = lean_nat_dec_eq(v_idx_2964_, v_idx_2966_);
lean_dec(v_idx_2966_);
lean_dec(v_idx_2964_);
if (v___x_2968_ == 0)
{
lean_object* v___x_2970_; 
lean_dec_ref(v___y_2963_);
lean_dec(v_snd_2950_);
lean_dec(v_fst_2949_);
lean_del_object(v___x_2947_);
lean_dec(v_res_2917_);
if (v_isShared_2920_ == 0)
{
lean_ctor_set_tag(v___x_2919_, 1);
lean_ctor_set(v___x_2919_, 1, v_err_2967_);
lean_ctor_set(v___x_2919_, 0, v_pos_2965_);
v___x_2970_ = v___x_2919_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_pos_2965_);
lean_ctor_set(v_reuseFailAlloc_2971_, 1, v_err_2967_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
else
{
lean_object* v___x_2972_; 
lean_dec(v_err_2967_);
lean_del_object(v___x_2919_);
v___x_2972_ = lean_box(0);
v___y_2955_ = v___y_2963_;
v_pos_2956_ = v_pos_2965_;
v_res_2957_ = v___x_2972_;
goto v___jp_2954_;
}
}
v___jp_2973_:
{
lean_object* v_idx_2978_; 
v_idx_2978_ = lean_ctor_get(v_pos_2976_, 1);
lean_inc(v_idx_2978_);
v___y_2963_ = v___y_2974_;
v_idx_2964_ = v_idx_2975_;
v_pos_2965_ = v_pos_2976_;
v_idx_2966_ = v_idx_2978_;
v_err_2967_ = v_err_2977_;
goto v___jp_2962_;
}
v___jp_2979_:
{
lean_object* v_array_2982_; lean_object* v_idx_2983_; lean_object* v___x_2984_; uint8_t v___x_2985_; 
v_array_2982_ = lean_ctor_get(v___y_2980_, 0);
v_idx_2983_ = lean_ctor_get(v___y_2980_, 1);
lean_inc(v_idx_2983_);
v___x_2984_ = lean_byte_array_size(v_array_2982_);
v___x_2985_ = lean_nat_dec_lt(v_idx_2983_, v___x_2984_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; 
lean_dec_ref(v_config_2913_);
v___x_2986_ = lean_box(0);
lean_inc(v_idx_2983_);
v___y_2963_ = v___y_2981_;
v_idx_2964_ = v_idx_2983_;
v_pos_2965_ = v___y_2980_;
v_idx_2966_ = v_idx_2983_;
v_err_2967_ = v___x_2986_;
goto v___jp_2962_;
}
else
{
uint8_t v___x_2987_; uint8_t v_c_2988_; uint8_t v___x_2989_; 
v___x_2987_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v_c_2988_ = lean_byte_array_fget(v_array_2982_, v_idx_2983_);
v___x_2989_ = lean_uint8_dec_eq(v_c_2988_, v___x_2987_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2990_; 
lean_dec_ref(v_config_2913_);
v___x_2990_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__4, &l_Std_Http_URI_Parser_parseURI___closed__4_once, _init_l_Std_Http_URI_Parser_parseURI___closed__4);
lean_inc(v_idx_2983_);
v___y_2963_ = v___y_2981_;
v_idx_2964_ = v_idx_2983_;
v_pos_2965_ = v___y_2980_;
v_idx_2966_ = v_idx_2983_;
v_err_2967_ = v___x_2990_;
goto v___jp_2962_;
}
else
{
lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3005_; 
lean_inc_ref(v_array_2982_);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___y_2980_);
if (v_isSharedCheck_3005_ == 0)
{
lean_object* v_unused_3006_; lean_object* v_unused_3007_; 
v_unused_3006_ = lean_ctor_get(v___y_2980_, 1);
lean_dec(v_unused_3006_);
v_unused_3007_ = lean_ctor_get(v___y_2980_, 0);
lean_dec(v_unused_3007_);
v___x_2992_ = v___y_2980_;
v_isShared_2993_ = v_isSharedCheck_3005_;
goto v_resetjp_2991_;
}
else
{
lean_dec(v___y_2980_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3005_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2994_; lean_object* v_it_x27_2996_; 
v___x_2994_ = lean_nat_add(v_idx_2983_, v___x_2939_);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 1, v___x_2994_);
v_it_x27_2996_ = v___x_2992_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_array_2982_);
lean_ctor_set(v_reuseFailAlloc_3004_, 1, v___x_2994_);
v_it_x27_2996_ = v_reuseFailAlloc_3004_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
lean_object* v___x_2997_; 
v___x_2997_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2913_, v_it_x27_2996_);
lean_dec_ref(v_config_2913_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_pos_2998_; lean_object* v_res_2999_; lean_object* v___x_3000_; 
v_pos_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_pos_2998_);
v_res_2999_ = lean_ctor_get(v___x_2997_, 1);
lean_inc(v_res_2999_);
lean_dec_ref(v___x_2997_);
v___x_3000_ = l_Std_Http_URI_EncodedFragment_decode(v_res_2999_);
lean_dec(v_res_2999_);
if (lean_obj_tag(v___x_3000_) == 1)
{
lean_dec(v_idx_2983_);
lean_del_object(v___x_2919_);
v___y_2955_ = v___y_2981_;
v_pos_2956_ = v_pos_2998_;
v_res_2957_ = v___x_3000_;
goto v___jp_2954_;
}
else
{
lean_object* v___x_3001_; 
lean_dec(v___x_3000_);
v___x_3001_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__6));
v___y_2974_ = v___y_2981_;
v_idx_2975_ = v_idx_2983_;
v_pos_2976_ = v_pos_2998_;
v_err_2977_ = v___x_3001_;
goto v___jp_2973_;
}
}
else
{
lean_object* v_pos_3002_; lean_object* v_err_3003_; 
v_pos_3002_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_pos_3002_);
v_err_3003_ = lean_ctor_get(v___x_2997_, 1);
lean_inc(v_err_3003_);
lean_dec_ref(v___x_2997_);
v___y_2974_ = v___y_2981_;
v_idx_2975_ = v_idx_2983_;
v_pos_2976_ = v_pos_3002_;
v_err_2977_ = v_err_3003_;
goto v___jp_2973_;
}
}
}
}
}
}
v___jp_3010_:
{
uint8_t v___x_3014_; 
v___x_3014_ = lean_nat_dec_eq(v_idx_3009_, v_idx_3012_);
lean_dec(v_idx_3012_);
lean_dec(v_idx_3009_);
if (v___x_3014_ == 0)
{
lean_object* v___x_3016_; 
lean_dec(v_snd_2950_);
lean_dec(v_fst_2949_);
lean_del_object(v___x_2947_);
lean_del_object(v___x_2919_);
lean_dec(v_res_2917_);
lean_dec_ref(v_config_2913_);
if (v_isShared_2953_ == 0)
{
lean_ctor_set_tag(v___x_2952_, 1);
lean_ctor_set(v___x_2952_, 1, v_err_3013_);
lean_ctor_set(v___x_2952_, 0, v_pos_3011_);
v___x_3016_ = v___x_2952_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_pos_3011_);
lean_ctor_set(v_reuseFailAlloc_3017_, 1, v_err_3013_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
else
{
lean_object* v___x_3018_; 
lean_dec(v_err_3013_);
lean_del_object(v___x_2952_);
v___x_3018_ = l_Std_Http_URI_Query_empty;
v___y_2980_ = v_pos_3011_;
v___y_2981_ = v___x_3018_;
goto v___jp_2979_;
}
}
}
}
}
else
{
lean_object* v_pos_3044_; lean_object* v_err_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3052_; 
lean_del_object(v___x_2919_);
lean_dec(v_res_2917_);
lean_dec_ref(v_config_2913_);
v_pos_3044_ = lean_ctor_get(v___x_2943_, 0);
v_err_3045_ = lean_ctor_get(v___x_2943_, 1);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3047_ = v___x_2943_;
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_err_3045_);
lean_inc(v_pos_3044_);
lean_dec(v___x_2943_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3050_; 
if (v_isShared_3048_ == 0)
{
v___x_3050_ = v___x_3047_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_pos_3044_);
lean_ctor_set(v_reuseFailAlloc_3051_, 1, v_err_3045_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
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
lean_object* v_pos_3058_; lean_object* v_err_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3066_; 
lean_dec_ref(v_config_2913_);
v_pos_3058_ = lean_ctor_get(v___x_2915_, 0);
v_err_3059_ = lean_ctor_get(v___x_2915_, 1);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3061_ = v___x_2915_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_err_3059_);
lean_inc(v_pos_3058_);
lean_dec(v___x_2915_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_pos_3058_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v_err_3059_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0(void){
_start:
{
uint8_t v___x_3067_; lean_object* v___x_3068_; 
v___x_3067_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_3068_ = lean_uint8_to_nat(v___x_3067_);
return v___x_3068_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1(void){
_start:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3069_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0);
v___x_3070_ = l_Nat_reprFast(v___x_3069_);
return v___x_3070_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2(void){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3071_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1);
v___x_3072_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_3073_ = lean_string_append(v___x_3072_, v___x_3071_);
return v___x_3073_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3(void){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3074_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_3075_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2);
v___x_3076_ = lean_string_append(v___x_3075_, v___x_3074_);
return v___x_3076_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4(void){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3077_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3);
v___x_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3077_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(lean_object* v_a_3079_){
_start:
{
lean_object* v_array_3080_; lean_object* v_idx_3081_; lean_object* v___x_3082_; uint8_t v___x_3083_; 
v_array_3080_ = lean_ctor_get(v_a_3079_, 0);
v_idx_3081_ = lean_ctor_get(v_a_3079_, 1);
v___x_3082_ = lean_byte_array_size(v_array_3080_);
v___x_3083_ = lean_nat_dec_lt(v_idx_3081_, v___x_3082_);
if (v___x_3083_ == 0)
{
lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3084_ = lean_box(0);
v___x_3085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3085_, 0, v_a_3079_);
lean_ctor_set(v___x_3085_, 1, v___x_3084_);
return v___x_3085_;
}
else
{
uint8_t v___x_3086_; uint8_t v_c_3087_; uint8_t v___x_3088_; 
v___x_3086_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v_c_3087_ = lean_byte_array_fget(v_array_3080_, v_idx_3081_);
v___x_3088_ = lean_uint8_dec_eq(v_c_3087_, v___x_3086_);
if (v___x_3088_ == 0)
{
lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3089_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4);
v___x_3090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3090_, 0, v_a_3079_);
lean_ctor_set(v___x_3090_, 1, v___x_3089_);
return v___x_3090_;
}
else
{
lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3101_; 
lean_inc(v_idx_3081_);
lean_inc_ref(v_array_3080_);
v_isSharedCheck_3101_ = !lean_is_exclusive(v_a_3079_);
if (v_isSharedCheck_3101_ == 0)
{
lean_object* v_unused_3102_; lean_object* v_unused_3103_; 
v_unused_3102_ = lean_ctor_get(v_a_3079_, 1);
lean_dec(v_unused_3102_);
v_unused_3103_ = lean_ctor_get(v_a_3079_, 0);
lean_dec(v_unused_3103_);
v___x_3092_ = v_a_3079_;
v_isShared_3093_ = v_isSharedCheck_3101_;
goto v_resetjp_3091_;
}
else
{
lean_dec(v_a_3079_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3101_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v_it_x27_3097_; 
v___x_3094_ = lean_unsigned_to_nat(1u);
v___x_3095_ = lean_nat_add(v_idx_3081_, v___x_3094_);
lean_dec(v_idx_3081_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 1, v___x_3095_);
v_it_x27_3097_ = v___x_3092_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_array_3080_);
lean_ctor_set(v_reuseFailAlloc_3100_, 1, v___x_3095_);
v_it_x27_3097_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3098_ = lean_box(3);
v___x_3099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3099_, 0, v_it_x27_3097_);
lean_ctor_set(v___x_3099_, 1, v___x_3098_);
return v___x_3099_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(lean_object* v_config_3107_, lean_object* v_a_3108_){
_start:
{
lean_object* v_array_3112_; lean_object* v_idx_3113_; lean_object* v___x_3114_; uint8_t v___x_3115_; 
v_array_3112_ = lean_ctor_get(v_a_3108_, 0);
v_idx_3113_ = lean_ctor_get(v_a_3108_, 1);
v___x_3114_ = lean_byte_array_size(v_array_3112_);
v___x_3115_ = lean_nat_dec_lt(v_idx_3113_, v___x_3114_);
if (v___x_3115_ == 0)
{
lean_dec_ref(v_config_3107_);
goto v___jp_3109_;
}
else
{
uint8_t v___x_3116_; uint8_t v___x_3117_; uint8_t v___x_3118_; 
v___x_3116_ = lean_byte_array_fget(v_array_3112_, v_idx_3113_);
v___x_3117_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_3118_ = lean_uint8_dec_eq(v___x_3116_, v___x_3117_);
if (v___x_3118_ == 0)
{
lean_dec_ref(v_config_3107_);
goto v___jp_3109_;
}
else
{
if (v___x_3118_ == 0)
{
lean_dec_ref(v_config_3107_);
goto v___jp_3109_;
}
else
{
lean_object* v___x_3119_; 
lean_inc_ref(v_a_3108_);
lean_inc_ref(v_config_3107_);
v___x_3119_ = l_Std_Http_URI_Parser_parsePath(v_config_3107_, v___x_3118_, v___x_3118_, v_a_3108_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v_pos_3120_; lean_object* v_res_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3166_; 
v_pos_3120_ = lean_ctor_get(v___x_3119_, 0);
v_res_3121_ = lean_ctor_get(v___x_3119_, 1);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3123_ = v___x_3119_;
v_isShared_3124_ = v_isSharedCheck_3166_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_res_3121_);
lean_inc(v_pos_3120_);
lean_dec(v___x_3119_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3166_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v_pos_3126_; lean_object* v_res_3127_; lean_object* v_array_3132_; lean_object* v_idx_3133_; lean_object* v_pos_3135_; lean_object* v_idx_3136_; lean_object* v_err_3137_; lean_object* v___x_3141_; uint8_t v___x_3142_; 
v_array_3132_ = lean_ctor_get(v_pos_3120_, 0);
v_idx_3133_ = lean_ctor_get(v_pos_3120_, 1);
lean_inc(v_idx_3133_);
v___x_3141_ = lean_byte_array_size(v_array_3132_);
v___x_3142_ = lean_nat_dec_lt(v_idx_3133_, v___x_3141_);
if (v___x_3142_ == 0)
{
lean_object* v___x_3143_; 
lean_dec_ref(v_config_3107_);
v___x_3143_ = lean_box(0);
lean_inc(v_idx_3133_);
v_pos_3135_ = v_pos_3120_;
v_idx_3136_ = v_idx_3133_;
v_err_3137_ = v___x_3143_;
goto v___jp_3134_;
}
else
{
uint8_t v___x_3144_; uint8_t v_c_3145_; uint8_t v___x_3146_; 
v___x_3144_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_c_3145_ = lean_byte_array_fget(v_array_3132_, v_idx_3133_);
v___x_3146_ = lean_uint8_dec_eq(v_c_3145_, v___x_3144_);
if (v___x_3146_ == 0)
{
lean_object* v___x_3147_; 
lean_dec_ref(v_config_3107_);
v___x_3147_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3133_);
v_pos_3135_ = v_pos_3120_;
v_idx_3136_ = v_idx_3133_;
v_err_3137_ = v___x_3147_;
goto v___jp_3134_;
}
else
{
lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3163_; 
lean_inc_ref(v_array_3132_);
v_isSharedCheck_3163_ = !lean_is_exclusive(v_pos_3120_);
if (v_isSharedCheck_3163_ == 0)
{
lean_object* v_unused_3164_; lean_object* v_unused_3165_; 
v_unused_3164_ = lean_ctor_get(v_pos_3120_, 1);
lean_dec(v_unused_3164_);
v_unused_3165_ = lean_ctor_get(v_pos_3120_, 0);
lean_dec(v_unused_3165_);
v___x_3149_ = v_pos_3120_;
v_isShared_3150_ = v_isSharedCheck_3163_;
goto v_resetjp_3148_;
}
else
{
lean_dec(v_pos_3120_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3163_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v_it_x27_3154_; 
v___x_3151_ = lean_unsigned_to_nat(1u);
v___x_3152_ = lean_nat_add(v_idx_3133_, v___x_3151_);
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 1, v___x_3152_);
v_it_x27_3154_ = v___x_3149_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_array_3132_);
lean_ctor_set(v_reuseFailAlloc_3162_, 1, v___x_3152_);
v_it_x27_3154_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
lean_object* v___x_3155_; 
v___x_3155_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3107_, v_it_x27_3154_);
if (lean_obj_tag(v___x_3155_) == 0)
{
lean_object* v_pos_3156_; lean_object* v_res_3157_; lean_object* v___x_3158_; 
lean_dec(v_idx_3133_);
lean_dec_ref(v_a_3108_);
v_pos_3156_ = lean_ctor_get(v___x_3155_, 0);
lean_inc(v_pos_3156_);
v_res_3157_ = lean_ctor_get(v___x_3155_, 1);
lean_inc(v_res_3157_);
lean_dec_ref(v___x_3155_);
v___x_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3158_, 0, v_res_3157_);
v_pos_3126_ = v_pos_3156_;
v_res_3127_ = v___x_3158_;
goto v___jp_3125_;
}
else
{
lean_object* v_pos_3159_; lean_object* v_err_3160_; lean_object* v_idx_3161_; 
v_pos_3159_ = lean_ctor_get(v___x_3155_, 0);
lean_inc(v_pos_3159_);
v_err_3160_ = lean_ctor_get(v___x_3155_, 1);
lean_inc(v_err_3160_);
lean_dec_ref(v___x_3155_);
v_idx_3161_ = lean_ctor_get(v_pos_3159_, 1);
lean_inc(v_idx_3161_);
v_pos_3135_ = v_pos_3159_;
v_idx_3136_ = v_idx_3161_;
v_err_3137_ = v_err_3160_;
goto v___jp_3134_;
}
}
}
}
}
v___jp_3125_:
{
lean_object* v___x_3128_; lean_object* v___x_3130_; 
v___x_3128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3128_, 0, v_res_3121_);
lean_ctor_set(v___x_3128_, 1, v_res_3127_);
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 1, v___x_3128_);
lean_ctor_set(v___x_3123_, 0, v_pos_3126_);
v___x_3130_ = v___x_3123_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_pos_3126_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v___x_3128_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
v___jp_3134_:
{
uint8_t v___x_3138_; 
v___x_3138_ = lean_nat_dec_eq(v_idx_3133_, v_idx_3136_);
lean_dec(v_idx_3136_);
lean_dec(v_idx_3133_);
if (v___x_3138_ == 0)
{
lean_object* v___x_3139_; 
lean_dec_ref(v_pos_3135_);
lean_del_object(v___x_3123_);
lean_dec(v_res_3121_);
v___x_3139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3139_, 0, v_a_3108_);
lean_ctor_set(v___x_3139_, 1, v_err_3137_);
return v___x_3139_;
}
else
{
lean_object* v___x_3140_; 
lean_dec(v_err_3137_);
lean_dec_ref(v_a_3108_);
v___x_3140_ = lean_box(0);
v_pos_3126_ = v_pos_3135_;
v_res_3127_ = v___x_3140_;
goto v___jp_3125_;
}
}
}
}
else
{
lean_object* v_err_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3174_; 
lean_dec_ref(v_config_3107_);
v_err_3167_ = lean_ctor_get(v___x_3119_, 1);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3174_ == 0)
{
lean_object* v_unused_3175_; 
v_unused_3175_ = lean_ctor_get(v___x_3119_, 0);
lean_dec(v_unused_3175_);
v___x_3169_ = v___x_3119_;
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_err_3167_);
lean_dec(v___x_3119_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3172_; 
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 0, v_a_3108_);
v___x_3172_ = v___x_3169_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_a_3108_);
lean_ctor_set(v_reuseFailAlloc_3173_, 1, v_err_3167_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
}
}
}
v___jp_3109_:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3110_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1));
v___x_3111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3111_, 0, v_a_3108_);
lean_ctor_set(v___x_3111_, 1, v___x_3110_);
return v___x_3111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(lean_object* v_config_3176_, lean_object* v_scheme_3177_, lean_object* v_a_3178_){
_start:
{
lean_object* v_array_3179_; lean_object* v_idx_3180_; lean_object* v___x_3181_; uint8_t v___x_3182_; 
v_array_3179_ = lean_ctor_get(v_a_3178_, 0);
v_idx_3180_ = lean_ctor_get(v_a_3178_, 1);
v___x_3181_ = lean_byte_array_size(v_array_3179_);
v___x_3182_ = lean_nat_dec_lt(v_idx_3180_, v___x_3181_);
if (v___x_3182_ == 0)
{
lean_object* v___x_3183_; lean_object* v___x_3184_; 
lean_dec_ref(v_scheme_3177_);
lean_dec_ref(v_config_3176_);
v___x_3183_ = lean_box(0);
v___x_3184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3184_, 0, v_a_3178_);
lean_ctor_set(v___x_3184_, 1, v___x_3183_);
return v___x_3184_;
}
else
{
uint8_t v___x_3185_; uint8_t v_c_3186_; uint8_t v___x_3187_; 
v___x_3185_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v_c_3186_ = lean_byte_array_fget(v_array_3179_, v_idx_3180_);
v___x_3187_ = lean_uint8_dec_eq(v_c_3186_, v___x_3185_);
if (v___x_3187_ == 0)
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
lean_dec_ref(v_scheme_3177_);
lean_dec_ref(v_config_3176_);
v___x_3188_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
v___x_3189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3189_, 0, v_a_3178_);
lean_ctor_set(v___x_3189_, 1, v___x_3188_);
return v___x_3189_;
}
else
{
lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3263_; 
lean_inc(v_idx_3180_);
lean_inc_ref(v_array_3179_);
v_isSharedCheck_3263_ = !lean_is_exclusive(v_a_3178_);
if (v_isSharedCheck_3263_ == 0)
{
lean_object* v_unused_3264_; lean_object* v_unused_3265_; 
v_unused_3264_ = lean_ctor_get(v_a_3178_, 1);
lean_dec(v_unused_3264_);
v_unused_3265_ = lean_ctor_get(v_a_3178_, 0);
lean_dec(v_unused_3265_);
v___x_3191_ = v_a_3178_;
v_isShared_3192_ = v_isSharedCheck_3263_;
goto v_resetjp_3190_;
}
else
{
lean_dec(v_a_3178_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3263_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v_it_x27_3196_; 
v___x_3193_ = lean_unsigned_to_nat(1u);
v___x_3194_ = lean_nat_add(v_idx_3180_, v___x_3193_);
lean_dec(v_idx_3180_);
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 1, v___x_3194_);
v_it_x27_3196_ = v___x_3191_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_array_3179_);
lean_ctor_set(v_reuseFailAlloc_3262_, 1, v___x_3194_);
v_it_x27_3196_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
lean_object* v___x_3197_; 
lean_inc_ref(v_config_3176_);
v___x_3197_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_3176_, v_it_x27_3196_);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v_res_3198_; lean_object* v_pos_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3252_; 
v_res_3198_ = lean_ctor_get(v___x_3197_, 1);
v_pos_3199_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3201_ = v___x_3197_;
v_isShared_3202_ = v_isSharedCheck_3252_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_res_3198_);
lean_inc(v_pos_3199_);
lean_dec(v___x_3197_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3252_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v_fst_3203_; lean_object* v_snd_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3251_; 
v_fst_3203_ = lean_ctor_get(v_res_3198_, 0);
v_snd_3204_ = lean_ctor_get(v_res_3198_, 1);
v_isSharedCheck_3251_ = !lean_is_exclusive(v_res_3198_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3206_ = v_res_3198_;
v_isShared_3207_ = v_isSharedCheck_3251_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_snd_3204_);
lean_inc(v_fst_3203_);
lean_dec(v_res_3198_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3251_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v_array_3217_; lean_object* v_idx_3218_; lean_object* v_pos_3220_; lean_object* v_idx_3221_; lean_object* v_err_3222_; lean_object* v___x_3228_; uint8_t v___x_3229_; 
v_array_3217_ = lean_ctor_get(v_pos_3199_, 0);
v_idx_3218_ = lean_ctor_get(v_pos_3199_, 1);
lean_inc(v_idx_3218_);
v___x_3228_ = lean_byte_array_size(v_array_3217_);
v___x_3229_ = lean_nat_dec_lt(v_idx_3218_, v___x_3228_);
if (v___x_3229_ == 0)
{
lean_object* v___x_3230_; 
lean_dec_ref(v_config_3176_);
v___x_3230_ = lean_box(0);
lean_inc(v_idx_3218_);
v_pos_3220_ = v_pos_3199_;
v_idx_3221_ = v_idx_3218_;
v_err_3222_ = v___x_3230_;
goto v___jp_3219_;
}
else
{
uint8_t v___x_3231_; uint8_t v_c_3232_; uint8_t v___x_3233_; 
v___x_3231_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_c_3232_ = lean_byte_array_fget(v_array_3217_, v_idx_3218_);
v___x_3233_ = lean_uint8_dec_eq(v_c_3232_, v___x_3231_);
if (v___x_3233_ == 0)
{
lean_object* v___x_3234_; 
lean_dec_ref(v_config_3176_);
v___x_3234_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3218_);
v_pos_3220_ = v_pos_3199_;
v_idx_3221_ = v_idx_3218_;
v_err_3222_ = v___x_3234_;
goto v___jp_3219_;
}
else
{
lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3248_; 
lean_inc_ref(v_array_3217_);
v_isSharedCheck_3248_ = !lean_is_exclusive(v_pos_3199_);
if (v_isSharedCheck_3248_ == 0)
{
lean_object* v_unused_3249_; lean_object* v_unused_3250_; 
v_unused_3249_ = lean_ctor_get(v_pos_3199_, 1);
lean_dec(v_unused_3249_);
v_unused_3250_ = lean_ctor_get(v_pos_3199_, 0);
lean_dec(v_unused_3250_);
v___x_3236_ = v_pos_3199_;
v_isShared_3237_ = v_isSharedCheck_3248_;
goto v_resetjp_3235_;
}
else
{
lean_dec(v_pos_3199_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3248_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3238_; lean_object* v_it_x27_3240_; 
v___x_3238_ = lean_nat_add(v_idx_3218_, v___x_3193_);
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 1, v___x_3238_);
v_it_x27_3240_ = v___x_3236_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_array_3217_);
lean_ctor_set(v_reuseFailAlloc_3247_, 1, v___x_3238_);
v_it_x27_3240_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
lean_object* v___x_3241_; 
v___x_3241_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3176_, v_it_x27_3240_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_pos_3242_; lean_object* v_res_3243_; 
lean_dec(v_idx_3218_);
lean_del_object(v___x_3206_);
v_pos_3242_ = lean_ctor_get(v___x_3241_, 0);
lean_inc(v_pos_3242_);
v_res_3243_ = lean_ctor_get(v___x_3241_, 1);
lean_inc(v_res_3243_);
lean_dec_ref(v___x_3241_);
v___y_3209_ = v_pos_3242_;
v___y_3210_ = v_res_3243_;
goto v___jp_3208_;
}
else
{
lean_object* v_pos_3244_; lean_object* v_err_3245_; lean_object* v_idx_3246_; 
v_pos_3244_ = lean_ctor_get(v___x_3241_, 0);
lean_inc(v_pos_3244_);
v_err_3245_ = lean_ctor_get(v___x_3241_, 1);
lean_inc(v_err_3245_);
lean_dec_ref(v___x_3241_);
v_idx_3246_ = lean_ctor_get(v_pos_3244_, 1);
lean_inc(v_idx_3246_);
v_pos_3220_ = v_pos_3244_;
v_idx_3221_ = v_idx_3246_;
v_err_3222_ = v_err_3245_;
goto v___jp_3219_;
}
}
}
}
}
v___jp_3208_:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3215_; 
v___x_3211_ = lean_box(0);
v___x_3212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3212_, 0, v_scheme_3177_);
lean_ctor_set(v___x_3212_, 1, v_fst_3203_);
lean_ctor_set(v___x_3212_, 2, v_snd_3204_);
lean_ctor_set(v___x_3212_, 3, v___y_3210_);
lean_ctor_set(v___x_3212_, 4, v___x_3211_);
v___x_3213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3212_);
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 1, v___x_3213_);
lean_ctor_set(v___x_3201_, 0, v___y_3209_);
v___x_3215_ = v___x_3201_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___y_3209_);
lean_ctor_set(v_reuseFailAlloc_3216_, 1, v___x_3213_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
v___jp_3219_:
{
uint8_t v___x_3223_; 
v___x_3223_ = lean_nat_dec_eq(v_idx_3218_, v_idx_3221_);
lean_dec(v_idx_3221_);
lean_dec(v_idx_3218_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3225_; 
lean_dec(v_snd_3204_);
lean_dec(v_fst_3203_);
lean_del_object(v___x_3201_);
lean_dec_ref(v_scheme_3177_);
if (v_isShared_3207_ == 0)
{
lean_ctor_set_tag(v___x_3206_, 1);
lean_ctor_set(v___x_3206_, 1, v_err_3222_);
lean_ctor_set(v___x_3206_, 0, v_pos_3220_);
v___x_3225_ = v___x_3206_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_pos_3220_);
lean_ctor_set(v_reuseFailAlloc_3226_, 1, v_err_3222_);
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
lean_object* v___x_3227_; 
lean_dec(v_err_3222_);
lean_del_object(v___x_3206_);
v___x_3227_ = l_Std_Http_URI_Query_empty;
v___y_3209_ = v_pos_3220_;
v___y_3210_ = v___x_3227_;
goto v___jp_3208_;
}
}
}
}
}
else
{
lean_object* v_pos_3253_; lean_object* v_err_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3261_; 
lean_dec_ref(v_scheme_3177_);
lean_dec_ref(v_config_3176_);
v_pos_3253_ = lean_ctor_get(v___x_3197_, 0);
v_err_3254_ = lean_ctor_get(v___x_3197_, 1);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3256_ = v___x_3197_;
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_err_3254_);
lean_inc(v_pos_3253_);
lean_dec(v___x_3197_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3259_; 
if (v_isShared_3257_ == 0)
{
v___x_3259_ = v___x_3256_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_pos_3253_);
lean_ctor_set(v_reuseFailAlloc_3260_, 1, v_err_3254_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(lean_object* v_config_3274_, lean_object* v_a_3275_){
_start:
{
lean_object* v___x_3279_; 
lean_inc_ref(v_a_3275_);
v___x_3279_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3274_, v_a_3275_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v_pos_3280_; lean_object* v_res_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3377_; 
v_pos_3280_ = lean_ctor_get(v___x_3279_, 0);
v_res_3281_ = lean_ctor_get(v___x_3279_, 1);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3283_ = v___x_3279_;
v_isShared_3284_ = v_isSharedCheck_3377_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_res_3281_);
lean_inc(v_pos_3280_);
lean_dec(v___x_3279_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3377_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v_idx_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v_pos_3300_; lean_object* v_idx_3301_; lean_object* v_err_3302_; uint8_t v___y_3307_; lean_object* v___x_3373_; uint8_t v___x_3374_; 
v___x_3373_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__4));
v___x_3374_ = lean_string_dec_eq(v_res_3281_, v___x_3373_);
if (v___x_3374_ == 0)
{
lean_object* v___x_3375_; uint8_t v___x_3376_; 
v___x_3375_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5));
v___x_3376_ = lean_string_dec_eq(v_res_3281_, v___x_3375_);
v___y_3307_ = v___x_3376_;
goto v___jp_3306_;
}
else
{
v___y_3307_ = v___x_3374_;
goto v___jp_3306_;
}
v___jp_3285_:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3294_; 
v___x_3290_ = lean_box(0);
v___x_3291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3291_, 0, v_res_3281_);
lean_ctor_set(v___x_3291_, 1, v___y_3287_);
lean_ctor_set(v___x_3291_, 2, v___y_3288_);
lean_ctor_set(v___x_3291_, 3, v___y_3289_);
lean_ctor_set(v___x_3291_, 4, v___x_3290_);
v___x_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3291_);
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 1, v___x_3292_);
lean_ctor_set(v___x_3283_, 0, v___y_3286_);
v___x_3294_ = v___x_3283_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v___y_3286_);
lean_ctor_set(v_reuseFailAlloc_3295_, 1, v___x_3292_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
v___jp_3296_:
{
uint8_t v___x_3303_; 
v___x_3303_ = lean_nat_dec_eq(v_idx_3297_, v_idx_3301_);
lean_dec(v_idx_3301_);
lean_dec(v_idx_3297_);
if (v___x_3303_ == 0)
{
lean_object* v___x_3304_; 
lean_dec_ref(v_pos_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_del_object(v___x_3283_);
lean_dec(v_res_3281_);
v___x_3304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3304_, 0, v_a_3275_);
lean_ctor_set(v___x_3304_, 1, v_err_3302_);
return v___x_3304_;
}
else
{
lean_object* v___x_3305_; 
lean_dec(v_err_3302_);
lean_dec_ref(v_a_3275_);
v___x_3305_ = l_Std_Http_URI_Query_empty;
v___y_3286_ = v_pos_3300_;
v___y_3287_ = v___y_3298_;
v___y_3288_ = v___y_3299_;
v___y_3289_ = v___x_3305_;
goto v___jp_3285_;
}
}
v___jp_3306_:
{
if (v___y_3307_ == 0)
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
lean_del_object(v___x_3283_);
lean_dec(v_res_3281_);
lean_dec(v_pos_3280_);
lean_dec_ref(v_config_3274_);
v___x_3308_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3));
v___x_3309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3309_, 0, v_a_3275_);
lean_ctor_set(v___x_3309_, 1, v___x_3308_);
return v___x_3309_;
}
else
{
lean_object* v_array_3310_; lean_object* v_idx_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3372_; 
v_array_3310_ = lean_ctor_get(v_pos_3280_, 0);
v_idx_3311_ = lean_ctor_get(v_pos_3280_, 1);
v_isSharedCheck_3372_ = !lean_is_exclusive(v_pos_3280_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3313_ = v_pos_3280_;
v_isShared_3314_ = v_isSharedCheck_3372_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_idx_3311_);
lean_inc(v_array_3310_);
lean_dec(v_pos_3280_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3372_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3315_; uint8_t v___x_3316_; 
v___x_3315_ = lean_byte_array_size(v_array_3310_);
v___x_3316_ = lean_nat_dec_lt(v_idx_3311_, v___x_3315_);
if (v___x_3316_ == 0)
{
lean_object* v___x_3317_; lean_object* v___x_3318_; 
lean_del_object(v___x_3313_);
lean_dec(v_idx_3311_);
lean_dec_ref(v_array_3310_);
lean_del_object(v___x_3283_);
lean_dec(v_res_3281_);
lean_dec_ref(v_config_3274_);
v___x_3317_ = lean_box(0);
v___x_3318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3318_, 0, v_a_3275_);
lean_ctor_set(v___x_3318_, 1, v___x_3317_);
return v___x_3318_;
}
else
{
uint8_t v___x_3319_; uint8_t v_c_3320_; uint8_t v___x_3321_; 
v___x_3319_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v_c_3320_ = lean_byte_array_fget(v_array_3310_, v_idx_3311_);
v___x_3321_ = lean_uint8_dec_eq(v_c_3320_, v___x_3319_);
if (v___x_3321_ == 0)
{
lean_object* v___x_3322_; lean_object* v___x_3323_; 
lean_del_object(v___x_3313_);
lean_dec(v_idx_3311_);
lean_dec_ref(v_array_3310_);
lean_del_object(v___x_3283_);
lean_dec(v_res_3281_);
lean_dec_ref(v_config_3274_);
v___x_3322_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
v___x_3323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3323_, 0, v_a_3275_);
lean_ctor_set(v___x_3323_, 1, v___x_3322_);
return v___x_3323_;
}
else
{
lean_object* v___x_3324_; lean_object* v___x_3325_; uint8_t v___x_3326_; 
v___x_3324_ = lean_unsigned_to_nat(1u);
v___x_3325_ = lean_nat_add(v_idx_3311_, v___x_3324_);
lean_dec(v_idx_3311_);
v___x_3326_ = lean_nat_dec_lt(v___x_3325_, v___x_3315_);
if (v___x_3326_ == 0)
{
lean_dec(v___x_3325_);
lean_del_object(v___x_3313_);
lean_dec_ref(v_array_3310_);
lean_del_object(v___x_3283_);
lean_dec(v_res_3281_);
lean_dec_ref(v_config_3274_);
goto v___jp_3276_;
}
else
{
uint8_t v___x_3327_; uint8_t v___x_3328_; uint8_t v___x_3329_; 
v___x_3327_ = lean_byte_array_fget(v_array_3310_, v___x_3325_);
v___x_3328_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_3329_ = lean_uint8_dec_eq(v___x_3327_, v___x_3328_);
if (v___x_3329_ == 0)
{
lean_dec(v___x_3325_);
lean_del_object(v___x_3313_);
lean_dec_ref(v_array_3310_);
lean_del_object(v___x_3283_);
lean_dec(v_res_3281_);
lean_dec_ref(v_config_3274_);
goto v___jp_3276_;
}
else
{
if (v___x_3329_ == 0)
{
lean_dec(v___x_3325_);
lean_del_object(v___x_3313_);
lean_dec_ref(v_array_3310_);
lean_del_object(v___x_3283_);
lean_dec(v_res_3281_);
lean_dec_ref(v_config_3274_);
goto v___jp_3276_;
}
else
{
lean_object* v_it_x27_3331_; 
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 1, v___x_3325_);
v_it_x27_3331_ = v___x_3313_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_array_3310_);
lean_ctor_set(v_reuseFailAlloc_3371_, 1, v___x_3325_);
v_it_x27_3331_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
lean_object* v___x_3332_; 
lean_inc_ref(v_config_3274_);
v___x_3332_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_3274_, v_it_x27_3331_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v_res_3333_; lean_object* v_pos_3334_; lean_object* v_fst_3335_; lean_object* v_snd_3336_; lean_object* v_array_3337_; lean_object* v_idx_3338_; lean_object* v___x_3339_; uint8_t v___x_3340_; 
v_res_3333_ = lean_ctor_get(v___x_3332_, 1);
lean_inc(v_res_3333_);
v_pos_3334_ = lean_ctor_get(v___x_3332_, 0);
lean_inc(v_pos_3334_);
lean_dec_ref(v___x_3332_);
v_fst_3335_ = lean_ctor_get(v_res_3333_, 0);
lean_inc(v_fst_3335_);
v_snd_3336_ = lean_ctor_get(v_res_3333_, 1);
lean_inc(v_snd_3336_);
lean_dec(v_res_3333_);
v_array_3337_ = lean_ctor_get(v_pos_3334_, 0);
v_idx_3338_ = lean_ctor_get(v_pos_3334_, 1);
lean_inc(v_idx_3338_);
v___x_3339_ = lean_byte_array_size(v_array_3337_);
v___x_3340_ = lean_nat_dec_lt(v_idx_3338_, v___x_3339_);
if (v___x_3340_ == 0)
{
lean_object* v___x_3341_; 
lean_dec_ref(v_config_3274_);
v___x_3341_ = lean_box(0);
lean_inc(v_idx_3338_);
v_idx_3297_ = v_idx_3338_;
v___y_3298_ = v_fst_3335_;
v___y_3299_ = v_snd_3336_;
v_pos_3300_ = v_pos_3334_;
v_idx_3301_ = v_idx_3338_;
v_err_3302_ = v___x_3341_;
goto v___jp_3296_;
}
else
{
uint8_t v___x_3342_; uint8_t v_c_3343_; uint8_t v___x_3344_; 
v___x_3342_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_c_3343_ = lean_byte_array_fget(v_array_3337_, v_idx_3338_);
v___x_3344_ = lean_uint8_dec_eq(v_c_3343_, v___x_3342_);
if (v___x_3344_ == 0)
{
lean_object* v___x_3345_; 
lean_dec_ref(v_config_3274_);
v___x_3345_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3338_);
v_idx_3297_ = v_idx_3338_;
v___y_3298_ = v_fst_3335_;
v___y_3299_ = v_snd_3336_;
v_pos_3300_ = v_pos_3334_;
v_idx_3301_ = v_idx_3338_;
v_err_3302_ = v___x_3345_;
goto v___jp_3296_;
}
else
{
lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3359_; 
lean_inc_ref(v_array_3337_);
v_isSharedCheck_3359_ = !lean_is_exclusive(v_pos_3334_);
if (v_isSharedCheck_3359_ == 0)
{
lean_object* v_unused_3360_; lean_object* v_unused_3361_; 
v_unused_3360_ = lean_ctor_get(v_pos_3334_, 1);
lean_dec(v_unused_3360_);
v_unused_3361_ = lean_ctor_get(v_pos_3334_, 0);
lean_dec(v_unused_3361_);
v___x_3347_ = v_pos_3334_;
v_isShared_3348_ = v_isSharedCheck_3359_;
goto v_resetjp_3346_;
}
else
{
lean_dec(v_pos_3334_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3359_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3349_; lean_object* v_it_x27_3351_; 
v___x_3349_ = lean_nat_add(v_idx_3338_, v___x_3324_);
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 1, v___x_3349_);
v_it_x27_3351_ = v___x_3347_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_array_3337_);
lean_ctor_set(v_reuseFailAlloc_3358_, 1, v___x_3349_);
v_it_x27_3351_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
lean_object* v___x_3352_; 
v___x_3352_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3274_, v_it_x27_3351_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v_pos_3353_; lean_object* v_res_3354_; 
lean_dec(v_idx_3338_);
lean_dec_ref(v_a_3275_);
v_pos_3353_ = lean_ctor_get(v___x_3352_, 0);
lean_inc(v_pos_3353_);
v_res_3354_ = lean_ctor_get(v___x_3352_, 1);
lean_inc(v_res_3354_);
lean_dec_ref(v___x_3352_);
v___y_3286_ = v_pos_3353_;
v___y_3287_ = v_fst_3335_;
v___y_3288_ = v_snd_3336_;
v___y_3289_ = v_res_3354_;
goto v___jp_3285_;
}
else
{
lean_object* v_pos_3355_; lean_object* v_err_3356_; lean_object* v_idx_3357_; 
v_pos_3355_ = lean_ctor_get(v___x_3352_, 0);
lean_inc(v_pos_3355_);
v_err_3356_ = lean_ctor_get(v___x_3352_, 1);
lean_inc(v_err_3356_);
lean_dec_ref(v___x_3352_);
v_idx_3357_ = lean_ctor_get(v_pos_3355_, 1);
lean_inc(v_idx_3357_);
v_idx_3297_ = v_idx_3338_;
v___y_3298_ = v_fst_3335_;
v___y_3299_ = v_snd_3336_;
v_pos_3300_ = v_pos_3355_;
v_idx_3301_ = v_idx_3357_;
v_err_3302_ = v_err_3356_;
goto v___jp_3296_;
}
}
}
}
}
}
else
{
lean_object* v_err_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3369_; 
lean_del_object(v___x_3283_);
lean_dec(v_res_3281_);
lean_dec_ref(v_config_3274_);
v_err_3362_ = lean_ctor_get(v___x_3332_, 1);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3369_ == 0)
{
lean_object* v_unused_3370_; 
v_unused_3370_ = lean_ctor_get(v___x_3332_, 0);
lean_dec(v_unused_3370_);
v___x_3364_ = v___x_3332_;
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_err_3362_);
lean_dec(v___x_3332_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3367_; 
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 0, v_a_3275_);
v___x_3367_ = v___x_3364_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_a_3275_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v_err_3362_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
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
lean_object* v_err_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3385_; 
lean_dec_ref(v_config_3274_);
v_err_3378_ = lean_ctor_get(v___x_3279_, 1);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3385_ == 0)
{
lean_object* v_unused_3386_; 
v_unused_3386_ = lean_ctor_get(v___x_3279_, 0);
lean_dec(v_unused_3386_);
v___x_3380_ = v___x_3279_;
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_err_3378_);
lean_dec(v___x_3279_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3383_; 
if (v_isShared_3381_ == 0)
{
lean_ctor_set(v___x_3380_, 0, v_a_3275_);
v___x_3383_ = v___x_3380_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_a_3275_);
lean_ctor_set(v_reuseFailAlloc_3384_, 1, v_err_3378_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
}
v___jp_3276_:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3277_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1));
v___x_3278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3278_, 0, v_a_3275_);
lean_ctor_set(v___x_3278_, 1, v___x_3277_);
return v___x_3278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(lean_object* v_config_3387_, lean_object* v_a_3388_){
_start:
{
lean_object* v___x_3389_; 
lean_inc_ref(v_a_3388_);
v___x_3389_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3387_, v_a_3388_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_object* v_pos_3390_; lean_object* v_res_3391_; lean_object* v___x_3392_; 
v_pos_3390_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_pos_3390_);
v_res_3391_ = lean_ctor_get(v___x_3389_, 1);
lean_inc(v_res_3391_);
lean_dec_ref(v___x_3389_);
v___x_3392_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(v_config_3387_, v_res_3391_, v_pos_3390_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_dec_ref(v_a_3388_);
return v___x_3392_;
}
else
{
lean_object* v_err_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3400_; 
v_err_3393_ = lean_ctor_get(v___x_3392_, 1);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3400_ == 0)
{
lean_object* v_unused_3401_; 
v_unused_3401_ = lean_ctor_get(v___x_3392_, 0);
lean_dec(v_unused_3401_);
v___x_3395_ = v___x_3392_;
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_err_3393_);
lean_dec(v___x_3392_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3398_; 
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 0, v_a_3388_);
v___x_3398_ = v___x_3395_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_a_3388_);
lean_ctor_set(v_reuseFailAlloc_3399_, 1, v_err_3393_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
}
else
{
lean_object* v_err_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
lean_dec_ref(v_config_3387_);
v_err_3402_ = lean_ctor_get(v___x_3389_, 1);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3409_ == 0)
{
lean_object* v_unused_3410_; 
v_unused_3410_ = lean_ctor_get(v___x_3389_, 0);
lean_dec(v_unused_3410_);
v___x_3404_ = v___x_3389_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_err_3402_);
lean_dec(v___x_3389_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 0, v_a_3388_);
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3388_);
lean_ctor_set(v_reuseFailAlloc_3408_, 1, v_err_3402_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(lean_object* v_config_3411_, lean_object* v_a_3412_){
_start:
{
lean_object* v___x_3413_; 
lean_inc_ref(v_a_3412_);
v___x_3413_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_3411_, v_a_3412_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_pos_3414_; lean_object* v_res_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3467_; 
v_pos_3414_ = lean_ctor_get(v___x_3413_, 0);
v_res_3415_ = lean_ctor_get(v___x_3413_, 1);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3417_ = v___x_3413_;
v_isShared_3418_ = v_isSharedCheck_3467_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_res_3415_);
lean_inc(v_pos_3414_);
lean_dec(v___x_3413_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3467_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v_array_3419_; lean_object* v_idx_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3466_; 
v_array_3419_ = lean_ctor_get(v_pos_3414_, 0);
v_idx_3420_ = lean_ctor_get(v_pos_3414_, 1);
v_isSharedCheck_3466_ = !lean_is_exclusive(v_pos_3414_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3422_ = v_pos_3414_;
v_isShared_3423_ = v_isSharedCheck_3466_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_idx_3420_);
lean_inc(v_array_3419_);
lean_dec(v_pos_3414_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3466_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3424_; uint8_t v___x_3425_; 
v___x_3424_ = lean_byte_array_size(v_array_3419_);
v___x_3425_ = lean_nat_dec_lt(v_idx_3420_, v___x_3424_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3426_; lean_object* v___x_3428_; 
lean_del_object(v___x_3422_);
lean_dec(v_idx_3420_);
lean_dec_ref(v_array_3419_);
lean_dec(v_res_3415_);
v___x_3426_ = lean_box(0);
if (v_isShared_3418_ == 0)
{
lean_ctor_set_tag(v___x_3417_, 1);
lean_ctor_set(v___x_3417_, 1, v___x_3426_);
lean_ctor_set(v___x_3417_, 0, v_a_3412_);
v___x_3428_ = v___x_3417_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3412_);
lean_ctor_set(v_reuseFailAlloc_3429_, 1, v___x_3426_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
else
{
uint8_t v___x_3430_; uint8_t v_c_3431_; uint8_t v___x_3432_; 
v___x_3430_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v_c_3431_ = lean_byte_array_fget(v_array_3419_, v_idx_3420_);
v___x_3432_ = lean_uint8_dec_eq(v_c_3431_, v___x_3430_);
if (v___x_3432_ == 0)
{
lean_object* v___x_3433_; lean_object* v___x_3435_; 
lean_del_object(v___x_3422_);
lean_dec(v_idx_3420_);
lean_dec_ref(v_array_3419_);
lean_dec(v_res_3415_);
v___x_3433_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
if (v_isShared_3418_ == 0)
{
lean_ctor_set_tag(v___x_3417_, 1);
lean_ctor_set(v___x_3417_, 1, v___x_3433_);
lean_ctor_set(v___x_3417_, 0, v_a_3412_);
v___x_3435_ = v___x_3417_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3412_);
lean_ctor_set(v_reuseFailAlloc_3436_, 1, v___x_3433_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
else
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v_it_x27_3440_; 
lean_del_object(v___x_3417_);
v___x_3437_ = lean_unsigned_to_nat(1u);
v___x_3438_ = lean_nat_add(v_idx_3420_, v___x_3437_);
lean_dec(v_idx_3420_);
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 1, v___x_3438_);
v_it_x27_3440_ = v___x_3422_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_array_3419_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v___x_3438_);
v_it_x27_3440_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
lean_object* v___x_3441_; 
v___x_3441_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v_it_x27_3440_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_pos_3442_; lean_object* v_res_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3455_; 
lean_dec_ref(v_a_3412_);
v_pos_3442_ = lean_ctor_get(v___x_3441_, 0);
v_res_3443_ = lean_ctor_get(v___x_3441_, 1);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3445_ = v___x_3441_;
v_isShared_3446_ = v_isSharedCheck_3455_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_res_3443_);
lean_inc(v_pos_3442_);
lean_dec(v___x_3441_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3455_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; uint16_t v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3453_; 
v___x_3447_ = lean_box(0);
v___x_3448_ = lean_alloc_ctor(2, 0, 2);
v___x_3449_ = lean_unbox(v_res_3443_);
lean_dec(v_res_3443_);
lean_ctor_set_uint16(v___x_3448_, 0, v___x_3449_);
v___x_3450_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3447_);
lean_ctor_set(v___x_3450_, 1, v_res_3415_);
lean_ctor_set(v___x_3450_, 2, v___x_3448_);
v___x_3451_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3450_);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 1, v___x_3451_);
v___x_3453_ = v___x_3445_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_pos_3442_);
lean_ctor_set(v_reuseFailAlloc_3454_, 1, v___x_3451_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
else
{
lean_object* v_err_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3463_; 
lean_dec(v_res_3415_);
v_err_3456_ = lean_ctor_get(v___x_3441_, 1);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3463_ == 0)
{
lean_object* v_unused_3464_; 
v_unused_3464_ = lean_ctor_get(v___x_3441_, 0);
lean_dec(v_unused_3464_);
v___x_3458_ = v___x_3441_;
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_err_3456_);
lean_dec(v___x_3441_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 0, v_a_3412_);
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3412_);
lean_ctor_set(v_reuseFailAlloc_3462_, 1, v_err_3456_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
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
lean_object* v_err_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3475_; 
v_err_3468_ = lean_ctor_get(v___x_3413_, 1);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3475_ == 0)
{
lean_object* v_unused_3476_; 
v_unused_3476_ = lean_ctor_get(v___x_3413_, 0);
lean_dec(v_unused_3476_);
v___x_3470_ = v___x_3413_;
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_err_3468_);
lean_dec(v___x_3413_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3473_; 
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 0, v_a_3412_);
v___x_3473_ = v___x_3470_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_a_3412_);
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
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority___boxed(lean_object* v_config_3477_, lean_object* v_a_3478_){
_start:
{
lean_object* v_res_3479_; 
v_res_3479_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3477_, v_a_3478_);
lean_dec_ref(v_config_3477_);
return v_res_3479_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object* v_config_3480_, lean_object* v_a_3481_){
_start:
{
lean_object* v___x_3482_; 
lean_inc_ref(v_a_3481_);
v___x_3482_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(v_a_3481_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_dec_ref(v_a_3481_);
lean_dec_ref(v_config_3480_);
return v___x_3482_;
}
else
{
lean_object* v_pos_3483_; lean_object* v_idx_3484_; lean_object* v_idx_3485_; uint8_t v___x_3486_; 
v_pos_3483_ = lean_ctor_get(v___x_3482_, 0);
lean_inc(v_pos_3483_);
v_idx_3484_ = lean_ctor_get(v_a_3481_, 1);
lean_inc(v_idx_3484_);
lean_dec_ref(v_a_3481_);
v_idx_3485_ = lean_ctor_get(v_pos_3483_, 1);
lean_inc(v_idx_3485_);
v___x_3486_ = lean_nat_dec_eq(v_idx_3484_, v_idx_3485_);
lean_dec(v_idx_3484_);
if (v___x_3486_ == 0)
{
lean_dec(v_idx_3485_);
lean_dec(v_pos_3483_);
lean_dec_ref(v_config_3480_);
return v___x_3482_;
}
else
{
lean_object* v___x_3487_; 
lean_dec_ref(v___x_3482_);
lean_inc_ref(v_config_3480_);
v___x_3487_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(v_config_3480_, v_pos_3483_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_dec(v_idx_3485_);
lean_dec_ref(v_config_3480_);
return v___x_3487_;
}
else
{
lean_object* v_pos_3488_; lean_object* v_idx_3489_; uint8_t v___x_3490_; 
v_pos_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_pos_3488_);
v_idx_3489_ = lean_ctor_get(v_pos_3488_, 1);
lean_inc(v_idx_3489_);
v___x_3490_ = lean_nat_dec_eq(v_idx_3485_, v_idx_3489_);
lean_dec(v_idx_3485_);
if (v___x_3490_ == 0)
{
lean_dec(v_idx_3489_);
lean_dec(v_pos_3488_);
lean_dec_ref(v_config_3480_);
return v___x_3487_;
}
else
{
lean_object* v___x_3491_; 
lean_dec_ref(v___x_3487_);
lean_inc_ref(v_config_3480_);
v___x_3491_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(v_config_3480_, v_pos_3488_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_dec(v_idx_3489_);
lean_dec_ref(v_config_3480_);
return v___x_3491_;
}
else
{
lean_object* v_pos_3492_; lean_object* v_idx_3493_; uint8_t v___x_3494_; 
v_pos_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_pos_3492_);
v_idx_3493_ = lean_ctor_get(v_pos_3492_, 1);
lean_inc(v_idx_3493_);
v___x_3494_ = lean_nat_dec_eq(v_idx_3489_, v_idx_3493_);
lean_dec(v_idx_3489_);
if (v___x_3494_ == 0)
{
lean_dec(v_idx_3493_);
lean_dec(v_pos_3492_);
lean_dec_ref(v_config_3480_);
return v___x_3491_;
}
else
{
lean_object* v___x_3495_; 
lean_dec_ref(v___x_3491_);
v___x_3495_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3480_, v_pos_3492_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_dec(v_idx_3493_);
lean_dec_ref(v_config_3480_);
return v___x_3495_;
}
else
{
lean_object* v_pos_3496_; lean_object* v_idx_3497_; uint8_t v___x_3498_; 
v_pos_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_pos_3496_);
v_idx_3497_ = lean_ctor_get(v_pos_3496_, 1);
v___x_3498_ = lean_nat_dec_eq(v_idx_3493_, v_idx_3497_);
lean_dec(v_idx_3493_);
if (v___x_3498_ == 0)
{
lean_dec(v_pos_3496_);
lean_dec_ref(v_config_3480_);
return v___x_3495_;
}
else
{
lean_object* v___x_3499_; 
lean_dec_ref(v___x_3495_);
v___x_3499_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(v_config_3480_, v_pos_3496_);
return v___x_3499_;
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
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader(lean_object* v_config_3506_, lean_object* v_a_3507_){
_start:
{
lean_object* v___y_3509_; lean_object* v___x_3512_; 
v___x_3512_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_3506_, v_a_3507_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v_pos_3513_; lean_object* v_res_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3587_; 
v_pos_3513_ = lean_ctor_get(v___x_3512_, 0);
v_res_3514_ = lean_ctor_get(v___x_3512_, 1);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3516_ = v___x_3512_;
v_isShared_3517_ = v_isSharedCheck_3587_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_res_3514_);
lean_inc(v_pos_3513_);
lean_dec(v___x_3512_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3587_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v_port_3519_; lean_object* v___y_3520_; lean_object* v_pos_3534_; lean_object* v_array_3536_; lean_object* v_idx_3537_; lean_object* v___x_3538_; uint8_t v___x_3539_; lean_object* v___y_3541_; lean_object* v_array_3542_; lean_object* v_idx_3543_; 
v_array_3536_ = lean_ctor_get(v_pos_3513_, 0);
v_idx_3537_ = lean_ctor_get(v_pos_3513_, 1);
v___x_3538_ = lean_byte_array_size(v_array_3536_);
v___x_3539_ = lean_nat_dec_lt(v_idx_3537_, v___x_3538_);
if (v___x_3539_ == 0)
{
v_pos_3534_ = v_pos_3513_;
goto v___jp_3533_;
}
else
{
uint8_t v___x_3547_; uint8_t v___x_3548_; uint8_t v___x_3549_; 
v___x_3547_ = lean_byte_array_fget(v_array_3536_, v_idx_3537_);
v___x_3548_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_3549_ = lean_uint8_dec_eq(v___x_3547_, v___x_3548_);
if (v___x_3549_ == 0)
{
v_pos_3534_ = v_pos_3513_;
goto v___jp_3533_;
}
else
{
if (v___x_3549_ == 0)
{
v_pos_3534_ = v_pos_3513_;
goto v___jp_3533_;
}
else
{
if (v___x_3539_ == 0)
{
lean_object* v___x_3550_; lean_object* v___x_3551_; 
lean_del_object(v___x_3516_);
lean_dec(v_res_3514_);
v___x_3550_ = lean_box(0);
v___x_3551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3551_, 0, v_pos_3513_);
lean_ctor_set(v___x_3551_, 1, v___x_3550_);
return v___x_3551_;
}
else
{
if (v___x_3549_ == 0)
{
lean_object* v___x_3552_; lean_object* v___x_3553_; 
lean_del_object(v___x_3516_);
lean_dec(v_res_3514_);
v___x_3552_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
v___x_3553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3553_, 0, v_pos_3513_);
lean_ctor_set(v___x_3553_, 1, v___x_3552_);
return v___x_3553_;
}
else
{
lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3584_; 
lean_inc(v_idx_3537_);
lean_inc_ref(v_array_3536_);
v_isSharedCheck_3584_ = !lean_is_exclusive(v_pos_3513_);
if (v_isSharedCheck_3584_ == 0)
{
lean_object* v_unused_3585_; lean_object* v_unused_3586_; 
v_unused_3585_ = lean_ctor_get(v_pos_3513_, 1);
lean_dec(v_unused_3585_);
v_unused_3586_ = lean_ctor_get(v_pos_3513_, 0);
lean_dec(v_unused_3586_);
v___x_3555_ = v_pos_3513_;
v_isShared_3556_ = v_isSharedCheck_3584_;
goto v_resetjp_3554_;
}
else
{
lean_dec(v_pos_3513_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3584_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v_it_x27_3560_; 
v___x_3557_ = lean_unsigned_to_nat(1u);
v___x_3558_ = lean_nat_add(v_idx_3537_, v___x_3557_);
lean_dec(v_idx_3537_);
lean_inc(v___x_3558_);
lean_inc_ref(v_array_3536_);
if (v_isShared_3556_ == 0)
{
lean_ctor_set(v___x_3555_, 1, v___x_3558_);
v_it_x27_3560_ = v___x_3555_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_array_3536_);
lean_ctor_set(v_reuseFailAlloc_3583_, 1, v___x_3558_);
v_it_x27_3560_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
uint8_t v___y_3562_; uint8_t v___x_3577_; 
v___x_3577_ = lean_nat_dec_lt(v___x_3558_, v___x_3538_);
if (v___x_3577_ == 0)
{
v___y_3541_ = v_it_x27_3560_;
v_array_3542_ = v_array_3536_;
v_idx_3543_ = v___x_3558_;
goto v___jp_3540_;
}
else
{
uint8_t v___x_3578_; uint8_t v___x_3579_; uint8_t v___x_3580_; 
v___x_3578_ = lean_byte_array_fget(v_array_3536_, v___x_3558_);
v___x_3579_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3);
v___x_3580_ = lean_uint8_dec_le(v___x_3579_, v___x_3578_);
if (v___x_3580_ == 0)
{
v___y_3562_ = v___x_3580_;
goto v___jp_3561_;
}
else
{
uint8_t v___x_3581_; uint8_t v___x_3582_; 
v___x_3581_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4);
v___x_3582_ = lean_uint8_dec_le(v___x_3578_, v___x_3581_);
v___y_3562_ = v___x_3582_;
goto v___jp_3561_;
}
}
v___jp_3561_:
{
if (v___y_3562_ == 0)
{
v___y_3541_ = v_it_x27_3560_;
v_array_3542_ = v_array_3536_;
v_idx_3543_ = v___x_3558_;
goto v___jp_3540_;
}
else
{
if (v___x_3539_ == 0)
{
v___y_3541_ = v_it_x27_3560_;
v_array_3542_ = v_array_3536_;
v_idx_3543_ = v___x_3558_;
goto v___jp_3540_;
}
else
{
lean_object* v___x_3563_; 
lean_dec(v___x_3558_);
lean_dec_ref(v_array_3536_);
v___x_3563_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v_it_x27_3560_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v_pos_3564_; lean_object* v_res_3565_; lean_object* v___x_3566_; uint16_t v___x_3567_; 
v_pos_3564_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_pos_3564_);
v_res_3565_ = lean_ctor_get(v___x_3563_, 1);
lean_inc(v_res_3565_);
lean_dec_ref(v___x_3563_);
v___x_3566_ = lean_alloc_ctor(2, 0, 2);
v___x_3567_ = lean_unbox(v_res_3565_);
lean_dec(v_res_3565_);
lean_ctor_set_uint16(v___x_3566_, 0, v___x_3567_);
v_port_3519_ = v___x_3566_;
v___y_3520_ = v_pos_3564_;
goto v___jp_3518_;
}
else
{
lean_object* v_pos_3568_; lean_object* v_err_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_del_object(v___x_3516_);
lean_dec(v_res_3514_);
v_pos_3568_ = lean_ctor_get(v___x_3563_, 0);
v_err_3569_ = lean_ctor_get(v___x_3563_, 1);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3563_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_err_3569_);
lean_inc(v_pos_3568_);
lean_dec(v___x_3563_);
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
}
}
}
}
}
}
}
}
v___jp_3518_:
{
lean_object* v_array_3521_; lean_object* v_idx_3522_; lean_object* v___x_3523_; uint8_t v___x_3524_; 
v_array_3521_ = lean_ctor_get(v___y_3520_, 0);
v_idx_3522_ = lean_ctor_get(v___y_3520_, 1);
v___x_3523_ = lean_byte_array_size(v_array_3521_);
v___x_3524_ = lean_nat_dec_lt(v_idx_3522_, v___x_3523_);
if (v___x_3524_ == 0)
{
lean_object* v___x_3525_; lean_object* v___x_3527_; 
v___x_3525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3525_, 0, v_res_3514_);
lean_ctor_set(v___x_3525_, 1, v_port_3519_);
if (v_isShared_3517_ == 0)
{
lean_ctor_set(v___x_3516_, 1, v___x_3525_);
lean_ctor_set(v___x_3516_, 0, v___y_3520_);
v___x_3527_ = v___x_3516_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___y_3520_);
lean_ctor_set(v_reuseFailAlloc_3528_, 1, v___x_3525_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
else
{
lean_object* v___x_3529_; lean_object* v___x_3531_; 
lean_dec(v_port_3519_);
lean_dec(v_res_3514_);
v___x_3529_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__3));
if (v_isShared_3517_ == 0)
{
lean_ctor_set_tag(v___x_3516_, 1);
lean_ctor_set(v___x_3516_, 1, v___x_3529_);
lean_ctor_set(v___x_3516_, 0, v___y_3520_);
v___x_3531_ = v___x_3516_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___y_3520_);
lean_ctor_set(v_reuseFailAlloc_3532_, 1, v___x_3529_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
v___jp_3533_:
{
lean_object* v___x_3535_; 
v___x_3535_ = lean_box(0);
v_port_3519_ = v___x_3535_;
v___y_3520_ = v_pos_3534_;
goto v___jp_3518_;
}
v___jp_3540_:
{
lean_object* v___x_3544_; uint8_t v___x_3545_; 
v___x_3544_ = lean_byte_array_size(v_array_3542_);
lean_dec_ref(v_array_3542_);
v___x_3545_ = lean_nat_dec_lt(v_idx_3543_, v___x_3544_);
lean_dec(v_idx_3543_);
if (v___x_3545_ == 0)
{
if (v___x_3539_ == 0)
{
lean_del_object(v___x_3516_);
lean_dec(v_res_3514_);
v___y_3509_ = v___y_3541_;
goto v___jp_3508_;
}
else
{
lean_object* v___x_3546_; 
v___x_3546_ = lean_box(1);
v_port_3519_ = v___x_3546_;
v___y_3520_ = v___y_3541_;
goto v___jp_3518_;
}
}
else
{
lean_del_object(v___x_3516_);
lean_dec(v_res_3514_);
v___y_3509_ = v___y_3541_;
goto v___jp_3508_;
}
}
}
}
else
{
lean_object* v_pos_3588_; lean_object* v_err_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3596_; 
v_pos_3588_ = lean_ctor_get(v___x_3512_, 0);
v_err_3589_ = lean_ctor_get(v___x_3512_, 1);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3591_ = v___x_3512_;
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_err_3589_);
lean_inc(v_pos_3588_);
lean_dec(v___x_3512_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3594_; 
if (v_isShared_3592_ == 0)
{
v___x_3594_ = v___x_3591_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_pos_3588_);
lean_ctor_set(v_reuseFailAlloc_3595_, 1, v_err_3589_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
v___jp_3508_:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3510_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__1));
v___x_3511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3511_, 0, v___y_3509_);
lean_ctor_set(v___x_3511_, 1, v___x_3510_);
return v___x_3511_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader___boxed(lean_object* v_config_3597_, lean_object* v_a_3598_){
_start:
{
lean_object* v_res_3599_; 
v_res_3599_ = l_Std_Http_URI_Parser_parseHostHeader(v_config_3597_, v_a_3598_);
lean_dec_ref(v_config_3597_);
return v_res_3599_;
}
}
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec_ByteArray(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_URI_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_URI_Config(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Http_Data_URI_Parser(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
res = runtime_initialize_Std_Internal_Http_Data_URI_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_URI_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Http_Data_URI_Parser(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Std_Internal_Parsec(uint8_t builtin);
lean_object* initialize_Std_Internal_Parsec_ByteArray(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_URI_Basic(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_URI_Config(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Http_Data_URI_Parser(uint8_t builtin) {
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
res = initialize_Std_Internal_Http_Data_URI_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_URI_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_URI_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Http_Data_URI_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Http_Data_URI_Parser(builtin);
}
#ifdef __cplusplus
}
#endif
